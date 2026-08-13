//! `xtask sources firewall` -- dependency firewall. Replaces `Tools/firewall.py`.
//!
//! SPEC section 10.1:
//!
//! > Foundation, Wasm, Gemm, Cost, and the extensional definitions in
//! > Universal/Competitor.lean, Correct.lean and Feasible.lean SHALL NOT import
//! > GNAF, Atlas, Artifact, Universal/LowerBound, Universal/Argmin, or Theorems.
//! > A source-and-environment gate SHALL reject an artifact-, selector-, or
//! > conclusion-dependent scope predicate.
//!
//! The point is that the competitor universe must be defined without reference
//! to the artifact it will be compared against. If `ProfileValid` could see the
//! selected artifact, `GlobalOptimal` would be a statement about a universe
//! built around its own answer. This makes that structurally impossible rather
//! than a convention someone remembers.

use std::path::Path;

use crate::lean::{import_target, splitlines};
use crate::repo::{lean_files, read_lossy, slash};
use crate::spec::{Outcome, Result};

const CLAUSE: &str = "10.1";

const PROTECTED: [&str; 7] = [
    "Foundation/",
    "Wasm/",
    "Gemm/",
    "Cost/",
    "Universal/Competitor.lean",
    "Universal/Correct.lean",
    "Universal/Feasible.lean",
];

const FORBIDDEN: [&str; 6] = [
    "WasmGemmGnaf.GNAF",
    "WasmGemmGnaf.Atlas",
    "WasmGemmGnaf.Artifact",
    "WasmGemmGnaf.Universal.LowerBound",
    "WasmGemmGnaf.Universal.Argmin",
    "WasmGemmGnaf.Theorems",
];

pub fn run() -> Result<Outcome> {
    match report()? {
        Ok(clean) => {
            println!("{clean}");
            Ok(Outcome::Pass)
        }
        Err(violated) => {
            println!("{violated}");
            Ok(Outcome::Fail)
        }
    }
}

/// The firewall's verdict as text: `Ok` is the clean line, `Err` the violation
/// report the gate quotes.
pub fn report() -> Result<std::result::Result<String, String>> {
    let mut violations = Vec::new();
    let mut checked = 0usize;

    for path in lean_files(CLAUSE, Path::new("WasmGemmGnaf"))? {
        let display = slash(&path);
        let Some(rel) = display.strip_prefix("WasmGemmGnaf/") else { continue };
        if !PROTECTED.iter().any(|p| rel == *p || rel.starts_with(p)) {
            continue;
        }
        checked += 1;

        let text = read_lossy(CLAUSE, &path)?;
        for (index, line) in splitlines(&text).iter().enumerate() {
            let Some(module) = import_target(line) else { continue };
            if FORBIDDEN
                .iter()
                .any(|bad| module == *bad || module.starts_with(&format!("{bad}.")))
            {
                violations.push(format!("{}:{}: imports {}", display, index + 1, module));
            }
        }
    }

    if !violations.is_empty() {
        let mut out = vec!["DEPENDENCY FIREWALL VIOLATED (SPEC 10.1):".to_string()];
        out.extend(violations.iter().map(|v| format!("  {v}")));
        out.push(String::new());
        out.push("The competitor universe must not depend on the artifact, the selector,".into());
        out.push("or any conclusion. Move the definition or invert the dependency.".into());
        return Ok(Err(out.join("\n")));
    }

    Ok(Ok(format!(
        "dependency firewall clean: {checked} protected modules, no forbidden import"
    )))
}
