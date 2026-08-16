//! `xtask axioms` -- axiom closure audit. Replaces `Tools/axioms.py`.
//!
//! SPEC section 19: the decisive audit inspects the compiled environment, not
//! the source text. Source scanning can be fooled by a macro, an `attribute`,
//! or an import; `#print axioms` cannot, because it reports what the kernel
//! actually depended on.

use std::path::Path;

use crate::json::{self, Value};
use crate::lean::probe_axioms;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "19";
const PROBE: &str = ".axioms_probe.lean";
const REGISTRY: &str = "model/claims.json";

/// Axioms that would make a "proof" vacuous or compiler-trusting.
const FORBIDDEN: [&str; 3] = ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"];

pub fn run(root: &Path) -> Result<Outcome> {
    let path = Path::new(REGISTRY);
    let text = std::fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io("17", "cannot read the claim registry", path, e))?;
    let registry = json::parse("17", &text)?;

    let claims = registry
        .get("claims")
        .and_then(Value::as_array)
        .ok_or_else(|| SpecError::new("17", format!("{REGISTRY} has no `claims` array")))?;

    let mut proved = Vec::new();
    for claim in claims {
        if claim.get("level").and_then(Value::as_str) == Some("formalProof") {
            let id = claim
                .get("id")
                .and_then(Value::as_str)
                .unwrap_or("<unidentified claim>");
            proved.push(
                claim
                    .required_str("17", "leanDeclaration", &format!("claim {id}"))?
                    .to_string(),
            );
        }
    }

    if proved.is_empty() {
        println!("no formalProof claims");
        return Ok(Outcome::Pass);
    }

    // Import the ROOT module, not one layer of it: probing `Cost.Objective`
    // alone made every claim outside that import cone an `unknownIdentifier`,
    // so those claims were never actually audited.
    let result = probe_axioms(CLAUSE, root, PROBE, &proved)?;

    let stdout = result.stdout.trim();
    println!(
        "{}",
        if stdout.is_empty() {
            result.stderr.trim()
        } else {
            stdout
        }
    );

    let hits: Vec<&str> = FORBIDDEN
        .iter()
        .copied()
        .filter(|b| result.stdout.contains(b))
        .collect();
    if !hits.is_empty() || !result.success {
        let listed = hits
            .iter()
            .map(|h| format!("'{h}'"))
            .collect::<Vec<_>>()
            .join(", ");
        println!();
        println!("FORBIDDEN AXIOM: [{listed}]");
        return Ok(Outcome::Fail);
    }

    println!();
    println!("axiom audit: clean (Lean core logical axioms only)");
    Ok(Outcome::Pass)
}
