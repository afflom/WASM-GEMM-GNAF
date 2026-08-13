//! `xtask sources releasepath` -- reject `noncomputable` on the release path.
//! Replaces `Tools/releasepath.py`.
//!
//! SPEC section 19 excludes noncomputable definitions from the product/proof
//! path, and SPEC section 6.3 requires executable proof-producing functions to
//! be computable. `xtask sources scan` deliberately ignores comments, so it
//! cannot see a `noncomputable def`; this checks declarations directly on the
//! modules that constitute the release path, reusing the same stripper so a
//! commented-out example does not fire.

use std::path::Path;

use crate::lean::{noncomputable_decl, splitlines, strip};
use crate::repo::{lean_files, read_lossy, slash};
use crate::spec::{Outcome, Result};

const CLAUSE: &str = "19";

const RELEASE_PATH: [&str; 3] = [
    "WasmGemmGnaf/Artifact/",
    "WasmGemmGnaf/Theorems/",
    "WasmGemmGnaf/Universal/",
];

pub fn run() -> Result<Outcome> {
    let mut hits = Vec::new();
    let mut scanned = 0usize;

    for base in RELEASE_PATH {
        for path in lean_files(CLAUSE, Path::new(base))? {
            scanned += 1;
            let code = strip(&read_lossy(CLAUSE, &path)?);
            for (index, line) in splitlines(&code).iter().enumerate() {
                if let Some((kind, name)) = noncomputable_decl(line) {
                    hits.push(format!(
                        "{}:{}: noncomputable {} {}",
                        slash(&path),
                        index + 1,
                        kind,
                        name
                    ));
                }
            }
        }
    }

    if !hits.is_empty() {
        println!("NONCOMPUTABLE ON THE RELEASE PATH (SPEC 19 / 6.3):");
        for hit in &hits {
            println!("  {hit}");
        }
        println!();
        println!("SPEC 19 excludes noncomputable definitions from the product/proof path.");
        println!("A classically-chosen evaluator decodes, validates, enumerates and");
        println!("executes nothing; it cannot stand in for the implemented explorer.");
        return Ok(Outcome::Fail);
    }

    println!("release path computable: {scanned} modules, no noncomputable definition");
    Ok(Outcome::Pass)
}
