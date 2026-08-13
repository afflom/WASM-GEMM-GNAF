//! `xtask sources scan` -- forbidden-construct scan. Replaces `Tools/scan.py`.
//!
//! SPEC section 19 bans `sorry`, `admit`, `native_decide`, project-declared
//! `axiom`s, and `unsafe`/`partial` definitions on the proof path. A plain text
//! search cannot express that: `sorry` appears legitimately in the doc comments
//! that explain the ban, and a gate that fires on its own documentation gets
//! switched off, which is the same failure as a gate that never fires. So the
//! scan runs over source with comments and string literals stripped.
//!
//! The decisive audit is still `#print axioms` over the compiled environment
//! (`xtask axioms`); this is defence in depth.

use std::path::{Path, PathBuf};

use crate::lean::{self, excerpt, splitlines};
use crate::repo::{lean_files, read_lossy};
use crate::spec::{Outcome, Result};

const CLAUSE: &str = "19";

pub fn run(targets: &[String]) -> Result<Outcome> {
    match report(targets)? {
        Ok(clean) => {
            println!("{clean}");
            Ok(Outcome::Pass)
        }
        Err(hits) => {
            println!("{hits}");
            Ok(Outcome::Fail)
        }
    }
}

/// The scan's verdict as text: `Ok` is the clean line, `Err` the violation
/// report. The gate quotes the report, so it is produced rather than printed.
pub fn report(targets: &[String]) -> Result<std::result::Result<String, String>> {
    let default = vec!["WasmGemmGnaf".to_string()];
    let targets = if targets.is_empty() { &default } else { targets };

    let mut hits = Vec::new();
    let mut scanned = 0usize;

    for target in targets {
        for path in collect(Path::new(target))? {
            scanned += 1;
            let code = lean::strip(&read_lossy(CLAUSE, &path)?);
            for (index, line) in splitlines(&code).iter().enumerate() {
                // One hit per violated rule, in SPEC order -- a line that is both
                // an `axiom` declaration and a placeholder breaks two promises and
                // should say so twice.
                for (violated, why) in [
                    (lean::has_placeholder(line), "placeholder"),
                    (lean::is_axiom_decl(line), "project-declared axiom"),
                    (lean::is_unsafe_or_partial_decl(line), "unsafe/partial"),
                ] {
                    if violated {
                        hits.push(format!(
                            "{}:{}: {}: {}",
                            path.display(),
                            index + 1,
                            why,
                            excerpt(line)
                        ));
                    }
                }
            }
        }
    }

    if !hits.is_empty() {
        let mut out = vec!["FORBIDDEN CONSTRUCT ON THE PROOF PATH (SPEC 19):".to_string()];
        out.extend(hits.iter().map(|hit| format!("  {hit}")));
        return Ok(Err(out.join("\n")));
    }
    Ok(Ok(format!(
        "forbidden-construct scan clean: {scanned} modules (comments and strings excluded)"
    )))
}

/// A target is either a single `.lean` file or a directory to walk.
fn collect(target: &Path) -> Result<Vec<PathBuf>> {
    if target.is_file() {
        return Ok(if target.extension().is_some_and(|e| e == "lean") {
            vec![target.to_path_buf()]
        } else {
            Vec::new()
        });
    }
    lean_files(CLAUSE, target)
}
