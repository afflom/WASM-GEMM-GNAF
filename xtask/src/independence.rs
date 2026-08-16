//! `xtask independence` -- the declarative side of a reflection theorem must not
//! be defined through, or proved through, the executable side.
//!
//! SPEC section 7.3 asks for `decode_sound`, `decode_complete` and
//! `validate_bool_iff` as REFLECTION theorems: an executable procedure
//! agrees with an independently stated declarative relation. The whole content
//! is the independence. If the declarative relation is the executable one in
//! disguise, the theorem degenerates -- at best to `Bool = true <-> Bool = true`,
//! at worst to `rfl` -- and proves nothing about the pinned format.
//!
//! Four external audits found that the repository's former three front-end
//! theorems were circular, and nothing in the gate could see it. The public
//! decoder theorems have since been repaired against the independent amended
//! Core grammar; the legacy subset validator remains circular and uncredited.
//! The audit originally traced the defects through these proof terms:
//!
//! * `Wasm.DeclarativelyValid` is a conjunction of the executable checker's own
//!   booleans -- `Module.checkClosed m = true`, `checkMems`, `checkGlobal`,
//!   `checkTag`, `exportsMemory`, `checkGemmExport`, `checkStart`, `checkTypes`,
//!   `checkExports` -- with only the function-body conjunct stated inductively.
//!   `Wasm.validate_bool_iff` is therefore very nearly a tautology.
//! * the former subset `Wasm.decode_sound` was proved as
//!   `(declarativeBinaryRelation_iff_encode ..).mpr (decode_is_encode h)`, and
//!   that lemma equates the "declarative" relation with `bytes = encode module`.
//!   A decoder proved inverse to its own encoder says nothing about Core 3.0.
//!
//! This check reads the COMPILED environment -- `#print` on the definition and
//! on the theorem, so the proof TERM is inspected, not the docstring -- and
//! refuses to credit a declaration whose declarative side, or whose proof,
//! mentions the executable side. `xtask claims required` demotes anything it
//! rejects, so the ledger falls rather than the finding being filed away.
//!
//! It is not a general circularity detector; no such thing exists. It is a
//! specific, checkable statement of independence for the declarations where
//! independence is the entire content, and each entry says which SPEC clause
//! makes it load-bearing.

use std::path::{Path, PathBuf};

use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "7.3";
const PROBE: &str = ".independence_probe.lean";

/// One reflection obligation: a required declaration, the declarative object it
/// is stated over, and the executable names neither may mention.
pub struct Entry {
    /// The SPEC section 15 name whose credit depends on this.
    pub required: &'static str,
    /// The declarative relation the theorem is stated against.
    pub declarative: &'static str,
    /// Executable names that must not appear in the declarative definition, nor
    /// in the theorem's proof term.
    pub forbidden: &'static [&'static str],
    /// Why independence is the content, in one line, printed on failure.
    pub why: &'static str,
}

const ENTRIES: &[Entry] = &[
    // The subset codec that made these two circular is now `Wasm.Subset.*`,
    // and `Wasm.decode` / `Wasm.DeclarativeBinaryRelation` are the Core 3.0
    // decoder and the amended grammar `Wasm.Core.Binary.BmoduleA`. Every
    // forbidden name below is spelled at its CURRENT fully qualified spelling:
    // a stale spelling would make the obligation pass for want of a match,
    // which is how `declarativeBinaryRelation_iff_encode` -- written here
    // unqualified, and therefore never matched, because `.` is an identifier
    // character -- was dead before this tranche.
    Entry {
        required: "WasmGemmGnaf.Wasm.decode_sound",
        declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
        forbidden: &[
            "WasmGemmGnaf.Wasm.Subset.encode",
            "WasmGemmGnaf.Wasm.Subset.encodeList",
            "WasmGemmGnaf.Wasm.Subset.decode",
            "WasmGemmGnaf.Wasm.Subset.decode_is_encode",
            "WasmGemmGnaf.Wasm.Subset.encode_decode_roundtrip",
            "WasmGemmGnaf.Wasm.Subset.declarativeBinaryRelation_iff_encode",
        ],
        why: "a decoder proved inverse to its own encoder says nothing about the amended \
              binary format",
    },
    Entry {
        required: "WasmGemmGnaf.Wasm.decode_complete",
        declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
        forbidden: &[
            "WasmGemmGnaf.Wasm.Subset.encode",
            "WasmGemmGnaf.Wasm.Subset.encodeList",
            "WasmGemmGnaf.Wasm.Subset.decode",
            "WasmGemmGnaf.Wasm.Subset.decode_is_encode",
            "WasmGemmGnaf.Wasm.Subset.encode_decode_roundtrip",
            "WasmGemmGnaf.Wasm.Subset.declarativeBinaryRelation_iff_encode",
        ],
        why: "same: completeness against one's own encoder is a round-trip lemma, not a \
              statement about Core 3.0",
    },
    Entry {
        required: "WasmGemmGnaf.Wasm.validate_bool_iff",
        declarative: "WasmGemmGnaf.Wasm.DeclarativelyValid",
        // `WasmGemmGnaf.Wasm.validate` is deliberately NOT here. A reflection
        // theorem's STATEMENT necessarily names the executable procedure it is
        // about -- `validate m = true <-> ...` -- so its proof term mentions it
        // unavoidably, and forbidding it would make the obligation unpassable
        // for a theorem that had been repaired. The circularity signal is the
        // checker's INTERNALS appearing in the declarative side, which is what
        // the rest of this list is, and which `DeclarativelyValid` trips.
        forbidden: &[
            "WasmGemmGnaf.Wasm.Subset.Module.checkClosed",
            "WasmGemmGnaf.Wasm.Subset.Module.checkMems",
            "WasmGemmGnaf.Wasm.Subset.Module.checkGlobal",
            "WasmGemmGnaf.Wasm.Subset.Module.checkTag",
            "WasmGemmGnaf.Wasm.Subset.Module.checkTypes",
            "WasmGemmGnaf.Wasm.Subset.Module.checkExports",
            "WasmGemmGnaf.Wasm.Subset.Module.checkStart",
            "WasmGemmGnaf.Wasm.Subset.Module.exportsMemory",
            "WasmGemmGnaf.Wasm.Subset.Module.checkGemmExport",
        ],
        why: "if the declarative judgment is the checker's own booleans, the biconditional \
              is `Bool = true <-> Bool = true`",
    },
];

pub struct Finding {
    pub required: String,
    pub detail: String,
}

pub struct Report {
    pub checked: usize,
    pub findings: Vec<Finding>,
}

impl Report {
    pub fn is_ok(&self) -> bool {
        self.findings.is_empty()
    }

    /// The SPEC 15 names this check refuses to credit, spelled as SPEC 15
    /// spells them -- `Wasm.decode_sound`, not the fully qualified Lean name.
    /// The entries above must be fully qualified so `#print` resolves them, and
    /// `xtask claims required` matches on SPEC's list, so the two spellings meet
    /// here rather than silently failing to match.
    pub fn rejected(&self) -> Vec<String> {
        let mut out: Vec<String> = self
            .findings
            .iter()
            .map(|f| f.required.trim_start_matches("WasmGemmGnaf.").to_string())
            .collect();
        out.sort();
        out.dedup();
        out
    }

    pub fn render(&self) -> String {
        let mut out = vec![format!(
            "reflection independence: {} obligation(s) checked against the compiled \
             environment",
            self.checked
        )];
        for finding in &self.findings {
            out.push(format!("  NOT INDEPENDENT {}", finding.required));
            out.push(format!("    {}", finding.detail));
        }
        if self.findings.is_empty() {
            out.push(
                "  every declarative relation is stated and proved without its executable \
                 counterpart"
                    .to_string(),
            );
        }
        out.join("\n")
    }
}

/// Ask the compiled environment for the definition and the proof term of every
/// reflection obligation, and look for the executable names in both.
pub fn report(root: &Path) -> Result<Report> {
    report_over(root, ENTRIES)
}

/// The same, over a caller-supplied table.
///
/// `M16` needs this: a falsifier that reimplemented the search would test its
/// own string matching, so it passes planted tables to the real function
/// instead. `M2`/`M13`/`M14`/`M15` all learned that lesson the hard way.
pub fn report_over(root: &Path, entries: &[Entry]) -> Result<Report> {
    let mut src = String::from("import WasmGemmGnaf\nset_option pp.fullNames true\n");
    for entry in entries {
        src.push_str(&format!("#print {}\n", entry.declarative));
        src.push_str(&format!("#print {}\n", entry.required));
    }
    let probe = crate::lean::probe_source(CLAUSE, root, &PathBuf::from(PROBE), &src)?;
    let output = probe.combined();

    // `#print X` emits a block that starts with a line naming X. Split on those
    // so a mention in one block is not blamed on another.
    let mut findings = Vec::new();
    for entry in entries {
        for (label, kind) in [
            (entry.declarative, "definition"),
            (entry.required, "proof term"),
        ] {
            let Some(block) = print_block(&output, label) else {
                return Err(SpecError::new(
                    CLAUSE,
                    format!(
                        "the compiled environment did not answer `#print {label}`; this check \
                         cannot pass for want of an answer:\n{}",
                        output.trim()
                    ),
                ));
            };
            for name in entry.forbidden {
                if mentions(block, name) {
                    findings.push(Finding {
                        required: entry.required.to_string(),
                        detail: format!(
                            "its {kind} `{label}` mentions the executable `{name}` -- {}",
                            entry.why
                        ),
                    });
                    break;
                }
            }
        }
    }

    Ok(Report {
        checked: entries.len(),
        findings,
    })
}

/// Whether `block` mentions the Lean constant `name` as a WHOLE identifier.
///
/// A plain substring test is wrong here and was wrong in the first version, in a
/// way that made one obligation permanently unpassable rather than merely
/// noisy: `WasmGemmGnaf.Wasm.validate` is a PREFIX of
/// `WasmGemmGnaf.Wasm.validate_bool_iff`, so the check fired on the
/// theorem's own name and would have gone on firing after the circularity was
/// repaired. Adversarial review caught it.
///
/// Lean identifiers are made of alphanumerics, `_`, `'` and `.`, so an
/// occurrence counts only when neither neighbour is one of those.
fn mentions(block: &str, name: &str) -> bool {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '.';
    let bytes = block.as_bytes();
    let mut from = 0usize;
    while let Some(offset) = block[from..].find(name) {
        let start = from + offset;
        let end = start + name.len();
        let before_ok = start == 0 || !is_ident(bytes[start - 1] as char);
        let after_ok = end >= bytes.len() || !is_ident(bytes[end] as char);
        if before_ok && after_ok {
            return true;
        }
        from = start + 1;
    }
    false
}

/// The text Lean printed for `#print name`, up to the next printed declaration.
fn print_block<'a>(output: &'a str, name: &str) -> Option<&'a str> {
    let start = output.find(name)?;
    let rest = &output[start..];
    // A `#print` block ends where the next one begins; `theorem`/`def` at column
    // zero is the marker Lean uses.
    let mut end = rest.len();
    for (index, _) in rest.match_indices('\n') {
        let line = &rest[index + 1..];
        if line.starts_with("theorem ")
            || line.starts_with("def ")
            || line.starts_with("inductive ")
        {
            end = index + 1;
            break;
        }
    }
    Some(&rest[..end])
}

pub fn run(root: &Path) -> Result<Outcome> {
    let report = report(root)?;
    println!("{}", report.render());
    Ok(if report.is_ok() {
        Outcome::Pass
    } else {
        Outcome::Fail
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_prefix_is_not_a_mention() {
        // The bug this test exists for: `...Wasm.validate` is a prefix of
        // `...Wasm.validate_bool_iff`, so a substring test fired on the
        // theorem's own name and made the obligation permanently unpassable.
        let block = "theorem WasmGemmGnaf.Wasm.validate_bool_iff : ...";
        assert!(!mentions(block, "WasmGemmGnaf.Wasm.validate"));
        assert!(mentions(block, "WasmGemmGnaf.Wasm.validate_bool_iff"));
    }

    #[test]
    fn a_real_mention_is_found() {
        let block = "theorem foo : ... := WasmGemmGnaf.Wasm.validate m";
        assert!(mentions(block, "WasmGemmGnaf.Wasm.validate"));
    }

    #[test]
    fn a_suffix_is_not_a_mention() {
        let block = "theorem foo : ... := MyWasmGemmGnaf.Wasm.validate m";
        assert!(!mentions(block, "WasmGemmGnaf.Wasm.validate"));
    }
}
