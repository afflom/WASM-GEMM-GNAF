//! `xtask independence` -- the declarative side of a reflection theorem must not
//! be defined through, or proved through, the executable side.
//!
//! SPEC section 7.3 asks for `decode_sound`, `decode_complete` and
//! `validate_iff_declarative` as REFLECTION theorems: an executable procedure
//! agrees with an independently stated declarative relation. The whole content
//! is the independence. If the declarative relation is the executable one in
//! disguise, the theorem degenerates -- at best to `Bool = true <-> Bool = true`,
//! at worst to `rfl` -- and proves nothing about the pinned format.
//!
//! Four external audits said the repository's three front-end theorems were
//! circular. They were right, and nothing in the gate could see it: the
//! STATEMENTS match SPEC exactly, so `xtask signature` binds them, and the axiom
//! closure is clean, so `xtask axioms` passes them. An adversarial review
//! finally traced it through the proof terms:
//!
//! * `Wasm.DeclarativelyValid` is a conjunction of the executable checker's own
//!   booleans -- `Module.checkClosed m = true`, `checkMems`, `checkGlobal`,
//!   `checkTag`, `exportsMemory`, `checkGemmExport`, `checkStart`, `checkTypes`,
//!   `checkExports` -- with only the function-body conjunct stated inductively.
//!   `Wasm.validate_iff_declarative` is therefore very nearly a tautology.
//! * `Wasm.decode_sound` is proved as
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
    Entry {
        required: "WasmGemmGnaf.Wasm.decode_sound",
        declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
        forbidden: &[
            "WasmGemmGnaf.Wasm.encode",
            "WasmGemmGnaf.Wasm.decode_is_encode",
            "WasmGemmGnaf.Wasm.encode_decode_roundtrip",
            "declarativeBinaryRelation_iff_encode",
        ],
        why: "a decoder proved inverse to its own encoder says nothing about the pinned \
              binary format",
    },
    Entry {
        required: "WasmGemmGnaf.Wasm.decode_complete",
        declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
        forbidden: &[
            "WasmGemmGnaf.Wasm.encode",
            "WasmGemmGnaf.Wasm.decode_is_encode",
            "WasmGemmGnaf.Wasm.encode_decode_roundtrip",
            "declarativeBinaryRelation_iff_encode",
        ],
        why: "same: completeness against one's own encoder is a round-trip lemma, not a \
              statement about Core 3.0",
    },
    Entry {
        required: "WasmGemmGnaf.Wasm.validate_iff_declarative",
        declarative: "WasmGemmGnaf.Wasm.DeclarativelyValid",
        forbidden: &[
            "WasmGemmGnaf.Wasm.validate",
            "WasmGemmGnaf.Wasm.Module.checkClosed",
            "WasmGemmGnaf.Wasm.Module.checkMems",
            "WasmGemmGnaf.Wasm.Module.checkGlobal",
            "WasmGemmGnaf.Wasm.Module.checkTag",
            "WasmGemmGnaf.Wasm.Module.checkTypes",
            "WasmGemmGnaf.Wasm.Module.checkExports",
            "WasmGemmGnaf.Wasm.Module.checkStart",
            "WasmGemmGnaf.Wasm.Module.exportsMemory",
            "WasmGemmGnaf.Wasm.Module.checkGemmExport",
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
        for (label, kind) in [(entry.declarative, "definition"), (entry.required, "proof term")] {
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
                if block.contains(name) {
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

    Ok(Report { checked: entries.len(), findings })
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
        if line.starts_with("theorem ") || line.starts_with("def ") || line.starts_with("inductive ")
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
    Ok(if report.is_ok() { Outcome::Pass } else { Outcome::Fail })
}
