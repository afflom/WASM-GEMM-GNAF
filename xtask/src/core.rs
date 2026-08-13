//! `xtask core [--list]` -- how much of the PINNED Core 3.0 front end the Lean
//! development actually covers.
//!
//! The problem this solves is not "is the transcription correct" -- the kernel
//! answers that. It is "is the transcription COMPLETE", which nothing answered
//! before. An external audit rejected `Wasm.decode_sound`, `Wasm.decode_complete`
//! and `Wasm.validate_iff_declarative` on exactly that ground: they were proved
//! about a hand-written subset codec and an i32-only validator, while the
//! released profile enables SIMD, GC and references, tables, bulk memory, tail
//! calls and exception handling. Nothing in the repository could contradict a
//! claim of coverage, so the claim survived.
//!
//! The checklist is not maintained here. It is EXTRACTED from the vendored
//! normative SpecTec sources at the pinned commit:
//!
//! * `specification/wasm-3.0/5.*-binary.*.spectec` -- every opcode production,
//!   e.g. `| 0x0C l:Blabelidx => BR l`;
//! * `specification/wasm-3.0/2.*-validation.*.spectec` -- every typing rule,
//!   e.g. `rule Instr_ok/select-impl:`;
//! * `specification/wasm-3.0/1.*-syntax.*.spectec` -- every syntax production.
//!
//! Lean claims an item by carrying a marker comment beside the declaration that
//! discharges it:
//!
//! ```lean
//! -- core-opcode: 0x0C BR
//! -- core-rule: Instr_ok/select-impl
//! -- core-syntax: reftype
//! ```
//!
//! A marker naming something the vendored sources do NOT define is a hard
//! failure, not a silent pass: that is the shape a fabricated coverage claim
//! would take. This is the same discipline as `xtask schema` (the authority JSON
//! supplies the list, the elaborator compares) and `xtask vendor` (the vendored
//! tree supplies the anchors) -- the tool never decides an obligation, it only
//! checks whether the kernel has one.
//!
//! Coverage here is NECESSARY, never sufficient. A marker says a case exists; it
//! says nothing about whether the case is right. Only `decode_sound` /
//! `decode_complete` / `validate_iff_declarative` say that, and they are proved
//! in Lean against the declarative relations, not here.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "7.1";

const SPECTEC_DIR: &str = "vendor/wasm-spec/specification/wasm-3.0";
const LEAN_DIR: &str = "WasmGemmGnaf";

/// The three kinds of obligation the pinned front end imposes.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Kind {
    Syntax,
    Opcode,
    Rule,
}

impl Kind {
    fn marker(self) -> &'static str {
        match self {
            Kind::Syntax => "core-syntax:",
            Kind::Opcode => "core-opcode:",
            Kind::Rule => "core-rule:",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Kind::Syntax => "syntax productions",
            Kind::Opcode => "binary opcode productions",
            Kind::Rule => "validation rules",
        }
    }

    /// The vendored sources that define this kind of obligation.
    fn sources(self) -> &'static [&'static str] {
        match self {
            Kind::Syntax => &[
                "1.1-syntax.values.spectec",
                "1.2-syntax.types.spectec",
                "1.3-syntax.instructions.spectec",
                "1.4-syntax.modules.spectec",
            ],
            Kind::Opcode => &[
                "5.1-binary.values.spectec",
                "5.2-binary.types.spectec",
                "5.3-binary.instructions.spectec",
                "5.4-binary.modules.spectec",
            ],
            Kind::Rule => &[
                "2.1-validation.types.spectec",
                "2.2-validation.subtyping.spectec",
                "2.3-validation.instructions.spectec",
                "2.4-validation.modules.spectec",
            ],
        }
    }
}

/// What the vendored sources require and what Lean claims, per kind.
pub struct Coverage {
    pub kind: Kind,
    /// Every obligation the vendored sources define, in source order.
    pub required: Vec<String>,
    /// Obligations Lean carries a marker for. Kept on the report so a caller can
    /// audit the claims themselves, not only the arithmetic over them.
    #[allow(dead_code)]
    pub claimed: Vec<String>,
    /// Required but unclaimed.
    pub missing: Vec<String>,
    /// Claimed but not defined by the vendored sources -- a fabricated claim.
    pub unknown: Vec<String>,
}

impl Coverage {
    pub fn covered(&self) -> usize {
        self.required.len() - self.missing.len()
    }

    fn render(&self, list: bool) -> Vec<String> {
        let mut out = vec![format!(
            "  {:<26} {} of {} covered",
            self.kind.label(),
            self.covered(),
            self.required.len()
        )];
        for name in &self.unknown {
            out.push(format!(
                "    FABRICATED `{} {name}` claims an item the vendored sources do not define",
                self.kind.marker()
            ));
        }
        if list {
            for name in &self.missing {
                out.push(format!("    MISSING {name}"));
            }
        }
        out
    }
}

/// Strip a SpecTec line comment (`;;`) so a commented-out production is not
/// counted as an obligation.
fn strip_comment(line: &str) -> &str {
    match line.find(";;") {
        Some(i) => &line[..i],
        None => line,
    }
}

/// Every `syntax <name>` production the vendored syntax sources declare.
///
/// SpecTec spells a variant family as `syntax absheaptype/syn`; the family name
/// before the slash is the obligation, since that is what a Lean type
/// corresponds to.
fn syntax_names(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = strip_comment(line);
        let Some(rest) = line.strip_prefix("syntax ") else { continue };
        let name = rest
            .split_whitespace()
            .next()
            .unwrap_or("")
            .split('/')
            .next()
            .unwrap_or("")
            .trim();
        if !name.is_empty() {
            out.push(name.to_string());
        }
    }
    out
}

/// Every `rule <Relation>/<case>:` the vendored validation sources declare.
fn rule_names(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = strip_comment(line);
        let Some(rest) = line.strip_prefix("rule ") else { continue };
        let name = rest.split(':').next().unwrap_or("").trim();
        if !name.is_empty() {
            out.push(name.to_string());
        }
    }
    out
}

/// Every opcode production of the vendored binary grammar, as
/// `<opcode bytes> <CONSTRUCTOR>`.
///
/// A production looks like
///
/// ```text
///   | 0x0C l:Blabelidx => BR l
///   | 0xFC 12:Bu32 y:Belemidx x:Btableidx => TABLE.INIT x y
///   | 0xFD 84:Bu32 => V128.NOT
/// ```
///
/// The identity taken is the leading hex byte, plus the immediate numeric
/// selector when the opcode is one of the multi-byte prefixes, plus the
/// constructor named on the right of `=>`. That is enough to distinguish every
/// production in the pinned grammar and is stable under renaming of the bound
/// variables.
fn opcode_productions(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = strip_comment(line).trim();
        let Some(rest) = line.strip_prefix('|') else { continue };
        let rest = rest.trim();
        if !rest.starts_with("0x") {
            continue;
        }
        let Some((lhs, rhs)) = rest.split_once("=>") else { continue };
        let mut tokens = lhs.split_whitespace();
        let Some(opcode) = tokens.next() else { continue };
        // A prefixed opcode carries its selector as the next `<n>:Bu32` token.
        let mut key = opcode.to_ascii_uppercase().replace("0X", "0x");
        if let Some(next) = tokens.next() {
            if let Some((num, _)) = next.split_once(':') {
                if num.bytes().all(|b| b.is_ascii_digit()) {
                    key.push(' ');
                    key.push_str(num);
                }
            }
        }
        let constructor = rhs.split_whitespace().next().unwrap_or("").trim();
        if constructor.is_empty() {
            continue;
        }
        out.push(format!("{key} {constructor}"));
    }
    out
}

/// Every marker of the given kind carried by the Lean tree.
fn lean_markers(root: &Path, kind: Kind) -> Result<Vec<String>> {
    let mut files = Vec::new();
    collect_lean(root, &mut files)?;
    files.sort();
    let mut out = Vec::new();
    for path in files {
        let text = crate::repo::read_lossy(CLAUSE, &path)?;
        for line in text.lines() {
            let Some(i) = line.find(kind.marker()) else { continue };
            // Only a comment may carry a marker; a marker inside code would be a
            // syntax error in Lean anyway, but be explicit about it.
            let before = &line[..i];
            if !before.contains("--") && !before.contains("/-") {
                continue;
            }
            let name = line[i + kind.marker().len()..].trim();
            let name = name.trim_end_matches("-/").trim();
            if !name.is_empty() {
                out.push(name.to_string());
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

fn collect_lean(dir: &Path, found: &mut Vec<PathBuf>) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read a Lean source directory", dir, e))?;
    for entry in entries {
        let entry =
            entry.map_err(|e| SpecError::io(CLAUSE, "cannot read a directory entry", dir, e))?;
        let path = entry.path();
        if path.is_dir() {
            collect_lean(&path, found)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            found.push(path);
        }
    }
    Ok(())
}

fn coverage(spectec_dir: &Path, lean_root: &Path, kind: Kind) -> Result<Coverage> {
    let mut required: Vec<String> = Vec::new();
    for file in kind.sources() {
        let path = spectec_dir.join(file);
        let text = crate::repo::read_lossy(CLAUSE, &path)?;
        let mut names = match kind {
            Kind::Syntax => syntax_names(&text),
            Kind::Rule => rule_names(&text),
            Kind::Opcode => opcode_productions(&text),
        };
        required.append(&mut names);
    }
    // The pinned grammar repeats a few productions across variant families; the
    // obligation is the SET.
    let mut seen: BTreeMap<String, ()> = BTreeMap::new();
    required.retain(|n| seen.insert(n.clone(), ()).is_none());

    if required.is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "{}: the vendored sources define no {}, so this check would pass for want of \
                 anything to check",
                spectec_dir.display(),
                kind.label()
            ),
        ));
    }

    let claimed = lean_markers(lean_root, kind)?;
    let missing: Vec<String> =
        required.iter().filter(|n| !claimed.contains(n)).cloned().collect();
    let unknown: Vec<String> =
        claimed.iter().filter(|n| !required.contains(n)).cloned().collect();

    Ok(Coverage { kind, required, claimed, missing, unknown })
}

pub struct Report {
    pub parts: Vec<Coverage>,
}

impl Report {
    pub fn is_ok(&self) -> bool {
        // A fabricated marker always fails. Incomplete coverage is REPORTED but
        // does not fail the gate on its own: SPEC 15's inventory is what decides
        // whether the three front-end theorems may be counted, and this number
        // is the evidence a reader needs to judge them.
        self.parts.iter().all(|p| p.unknown.is_empty())
    }

    pub fn render(&self, list: bool) -> String {
        let mut out =
            vec!["pinned Core 3.0 front end, checklist extracted from the vendored SpecTec sources"
                .to_string()];
        let mut total = 0usize;
        let mut done = 0usize;
        for part in &self.parts {
            out.extend(part.render(list));
            total += part.required.len();
            done += part.covered();
        }
        out.push(format!("  TOTAL                      {done} of {total} covered"));
        if done < total {
            out.push(
                "  SCOPE: coverage is NECESSARY, never sufficient -- a marker says a case \
                 exists, not that it is right. Correctness is decode_sound / decode_complete / \
                 validate_iff_declarative, proved in Lean."
                    .to_string(),
            );
        }
        out.join("\n")
    }
}

pub fn report(spectec_dir: &Path, lean_root: &Path) -> Result<Report> {
    Ok(Report {
        parts: vec![
            coverage(spectec_dir, lean_root, Kind::Syntax)?,
            coverage(spectec_dir, lean_root, Kind::Opcode)?,
            coverage(spectec_dir, lean_root, Kind::Rule)?,
        ],
    })
}

pub fn run(list: bool) -> Result<Outcome> {
    let report = report(Path::new(SPECTEC_DIR), Path::new(LEAN_DIR))?;
    println!("{}", report.render(list));
    Ok(if report.is_ok() { Outcome::Pass } else { Outcome::Fail })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_opcode_productions() {
        let src = "\
grammar Binstr/control : instr = ...
  | 0x0C l:Blabelidx => BR l
  | 0xFC 12:Bu32 y:Belemidx x:Btableidx => TABLE.INIT x y
  | 0x0E l*:Blist(Blabelidx) l_n:Blabelidx => BR_TABLE l* l_n
  ;; | 0x99 x:Bfuncidx => COMMENTED_OUT x
  | ...
";
        let got = opcode_productions(src);
        assert_eq!(got, vec!["0x0C BR", "0xFC 12 TABLE.INIT", "0x0E BR_TABLE"]);
    }

    #[test]
    fn reads_rule_names() {
        let src = "\
relation Instr_ok: context |- instr : instrtype
rule Instr_ok/nop:
  C |- NOP : eps -> eps
rule Instr_ok/select-impl:
;; rule Instr_ok/commented:
";
        assert_eq!(rule_names(src), vec!["Instr_ok/nop", "Instr_ok/select-impl"]);
    }

    #[test]
    fn reads_syntax_names_collapsing_variant_families() {
        let src = "\
syntax numtype hint(desc \"number type\") =
syntax absheaptype/syn hint(desc \"abstract heap type\") =
syntax absheaptype/sem =
;; syntax commented =
";
        assert_eq!(syntax_names(src), vec!["numtype", "absheaptype", "absheaptype"]);
    }

    #[test]
    fn a_marker_must_sit_in_a_comment() {
        let scratch = std::env::temp_dir().join("wgg-core-marker-test");
        let _ = std::fs::remove_dir_all(&scratch);
        std::fs::create_dir_all(&scratch).unwrap();
        std::fs::write(
            scratch.join("A.lean"),
            "-- core-rule: Instr_ok/nop\ndef notAMarker := \"core-rule: Instr_ok/drop\"\n",
        )
        .unwrap();
        let got = lean_markers(&scratch, Kind::Rule).unwrap();
        let _ = std::fs::remove_dir_all(&scratch);
        assert_eq!(got, vec!["Instr_ok/nop"]);
    }
}
