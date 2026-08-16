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
const GENERATED_BINDINGS: &str = "WasmGemmGnaf/Wasm/CoreAuthorityBindings.lean";

/// The five kinds of obligation the pinned Core semantics imposes.
///
/// `Exec` was absent from the first version of this checker, and an external
/// audit was right to name the omission: measuring the binary format and the
/// typing rules while leaving execution, instantiation and allocation unmeasured
/// understates the job by a quarter.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Kind {
    Syntax,
    Opcode,
    Rule,
    Exec,
    /// Auxiliary functions the pinned numerics sources define BY EQUATION.
    ///
    /// Added after the execution transcription disclosed that the vector
    /// operator semantics of `3.2` were left as fields of a parameter record
    /// while the ~30 vector step rules that call them were transcribed and
    /// counted. Counting rules alone made that invisible: a step relation whose
    /// SIMD operators are uninterpreted is quantified over every interpretation,
    /// which is not the pinned semantics however many rules it has.
    ///
    /// `hint(builtin)` declarations are deliberately NOT obligations. The pinned
    /// source declares 74 of them and gives no equations, so a transcription of
    /// these files cannot define what these files do not define; those are
    /// legitimately parameters.
    Aux,
}

impl Kind {
    fn marker(self) -> &'static str {
        match self {
            Kind::Syntax => "core-syntax:",
            Kind::Opcode => "core-opcode:",
            Kind::Rule => "core-rule:",
            Kind::Exec => "core-exec:",
            Kind::Aux => "core-def:",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Kind::Syntax => "syntax productions",
            Kind::Opcode => "binary opcode productions",
            Kind::Rule => "validation rules",
            Kind::Exec => "execution rules",
            Kind::Aux => "numerics definitions",
        }
    }

    fn lean_ctor(self) -> &'static str {
        match self {
            Kind::Syntax => "syntax",
            Kind::Opcode => "opcode",
            Kind::Rule => "validation",
            Kind::Exec => "execution",
            Kind::Aux => "numerics",
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
            // Execution, instantiation, allocation and the runtime type rules.
            // `4.4-execution.modules.spectec` is where instantiation and
            // allocation live; `3.*-numerics` are the scalar and vector
            // operator semantics the step rules call out to.
            Kind::Exec => &[
                "3.1-numerics.scalar.spectec",
                "3.2-numerics.vector.spectec",
                "4.0-execution.configurations.spectec",
                "4.1-execution.values.spectec",
                "4.2-execution.types.spectec",
                "4.3-execution.instructions.spectec",
                "4.4-execution.modules.spectec",
            ],
            Kind::Aux => &["3.1-numerics.scalar.spectec", "3.2-numerics.vector.spectec"],
        }
    }
}

fn lean_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Mechanically render the complete extracted inventory as a Lean module.
///
/// Each generated declaration is a definitional alias of the declaration to
/// which the source marker is attached. Consequently the finite map used by
/// `Wasm.profile_matches_pinned_revision` is kernel-connected to the actual
/// decoder/validator/runtime declaration rather than to an unchecked string.
fn generated_bindings(report: &Report) -> Result<String> {
    if !report.is_ok() || !report.complete() {
        return Err(SpecError::new(
            CLAUSE,
            "cannot generate the Core authority map from an incomplete or faulty inventory",
        ));
    }

    let mut rows: Vec<(Kind, &str, &Marker)> = Vec::new();
    for part in &report.parts {
        for item in &part.required {
            let matches: Vec<&Marker> = part
                .claimed
                .iter()
                .filter(|marker| &marker.item == item)
                .collect();
            if matches.len() != 1 {
                return Err(SpecError::new(
                    CLAUSE,
                    format!(
                        "{} `{item}` has {} attached declarations; the generated map requires exactly one",
                        part.kind.label(),
                        matches.len()
                    ),
                ));
            }
            rows.push((part.kind, item, matches[0]));
        }
    }

    let mut declarations: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (_, item, marker) in &rows {
        declarations
            .entry(marker.declaration.as_str())
            .or_default()
            .push(item);
    }
    let duplicates: Vec<String> = declarations
        .into_iter()
        .filter(|(_, items)| items.len() > 1)
        .map(|(declaration, items)| format!("`{declaration}`: {}", items.join(", ")))
        .collect();
    if !duplicates.is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "distinct Core obligations share attached declarations:\n{}",
                duplicates.join("\n")
            ),
        ));
    }

    let mut out = String::new();
    out.push_str("/-\n");
    out.push_str("  GENERATED by `xtask core --generate`; do not edit by hand.\n\n");
    out.push_str("  The source inventory is extracted from the pinned SpecTec files. Every\n");
    out.push_str("  `rN` below is definitionally the unique Lean declaration carrying that\n");
    out.push_str("  obligation's coverage marker. `just core` regenerates this text in\n");
    out.push_str("  memory, compares it byte-for-byte, and asks Lean to elaborate every alias.\n");
    out.push_str("-/\n");
    out.push_str("import WasmGemmGnaf.Wasm.Core.BinaryGrammar\n");
    out.push_str("import WasmGemmGnaf.Wasm.Core.Validation.Modules\n");
    out.push_str("import WasmGemmGnaf.Wasm.Core.Execution\n\n");
    out.push_str("set_option autoImplicit false\n");
    out.push_str("set_option maxRecDepth 10000\n\n");
    out.push_str("namespace WasmGemmGnaf.Wasm.Core.AuthorityBindings\n\n");
    for (index, (_, _, marker)) in rows.iter().enumerate() {
        out.push_str(&format!("def r{index} := @{}\n", marker.declaration));
    }
    out.push_str("\nend WasmGemmGnaf.Wasm.Core.AuthorityBindings\n\n");
    out.push_str("namespace WasmGemmGnaf.Wasm\n\n");
    out.push_str("inductive CoreAuthorityKind\n");
    out.push_str("  | syntax | opcode | validation | execution | numerics\n");
    out.push_str("  deriving DecidableEq, Repr, Inhabited\n\n");
    out.push_str("structure CoreAuthoritySource where\n");
    out.push_str("  kind : CoreAuthorityKind\n");
    out.push_str("  item : String\n");
    out.push_str("  authorityAnchor : String\n");
    out.push_str("  originalDeclaration : String\n");
    out.push_str("  markerLocation : String\n");
    out.push_str("  rejectedByProfile : Bool\n");
    out.push_str("  deriving DecidableEq, Repr, Inhabited\n\n");
    out.push_str("def pinnedCoreAuthoritySources : List CoreAuthoritySource :=\n  [");
    for (index, (kind, item, marker)) in rows.iter().enumerate() {
        if index > 0 {
            out.push_str("\n  , ");
        }
        let rejected = marker.declaration.contains("Relaxed") || item.starts_with("irelaxed_");
        out.push_str(&format!(
            "{{ kind := .{}, item := {}, authorityAnchor := {}, originalDeclaration := {}, markerLocation := {}, rejectedByProfile := {} }}",
            kind.lean_ctor(),
            lean_string(item),
            lean_string(&format!("spectec:{}:{item}", kind.lean_ctor())),
            lean_string(&marker.declaration),
            lean_string(&marker.location),
            rejected
        ));
    }
    out.push_str(" ]\n\n");
    out.push_str(&format!(
        "theorem pinnedCoreAuthoritySources_length :\n    pinnedCoreAuthoritySources.length = {} := rfl\n\n",
        rows.len()
    ));
    out.push_str("end WasmGemmGnaf.Wasm\n");
    Ok(out)
}

/// What the vendored sources require and what Lean claims, per kind.
pub struct Coverage {
    pub kind: Kind,
    /// Every obligation the vendored sources define, in source order.
    pub required: Vec<String>,
    /// Obligations Lean carries a marker for, each bound to its declaration.
    pub claimed: Vec<Marker>,
    /// Required but unclaimed.
    pub missing: Vec<String>,
    /// Claimed but not defined by the vendored sources -- a fabricated claim.
    pub unknown: Vec<String>,
    /// Markers that are attached to no declaration at all.
    pub unattached: Vec<String>,
    /// Markers whose declaration does not exist in the COMPILED environment.
    pub unelaborated: Vec<String>,
}

impl Coverage {
    pub fn covered(&self) -> usize {
        self.required.len() - self.missing.len()
    }

    /// Every reason this kind's coverage claim is not sound.
    fn faults(&self) -> usize {
        self.unknown.len() + self.unattached.len() + self.unelaborated.len()
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
        for note in &self.unattached {
            out.push(format!("    UNATTACHED {note}"));
        }
        for note in &self.unelaborated {
            out.push(format!("    UNELABORATED {note}"));
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

/// Remove SpecTec block comments `(; … ;)`, keeping newlines so line-oriented
/// extraction still sees the original line structure.
///
/// Without this the checklist counted commented-out rules as obligations.
/// `2.3-validation.instructions.spectec` block-comments out `rule Instr_ok/load`
/// and `rule Instr_ok/store` — the pinned spec's own superseded forms, replaced
/// by the `-val` / `-pack` pairs below them — so the validation denominator read
/// 258 when the honest number is 256. An adversarial review found it; the two
/// rules are not obligations and no Lean declaration should claim them.
///
/// Nesting is honoured: SpecTec allows `(; (; … ;) ;)`.
fn strip_block_comments(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut depth = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'(' && i + 1 < bytes.len() && bytes[i + 1] == b';' {
            depth += 1;
            i += 2;
            continue;
        }
        if depth > 0 && bytes[i] == b';' && i + 1 < bytes.len() && bytes[i + 1] == b')' {
            depth -= 1;
            i += 2;
            continue;
        }
        if depth == 0 {
            out.push(bytes[i] as char);
        } else if bytes[i] == b'\n' {
            // Keep the line structure so nothing downstream shifts.
            out.push('\n');
        }
        i += 1;
    }
    out
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
        let Some(rest) = line.strip_prefix("syntax ") else {
            continue;
        };
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

/// Every auxiliary function the pinned numerics sources define BY EQUATION.
///
/// A `def $f(...) : T` line declares one; a following `def $f hint(builtin)`
/// says the pinned source gives no equations for it. Only the ones it does
/// define are obligations -- a transcription cannot define what the source
/// leaves abstract, and pretending otherwise would invent content.
fn aux_names(text: &str) -> Vec<String> {
    let mut declared: Vec<String> = Vec::new();
    let mut builtin: Vec<String> = Vec::new();
    for line in text.lines() {
        let line = strip_comment(line);
        let Some(rest) = line.strip_prefix("def $") else {
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if name.is_empty() {
            continue;
        }
        if rest[name.len()..].trim_start().starts_with("hint(builtin)") {
            builtin.push(name);
        } else if !declared.contains(&name) {
            declared.push(name);
        }
    }
    declared.retain(|n| !builtin.contains(n));
    declared
}

/// Every `rule <Relation>/<case>:` the vendored validation sources declare.
fn rule_names(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = strip_comment(line);
        let Some(rest) = line.strip_prefix("rule ") else {
            continue;
        };
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
fn opcode_production(rest: &str) -> Option<String> {
    let (lhs, rhs) = rest.split_once("=>")?;
    let mut tokens = lhs.split_whitespace();
    let opcode = tokens.next()?;
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
        return None;
    }
    // Core 3.0 has two 0x04 productions with the same result constructor:
    // one ends the then arm directly and one carries an explicit 0x05 else
    // arm. Their encodings are distinct authority obligations.
    let form = if key == "0x04" && constructor == "IF" {
        if lhs.split_whitespace().any(|token| token == "0x05") {
            "IF/else"
        } else {
            "IF/empty-else"
        }
    } else {
        constructor
    };
    Some(format!("{key} {form}"))
}

fn opcode_productions(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut pending: Option<String> = None;
    for line in text.lines() {
        let line = strip_comment(line).trim();
        if let Some(rest) = line.strip_prefix('|').map(str::trim) {
            if rest.starts_with("0x") {
                pending = Some(rest.to_string());
            } else {
                pending = None;
            }
        } else if let Some(production) = &mut pending {
            if !line.is_empty() {
                production.push(' ');
                production.push_str(line);
            }
        }
        let Some(production) = pending.as_ref() else {
            continue;
        };
        if production.contains("=>") {
            if let Some(item) = opcode_production(production) {
                out.push(item);
            }
            pending = None;
        }
    }
    out
}

/// One marker, together with the Lean declaration it is attached to.
#[derive(Clone, Debug)]
pub struct Marker {
    /// The pinned-source item claimed, e.g. `0x0C BR`.
    pub item: String,
    /// The fully qualified Lean name the marker sits above.
    pub declaration: String,
    /// Where it was found, for a legible failure.
    pub location: String,
}

/// Whether a line opens a Lean declaration, and under what name.
///
/// A marker must be attached to one of these or to a constructor line. A comment
/// floating anywhere in a file is NOT coverage -- an external audit made exactly
/// that objection, and it was right: the first version of this checker counted
/// comments.
fn declaration_name(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    for keyword in [
        "inductive ",
        "structure ",
        "def ",
        "abbrev ",
        "theorem ",
        "instance ",
        "class ",
    ] {
        if let Some(rest) = trimmed.strip_prefix(keyword) {
            if let Some(name) = identifier_prefix(rest) {
                return Some(name);
            }
        }
    }
    None
}

/// Whether a line is an inductive constructor, and under what name.
///
/// Guillemet-quoted identifiers are kept WITH their quotes. Lean spells a
/// constructor whose name collides with a keyword as `| «struct»`, and the
/// probe must ask for `@Ns.Ref_ok.«struct»` -- the bare form does not parse.
/// An earlier version stopped at the `«` and reported two real constructors of
/// `Wasm.Core.Ref_ok` as attached to nothing.
fn constructor_name(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    if !line.starts_with(' ') && !line.starts_with('\t') {
        // A top-level `|` belongs to a `match`, not to a constructor list.
        return None;
    }
    let rest = trimmed.strip_prefix("| ")?;
    identifier_prefix(rest)
}

/// The leading Lean identifier of `s`, including guillemets when it is quoted.
fn identifier_prefix(s: &str) -> Option<&str> {
    if s.starts_with('«') {
        let close = s.find('»')?;
        return Some(&s[..close + '»'.len_utf8()]);
    }
    let name = s
        .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '{')
        .next()?;
    (!name.is_empty()
        && name
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_'))
    .then_some(name)
}

/// Every marker of the given kind carried by the Lean tree, each bound to the
/// declaration it is attached to.
///
/// The binding rule: the marker must be a comment, and the next non-blank,
/// non-comment line must open a declaration or be a constructor. Anything else
/// is reported as an unattached marker and does not count.
fn lean_markers(root: &Path, kind: Kind) -> Result<(Vec<Marker>, Vec<String>)> {
    let mut files = Vec::new();
    collect_lean(root, &mut files)?;
    files.sort();

    let mut out: Vec<Marker> = Vec::new();
    let mut unattached: Vec<String> = Vec::new();

    for path in files {
        let text = crate::repo::read_lossy(CLAUSE, &path)?;
        let lines: Vec<&str> = text.lines().collect();
        let mut namespaces: Vec<String> = Vec::new();
        let mut current_inductive: Option<String> = None;

        for (index, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("namespace ") {
                namespaces.push(rest.trim().to_string());
            } else if let Some(rest) = trimmed.strip_prefix("end ") {
                let name = rest.trim();
                if namespaces.last().map(String::as_str) == Some(name) {
                    namespaces.pop();
                }
            }
            if let Some(name) = declaration_name(line) {
                if trimmed.starts_with("inductive ") || trimmed.starts_with("structure ") {
                    current_inductive = Some(name.to_string());
                }
            }

            let Some(i) = line.find(kind.marker()) else {
                continue;
            };
            let before = &line[..i];
            if !before.contains("--") && !before.contains("/-") {
                continue;
            }
            let item = line[i + kind.marker().len()..]
                .trim()
                .trim_end_matches("-/")
                .trim();
            if item.is_empty() {
                continue;
            }
            let location = format!("{}:{}", path.display(), index + 1);

            // Find the declaration or constructor this marker is attached to.
            let mut declaration: Option<String> = None;
            for next in lines.iter().skip(index + 1) {
                let t = next.trim();
                if t.is_empty() || t.starts_with("--") || t.starts_with("/-") || t.starts_with("-/")
                {
                    continue;
                }
                if let Some(name) = declaration_name(next) {
                    let mut full = namespaces.clone();
                    full.push(name.to_string());
                    declaration = Some(full.join("."));
                } else if let Some(name) = constructor_name(next) {
                    if let Some(ind) = &current_inductive {
                        let mut full = namespaces.clone();
                        full.push(ind.clone());
                        full.push(name.to_string());
                        declaration = Some(full.join("."));
                    }
                }
                break;
            }

            match declaration {
                Some(declaration) => out.push(Marker {
                    item: item.to_string(),
                    declaration,
                    location,
                }),
                None => unattached.push(format!(
                    "{location}: `{} {item}` is attached to no declaration or constructor",
                    kind.marker()
                )),
            }
        }
    }
    out.sort_by(|a, b| a.item.cmp(&b.item));
    unattached.sort();
    Ok((out, unattached))
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
        let raw = crate::repo::read_lossy(CLAUSE, &path)?;
        let text = strip_block_comments(&raw);
        let mut names = match kind {
            Kind::Syntax => syntax_names(&text),
            Kind::Rule | Kind::Exec => rule_names(&text),
            Kind::Aux => aux_names(&text),
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

    let (claimed, unattached) = lean_markers(lean_root, kind)?;
    let missing: Vec<String> = required
        .iter()
        .filter(|n| !claimed.iter().any(|m| &&m.item == n))
        .cloned()
        .collect();
    let unknown: Vec<String> = claimed
        .iter()
        .filter(|m| !required.contains(&m.item))
        .map(|m| m.item.clone())
        .collect();

    Ok(Coverage {
        kind,
        required,
        claimed,
        missing,
        unknown,
        unattached,
        unelaborated: Vec::new(),
    })
}

pub struct Report {
    pub parts: Vec<Coverage>,
    /// Whether the compiled environment was consulted. A source-only run is
    /// weaker evidence and says so.
    pub elaborated: bool,
}

impl Report {
    pub fn is_ok(&self) -> bool {
        // A marker that is fabricated, unattached, or attached to a name the
        // compiled environment does not have always fails: each is a way for the
        // number to say more than the tree does.
        //
        // Incomplete coverage is REPORTED here and FAILED by `--check`. The gate
        // runs `--check`; this bare form exists so a work-in-progress run can
        // still print the arithmetic.
        self.parts.iter().all(|p| p.faults() == 0)
    }

    pub fn complete(&self) -> bool {
        self.parts.iter().all(|p| p.missing.is_empty())
    }

    pub fn render(&self, list: bool) -> String {
        let mut out = vec![
            "pinned Core 3.0 front end, checklist extracted from the vendored SpecTec sources"
                .to_string(),
        ];
        let mut total = 0usize;
        let mut done = 0usize;
        for part in &self.parts {
            out.extend(part.render(list));
            total += part.required.len();
            done += part.covered();
        }
        out.push(format!(
            "  TOTAL                      {done} of {total} covered"
        ));
        out.push(if self.elaborated {
            "  every marker is bound to a declaration the COMPILED environment has".to_string()
        } else {
            "  WARNING: source-only run; marker declarations were not checked against the \
             compiled environment"
                .to_string()
        });
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

    /// The exact source obligation to attached Lean-declaration correspondence.
    /// This is diagnostic output for constructing/reviewing the kernel map; the
    /// release check still uses the ordinary compiled-environment audit.
    pub fn render_bindings(&self) -> String {
        let mut out = Vec::new();
        for part in &self.parts {
            for item in &part.required {
                for marker in part.claimed.iter().filter(|marker| &marker.item == item) {
                    out.push(format!(
                        "{}\t{}\t{}\t{}",
                        part.kind.label(),
                        item,
                        marker.declaration,
                        marker.location
                    ));
                }
            }
        }
        out.join("\n")
    }
}

/// Coverage from source alone. Used by the mutation suite, which plants markers
/// in a COPY of the Lean tree that no compiled environment corresponds to.
pub fn report(spectec_dir: &Path, lean_root: &Path) -> Result<Report> {
    Ok(Report {
        parts: vec![
            coverage(spectec_dir, lean_root, Kind::Syntax)?,
            coverage(spectec_dir, lean_root, Kind::Opcode)?,
            coverage(spectec_dir, lean_root, Kind::Rule)?,
            coverage(spectec_dir, lean_root, Kind::Exec)?,
            coverage(spectec_dir, lean_root, Kind::Aux)?,
        ],
        elaborated: false,
    })
}

/// Coverage, with every marker's declaration checked against the COMPILED
/// environment.
///
/// This is the answer to the objection that coverage "consists of comments
/// anywhere in Lean files, with no connection to an elaborated declaration".
/// A marker must sit above a declaration or constructor, and that name must
/// elaborate: `#check @Name` is put to Lean itself, so a marker above a
/// commented-out case, a renamed constructor or a deleted definition is
/// reported UNELABORATED and does not count.
pub fn report_elaborated(root: &Path, spectec_dir: &Path, lean_root: &Path) -> Result<Report> {
    let mut report = report(spectec_dir, lean_root)?;

    let mut names: Vec<String> = Vec::new();
    for part in &report.parts {
        for marker in &part.claimed {
            if !names.contains(&marker.declaration) {
                names.push(marker.declaration.clone());
            }
        }
    }
    if names.is_empty() {
        report.elaborated = true;
        return Ok(report);
    }

    let mut src = String::from("import WasmGemmGnaf.Wasm.CoreAuthorityBindings\n");
    for name in &names {
        src.push_str("#check @");
        src.push_str(name);
        src.push('\n');
    }
    let probe = crate::lean::probe_source(CLAUSE, root, &PathBuf::from(".core_probe.lean"), &src)?;
    let output = format!("{}\n{}", probe.stdout, probe.stderr);

    // Lean reports an unresolvable name as an `unknownIdentifier` /
    // `unknownConstant` error naming it. Matched case-insensitively because the
    // wording is a toolchain detail: Lean 4.30 prints
    // `error(lean.unknownIdentifier): Unknown identifier `foo``, and an earlier
    // version of this matcher looked for the lowercase spelling and therefore
    // never fired -- the falsifier caught that, which is what it is for.
    let mut bad: Vec<String> = Vec::new();
    for line in output.lines() {
        let lowered = line.to_ascii_lowercase();
        if !lowered.contains("unknownidentifier")
            && !lowered.contains("unknown identifier")
            && !lowered.contains("unknownconstant")
            && !lowered.contains("unknown constant")
        {
            continue;
        }
        for name in &names {
            if line.contains(name.as_str()) && !bad.contains(name) {
                bad.push(name.clone());
            }
        }
    }
    // An error we could not attribute to a name is still an error: the probe was
    // supposed to elaborate cleanly. Refusing to guess is safer than passing.
    if bad.is_empty() && !probe.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the Core-coverage probe did not elaborate, and no marker declaration could be \
                 blamed:\n{}",
                output.trim()
            ),
        ));
    }

    for part in &mut report.parts {
        for marker in &part.claimed {
            if bad.contains(&marker.declaration) {
                part.unelaborated.push(format!(
                    "{}: `{}` names `{}`, which the compiled environment does not have",
                    marker.location, marker.item, marker.declaration
                ));
            }
        }
        part.unelaborated.sort();
        part.unelaborated.dedup();
    }
    report.elaborated = true;
    Ok(report)
}

pub fn run(
    root: &Path,
    list: bool,
    check: bool,
    source_only: bool,
    bindings: bool,
    generate: bool,
) -> Result<Outcome> {
    let source_report = report(Path::new(SPECTEC_DIR), Path::new(LEAN_DIR))?;
    if !source_report.is_ok() || !source_report.complete() {
        println!("{}", source_report.render(list));
        return Ok(Outcome::Fail);
    }
    let expected = generated_bindings(&source_report)?;
    let generated_path = root.join(GENERATED_BINDINGS);
    if generate {
        std::fs::write(&generated_path, expected).map_err(|e| {
            SpecError::io(
                CLAUSE,
                "cannot write the generated Core authority bindings",
                &generated_path,
                e,
            )
        })?;
        println!("generated {}", generated_path.display());
        return Ok(Outcome::Pass);
    }

    let generated_current = crate::repo::read_lossy(CLAUSE, &generated_path)?;
    let generated_matches = generated_current == expected;
    let report = if source_only {
        source_report
    } else {
        report_elaborated(root, Path::new(SPECTEC_DIR), Path::new(LEAN_DIR))?
    };
    println!("{}", report.render(list));
    if !generated_matches {
        println!(
            "  STALE generated authority map: run `cargo run --manifest-path xtask/Cargo.toml -- core --generate`"
        );
    }
    if bindings {
        println!("{}", report.render_bindings());
    }
    if !report.is_ok() || !generated_matches {
        return Ok(Outcome::Fail);
    }
    Ok(if check && !report.complete() {
        Outcome::Fail
    } else {
        Outcome::Pass
    })
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
    fn reads_multiline_opcode_productions_without_collapsing_if_forms() {
        let src = "\
grammar Binstr/block : instr = ...
  | 0x04 bt:Bblocktype (in:Binstr)* 0x0B => IF bt in* ELSE eps
  | 0x04 bt:Bblocktype (in_1:Binstr)*
    0x05 (in_2:Binstr)* 0x0B => IF bt in_1* ELSE in_2*
";
        assert_eq!(
            opcode_productions(src),
            vec!["0x04 IF/empty-else", "0x04 IF/else"]
        );
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
        assert_eq!(
            rule_names(src),
            vec!["Instr_ok/nop", "Instr_ok/select-impl"]
        );
    }

    #[test]
    fn reads_syntax_names_collapsing_variant_families() {
        let src = "\
syntax numtype hint(desc \"number type\") =
syntax absheaptype/syn hint(desc \"abstract heap type\") =
syntax absheaptype/sem =
;; syntax commented =
";
        assert_eq!(
            syntax_names(src),
            vec!["numtype", "absheaptype", "absheaptype"]
        );
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
        let (markers, unattached) = lean_markers(&scratch, Kind::Rule).unwrap();
        let _ = std::fs::remove_dir_all(&scratch);
        assert!(unattached.is_empty(), "unattached: {unattached:?}");
        assert_eq!(markers.len(), 1);
        assert_eq!(markers[0].item, "Instr_ok/nop");
        assert_eq!(markers[0].declaration, "notAMarker");
    }

    #[test]
    fn a_marker_must_be_attached_to_a_declaration() {
        let scratch = std::env::temp_dir().join("wgg-core-attach-test");
        let _ = std::fs::remove_dir_all(&scratch);
        std::fs::create_dir_all(&scratch).unwrap();
        // A marker with nothing after it but a block comment claims nothing.
        std::fs::write(
            scratch.join("A.lean"),
            "-- core-rule: Instr_ok/nop\n\n/- an ordinary block comment -/\n",
        )
        .unwrap();
        let (markers, unattached) = lean_markers(&scratch, Kind::Rule).unwrap();
        let _ = std::fs::remove_dir_all(&scratch);
        assert!(markers.is_empty(), "markers: {markers:?}");
        assert_eq!(unattached.len(), 1, "unattached: {unattached:?}");
    }

    #[test]
    fn a_block_commented_rule_is_not_an_obligation() {
        // The pinned `2.3-validation.instructions.spectec` block-comments out its
        // superseded `Instr_ok/load` and `Instr_ok/store`, replacing them with
        // the `-val` / `-pack` pairs. Counting them made the denominator 258
        // where the honest number is 256.
        let src = "\
rule Instr_ok/data.drop:
  C |- DATA.DROP x : eps -> eps

(;
rule Instr_ok/load:
  C |- LOAD nt x memarg : at -> nt
;)

rule Instr_ok/load-val:
  C |- LOAD nt x memarg : at -> nt
";
        let stripped = strip_block_comments(src);
        assert_eq!(
            rule_names(&stripped),
            vec!["Instr_ok/data.drop", "Instr_ok/load-val"]
        );
        // Nesting.
        assert_eq!(strip_block_comments("a(;b(;c;)d;)e").trim(), "ae");
    }

    #[test]
    fn a_guillemet_quoted_constructor_is_attached() {
        // Lean spells a constructor whose name collides with a keyword as
        // `| «struct»`, and the probe must ask for it the same way. Stopping at
        // the opening guillemet reported two real constructors of
        // `Wasm.Core.Ref_ok` as attached to nothing.
        let scratch = std::env::temp_dir().join("wgg-core-guillemet-test");
        let _ = std::fs::remove_dir_all(&scratch);
        std::fs::create_dir_all(&scratch).unwrap();
        std::fs::write(
            scratch.join("A.lean"),
            "namespace N\n\ninductive Ref_ok where\n  \
             -- core-exec: Ref_ok/struct\n  | «struct» (a : Nat)\n\nend N\n",
        )
        .unwrap();
        let (markers, unattached) = lean_markers(&scratch, Kind::Exec).unwrap();
        let _ = std::fs::remove_dir_all(&scratch);
        assert!(unattached.is_empty(), "unattached: {unattached:?}");
        assert_eq!(markers.len(), 1);
        assert_eq!(markers[0].declaration, "N.Ref_ok.«struct»");
    }

    #[test]
    fn a_constructor_marker_takes_the_enclosing_inductive_name() {
        let scratch = std::env::temp_dir().join("wgg-core-ctor-test");
        let _ = std::fs::remove_dir_all(&scratch);
        std::fs::create_dir_all(&scratch).unwrap();
        std::fs::write(
            scratch.join("A.lean"),
            "namespace Foo.Bar\n\ninductive Instr where\n  \
             -- core-opcode: 0x0C BR\n  | br (label : Nat)\n\nend Foo.Bar\n",
        )
        .unwrap();
        let (markers, unattached) = lean_markers(&scratch, Kind::Opcode).unwrap();
        let _ = std::fs::remove_dir_all(&scratch);
        assert!(unattached.is_empty(), "unattached: {unattached:?}");
        assert_eq!(markers.len(), 1);
        assert_eq!(markers[0].declaration, "Foo.Bar.Instr.br");
    }
}
