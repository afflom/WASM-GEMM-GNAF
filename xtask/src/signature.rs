//! `xtask signature` -- the SPEC section 15 proposition bindings. SPEC section 15.
//!
//! The audit's objection was precise:
//!
//! > The repository's reported 36/58 remains inflated. Its checker verifies names
//! > rather than exact proposition types; its own M12 test demonstrates that a
//! > matching-name `Nat := 0` is counted as discharged.
//!
//! It was right. `required.rs` asks the compiled environment whether each SPEC
//! section 15 NAME exists and what its axiom closure is. A declaration named
//! `Wasm.validation_progress` with type `Nat` and body `0` passed that check.
//!
//! This closes it the same way `schema.rs` closed the WGG-GO-1 objection, one
//! layer up, by splitting the job between the two things that can do it:
//!
//!   * `SPEC.md` is the SOURCE OF THE LIST. The names come from its section 15
//!     fence, read by `required::required_names`. Nothing here enumerates them,
//!     so a declaration added to SPEC immediately fails this check rather than
//!     passing unnoticed.
//!
//!   * The LEAN ELABORATOR is the comparator. Each binding in
//!     `WasmGemmGnaf/Conformance/RequiredSignatures.lean` restates the required
//!     proposition in full and closes it with `:= @Name`, so the type equality
//!     checked is DEFINITIONAL. A `Nat := 0` under the right name does not
//!     elaborate; nor does a narrowed quantifier, an added hypothesis, a dropped
//!     conjunct, or a weakened conclusion.
//!
//! Five things that wiring can get wrong are enforced here:
//!
//!   1. a required name the environment credits, with no binding;
//!   2. a binding closed by a tactic rather than by `:= @Name` -- `by exact @Name`
//!      would prove the same proposition, but `by` accepts anything, and the whole
//!      value of this file is that it accepts only definitional agreement;
//!   3. a marker naming something SPEC section 15 does not require;
//!   4. a docstring whose quotation of SPEC has drifted from `SPEC.md`. Where
//!      SPEC states the theorem in a fenced block, that block is re-read from
//!      `SPEC.md` and must appear verbatim in the binding's docstring, so a SPEC
//!      amendment cannot leave a stale binding looking authoritative.
//!   5. theorem-shaped prose outside a Lean fence masquerading as SPEC's formal
//!      statement and hiding a drift in the real fenced proposition.
//!
//! ## What this CANNOT check, stated because it matters
//!
//! For the twenty-nine required names SPEC states only in prose, no tool can
//! decide that the proposition written in the Lean file is the one SPEC means.
//! The binding pins the declaration to a written proposition and the docstring
//! quotes the governing prose; a reader closes the last step. That residual is
//! the same one `Conformance/Schema.lean` carries, and naming it is not a
//! weakness of the check -- concealing it would be.

use std::path::Path;

use crate::json::{self, Value};
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "15";
const BINDINGS: &str = "WasmGemmGnaf/Conformance/RequiredSignatures.lean";
const DEVIATIONS: &str = "model/spec-deviations.json";

/// The marker announcing a binding that carries SPEC's proposition.
const EXACT: &str = "-- spec-signature:";
/// A binding whose proposition differs from SPEC's under a filed deviation.
const AMENDED: &str = "-- spec-signature-amended:";
/// A binding strictly weaker than SPEC's text, with no deviation filed.
const WEAKER: &str = "-- spec-signature-weaker:";

/// Declaration keywords a binding may open with. `abbrev` is here because two
/// required declarations are `Fintype` instances -- DATA, not propositions -- and
/// a `theorem` of a non-`Prop` type does not elaborate.
const OPENERS: [&str; 4] = ["theorem ", "def ", "abbrev ", "instance "];

/// What a binding claims about its declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// The declaration carries SPEC's proposition. Counts as discharged.
    Exact,
    /// It carries an amended proposition under the named deviation id.
    Amended(String),
    /// It is strictly weaker than SPEC's text and no deviation is filed.
    Weaker,
}

impl Kind {
    fn label(&self) -> &'static str {
        match self {
            Kind::Exact => "BOUND",
            Kind::Amended(_) => "AMENDED",
            Kind::Weaker => "WEAKER",
        }
    }
}

/// One `-- spec-signature*:` block found in the Lean source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    /// The SPEC section 15 name the marker claims to bind.
    pub name: String,
    pub kind: Kind,
    /// The Lean declaration carrying the binding.
    pub declaration: String,
    /// Everything between the declaration head and the `:=`.
    pub statement: String,
    /// The proof term, as written.
    pub proof: String,
    /// The `/-- ... -/` docstring immediately above the marker.
    pub doc: String,
    /// 1-indexed line of the marker.
    pub line: usize,
}

pub fn run(root: &Path) -> Result<Outcome> {
    let spec = read(Path::new("SPEC.md"))?;
    let required = crate::required::required_names(&spec)?;
    let source = read(Path::new(BINDINGS))?;
    let bindings = parse(&source);
    let deviations = deviation_ids()?;

    println!("SPEC 15 proposition bindings (SPEC 15)");
    println!("  declarations: SPEC.md section 15");
    println!("  bindings    : {BINDINGS}");
    println!("  required    : {} declaration(s)\n", required.len());

    let mut failures = audit(&required, &bindings, &deviations, &spec);

    // A name the environment credits but nothing binds is the exact defect this
    // command exists to catch, so it is asked of the ENVIRONMENT rather than
    // inferred from the source. `environment_report` is the old name-and-axiom
    // rule, deliberately un-demoted here: otherwise the two checks would agree by
    // construction and neither would test the other.
    let environment = crate::required::environment_report(root)?;
    let exact = exact_names(&bindings);
    let mut disclosed: Vec<String> = Vec::new();
    for name in &environment.credited {
        if exact.iter().any(|e| e == name) {
            continue;
        }
        match bindings.iter().find(|b| b.name == *name) {
            // An AMENDED or WEAKER binding is a DISCLOSURE, not a defect in this
            // wiring: the proposition is written out, pinned by `:= @Name`, and
            // reported OUTSTANDING by `xtask claims required`. Failing here as
            // well would make one obligation read as two, and would give the next
            // reader no way to tell a disclosed gap from a broken checker.
            Some(b) => disclosed.push(format!(
                "{name} -- {} at line {}: present in the compiled environment, but the \
                 proposition it carries is not SPEC's. NOT discharged.{}",
                b.kind.label(),
                b.line,
                match &b.kind {
                    Kind::Amended(id) => format!(" Deviation {id} filed."),
                    _ => " No deviation filed.".to_string(),
                }
            )),
            None => failures.push(format!(
                "{name} -- present in the compiled environment with NO SIGNATURE BINDING. \
                 Add `{EXACT} {name}` above a declaration in {BINDINGS} stating SPEC's \
                 proposition in full and closed by `:= @{name}`. A name check alone cannot \
                 reject a `Nat := 0` wearing the right name."
            )),
        }
    }

    for binding in &bindings {
        let detail = match &binding.kind {
            Kind::Amended(id) => format!("  (deviation {id})"),
            _ => String::new(),
        };
        println!(
            "  [{:<7}] {:<52} {}{}",
            binding.kind.label(),
            binding.name,
            binding.declaration,
            detail
        );
    }

    let quoted = bindings
        .iter()
        .filter(|b| spec_block(&spec, &b.name).is_some())
        .count();
    println!(
        "\n  {} binding(s); {} exact, {} quoting a verbatim SPEC block",
        bindings.len(),
        exact.len(),
        quoted
    );
    println!(
        "  {} of {} SPEC 15 declarations carry SPEC's proposition",
        exact.len(),
        required.len()
    );

    if !disclosed.is_empty() {
        println!("\n  DISCLOSED — present but not SPEC's proposition, reported outstanding:");
        for note in &disclosed {
            println!("    {note}");
        }
    }

    if !failures.is_empty() {
        println!(
            "\nSIGNATURE: FAIL — {} unbound or unsound binding(s):",
            failures.len()
        );
        for failure in &failures {
            println!("  {failure}");
        }
        println!(
            "\nSPEC 15: the required declarations SHALL exist with fully implemented bodies \
             and proofs,\nand \"names may gain namespaces but not weaker propositions\". A \
             binding closed by\n`:= @Name` is what makes that a check on the PROPOSITION \
             rather than on the name."
        );
        return Ok(Outcome::Fail);
    }
    println!("SIGNATURE: PASS — every credited SPEC 15 declaration is definitionally bound");
    Ok(Outcome::Pass)
}

/// The SPEC 15 names carrying an EXACT binding. These, and only these, may be
/// counted discharged by `xtask claims required`.
pub fn exact_names(bindings: &[Binding]) -> Vec<String> {
    bindings
        .iter()
        .filter(|b| b.kind == Kind::Exact)
        .map(|b| b.name.clone())
        .collect()
}

/// The bindings as the tracked file has them. Used by `required.rs`, which must
/// not count a name the file does not bind exactly.
pub fn tracked_bindings() -> Result<Vec<Binding>> {
    Ok(parse(&read(Path::new(BINDINGS))?))
}

/// The deviation ids `model/spec-deviations.json` records.
pub fn deviation_ids() -> Result<Vec<String>> {
    let text = read(Path::new(DEVIATIONS))?;
    let parsed = json::parse(CLAUSE, &text)?;
    let rows = parsed
        .get("deviations")
        .and_then(Value::as_array)
        .ok_or_else(|| SpecError::new(CLAUSE, format!("{DEVIATIONS} has no `deviations` array")))?;
    Ok(rows
        .iter()
        .filter_map(|d| d.get("id").and_then(Value::as_str))
        .map(String::from)
        .collect())
}

/// Every rule decidable from the SPEC 15 list, the parsed bindings, the filed
/// deviations and the SPEC text. Pure, so `M15` can attack it directly.
pub fn audit(
    required: &[&str],
    bindings: &[Binding],
    deviations: &[String],
    spec: &str,
) -> Vec<String> {
    let mut failures = Vec::new();

    for binding in bindings {
        // A marker naming something SPEC does not require is a stale binding
        // claiming an authority it does not have.
        if !required.iter().any(|r| *r == binding.name) {
            failures.push(format!(
                "{} -- bound at line {} but SPEC section 15 does not require it",
                binding.name, binding.line
            ));
            continue;
        }

        if bindings.iter().filter(|b| b.name == binding.name).count() > 1 {
            failures.push(format!(
                "{} -- bound more than once; one declaration, one binding",
                binding.name
            ));
        }

        if binding.declaration.is_empty() {
            failures.push(format!(
                "{} -- the marker at line {} is not followed by a declaration",
                binding.name, binding.line
            ));
            continue;
        }

        // THE rule. `:= @Name` is a definitional coercion: the declaration's type
        // must be defeq to the stated proposition or the file does not elaborate.
        // `by exact @Name` proves the same thing today and accepts anything
        // tomorrow, which is why the check is on the syntax and not on whether
        // Lean happened to close it.
        if !closes_definitionally(&binding.proof, &binding.name) {
            failures.push(format!(
                "{} -- `{}` is closed by `{}`, not by `:= @{}`; only a definitional \
                 coercion rejects a declaration whose type merely resembles the stated \
                 proposition",
                binding.name, binding.declaration, binding.proof, binding.name
            ));
        }

        // The statement must mention the declaration it claims to state. A marker
        // over `True` closed by an unrelated name is a label, not a binding.
        if !mentions(&binding.statement, &binding.name) {
            failures.push(format!(
                "{} -- the declaration `{}` at line {} does not mention it; a marker is \
                 not a binding",
                binding.name, binding.declaration, binding.line
            ));
        }

        if let Kind::Amended(id) = &binding.kind {
            if !deviations.iter().any(|d| d == id) {
                failures.push(format!(
                    "{} -- cites deviation `{id}`, which {DEVIATIONS} does not record; an \
                     amended proposition with no filed deviation is an undisclosed weakening",
                    binding.name
                ));
            }
        }

        // Where SPEC states the theorem in a fenced block, the docstring must
        // carry that block verbatim. This is what keeps the binding honest across
        // a SPEC amendment: change SPEC and the quotation no longer matches.
        if let Some(block) = spec_block(spec, &binding.name) {
            if !normalise(&binding.doc).contains(&normalise(&block)) {
                failures.push(format!(
                    "{} -- SPEC states this theorem in a fenced block and the binding's \
                     docstring does not quote it verbatim; quote SPEC.md or the binding \
                     cannot be compared with what SPEC asks for",
                    binding.name
                ));
            }
        }
    }

    failures
}

/// Is the proof term an accepted `@Name` spelling for this SPEC 15 name?
///
/// `required.rs` credits a declaration under `WasmGemmGnaf.<name>` or under a
/// `WasmGemmGnaf.Theorems.<leaf>` re-export, so both spellings are accepted here
/// and the namespace prefix is optional -- the binding file sits inside
/// `WasmGemmGnaf`, so it writes the relative form.
fn closes_definitionally(proof: &str, name: &str) -> bool {
    let Some(term) = proof.strip_prefix('@') else {
        return false;
    };
    let term = term.trim();
    if term.is_empty() || term.contains(char::is_whitespace) {
        return false;
    }
    let leaf = name.rsplit('.').next().unwrap_or(name);
    [
        name.to_string(),
        format!("WasmGemmGnaf.{name}"),
        format!("Theorems.{leaf}"),
        format!("WasmGemmGnaf.Theorems.{leaf}"),
    ]
    .iter()
    .any(|accepted| accepted == term)
}

/// Does the statement reference the declaration it binds?
///
/// The final component only: the Lean source writes names relative to the open
/// namespace, and a binding for `Wasm.decode_sound` states `Wasm.decode`, not
/// `Wasm.decode_sound`. What the statement must mention is therefore the subject
/// matter, which for these theorems is reliably the leaf's stem.
fn mentions(statement: &str, name: &str) -> bool {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    // The statement of `decode_sound` mentions `decode`; of `abi_roundtrip`,
    // `decodeHeader`. Match on the longest leading word of the leaf that the
    // statement actually contains, which is a real test for a marker pasted onto
    // an unrelated theorem and not a test the binding can trivially satisfy.
    leaf.split('_')
        .any(|part| part.len() >= 4 && statement.contains(part))
}

/// The `theorem <leaf>` block inside a Lean fence in `SPEC.md`, if any.
///
/// SPEC's blocks are separated by a blank line or by the next declaration
/// keyword; `theorem decode_emit` follows `compile_cost_exact` with neither a
/// blank line nor a fence between them, which is why both terminators are needed.
/// The fence restriction is load-bearing: theorem-shaped prose is not a formal
/// proposition and must not mask a later change to the fenced statement.
pub fn spec_block(spec: &str, name: &str) -> Option<String> {
    const KEYWORDS: [&str; 8] = [
        "theorem ",
        "def ",
        "structure ",
        "inductive ",
        "instance ",
        "abbrev ",
        "end ",
        "namespace ",
    ];
    let leaf = name.rsplit('.').next().unwrap_or(name);
    let head = format!("theorem {leaf}");
    let lines: Vec<&str> = crate::lean::splitlines(spec);
    let mut in_lean_fence = false;
    let mut start = None;
    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("```") {
            if in_lean_fence {
                in_lean_fence = false;
            } else {
                in_lean_fence = trimmed == "```lean";
            }
            continue;
        }
        if !in_lean_fence {
            continue;
        }
        let candidate = line.trim_start();
        if candidate
            .strip_prefix(&head)
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
        {
            start = Some(index);
            break;
        }
    }
    let start = start?;
    let mut block = vec![lines[start]];
    for line in &lines[start + 1..] {
        let candidate = line.trim_start();
        if line.trim().is_empty()
            || candidate.starts_with("```")
            || KEYWORDS.iter().any(|k| candidate.starts_with(k))
        {
            break;
        }
        block.push(line);
    }
    Some(block.join("\n"))
}

/// Collapse every whitespace run to one space, so a quotation survives
/// re-indentation and line rewrapping but not an edit to what it says.
fn normalise(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Find every `-- spec-signature*:` block in the Lean source.
///
/// A source parse, not a Lean query, for the same reason `schema.rs` uses one:
/// the marker ties a SPEC NAME to a declaration, and that tie exists only in the
/// source. Whether the declaration has the stated type is Lean's job, asked by
/// elaborating the module.
pub fn parse(source: &str) -> Vec<Binding> {
    let lines: Vec<&str> = crate::lean::splitlines(source);
    let mut bindings = Vec::new();

    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let Some((kind, rest)) = marker(trimmed) else {
            continue;
        };
        let (name, kind) = match kind {
            MarkerKind::Exact => (rest.trim().to_string(), Kind::Exact),
            MarkerKind::Weaker => (rest.trim().to_string(), Kind::Weaker),
            MarkerKind::Amended => {
                let (name, id) = split_deviation(rest);
                (name, Kind::Amended(id))
            }
        };
        if name.is_empty() {
            continue;
        }

        // The declaration is the next non-blank, non-comment line.
        let mut cursor = index + 1;
        while cursor < lines.len() {
            let candidate = lines[cursor].trim();
            if candidate.is_empty() || candidate.starts_with("--") {
                cursor += 1;
                continue;
            }
            break;
        }
        let Some(head) = lines.get(cursor) else {
            continue;
        };
        let opener = OPENERS.iter().find_map(|k| head.trim().strip_prefix(k));
        let Some(opener) = opener else {
            bindings.push(Binding {
                name,
                kind,
                declaration: String::new(),
                statement: String::new(),
                proof: head.trim().to_string(),
                doc: docstring(&lines, index),
                line: index + 1,
            });
            continue;
        };
        let declaration = opener
            .split(|c: char| c.is_whitespace() || c == '(' || c == '{' || c == '[' || c == ':')
            .next()
            .unwrap_or("")
            .to_string();

        let (statement, proof) = statement_and_proof(&lines[cursor..]);

        bindings.push(Binding {
            name,
            kind,
            declaration,
            statement,
            proof,
            doc: docstring(&lines, index),
            line: index + 1,
        });
    }

    bindings
}

enum MarkerKind {
    Exact,
    Amended,
    Weaker,
}

/// Longest marker first: `-- spec-signature-amended:` also starts with
/// `-- spec-signature`, so testing the short form first would swallow both and
/// silently promote an amended binding to an exact one.
fn marker(trimmed: &str) -> Option<(MarkerKind, &str)> {
    if let Some(rest) = trimmed.strip_prefix(AMENDED) {
        return Some((MarkerKind::Amended, rest));
    }
    if let Some(rest) = trimmed.strip_prefix(WEAKER) {
        return Some((MarkerKind::Weaker, rest));
    }
    trimmed
        .strip_prefix(EXACT)
        .map(|rest| (MarkerKind::Exact, rest))
}

/// `Name (deviation DEV-001)` -> `("Name", "DEV-001")`. A missing or malformed
/// citation yields an empty id, which the audit then reports as unrecorded.
fn split_deviation(rest: &str) -> (String, String) {
    let rest = rest.trim();
    let Some(open) = rest.find('(') else {
        return (rest.to_string(), String::new());
    };
    let name = rest[..open].trim().to_string();
    let inside = rest[open + 1..].trim_end_matches(')').trim();
    let id = inside
        .strip_prefix("deviation")
        .unwrap_or("")
        .trim()
        .to_string();
    (name, id)
}

/// Split a declaration into its statement and its proof term.
fn statement_and_proof(lines: &[&str]) -> (String, String) {
    let mut statement = String::new();
    let mut proof = String::new();
    let mut in_proof = false;
    let mut depth = 0i32;
    for body in lines {
        if in_proof {
            if body.trim().is_empty() {
                break;
            }
            proof.push(' ');
            proof.push_str(body.trim());
            continue;
        }
        let (split, carried) = split_assignment(body, depth);
        depth = carried;
        match split {
            Some((before, after)) => {
                statement.push(' ');
                statement.push_str(before.trim());
                proof.push_str(after.trim());
                in_proof = true;
            }
            None => {
                if body.trim().is_empty() {
                    break;
                }
                statement.push(' ');
                statement.push_str(body.trim());
            }
        }
    }
    (statement.trim().to_string(), proof.trim().to_string())
}

/// Split a line at the `:=` that ends a declaration's statement, carrying the
/// bracket depth in and out.
///
/// Depth is threaded through the whole declaration rather than recomputed per
/// line: a statement spanning several lines closes its brackets on a later line
/// than it opens them, so a per-line scan starts the closing line at a NEGATIVE
/// depth and never recognises its terminating `:=`. `schema.rs` learned this on
/// the real bindings; the same shape occurs here.
fn split_assignment(line: &str, entering: i32) -> (Option<(&str, &str)>, i32) {
    let bytes = line.as_bytes();
    let mut depth = entering;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b':' if depth == 0 && i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                return (Some((&line[..i], &line[i + 2..])), depth);
            }
            _ => {}
        }
        i += 1;
    }
    (None, depth)
}

/// The `/-- ... -/` docstring immediately above a marker, if there is one.
fn docstring(lines: &[&str], marker_line: usize) -> String {
    let mut end = marker_line;
    while end > 0 && lines[end - 1].trim().is_empty() {
        end -= 1;
    }
    if end == 0 || lines[end - 1].trim() != "-/" {
        return String::new();
    }
    let mut start = end - 1;
    while start > 0 && !lines[start].trim_start().starts_with("/--") {
        start -= 1;
    }
    if !lines[start].trim_start().starts_with("/--") {
        return String::new();
    }
    lines[start..end].join("\n")
}

fn read(path: &Path) -> Result<String> {
    std::fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", path, e))
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "\
/--
**SPEC §7.3**, quoted verbatim:

```lean
theorem decode_sound
    (h : Wasm.decode bytes = .ok module) :
  Wasm.DeclarativeBinaryRelation bytes module
```
-/
-- spec-signature: Wasm.decode_sound
theorem decode_sound_signature :
    ∀ {bytes : ByteArray} {module : Wasm.Module},
      Wasm.decode bytes = .ok module → Wasm.DeclarativeBinaryRelation bytes module :=
  @Wasm.decode_sound

/-- prose only -/
-- spec-signature-amended: Wasm.costed_erase_iff_plain_run (deviation DEV-001)
theorem costed_erase_iff_plain_run_signature :
    ∀ (t : Nat), Wasm.CostedRun t :=
  @Wasm.costed_erase_iff_plain_run
";

    const SPEC: &str = "\
## 15. Required Lean declarations

```lean
Wasm.decode_sound
Wasm.costed_erase_iff_plain_run
```

## 16. Next
### 7.3
```lean
theorem decode_sound
    (h : Wasm.decode bytes = .ok module) :
  Wasm.DeclarativeBinaryRelation bytes module
```
";

    fn sample_required() -> Vec<&'static str> {
        vec!["Wasm.decode_sound", "Wasm.costed_erase_iff_plain_run"]
    }

    #[test]
    fn parses_marker_kind_declaration_statement_and_proof() {
        let found = parse(SAMPLE);
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].name, "Wasm.decode_sound");
        assert_eq!(found[0].kind, Kind::Exact);
        assert_eq!(found[0].declaration, "decode_sound_signature");
        assert_eq!(found[0].proof, "@Wasm.decode_sound");
        assert!(found[0].doc.contains("DeclarativeBinaryRelation"));
        assert_eq!(found[1].kind, Kind::Amended("DEV-001".to_string()));
        assert_eq!(found[1].name, "Wasm.costed_erase_iff_plain_run");
    }

    #[test]
    fn the_amended_marker_is_not_read_as_an_exact_one() {
        // `-- spec-signature-amended:` also starts with `-- spec-signature`, so a
        // shortest-first test would promote every amended binding to exact and
        // silently restore the inflation this file exists to remove.
        let found = parse(SAMPLE);
        assert_eq!(exact_names(&found), vec!["Wasm.decode_sound".to_string()]);
    }

    #[test]
    fn a_tactic_proof_is_not_a_binding() {
        // `by exact @Name` proves the same proposition today. `by` accepts
        // anything tomorrow, and the entire value of this file is that it accepts
        // only definitional agreement.
        assert!(closes_definitionally(
            "@Wasm.decode_sound",
            "Wasm.decode_sound"
        ));
        assert!(closes_definitionally(
            "@WasmGemmGnaf.Wasm.decode_sound",
            "Wasm.decode_sound"
        ));
        assert!(closes_definitionally(
            "@Theorems.decode_sound",
            "Wasm.decode_sound"
        ));
        assert!(!closes_definitionally(
            "by exact @Wasm.decode_sound",
            "Wasm.decode_sound"
        ));
        assert!(!closes_definitionally("by simp", "Wasm.decode_sound"));
        assert!(!closes_definitionally(
            "Wasm.decode_sound",
            "Wasm.decode_sound"
        ));
        assert!(!closes_definitionally(
            "@Wasm.decode_sound_weaker",
            "Wasm.decode_sound"
        ));
        assert!(!closes_definitionally("@Wasm.other", "Wasm.decode_sound"));
    }

    #[test]
    fn a_missing_binding_is_not_silently_forgiven_by_the_audit() {
        let source = SAMPLE.replace("-- spec-signature: Wasm.decode_sound\n", "");
        let found = parse(&source);
        assert!(!exact_names(&found).contains(&"Wasm.decode_sound".to_string()));
    }

    #[test]
    fn a_marker_naming_something_spec_does_not_require_is_rejected() {
        let source = SAMPLE.replace("Wasm.decode_sound\n", "Wasm.not_required\n");
        let failures = audit(
            &sample_required(),
            &parse(&source),
            &["DEV-001".into()],
            SPEC,
        );
        assert!(
            failures
                .iter()
                .any(|f| f.contains("SPEC section 15 does not require it")),
            "{failures:?}"
        );
    }

    #[test]
    fn an_unrecorded_deviation_is_rejected() {
        let failures = audit(&sample_required(), &parse(SAMPLE), &[], SPEC);
        assert!(
            failures.iter().any(|f| f.contains("does not record")),
            "{failures:?}"
        );
    }

    #[test]
    fn a_docstring_that_has_drifted_from_spec_is_rejected() {
        // SPEC is the source of the quoted block. Edit SPEC and the binding must
        // stop passing, so nobody can leave a stale quotation looking normative.
        let drifted = SPEC.replace("DeclarativeBinaryRelation", "SomeWeakerRelation");
        let failures = audit(
            &sample_required(),
            &parse(SAMPLE),
            &["DEV-001".into()],
            &drifted,
        );
        assert!(
            failures
                .iter()
                .any(|f| f.contains("does not quote it verbatim")),
            "{failures:?}"
        );
    }

    #[test]
    fn requoting_survives_reindentation_but_not_rewording() {
        let block = spec_block(SPEC, "Wasm.decode_sound").expect("SPEC states this one");
        assert!(block.starts_with("theorem decode_sound"));
        assert!(block.contains("DeclarativeBinaryRelation bytes module"));
        assert!(normalise("  a\n   b ").contains(&normalise("a b")));
        assert!(!normalise("a c").contains(&normalise("a b")));
        assert!(spec_block(SPEC, "Wasm.costed_erase_iff_plain_run").is_none());
    }

    #[test]
    fn theorem_like_prose_outside_a_lean_fence_is_not_authoritative() {
        let original = spec_block(SPEC, "Wasm.decode_sound").expect("SPEC states this one");
        let drifted = SPEC.replace("DeclarativeBinaryRelation", "SomeWeakerRelation");
        let attacked = format!("{original}\n\n{drifted}");

        let found = spec_block(&attacked, "Wasm.decode_sound").expect("fenced theorem remains");
        assert!(found.contains("SomeWeakerRelation"));
        assert!(!found.contains("DeclarativeBinaryRelation"));
        assert!(spec_block(&original, "Wasm.decode_sound").is_none());
    }

    #[test]
    fn a_marker_over_an_unrelated_declaration_is_not_a_binding() {
        let source = "-- spec-signature: Wasm.decode_sound\n\
                      theorem unrelated : True :=\n  @Wasm.decode_sound\n";
        let failures = audit(&["Wasm.decode_sound"], &parse(source), &[], SPEC);
        assert!(
            failures.iter().any(|f| f.contains("does not mention it")),
            "{failures:?}"
        );
    }

    #[test]
    fn depth_is_carried_across_lines_of_one_statement() {
        let (_, after_open) = split_assignment("    ∀ {bytes : ByteArray} (h : P bytes", 0);
        assert_eq!(after_open, 1);
        let (split, _) = split_assignment("      → Q bytes) :=", after_open);
        assert!(
            split.is_some(),
            "the terminating := must be found at carried depth"
        );
    }

    /// A tracked file, located from the crate rather than the working directory:
    /// `cargo test` runs from `xtask/`, while the checkers run from the repo root.
    fn repo_file(relative: &str) -> String {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the xtask crate sits inside the repository");
        String::from_utf8_lossy(&std::fs::read(root.join(relative)).expect("tracked file"))
            .into_owned()
    }

    #[test]
    fn the_real_bindings_pass_the_real_audit() {
        let spec = repo_file("SPEC.md");
        let required = crate::required::required_names(&spec).expect("SPEC 15 parsed");
        let source = repo_file(BINDINGS);
        let deviations: Vec<String> = {
            let text = repo_file(DEVIATIONS);
            let parsed = json::parse(CLAUSE, &text).expect("deviations parse");
            parsed
                .get("deviations")
                .and_then(Value::as_array)
                .expect("deviations array")
                .iter()
                .filter_map(|d| d.get("id").and_then(Value::as_str))
                .map(String::from)
                .collect()
        };
        let failures = audit(&required, &parse(&source), &deviations, &spec);
        assert!(failures.is_empty(), "{failures:#?}");
    }

    #[test]
    fn spec_is_the_source_of_the_list_not_this_file() {
        // Regression guard for the audit's objection. Nothing here enumerates the
        // fifty-eight names; they are read from SPEC.md every run.
        let spec = repo_file("SPEC.md");
        let required = crate::required::required_names(&spec).expect("SPEC 15 parsed");
        assert!(
            required.len() >= 60,
            "SPEC section 15 lists {}",
            required.len()
        );
        assert!(required.contains(&"Artifact.released_wasm_gemm_gnaf_global_optimal"));
    }
}
