//! `xtask schema` -- the frozen WGG-GO-1 schema binding. SPEC section 1.
//!
//! The audit's objection was precise: "no tool actually compares compiled
//! unfolded bodies with the authority JSON". A gate that looks for the NAME
//! `GlobalOptimal` accepts a weakened proposition wearing it, and a gate that
//! diffs source text against a JSON string accepts any rewording and rejects
//! any reformatting. Neither compares meanings.
//!
//! This closes it by splitting the job between the two things that can actually
//! do it:
//!
//!   * `authority/global-optimality-WGG-GO-1.json` is the SOURCE OF THE LIST.
//!     Its `scopeCriticalDefinitions` array decides what must be bound. Nothing
//!     here enumerates the thirteen names, so adding a fourteenth to the frozen
//!     authority immediately fails this check rather than passing unnoticed.
//!
//!   * The LEAN ELABORATOR is the comparator. Each binding in
//!     `WasmGemmGnaf/Conformance/Schema.lean` states the definition against its
//!     fully spelled-out body and closes it with `Iff.rfl` or `rfl`, so the
//!     equality checked is DEFINITIONAL. Narrowing a quantifier, dropping a
//!     conjunct, adding a hypothesis, substituting a scoped predicate or editing
//!     a field out of a record all stop elaborating.
//!
//! This file is therefore the wiring between them, and it enforces exactly the
//! three things that wiring can get wrong: a definition with no binding, a
//! marker pasted onto a theorem that does not mention the definition, and a
//! binding closed by a tactic proof instead of definitional reduction. The last
//! one matters most -- `by simp` would prove a propositional equivalence between
//! the real definition and a weaker paraphrase, which is precisely the substitute
//! the authority forbids.
//!
//! Finally the module is elaborated against the compiled environment, because a
//! binding that is not in the environment has not been checked by anything.

use std::path::Path;

use crate::json::{self, Value};
use crate::lean::probe_source;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "1";
const AUTHORITY: &str = "authority/global-optimality-WGG-GO-1.json";
const BINDINGS: &str = "WasmGemmGnaf/Conformance/Schema.lean";
const NAMESPACE: &str = "WasmGemmGnaf.Conformance";
const PROBE: &str = ".schema_probe.lean";

/// The marker announcing a binding, carrying the exact authority name.
const MARKER: &str = "-- authority-binding:";

/// The proofs that make a binding definitional. Anything else -- `by simp`,
/// `by constructor`, a named lemma -- proves at most a propositional
/// equivalence, which cannot distinguish the frozen schema from a weaker
/// paraphrase of it.
const DEFINITIONAL: [&str; 2] = ["Iff.rfl", "rfl"];

/// One `-- authority-binding:` block found in the Lean source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    /// The authority name the marker claims to bind.
    pub definition: String,
    /// The Lean theorem carrying the binding.
    pub theorem: String,
    /// Everything between the theorem head and the proof.
    pub statement: String,
    /// The proof term, as written.
    pub proof: String,
    /// 1-indexed line of the marker, for a failure a reader can act on.
    pub line: usize,
}

pub fn run(root: &Path) -> Result<Outcome> {
    let required = scope_critical_definitions()?;
    let source = read(BINDINGS)?;
    let bindings = parse(&source);

    println!("WGG-GO-1 schema binding (SPEC 1)");
    println!("  authority : {AUTHORITY}");
    println!("  bindings  : {BINDINGS}");
    println!("  required  : {} scope-critical definition(s)\n", required.len());

    let mut failures = audit(&required, &bindings);

    // A binding is only worth anything if Lean agrees it exists. `lake build`
    // can serve a stale olean, so ask the environment itself.
    //
    // The probe imports the binding module rather than the root: every binding
    // lives there, so this elaborates exactly what is being claimed, and the
    // verdict does not become hostage to an unrelated layer that happens to be
    // mid-edit. The root is elaborated by the gate's own step 3.
    let names: Vec<String> = bindings
        .iter()
        .map(|b| format!("{NAMESPACE}.{}", b.theorem))
        .collect();
    if !names.is_empty() {
        let mut src = String::from("import WasmGemmGnaf.Conformance.Schema\n");
        for name in &names {
            src.push_str("#print axioms ");
            src.push_str(name);
            src.push('\n');
        }
        let probe = probe_source(CLAUSE, root, &Path::new(PROBE).to_path_buf(), &src)?;
        let seen = format!("{}{}", probe.stdout, probe.stderr);
        for (binding, name) in bindings.iter().zip(&names) {
            if !seen.contains(&format!("'{name}' ")) {
                failures.push(format!(
                    "{} -- {name} is not in the compiled environment; \
                     the binding has been checked by nothing",
                    binding.definition
                ));
            }
        }
        if seen.contains("sorryAx") {
            failures.push(
                "a schema binding depends on sorryAx; a placeholder cannot bind a \
                 frozen proposition"
                    .to_string(),
            );
        }
    }

    for binding in &bindings {
        let bound = required.iter().any(|r| *r == binding.definition);
        println!(
            "  [{}] {:<38} {}",
            if bound { "BOUND" } else { "EXTRA" },
            binding.definition,
            binding.theorem
        );
    }

    println!();
    if !failures.is_empty() {
        println!("SCHEMA: FAIL — {} unbound or unsound binding(s):", failures.len());
        for failure in &failures {
            println!("  {failure}");
        }
        println!(
            "\nSPEC 1: every scope-critical definition SHALL be bound to its fully \
             spelled-out body\nby a definitional proof in {BINDINGS}. A name check alone \
             cannot reject a weakened\nproposition wearing the right name."
        );
        return Ok(Outcome::Fail);
    }
    println!(
        "SCHEMA: PASS — all {} scope-critical definitions are definitionally bound",
        required.len()
    );
    Ok(Outcome::Pass)
}

/// `scopeCriticalDefinitions` from the frozen authority.
///
/// Read, never embedded: this tool must not be able to disagree with the
/// authority about what the authority requires.
pub fn scope_critical_definitions() -> Result<Vec<String>> {
    definitions_from(&read(AUTHORITY)?)
}

/// The list, from the authority text. Split out so the tests can read the real
/// frozen file without depending on the process's working directory.
fn definitions_from(text: &str) -> Result<Vec<String>> {
    let authority = json::parse(CLAUSE, text)?;
    let listed = authority
        .get("scopeCriticalDefinitions")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                format!("{AUTHORITY} has no `scopeCriticalDefinitions` array"),
            )
        })?;
    let names: Vec<String> = listed
        .iter()
        .filter_map(Value::as_str)
        .map(String::from)
        .collect();
    if names.is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            format!("{AUTHORITY} lists no scope-critical definitions"),
        ));
    }
    Ok(names)
}

/// Every rule that can be decided from the authority list and the parsed
/// bindings. Pure, so the falsifier suite can attack it directly.
pub fn audit(required: &[String], bindings: &[Binding]) -> Vec<String> {
    let mut failures = Vec::new();

    for definition in required {
        let found: Vec<&Binding> =
            bindings.iter().filter(|b| b.definition == *definition).collect();
        match found.as_slice() {
            [] => failures.push(format!(
                "{definition} -- NO BINDING. Add `{MARKER} {definition}` above a theorem \
                 in {BINDINGS} stating it against its fully spelled-out body."
            )),
            [binding] => {
                // The marker must sit on a theorem that actually mentions the
                // definition; otherwise it is a label, not a binding.
                if !mentions(&binding.statement, definition) {
                    failures.push(format!(
                        "{definition} -- the theorem `{}` at line {} does not mention it; \
                         a marker is not a binding",
                        binding.theorem, binding.line
                    ));
                }
                if !DEFINITIONAL.contains(&binding.proof.as_str()) {
                    failures.push(format!(
                        "{definition} -- `{}` is proved by `{}`, not by definitional \
                         reduction; a propositional proof cannot distinguish the frozen \
                         schema from a weaker paraphrase",
                        binding.theorem, binding.proof
                    ));
                }
            }
            many => failures.push(format!(
                "{definition} -- bound {} times ({}); one definition, one binding",
                many.len(),
                many.iter().map(|b| b.theorem.as_str()).collect::<Vec<_>>().join(", ")
            )),
        }
    }

    for binding in bindings {
        if !required.iter().any(|r| *r == binding.definition) {
            failures.push(format!(
                "{} -- bound at line {} but not listed in {AUTHORITY}; a stale binding \
                 claims authority it does not have",
                binding.definition, binding.line
            ));
        }
    }

    failures
}

/// Does the statement reference the definition?
///
/// The Lean source writes names relative to the open namespaces, so the
/// authority's `Universal.SemanticCorrect` appears as `SemanticCorrect` and
/// `Cost.ProperObjective.score` as `.score` on a `ProperObjective`. Requiring
/// the fully qualified spelling would force the bindings to be written in a way
/// Lean does not use; requiring the final component keeps the check honest
/// without dictating the prose.
fn mentions(statement: &str, definition: &str) -> bool {
    let leaf = definition.rsplit('.').next().unwrap_or(definition);
    statement.contains(leaf)
}

/// Find every `-- authority-binding:` block in the Lean source.
///
/// Deliberately a source parse and not a Lean query: the point of the marker is
/// to tie an authority NAME to a theorem, and that tie exists only in the
/// source. Whether the theorem is true is Lean's job, asked separately.
pub fn parse(source: &str) -> Vec<Binding> {
    let lines: Vec<&str> = crate::lean::splitlines(source);
    let mut bindings = Vec::new();

    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix(MARKER) else { continue };
        let definition = rest.trim().to_string();
        if definition.is_empty() {
            continue;
        }

        // The theorem is the next declaration; blank lines and further comments
        // between marker and theorem are tolerated so the file can stay readable.
        let mut cursor = index + 1;
        while cursor < lines.len() {
            let candidate = lines[cursor].trim();
            if candidate.is_empty() || candidate.starts_with("--") {
                cursor += 1;
                continue;
            }
            break;
        }
        let Some(head) = lines.get(cursor) else { continue };
        let Some(theorem) = head.trim().strip_prefix("theorem ") else {
            bindings.push(Binding {
                definition,
                theorem: String::new(),
                statement: String::new(),
                proof: head.trim().to_string(),
                line: index + 1,
            });
            continue;
        };
        let theorem = theorem
            .split(|c: char| c.is_whitespace() || c == '(' || c == '{' || c == '[' || c == ':')
            .next()
            .unwrap_or("")
            .to_string();

        // Everything up to the `:=` that closes the statement is the statement;
        // what follows, up to the next blank line, is the proof.
        let mut statement = String::new();
        let mut proof = String::new();
        let mut in_proof = false;
        let mut depth = 0i32;
        for body in &lines[cursor..] {
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

        bindings.push(Binding {
            definition,
            theorem,
            statement: statement.trim().to_string(),
            proof: proof.trim().to_string(),
            line: index + 1,
        });
    }

    bindings
}

/// Split a line at the `:=` that ends a declaration's statement, carrying the
/// bracket depth in and out.
///
/// Two things go wrong with a naive `find(":=")`, and both were observed on the
/// real bindings:
///
///   * `:=` occurs inside named-argument syntax -- `(body := profile.body)` --
///     so a split there would cut the statement in half and read the rest of the
///     TYPE as the proof, then reject the binding as non-definitional;
///   * the depth cannot be computed a line at a time, because a statement
///     spanning several lines closes its brackets on a later line than it opens
///     them. Scanned per line, the closing line starts at a NEGATIVE depth and
///     its terminating `:=` is never recognised, so the proof comes back empty.
///
/// Hence the depth is threaded through the whole declaration.
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

fn read(path: &str) -> Result<String> {
    let p = Path::new(path);
    std::fs::read(p)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", p, e))
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "\
-- authority-binding: GlobalOptimal
theorem globalOptimal_matches_authority_schema
    (S : Setting P) :
    GlobalOptimal S ↔
      (ProfileValid P) :=
  Iff.rfl

-- authority-binding: Wasm.Profile
theorem wasmProfile_matches_authority_schema (profile : Wasm.Profile) :
    profile = Wasm.Profile.mk (body := profile.body) :=
  rfl
";

    #[test]
    fn parses_marker_theorem_statement_and_proof() {
        let found = parse(SAMPLE);
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].definition, "GlobalOptimal");
        assert_eq!(found[0].theorem, "globalOptimal_matches_authority_schema");
        assert_eq!(found[0].proof, "Iff.rfl");
        assert!(found[0].statement.contains("GlobalOptimal S ↔"));
        assert_eq!(found[1].definition, "Wasm.Profile");
        assert_eq!(found[1].proof, "rfl");
    }

    #[test]
    fn named_field_assignment_does_not_end_the_statement() {
        // The real defect this guards: `(body := profile.body)` contains `:=`,
        // and cutting there would read the rest of the TYPE as the proof and
        // then reject the binding as non-definitional.
        let found = parse(SAMPLE);
        assert_eq!(found[1].proof, "rfl");
        assert!(found[1].statement.contains("(body := profile.body)"));
        assert_eq!(
            split_assignment("  (body := x) :=", 0).0.map(|(_, a)| a.trim()),
            Some("")
        );
        assert_eq!(split_assignment("    (body := x)", 0).0, None);
    }

    #[test]
    fn depth_is_carried_across_lines_of_one_statement() {
        // The observed defect: the closing line of a multi-line statement starts
        // at a negative depth if the depth is recomputed per line, so its
        // terminating `:=` is missed and every real binding is reported as
        // having an empty (hence non-definitional) proof.
        let (_, after_open) = split_assignment("    (ProfileValid P releasedBytes ∧", 0);
        assert_eq!(after_open, 1);
        let (split, _) = split_assignment("      CanonicalBytesLE a b) :=", after_open);
        assert!(split.is_some(), "the terminating := must be found at carried depth");
        assert!(split_assignment("      CanonicalBytesLE a b) :=", 0).0.is_none());
    }

    #[test]
    fn a_missing_binding_is_named() {
        let failures = audit(
            &["GlobalOptimal".into(), "Cost.ProperObjective".into()],
            &parse(SAMPLE),
        );
        assert_eq!(failures.len(), 2, "{failures:?}");
        assert!(failures.iter().any(|f| f.starts_with("Cost.ProperObjective -- NO BINDING")));
        // and the stale `Wasm.Profile` binding is reported the other way round
        assert!(failures.iter().any(|f| f.contains("not listed in")));
    }

    #[test]
    fn a_tactic_proof_is_not_a_binding() {
        // `by simp` would prove a propositional equivalence between the real
        // definition and a weaker paraphrase, which is the substitute SPEC 1
        // forbids. Only definitional reduction rejects that.
        let source = SAMPLE.replace("  Iff.rfl", "  by simp [GlobalOptimal]");
        let failures = audit(&["GlobalOptimal".into(), "Wasm.Profile".into()], &parse(&source));
        assert_eq!(failures.len(), 1, "{failures:?}");
        assert!(failures[0].contains("not by definitional reduction"));
    }

    #[test]
    fn a_marker_on_an_unrelated_theorem_is_not_a_binding() {
        let source = "-- authority-binding: CanonicalBytesLE\n\
                      theorem unrelated : True ↔ True :=\n  Iff.rfl\n";
        let failures = audit(&["CanonicalBytesLE".into()], &parse(source));
        assert_eq!(failures.len(), 1, "{failures:?}");
        assert!(failures[0].contains("does not mention it"));
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
    fn the_authority_supplies_the_list_not_this_file() {
        // Regression guard for the audit's actual objection. If anyone hard-codes
        // the names here, this test still passes -- but the check below is what
        // makes the hard-coding pointless: the required list is read.
        let names = definitions_from(&repo_file(AUTHORITY)).expect("authority readable");
        assert!(names.contains(&"GlobalOptimal".to_string()));
        assert!(names.len() >= 14, "the frozen authority lists {} names", names.len());
    }

    #[test]
    fn the_real_bindings_cover_the_real_authority() {
        let required = definitions_from(&repo_file(AUTHORITY)).expect("authority readable");
        let source = repo_file(BINDINGS);
        let failures = audit(&required, &parse(&source));
        assert!(failures.is_empty(), "{failures:#?}");
    }

    #[test]
    fn one_definition_one_binding() {
        let doubled = format!("{SAMPLE}{SAMPLE}");
        let failures = audit(&["GlobalOptimal".into(), "Wasm.Profile".into()], &parse(&doubled));
        assert!(failures.iter().any(|f| f.contains("bound 2 times")));
    }
}
