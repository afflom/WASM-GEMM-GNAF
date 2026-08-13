//! `xtask claims required [--list] [--check]` -- SPEC section 15 inventory,
//! checked against the COMPILED environment. Replaces `Tools/required.py`.
//!
//! SPEC section 15 lists the public declarations a conforming repository must
//! have with fully implemented bodies and proofs. The claims registry tracks
//! obligations at a coarser grain, so it understates the remaining proof
//! surface. This derives the inventory from `SPEC.md` itself and asks Lean
//! whether each name exists, rather than trusting a hand-maintained status
//! field.

use std::path::Path;

use crate::lean::probe_axioms;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "15";
const PROBE: &str = ".required_probe.lean";

/// SPEC section 4: "Classical.choice SHALL NOT produce executable witnesses."
///
/// A `Fintype` instance, an enumerator and a decision procedure are DATA, so a
/// choice-tainted closure disqualifies them however well-named they are. Name
/// presence alone is not discharge; an external audit correctly refused to
/// credit one declaration that a name-only check had passed.
const EXECUTABLE_WITNESS: [&str; 4] = [
    "_finite",         // Foundation.Fintype instances
    "enumerator",      // input/byte enumerators
    "_enumerate",
    "decode_complete", // executable decoder completeness carries the decoder
];

/// What the compiled environment says about the SPEC section 15 inventory.
pub struct Report {
    pub total: usize,
    pub discharged: usize,
    /// Not discharged: absent, choice-tainted, or with no exact signature binding.
    pub missing: Vec<String>,
    /// Present, but a `Classical.choice` closure in a declaration SPEC section 4
    /// requires to be an executable witness. Also counted in `missing`.
    pub tainted: Vec<String>,
    /// Present and choice-free -- what the NAME-and-axiom rule alone credits.
    /// This is the pre-signature verdict, kept so `xtask signature` can ask what
    /// the environment says without the two checks agreeing by construction.
    pub credited: Vec<String>,
    /// Present and choice-free, but with no `-- spec-signature:` binding, so not
    /// known to carry SPEC's proposition. Also counted in `missing`.
    pub unsigned: Vec<String>,
    /// Present, signed, but whose reflection independence fails: the declarative
    /// side is defined or proved through the executable side, so the theorem is
    /// circular. Also counted in `missing`.
    pub circular: Vec<String>,
    /// Credited, and bound -- but to a proposition this repository CHOSE, because
    /// SPEC 15 lists the name while no section states it in a fenced block. The
    /// binding is exact against that reading; there is no SPEC text to compare
    /// it with. Reported so the headline number never appears without it.
    pub in_house: usize,
}

impl Report {
    /// Exactly the lines `xtask claims required` prints. The gate quotes these,
    /// so the rendering lives here rather than in two places that can drift.
    pub fn render(&self, list: bool) -> String {
        let mut out = vec![
            format!("SPEC 15 required declarations: {}", self.total),
            format!("  discharged : {}", self.discharged),
            format!("  outstanding: {}", self.missing.len()),
        ];
        if !self.tainted.is_empty() {
            out.push(format!(
                "  of which choice-tainted executable witnesses: {}",
                self.tainted.len()
            ));
            for name in &self.tainted {
                out.push(format!(
                    "    TAINTED  {name}  (Classical.choice in an executable witness, SPEC 4)"
                ));
            }
        }
        if !self.unsigned.is_empty() {
            out.push(format!(
                "  of which present but not bound to SPEC's proposition: {}",
                self.unsigned.len()
            ));
            for name in &self.unsigned {
                out.push(format!(
                    "    UNBOUND  {name}  (no exact `-- spec-signature:` binding, SPEC 15)"
                ));
            }
        }
        if self.in_house > 0 {
            out.push(format!(
                "  of which bound to an IN-HOUSE reading -- SPEC states no fenced \
                 proposition for the name: {}",
                self.in_house
            ));
        }
        if !self.circular.is_empty() {
            out.push(format!(
                "  of which circular -- the declarative side is the executable side: {}",
                self.circular.len()
            ));
            for name in &self.circular {
                out.push(format!(
                    "    CIRCULAR {name}  (reflection independence fails, SPEC 7.3; \
                     run `xtask independence`)"
                ));
            }
        }
        if list {
            for name in &self.missing {
                if !self.tainted.contains(name)
                    && !self.unsigned.contains(name)
                    && !self.circular.contains(name)
                {
                    out.push(format!("    MISSING  {name}"));
                }
            }
        }
        out.join("\n")
    }
}

/// Every registry integrity violation SPEC section 17.1 forbids, as a list of
/// human-readable findings. Empty means the registry is well formed.
///
/// This takes a PATH rather than reading the tracked file directly, because the
/// mutation suite must be able to run it against a planted copy. A falsifier
/// that reimplements the check instead of calling it tests its own arithmetic
/// and nothing else; `M2`/`M3`/`M4` did exactly that before this existed, and
/// reported PASS while `model/claims.json` genuinely carried a duplicate id.
pub fn registry_violations(path: &Path) -> Result<Vec<String>> {
    let text = std::fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io("17.1", "cannot read the claim registry", path, e))?;
    let registry = crate::json::parse("17.1", &text)?;
    let claims = registry
        .get("claims")
        .and_then(crate::json::Value::as_array)
        .ok_or_else(|| SpecError::new("17.1", "the claim registry has no `claims` array"))?;

    let field = |claim: &crate::json::Value, key: &str| -> String {
        claim.get(key).and_then(crate::json::Value::as_str).unwrap_or("").to_string()
    };

    let mut findings = Vec::new();

    if claims.is_empty() {
        findings.push("the claim registry is empty".to_string());
    }

    // SPEC 20.2 condition 2: claim ids are unique.
    let ids: Vec<String> = claims.iter().map(|c| field(c, "id")).collect();
    let mut seen: Vec<&String> = Vec::new();
    let mut duplicates: Vec<&String> = Vec::new();
    for id in &ids {
        if seen.contains(&id) {
            if !duplicates.contains(&id) {
                duplicates.push(id);
            }
        } else {
            seen.push(id);
        }
    }
    for id in duplicates {
        findings.push(format!("duplicate claim id: {id}"));
    }

    // SPEC 20.2 condition 2: no `dependsOn` names a claim that is not present.
    for claim in claims {
        for dep in claim.get("dependsOn").and_then(crate::json::Value::as_array).unwrap_or(&[]) {
            if let Some(dep) = dep.as_str() {
                if !ids.iter().any(|id| id == dep) {
                    findings.push(format!(
                        "orphan dependency: {} depends on {dep}, which is not a claim",
                        field(claim, "id")
                    ));
                }
            }
        }
    }

    // SPEC 17.1: only `formalProof` supports "proved"/"theorem"/"globally
    // optimal", and a `formalProof` row without a Lean declaration is exactly
    // the promotion that word discipline forbids.
    for claim in claims {
        if field(claim, "level") == "formalProof" && field(claim, "leanDeclaration").is_empty() {
            findings.push(format!(
                "claim {} is level formalProof with no leanDeclaration",
                field(claim, "id")
            ));
        }
    }

    Ok(findings)
}

/// `xtask claims list` -- the claim registry as a table, and its integrity.
///
/// SPEC section 17.1 makes the LEVEL load-bearing: only `formalProof` supports
/// the words "proved", "theorem" or "globally optimal". Printing the level next
/// to every status is what stops a `documented` row being read as a proof.
///
/// It also VALIDATES. `VERIFICATION.md` has always described this command as
/// checking that the registry is nonempty, its ids unique and its dependencies
/// resolved; until now only `xtask gate` did any of that, so a duplicate id
/// survived `just claims` and was reported only at the very end of `just vv`.
pub fn list_registry() -> Result<Outcome> {
    let path = Path::new("model/claims.json");
    let text = std::fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io("17.1", "cannot read the claim registry", path, e))?;
    let registry = crate::json::parse("17.1", &text)?;
    let claims = registry
        .get("claims")
        .and_then(crate::json::Value::as_array)
        .ok_or_else(|| SpecError::new("17.1", "model/claims.json has no `claims` array"))?;

    println!("claims: {}", claims.len());
    for claim in claims {
        let field = |key: &str| {
            claim
                .get(key)
                .and_then(crate::json::Value::as_str)
                .unwrap_or("")
                .to_string()
        };
        println!("  {:<8} {:<13} {}", field("id"), field("level"), field("status"));
    }

    let findings = registry_violations(path)?;
    if findings.is_empty() {
        println!("\nregistry integrity: ids unique, dependencies resolved, levels backed");
        Ok(Outcome::Pass)
    } else {
        for finding in &findings {
            println!("  REGISTRY VIOLATION: {finding}");
        }
        Ok(Outcome::Fail)
    }
}

pub fn run(root: &Path, list: bool, check: bool) -> Result<Outcome> {
    let report = report(root)?;
    println!("{}", report.render(list));
    Ok(if check && !report.missing.is_empty() { Outcome::Fail } else { Outcome::Pass })
}

/// The SPEC section 15 inventory: the compiled environment's answer, then the
/// signature bindings, then reflection independence.
///
/// Three halves, and none is sufficient. `#print axioms` decides whether a
/// declaration EXISTS and what it rests on. The elaborated `:= @Name` bindings
/// in `Conformance/RequiredSignatures.lean` decide whether it carries SPEC's
/// PROPOSITION -- an external audit found this command crediting a name whose
/// type was `Nat`. And `xtask independence` decides, for the reflection
/// theorems, whether the declarative side is genuinely independent of the
/// executable side -- four audits called those three names circular while the
/// first two checks passed them, because a circular theorem has the right name
/// AND the right statement AND a clean axiom closure. Only the proof term shows
/// it.
pub fn report(root: &Path) -> Result<Report> {
    let mut report = environment_report(root)?;
    let bindings = crate::signature::tracked_bindings()?;
    apply_signatures(&mut report, &crate::signature::exact_names(&bindings));
    apply_independence(&mut report, &crate::independence::report(root)?.rejected());

    // How many credited names are bound to a proposition SPEC never states in a
    // fenced block. An adversarial review found one such -- SPEC 15 lists
    // `Atlas.seal_verifier_reconstructs_every_preimage` but no section states it
    // -- and observed that the ledger credits it identically to a
    // verbatim-fenced one. It is not a defect and the binding is honest, but
    // "37 of 58" should never be read as 37 SPEC-fenced statements.
    let spec = std::fs::read(Path::new("SPEC.md"))
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new("SPEC.md"), e))?;
    report.in_house = bindings
        .iter()
        .filter(|b| {
            !report.missing.contains(&b.name) && crate::signature::spec_block(&spec, &b.name).is_none()
        })
        .count();
    Ok(report)
}

/// Demote every credited name whose reflection independence fails.
///
/// Pure and separate for the same reason `apply_signatures` is: `M16` attacks
/// this rule directly, and emptying this function must turn it red.
pub fn apply_independence(report: &mut Report, rejected: &[String]) {
    let circular: Vec<String> = report
        .credited
        .iter()
        .filter(|name| rejected.iter().any(|r| r == *name))
        .cloned()
        .collect();
    for name in &circular {
        if !report.missing.contains(name) {
            report.missing.push(name.clone());
            report.discharged = report.discharged.saturating_sub(1);
        }
    }
    report.circular = circular;
}

/// The compiled environment's answer alone: present, and choice-free where SPEC
/// section 4 requires an executable witness. Split out because `xtask signature`
/// must be able to ask what the environment says WITHOUT the signature rule
/// already applied -- otherwise the two checks would agree by construction and
/// neither would test the other.
pub fn environment_report(root: &Path) -> Result<Report> {
    let spec = std::fs::read(Path::new("SPEC.md"))
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new("SPEC.md"), e))?;
    let names = required_names(&spec)?;

    let probe: Vec<String> = candidates(&names).into_iter().flatten().collect();
    let result = probe_axioms(CLAUSE, root, PROBE, &probe)?;
    Ok(classify(&names, &flatten(&result.combined())))
}

/// Demote every credited name with no EXACT signature binding.
///
/// Pure, and separated from the probe on purpose: this is the rule `M15` has to
/// be able to attack directly. Deleting the body of this function must turn M15
/// red -- that is what makes the falsifier a test of the rule rather than of its
/// own arithmetic.
pub fn apply_signatures(report: &mut Report, exact: &[String]) {
    let unsigned: Vec<String> = report
        .credited
        .iter()
        .filter(|name| !exact.iter().any(|e| e == *name))
        .cloned()
        .collect();
    for name in &unsigned {
        if !report.missing.contains(name) {
            report.missing.push(name.clone());
        }
        report.discharged = report.discharged.saturating_sub(1);
    }
    report.unsigned = unsigned;
}

/// Namespace each bare name under `WasmGemmGnaf`; a `Theorems/` re-export
/// satisfies the requirement too.
fn candidates(names: &[&str]) -> Vec<Vec<String>> {
    names
        .iter()
        .map(|n| {
            let leaf = n.rsplit('.').next().unwrap_or(n);
            vec![format!("WasmGemmGnaf.{n}"), format!("WasmGemmGnaf.Theorems.{leaf}")]
        })
        .collect()
}

/// `#print axioms` output can wrap across lines; flatten the whitespace so a
/// wrapped closure is still one searchable run of text.
pub fn flatten(output: &str) -> String {
    output.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Decide each required declaration from what Lean actually printed.
///
/// Pure, and separated from the probe on purpose: this is the rule the M12
/// falsifier has to be able to attack directly. A declaration that is PRESENT
/// but choice-tainted must come back TAINTED and must NOT be counted as
/// discharged -- an external audit found a name-only check crediting exactly
/// that shape.
pub fn classify(names: &[&str], flat: &str) -> Report {
    let candidates = candidates(names);
    let mut discharged = 0usize;
    let mut missing: Vec<String> = Vec::new();
    let mut tainted: Vec<String> = Vec::new();
    let mut credited: Vec<String> = Vec::new();

    for (name, cands) in names.iter().zip(&candidates) {
        let Some(closure) = cands.iter().find_map(|c| closure_of(flat, c)) else {
            missing.push((*name).to_string());
            continue;
        };
        let axioms = axioms_of(closure).unwrap_or_default();
        let is_witness = EXECUTABLE_WITNESS.iter().any(|k| name.contains(k));
        if is_witness && axioms.contains(&"Classical.choice") {
            tainted.push((*name).to_string());
            missing.push((*name).to_string());
        } else {
            discharged += 1;
            credited.push((*name).to_string());
        }
    }

    Report { total: names.len(), discharged, missing, tainted, credited, unsigned: Vec::new(), circular: Vec::new(), in_house: 0 }
}

/// The declaration list fenced in SPEC section 15.
pub fn required_names(spec: &str) -> Result<Vec<&str>> {
    const HEADING: &str = "## 15. Required Lean declarations";
    let start = spec
        .find(HEADING)
        .ok_or_else(|| SpecError::new(CLAUSE, "SPEC section 15 not found in SPEC.md"))?;
    let section = &spec[start + HEADING.len()..];
    let section = match section.find("\n## 16.") {
        Some(end) => &section[..end],
        None => {
            return Err(SpecError::new(
                CLAUSE,
                "SPEC section 15 is not terminated by section 16; cannot delimit the \
                 required-declaration list",
            ))
        }
    };

    const FENCE: &str = "```lean\n";
    let open = section.find(FENCE).ok_or_else(|| {
        SpecError::new(CLAUSE, "SPEC section 15 has no ```lean block listing the required declarations")
    })?;
    let body = &section[open + FENCE.len()..];
    let close = body
        .find("```")
        .ok_or_else(|| SpecError::new(CLAUSE, "SPEC section 15's ```lean block is unterminated"))?;

    let names: Vec<&str> = body[..close]
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    if names.is_empty() {
        return Err(SpecError::new(CLAUSE, "SPEC section 15 lists no required declarations"));
    }
    Ok(names)
}

/// The `#print axioms` verdict for `declaration`, if Lean reported one.
///
/// Lean answers as `'Name' depends on axioms: [...]`, so the text between the
/// closing quote of the name and the next quote is that declaration's verdict.
fn closure_of<'a>(flat: &'a str, declaration: &str) -> Option<&'a str> {
    let marker = format!("'{declaration}' ");
    let at = flat.find(&marker)?;
    let rest = &flat[at + marker.len()..];
    Some(rest.split('\'').next().unwrap_or(rest))
}

/// Parse the axiom list out of one verdict. `None` means Lean said something
/// that was neither "no axioms" nor an axiom list -- an error, typically.
fn axioms_of(verdict: &str) -> Option<Vec<&str>> {
    if verdict.contains("does not depend on any axioms") {
        return Some(Vec::new());
    }
    const TAG: &str = "depends on axioms:";
    let at = verdict.find(TAG)?;
    Some(
        verdict[at + TAG.len()..]
            .trim()
            .trim_matches(|c| c == '[' || c == ']')
            .split(',')
            .map(str::trim)
            .filter(|a| !a.is_empty())
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_verdict() {
        let flat = "'A.b' depends on axioms: [propext, Classical.choice, Quot.sound] 'A.c' \
                    does not depend on any axioms";
        let b = closure_of(flat, "A.b").expect("found");
        assert_eq!(
            axioms_of(b).expect("list"),
            vec!["propext", "Classical.choice", "Quot.sound"]
        );
        let c = closure_of(flat, "A.c").expect("found");
        assert_eq!(axioms_of(c).expect("list"), Vec::<&str>::new());
        assert!(closure_of(flat, "A.missing").is_none());
    }

    #[test]
    fn executable_witness_names_are_recognised() {
        for name in [
            "Gemm.valid_input_finite",
            "Universal.byte_enumerator_complete",
            "Wasm.decode_complete",
        ] {
            assert!(
                EXECUTABLE_WITNESS.iter().any(|k| name.contains(k)),
                "{name} should count as an executable witness"
            );
        }
        assert!(!EXECUTABLE_WITNESS
            .iter()
            .any(|k| "Universal.all_competitors_lower_bound".contains(k)));
    }

    #[test]
    fn reads_the_spec_block() {
        let spec = "## 15. Required Lean declarations\n\nblah\n\n```lean\nA.one\n\nB.two\n```\n\n## 16. Next\n";
        assert_eq!(required_names(spec).expect("parsed"), vec!["A.one", "B.two"]);
    }

    #[test]
    fn missing_spec_section_is_an_error() {
        assert!(required_names("nothing here").is_err());
    }
}
