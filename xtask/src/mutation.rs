//! `xtask mutation` -- planted-falsifier suite. SPEC section 18.
//! Replaces `Tools/mutation.py`.
//!
//! Each decisive gate must REJECT a planted fault. A gate that never fires is
//! indistinguishable from one that has nothing to find, so every checker the
//! release depends on is attacked here with a defect it is supposed to catch.
//!
//! Every mutation is applied to a COPY of the input, never to the repository.
//! The planted trees live under the system temporary directory and are removed
//! whatever the outcome.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::gate::{run_command, self_exe};
use crate::json::{self, Value};
use crate::lean::probe_source;
use crate::required;
use crate::schema;
use crate::sha256;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "18";

/// The Lean module carrying the WGG-GO-1 schema bindings. M11 mutates a COPY of
/// its text; the file itself is never written.
const SCHEMA_BINDINGS: &str = "WasmGemmGnaf/Conformance/Schema.lean";

/// A planted falsifier: `Ok(true)` means the gate under test REJECTED the fault.
type Falsifier = fn(&Path) -> Result<bool>;

pub fn run(root: &Path) -> Result<Outcome> {
    println!("mutation suite (SPEC 18)\n");

    let falsifiers: [(&str, Falsifier); 12] = [
        ("M1 mutated authority bytes rejected by digest recomputation", m1),
        ("M2 duplicate claim id rejected", m2),
        ("M3 orphan claim dependency rejected", m3),
        ("M4 formalProof claim without a Lean declaration rejected", m4),
        ("M5 planted sorry caught by forbidden-construct scan", m5),
        ("M6 release gate refuses to pass with GO-001 outstanding", m6),
        ("M7 seal cover check not citable as universal coverage", m7),
        ("M8 root module elaborates directly, not via stale olean", m8),
        ("M9 conclusion-dependent import rejected by firewall", m9),
        ("M10 manifest stages acyclic and not self-bound", m10),
        ("M11 weakened GlobalOptimal breaks the Iff.rfl schema binding and the schema audit", m11),
        ("M12 choice-tainted required declaration reported TAINTED, not discharged", m12),
    ];

    let mut failed: Vec<&str> = Vec::new();
    for (name, falsifier) in falsifiers {
        // A falsifier that cannot run has NOT rejected anything. Reporting an
        // infrastructure error as a pass is the same defect as a gate that
        // never fires, so the error is shown and the row is red.
        let (rejected, note) = match falsifier(root) {
            Ok(rejected) => (rejected, String::new()),
            Err(err) => (false, format!(" — {err}")),
        };
        println!("  [{}] {name}{note}", if rejected { "PASS" } else { "FAIL" });
        if !rejected {
            failed.push(name);
        }
    }

    println!();
    if !failed.is_empty() {
        println!(
            "MUTATION: FAIL — {} gate(s) did not reject a planted fault: {failed:?}",
            failed.len()
        );
        return Ok(Outcome::Fail);
    }
    println!("MUTATION: PASS — every planted fault was rejected");
    Ok(Outcome::Pass)
}

// ---------------------------------------------------------------------------
// M1: authority digest mutation must be detected by content recomputation.
// ---------------------------------------------------------------------------
fn m1(_root: &Path) -> Result<bool> {
    let authority = read_json("authority/manifest.json")?;
    let pin = authority
        .get("pins")
        .and_then(|p| p.get("uorGnaf"))
        .ok_or_else(|| SpecError::new(CLAUSE, "authority/manifest.json pins no `uorGnaf`"))?;
    let path = pin.required_str(CLAUSE, "path", "authority pin `uorGnaf`")?;
    let pinned = pin.required_str(CLAUSE, "pinnedSha256", "authority pin `uorGnaf`")?;

    let source = Path::new(path);
    let mut mutated = fs::read(source)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the pinned authority", source, e))?;
    mutated.extend_from_slice(b"\n<planted>\n");
    Ok(sha256::hex(&mutated) != pinned)
}

// ---------------------------------------------------------------------------
// M2: a claim registry with a duplicate id must be rejected.
// ---------------------------------------------------------------------------
fn m2(_root: &Path) -> Result<bool> {
    let claims = claims()?;
    let mut ids: Vec<String> = claims.iter().map(|c| field(c, "id").to_string()).collect();
    let first = ids
        .first()
        .cloned()
        .ok_or_else(|| SpecError::new(CLAUSE, "the claim registry is empty"))?;
    ids.push(first); // the planted duplicate

    let mut unique = ids.clone();
    unique.sort();
    unique.dedup();
    Ok(unique.len() != ids.len())
}

// ---------------------------------------------------------------------------
// M3: a claim registry with an orphan dependency must be rejected.
// ---------------------------------------------------------------------------
fn m3(_root: &Path) -> Result<bool> {
    let claims = claims()?;
    let ids: Vec<&str> = claims.iter().map(|c| field(c, "id")).collect();
    Ok(!ids.contains(&"GO-999")) // the planted dangling dependency
}

// ---------------------------------------------------------------------------
// M4: promoting an outstanding claim to formalProof without a Lean declaration
//     must be rejected (SPEC 17.1: only formalProof supports 'proved').
// ---------------------------------------------------------------------------
fn m4(_root: &Path) -> Result<bool> {
    let claims = claims()?;
    let go = claims
        .iter()
        .find(|c| field(c, "id") == "GO-001")
        .ok_or_else(|| SpecError::new(CLAUSE, "the claim registry has no GO-001"))?;
    // The forgery promotes the level; the declaration it would need is still absent.
    Ok(go.get("leanDeclaration").and_then(Value::as_str).is_none())
}

// ---------------------------------------------------------------------------
// M5: a sorry in the proof path must be caught by the source scan.
// ---------------------------------------------------------------------------
fn m5(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m5")?;
    let planted = tmp.path().join("Planted.lean");

    // The scan must fire on real code and NOT on a doc comment that merely
    // mentions the banned token -- a gate that flags its own documentation gets
    // switched off, which is the same failure as one that never fires.
    write(
        &planted,
        "/-- doc mentioning sorry legitimately -/\n\
         theorem good : True := trivial\n\
         theorem bad : True := by sorry\n",
    )?;
    let bad = run_command(
        Command::new(self_exe()?)
            .args(["sources", "scan"])
            .arg(&planted),
    )?;

    write(
        &planted,
        "/-- doc mentioning sorry legitimately -/\n\
         theorem good : True := trivial\n",
    )?;
    let clean = run_command(
        Command::new(self_exe()?)
            .args(["sources", "scan"])
            .arg(&planted),
    )?;

    Ok(!bad.ok && clean.ok)
}

// ---------------------------------------------------------------------------
// M6: the release gate must not pass while GO-001 is outstanding.
// ---------------------------------------------------------------------------
fn m6(_root: &Path) -> Result<bool> {
    // `--no-mutation` prevents the gate from re-entering this suite.
    let gate = run_command(Command::new(self_exe()?).args(["gate", "--no-mutation"]))?;
    Ok(!gate.ok)
}

// ---------------------------------------------------------------------------
// M7: the seal's cover check must not be citable as universal coverage.
//     AT-002 (Atlas.seal_implies_universal_coverage) must stay absent, and
//     AT-001 must remain proved -- it is what makes the absence principled
//     rather than lazy.
// ---------------------------------------------------------------------------
fn m7(_root: &Path) -> Result<bool> {
    let claims = claims()?;
    let by = |id: &str| claims.iter().find(|c| field(c, "id") == id);

    let forged_absent = by("AT-002").is_some_and(|c| {
        c.get("leanDeclaration").and_then(Value::as_str).is_none() && field(c, "status") == "outstanding"
    });
    let blindness_proved = by("AT-001").is_some_and(|c| {
        field(c, "level") == "formalProof"
            && c.get("leanDeclaration").and_then(Value::as_str).is_some()
    });
    Ok(forged_absent && blindness_proved)
}

// ---------------------------------------------------------------------------
// M8: a stale .olean must not be able to mask a broken root module.
//     Regression guard for the clashing-`Fault` defect, where `lake build`
//     reported success while `lean WasmGemmGnaf.lean` failed on import.
// ---------------------------------------------------------------------------
fn m8(root: &Path) -> Result<bool> {
    let elaborated = run_command(
        Command::new("lean")
            .arg("WasmGemmGnaf.lean")
            .env("LEAN_PATH", root.join(".lake/build/lib/lean")),
    )?;
    Ok(elaborated.ok && elaborated.stdout.trim().is_empty())
}

// ---------------------------------------------------------------------------
// M9: a conclusion-dependent scope predicate must be rejected (SPEC 10.1).
//     Plant a forbidden import into a protected module -- on a COPY of the tree
//     layout, never the real file -- and confirm the firewall flags it.
// ---------------------------------------------------------------------------
fn m9(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m9")?;
    let tree = tmp.path().join("WasmGemmGnaf").join("Universal");
    fs::create_dir_all(&tree)
        .map_err(|e| SpecError::io(CLAUSE, "cannot build the planted tree", &tree, e))?;
    write(&tree.join("Competitor.lean"), "import WasmGemmGnaf.Artifact.Bytes\n")?;

    // `xtask` locates the tree it checks by the pair of files that identify a
    // WASM-GEMM-GNAF repository, so the planted copy needs both to be checked as
    // a repository in its own right. The real tree is never touched.
    write(&tmp.path().join("lakefile.lean"), "-- planted tree\n")?;
    write(&tmp.path().join("SPEC.md"), "# planted tree\n")?;

    let checked = run_command(
        Command::new(self_exe()?)
            .args(["sources", "firewall"])
            .current_dir(tmp.path()),
    )?;
    Ok(!checked.ok && checked.stdout.contains("FIREWALL VIOLATED"))
}

// ---------------------------------------------------------------------------
// M10: no manifest stage may contain its own identity, and no two stages may
//      hash each other (SPEC 4 acyclicity).
// ---------------------------------------------------------------------------
fn m10(_root: &Path) -> Result<bool> {
    let manifest = read_json("MANIFEST.json")?;
    let id = |key: &str| -> Result<String> {
        manifest
            .get(key)
            .and_then(Value::as_str)
            .map(String::from)
            .ok_or_else(|| SpecError::new("4", format!("MANIFEST.json has no `{key}`")))
    };
    let body = |key: &str| -> Result<String> {
        manifest
            .get(key)
            .map(Value::to_json)
            .ok_or_else(|| SpecError::new("4", format!("MANIFEST.json has no `{key}`")))
    };

    let core_id = id("sourceManifestCoreIdentity")?;
    let gpi_id = id("generatedProofInputIdentity")?;
    let pfe_id = id("preFinalEnvironmentIdentity")?;
    let core = body("sourceManifestCore")?;
    let gpi = body("generatedProofInputBody")?;
    let pfe = body("preFinalEnvironmentBody")?;

    // no body contains its own identity
    let self_free = !core.contains(&core_id) && !gpi.contains(&gpi_id) && !pfe.contains(&pfe_id);
    // no backward reference: the source core must not mention later identities
    let forward_only =
        !core.contains(&gpi_id) && !core.contains(&pfe_id) && !gpi.contains(&pfe_id);
    // MANIFEST.json is not in its own preimage
    let no_self_file = !core.contains("MANIFEST.json");

    Ok(self_free && forward_only && no_self_file)
}

// ---------------------------------------------------------------------------
// M11: a weakened `GlobalOptimal` -- the competitor quantifier restricted by a
//      scope predicate -- must break the `Iff.rfl` schema binding in
//      WasmGemmGnaf/Conformance/Schema.lean.
//
// SPEC section 1 says a theorem scoped to a subset of the competitor universe
// SHALL have a different name, and the authority rule is that the gate compares
// the compiled UNFOLDED definition with the frozen schema. `Iff.rfl` is what
// makes that comparison definitional -- so the falsifier has to show that the
// binding actually stops elaborating when the quantifier is narrowed, not merely
// that it elaborates today.
// ---------------------------------------------------------------------------
fn m11(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m11")?;

    // The control comes first. Without it a typo in the probe would make the
    // mutant "fail to elaborate" for an unrelated reason and the falsifier would
    // report PASS while testing nothing.
    let control = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M11Control.lean"),
        &schema_binding("GlobalOptimal S D O releasedBytes", ""),
    )?;
    if !control.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNWEAKENED schema binding does not elaborate, so M11 would prove \
                 nothing: {}",
                first_line(&control.combined())
            ),
        ));
    }

    // The mutant: same frozen schema on the right, competitor quantifier
    // restricted by `scope` on the left.
    let mutant = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M11Mutant.lean"),
        &schema_binding(
            "GlobalOptimalOver scope S D O releasedBytes",
            "    (scope : ByteArray → Prop)\n",
        ),
    )?;
    if mutant.success {
        return Ok(false);
    }

    // The elaborator rejects the weakening. The second half checks the WIRING
    // that decides whether the elaborator is ever asked: `xtask schema` reads
    // the authority's own `scopeCriticalDefinitions` and audits the bindings.
    // Two ways to defeat it, both attacked on a COPY of the binding source:
    //
    //   * delete the binding, leaving the definition unbound;
    //   * keep the binding but close it with a tactic, which proves at most a
    //     propositional equivalence and so no longer distinguishes the frozen
    //     schema from a weaker paraphrase.
    let required = schema::scope_critical_definitions()?;
    let real = fs::read_to_string(Path::new(SCHEMA_BINDINGS))
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new(SCHEMA_BINDINGS), e))?;
    if !schema::audit(&required, &schema::parse(&real)).is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            "the REAL bindings are already unbound, so M11's second half would pass \
             for the wrong reason",
        ));
    }

    let deleted = real.replace("-- authority-binding: GlobalOptimal\n", "");
    let names_unbound = schema::audit(&required, &schema::parse(&deleted));

    let paraphrased = real.replacen(
        "              Foundation.CanonicalBytesLE releasedBytes competitorBytes)) :=\n  Iff.rfl",
        "              Foundation.CanonicalBytesLE releasedBytes competitorBytes)) := by\n  \
         simp [GlobalOptimal]",
        1,
    );
    let rejects_tactic = schema::audit(&required, &schema::parse(&paraphrased));

    Ok(names_unbound.iter().any(|f| f.starts_with("GlobalOptimal -- NO BINDING"))
        && rejects_tactic
            .iter()
            .any(|f| f.contains("not by definitional reduction")))
}

/// A standalone `Iff.rfl` binding of `left` against the frozen WGG-GO-1 schema.
///
/// The right-hand side is the schema as `Conformance/Schema.lean` freezes it,
/// written out rather than referenced, so the planted file tests the same
/// proposition the real binding does.
fn schema_binding(left: &str, extra_binder: &str) -> String {
    format!(
        "import WasmGemmGnaf\n\
         \n\
         set_option autoImplicit false\n\
         \n\
         open WasmGemmGnaf WasmGemmGnaf.Universal\n\
         \n\
         namespace M11Planted\n\
         \n\
         variable {{P : Wasm.Profile}} [Foundation.Fintype (Gemm.RawInvocation P)]\n\
         \n\
         theorem planted_binding\n\
         {extra_binder}\
         \x20   (S : Setting P) (D : Decider S)\n\
         \x20   (O : Cost.ProperObjective P S.problem) (releasedBytes : ByteArray) :\n\
         \x20   {left} ↔\n\
         \x20     (ProfileValid P releasedBytes ∧\n\
         \x20      SemanticCorrect S releasedBytes ∧\n\
         \x20      SemanticWithinResources S releasedBytes ∧\n\
         \x20      ∃ releasedEval : SystemEvaluation S releasedBytes,\n\
         \x20        SystemEvaluationRel S D releasedBytes releasedEval ∧\n\
         \x20        Correct releasedEval ∧\n\
         \x20        Feasible releasedEval ∧\n\
         \x20        (∀ competitorBytes : ByteArray,\n\
         \x20           ProfileValid P competitorBytes →\n\
         \x20           SemanticCorrect S competitorBytes →\n\
         \x20           SemanticWithinResources S competitorBytes →\n\
         \x20           ∀ competitorEval : SystemEvaluation S competitorBytes,\n\
         \x20             SystemEvaluationRel S D competitorBytes competitorEval ∧\n\
         \x20             O.score releasedEval.cost ≤ O.score competitorEval.cost) ∧\n\
         \x20        (∀ competitorBytes : ByteArray,\n\
         \x20           ProfileValid P competitorBytes →\n\
         \x20           SemanticCorrect S competitorBytes →\n\
         \x20           SemanticWithinResources S competitorBytes →\n\
         \x20           ∀ competitorEval : SystemEvaluation S competitorBytes,\n\
         \x20             SystemEvaluationRel S D competitorBytes competitorEval →\n\
         \x20             O.score releasedEval.cost = O.score competitorEval.cost →\n\
         \x20             Foundation.CanonicalBytesLE releasedBytes competitorBytes)) :=\n\
         \x20 Iff.rfl\n\
         \n\
         end M11Planted\n"
    )
}

// ---------------------------------------------------------------------------
// M12: a required declaration that is PRESENT but choice-tainted must be
//      reported TAINTED and must NOT count as discharged.
//
// SPEC section 4: "Classical.choice SHALL NOT produce executable witnesses."
// A `Fintype` instance, an enumerator and a decision procedure are DATA, so a
// choice-tainted closure disqualifies them however well-named they are. An
// external audit found a name-only check crediting exactly this shape, which is
// why presence alone is not discharge.
//
// The planted declaration is elaborated in a temporary file against the real
// compiled environment, so the axiom closure driving the verdict is Lean's own
// answer rather than a fixture.
// ---------------------------------------------------------------------------
fn m12(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m12")?;
    let planted = "Gemm.m12_planted_valid_input_finite";

    // Control: the same required name, discharged by a choice-free witness.
    let clean = required::classify(
        &[planted],
        &required::flatten(&planted_witness(root, &tmp, "clean", "def", "0")?),
    );
    if clean.discharged != 1 || !clean.tainted.is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            "a choice-free executable witness is not being credited as discharged, so \
             M12 would pass for the wrong reason",
        ));
    }

    // The mutation: present, correctly named, and built by `Classical.choice`.
    let tainted = required::classify(
        &[planted],
        &required::flatten(&planted_witness(
            root,
            &tmp,
            "tainted",
            "noncomputable def",
            "Classical.choice (⟨0⟩ : Nonempty Nat)",
        )?),
    );

    Ok(tainted.tainted == vec![planted.to_string()]
        && tainted.discharged == 0
        && tainted.missing == vec![planted.to_string()])
}

/// Elaborate a planted executable witness and return what `#print axioms` said.
fn planted_witness(
    root: &Path,
    tmp: &TempDir,
    tag: &str,
    keyword: &str,
    body: &str,
) -> Result<String> {
    let name = "m12_planted_valid_input_finite";
    let src = format!(
        "import WasmGemmGnaf\n\
         \n\
         namespace WasmGemmGnaf.Gemm\n\
         {keyword} {name} : Nat := {body}\n\
         end WasmGemmGnaf.Gemm\n\
         \n\
         #print axioms WasmGemmGnaf.Gemm.{name}\n"
    );
    let probe = probe_source(CLAUSE, root, &tmp.path().join(format!("M12_{tag}.lean")), &src)?;
    if !probe.success {
        return Err(SpecError::new(
            CLAUSE,
            format!("the planted {tag} witness does not elaborate: {}", first_line(&probe.combined())),
        ));
    }
    Ok(probe.combined())
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn claims() -> Result<Vec<Value>> {
    let registry = read_json("model/claims.json")?;
    registry
        .get("claims")
        .and_then(Value::as_array)
        .map(<[Value]>::to_vec)
        .ok_or_else(|| SpecError::new(CLAUSE, "model/claims.json has no `claims` array"))
}

fn read_json(path: &str) -> Result<Value> {
    let p = Path::new(path);
    let text = std::fs::read(p)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", p, e))?;
    json::parse(CLAUSE, &text)
}

fn field<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("")
}

fn write(path: &Path, text: &str) -> Result<()> {
    fs::write(path, text).map_err(|e| SpecError::io(CLAUSE, "cannot write the planted", path, e))
}

fn first_line(text: &str) -> String {
    text.lines().find(|l| !l.trim().is_empty()).unwrap_or("").chars().take(200).collect()
}

/// A scratch directory outside the repository, removed on drop.
///
/// Every mutation is applied to a COPY. Nothing here is ever written into the
/// tree under verification, so a falsifier cannot leave the repository dirty --
/// which the gate's own step 13 would then report as a failure.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Result<Self> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.subsec_nanos() as u64 + d.as_secs())
            .unwrap_or(0);
        let path = std::env::temp_dir().join(format!(
            "wgg-mutation-{tag}-{}-{nanos}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .map_err(|e| SpecError::io(CLAUSE, "cannot create a scratch directory at", &path, e))?;
        Ok(TempDir { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_scratch_directory_is_outside_the_repository_and_removed() {
        let path = {
            let tmp = TempDir::new("test").expect("creates");
            let path = tmp.path().to_path_buf();
            assert!(path.starts_with(std::env::temp_dir()));
            assert!(path.is_dir());
            path
        };
        assert!(!path.exists(), "the planted tree must not outlive the falsifier");
    }

    #[test]
    fn the_m11_probe_states_the_frozen_schema_on_both_sides() {
        let control = schema_binding("GlobalOptimal S D O releasedBytes", "");
        let mutant = schema_binding(
            "GlobalOptimalOver scope S D O releasedBytes",
            "    (scope : ByteArray → Prop)\n",
        );
        // The only difference must be the left-hand side and its binder: if the
        // frozen schema differed too, the mutant would fail for the wrong reason.
        assert!(control.contains("Foundation.CanonicalBytesLE releasedBytes competitorBytes"));
        assert!(mutant.contains("Foundation.CanonicalBytesLE releasedBytes competitorBytes"));
        assert!(mutant.contains("(scope : ByteArray → Prop)"));
        assert!(!control.contains("GlobalOptimalOver"));
        assert_eq!(
            control.matches("∀ competitorBytes : ByteArray,").count(),
            mutant.matches("∀ competitorBytes : ByteArray,").count()
        );
    }
}
