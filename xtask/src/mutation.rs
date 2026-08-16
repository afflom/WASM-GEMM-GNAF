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

    let falsifiers: [(&str, Falsifier); 38] = [
        (
            "M1 mutated authority bytes rejected by digest recomputation",
            m1,
        ),
        ("M2 duplicate claim id rejected", m2),
        ("M3 orphan claim dependency rejected", m3),
        (
            "M4 formalProof claim without a Lean declaration rejected",
            m4,
        ),
        ("M5 planted sorry caught by forbidden-construct scan", m5),
        ("M6 release gate step 9 rejects an absent final theorem", m6),
        (
            "M7 Atlas scope-blindness proof rejects a missing dependency",
            m7,
        ),
        (
            "M8 root checker rejects source drift despite a stale olean",
            m8,
        ),
        ("M9 conclusion-dependent import rejected by firewall", m9),
        (
            "M10 manifest checker rejects a backward stage-identity binding",
            m10,
        ),
        (
            "M11 weakened GlobalOptimal breaks the Iff.rfl schema binding and the schema audit",
            m11,
        ),
        (
            "M12 choice-tainted required declaration reported TAINTED, not discharged",
            m12,
        ),
        (
            "M13 mutated vendored SHA256SUMS breaks the pinned-revision binding",
            m13,
        ),
        (
            "M14 fabricated Core coverage marker rejected by the extracted checklist",
            m14,
        ),
        (
            "M15 required name carrying `Nat := 0` rejected by the signature binding",
            m15,
        ),
        (
            "M16 circular reflection theorem rejected by the independence check",
            m16,
        ),
        (
            "M17 amendment-set identity drift rejected by the authority binding",
            m17,
        ),
        (
            "M18 malformed opcode-275 shape rejected by the AMD-012 binding",
            m18,
        ),
        (
            "M19 missing supertype validity rejected by the AMD-013 binding",
            m19,
        ),
        (
            "M20 wrapped Core type-group indices rejected by validator soundness",
            m20,
        ),
        (
            "M21 overlapping lane-store successors retained by exact enumeration",
            m21,
        ),
        (
            "M22 broken public encoders rejected by both round-trip proofs",
            m22,
        ),
        (
            "M23 aggregate byte accounting rejected when detached from emitted bytes",
            m23,
        ),
        (
            "M24 pinned same-state constant initialization rejected by AMD-014",
            m24,
        ),
        (
            "M25 mixed recursive-suffix scope reset rejected by AMD-015",
            m25,
        ),
        ("M26 public costed-step erasure mismatch rejected", m26),
        ("M27 public compiler status epilogue deletion rejected", m27),
        ("M28 forged public evaluator completion rejected", m28),
        ("M29 malformed byte-solved float target rejected", m29),
        ("M30 disconnected canonical costed explorer rejected", m30),
        ("M31 one-page-short Harness raw growth rejected", m31),
        ("M32 implicit-select BOT rejection detected", m32),
        (
            "M33 reducible indexed-null initializer target rejected",
            m33,
        ),
        ("M34 missing computed Harness ABI readiness rejected", m34),
        ("M35 missing local value-type validity rejected", m35),
        ("M36 missing recursive heap-shape coherence rejected", m36),
        ("M37 omitted compiled status assignment rejected", m37),
        ("M38 perturbed compiler execution charge rejected", m38),
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
        println!(
            "  [{}] {name}{note}",
            if rejected { "PASS" } else { "FAIL" }
        );
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
// Registry falsifiers M2-M4.
//
// All three plant a fault in a COPY of `model/claims.json` and then run the
// repository's own checker, `required::registry_violations`, against that copy.
//
// They did not always. Until this rewrite each one reimplemented the check
// inside itself -- M2 appended a duplicate to an in-memory `Vec` and asserted
// that `dedup` shrank it -- so all three tested Rust's standard library and
// nothing else. The suite reported `[PASS] M2 duplicate claim id rejected` at a
// moment when `model/claims.json` genuinely carried two rows with the id
// `UV-004` and `just claims` accepted them. A falsifier that does not invoke
// the gate it names is worth less than no falsifier at all, because it reads as
// evidence.
//
// Every one of the three carries a control: the UNMUTATED copy must produce no
// finding, so a falsifier cannot pass by failing for an unrelated reason (an
// unparseable copy, a missing file, a checker that rejects everything).
// ---------------------------------------------------------------------------

/// Write `registry` to a scratch file and ask the real checker about it,
/// returning the findings it reports.
fn registry_findings(tmp: &TempDir, name: &str, registry: &str) -> Result<Vec<String>> {
    let planted = tmp.path().join(name);
    write(&planted, registry)?;
    required::registry_violations(&planted)
}

/// The tracked registry as text, for mutation.
fn registry_text() -> Result<String> {
    let path = Path::new("model/claims.json");
    fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the claim registry", path, e))
}

/// Duplicate the first claim object of the registry text, verbatim, by splicing
/// a second copy in after it. Working on the TEXT rather than on a parsed value
/// keeps the planted file a genuine input to the parser.
fn plant_duplicate_claim(text: &str) -> Result<String> {
    let start = text.find("\n    {").ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            "the claim registry has no claim object to duplicate",
        )
    })?;
    let end = text[start..]
        .find("\n    },")
        .map(|i| start + i + "\n    },".len())
        .ok_or_else(|| SpecError::new(CLAUSE, "the first claim object is unterminated"))?;
    let first = &text[start..end];
    Ok(format!("{}{}{}", &text[..end], first, &text[end..]))
}

// M2: a claim registry with a duplicate id must be rejected.
fn m2(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m2")?;
    let text = registry_text()?;

    let control = registry_findings(&tmp, "control.json", &text)?;
    let planted = registry_findings(&tmp, "planted.json", &plant_duplicate_claim(&text)?)?;

    Ok(control.is_empty() && planted.iter().any(|f| f.starts_with("duplicate claim id")))
}

// M3: a claim registry with an orphan dependency must be rejected.
fn m3(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m3")?;
    let text = registry_text()?;
    let claims = claims()?;
    let victim = claims
        .first()
        .map(|c| field(c, "id").to_string())
        .ok_or_else(|| SpecError::new(CLAUSE, "the claim registry is empty"))?;

    // Give the first claim a dependency on a claim id that does not exist.
    let anchor = format!("\"id\": \"{victim}\",");
    let planted_text = text.replacen(
        &anchor,
        &format!("{anchor}\n      \"dependsOn\": [\"GO-999-PLANTED\"],"),
        1,
    );
    if planted_text == text {
        return Err(SpecError::new(
            CLAUSE,
            "could not plant an orphan dependency",
        ));
    }

    let control = registry_findings(&tmp, "control.json", &text)?;
    let planted = registry_findings(&tmp, "planted.json", &planted_text)?;

    Ok(control.is_empty() && planted.iter().any(|f| f.contains("orphan dependency")))
}

// M4: promoting an outstanding claim to formalProof without a Lean declaration
//     must be rejected (SPEC 17.1: only formalProof supports 'proved').
fn m4(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m4")?;
    let text = registry_text()?;
    let claims = claims()?;

    // The forgery promotes an OPEN claim -- one with no `leanDeclaration` -- to
    // `formalProof`. That is the exact edit SPEC 17.1 forbids and the exact one
    // a repository under pressure to show a green gate would reach for.
    let victim = claims
        .iter()
        .find(|c| {
            field(c, "level") == "open"
                && c.get("leanDeclaration").and_then(Value::as_str).is_none()
        })
        .map(|c| field(c, "id").to_string())
        .ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                "the claim registry has no open claim to forge a promotion of",
            )
        })?;

    let anchor = format!("\"id\": \"{victim}\",\n      \"level\": \"open\"");
    let planted_text = text.replacen(
        &anchor,
        &format!("\"id\": \"{victim}\",\n      \"level\": \"formalProof\""),
        1,
    );
    if planted_text == text {
        return Err(SpecError::new(
            CLAUSE,
            &format!("could not plant a level promotion on {victim}"),
        ));
    }

    let control = registry_findings(&tmp, "control.json", &text)?;
    let planted = registry_findings(&tmp, "planted.json", &planted_text)?;

    Ok(control.is_empty()
        && planted
            .iter()
            .any(|f| f.contains("formalProof with no leanDeclaration")))
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
// M6: release-gate step 9 must reject an environment response in which the
//     final theorem is absent, and accept the exact declaration when present.
//     This attacks the actual step-9 predicate and remains valid after closure.
// ---------------------------------------------------------------------------
fn m6(_root: &Path) -> Result<bool> {
    let absent = "'WasmGemmGnaf.Artifact.some_other_theorem' : True\n";
    let present = format!("'{}' : True\n", crate::gate::RELEASE_THEOREM);
    Ok(!crate::gate::release_theorem_declared(absent)
        && crate::gate::release_theorem_declared(&present))
}

// ---------------------------------------------------------------------------
// M7: the real Atlas scope-blindness theorem must retain every dependency its
//     proof uses. The control is an exact copy of CoverageScope.lean; the mutant
//     replaces its search-partition equality with an unrelated equality while
//     retaining the real statement conclusion and proof.
// ---------------------------------------------------------------------------
fn m7(root: &Path) -> Result<bool> {
    const COVERAGE_SCOPE: &str = "WasmGemmGnaf/Atlas/CoverageScope.lean";
    const REQUIRED_HYPOTHESIS: &str = "(hp : s₁.body.searchPartitions = s₂.body.searchPartitions)";
    const UNRELATED_HYPOTHESIS: &str = "(hp : s₁.body.declarationBase = s₂.body.declarationBase)";

    let source_path = root.join(COVERAGE_SCOPE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the Atlas coverage-scope theorem",
            &source_path,
            e,
        )
    })?;
    if source.matches(REQUIRED_HYPOTHESIS).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M7 expected exactly one search-partition hypothesis in {COVERAGE_SCOPE}"),
        ));
    }

    let tmp = TempDir::new("m7")?;
    let control_result = probe_source(CLAUSE, root, &tmp.path().join("M7Control.lean"), &source)?;
    if !control_result.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED CoverageScope copy does not elaborate, so M7 would prove \
                 nothing: {}",
                first_line(&control_result.combined())
            ),
        ));
    }

    let mutant = source.replacen(REQUIRED_HYPOTHESIS, UNRELATED_HYPOTHESIS, 1);
    let mutant_result = probe_source(CLAUSE, root, &tmp.path().join("M7Mutant.lean"), &mutant)?;
    Ok(control_result.success && !mutant_result.success)
}

// ---------------------------------------------------------------------------
// M8: the real root checker must reject an owned Lean source added after the
//     root was generated, even if a stale compiled root object is present.
//     Both control and mutant live in a disposable repository copy.
// ---------------------------------------------------------------------------
fn m8(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m8")?;
    let planted = tmp.path().join("repo");
    let layer = planted.join("WasmGemmGnaf/Foundation");
    fs::create_dir_all(&layer)
        .map_err(|e| SpecError::io(CLAUSE, "cannot create the M8 layer at", &layer, e))?;
    write(&planted.join("lakefile.lean"), "-- M8 repository marker\n")?;
    write(&planted.join("SPEC.md"), "# M8 repository marker\n")?;
    write(
        &layer.join("Control.lean"),
        "set_option autoImplicit false\n\ntheorem m8Control : True := trivial\n",
    )?;

    let generated = run_command(
        Command::new(self_exe()?)
            .args(["sources", "root"])
            .current_dir(&planted),
    )?;
    if !generated.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the real root generator rejected M8's control: {}",
                first_line(&format!("{}\n{}", generated.stdout, generated.stderr))
            ),
        ));
    }
    let control = run_command(
        Command::new(self_exe()?)
            .args(["sources", "root", "--check"])
            .current_dir(&planted),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED root copy already fails its check: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let olean = planted.join(".lake/build/lib/lean/WasmGemmGnaf.olean");
    fs::create_dir_all(olean.parent().expect("M8 olean has a parent")).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot create the M8 stale-object directory at",
            &olean,
            e,
        )
    })?;
    write(
        &olean,
        "stale compiled root -- intentionally not a valid olean\n",
    )?;
    write(
        &layer.join("Planted.lean"),
        "set_option autoImplicit false\n\ntheorem m8Planted : True := trivial\n",
    )?;

    let mutant = run_command(
        Command::new(self_exe()?)
            .args(["sources", "root", "--check"])
            .current_dir(&planted),
    )?;
    Ok(!mutant.ok && mutant.stdout.contains("STALE"))
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
    write(
        &tree.join("Competitor.lean"),
        "import WasmGemmGnaf.Artifact.Bytes\n",
    )?;

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
// M10: the real manifest checker must reject a backward identity binding. It
//      first creates and accepts a fresh manifest in a disposable minimal repo,
//      then binds the source-core identity field to the later generated-input
//      identity and asks the same production checker again.
// ---------------------------------------------------------------------------
fn m10(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m10")?;
    let planted = tmp.path().join("repo");
    let model = planted.join("model");
    fs::create_dir_all(&model)
        .map_err(|e| SpecError::io(CLAUSE, "cannot create the M10 model at", &model, e))?;
    write(&planted.join("lakefile.lean"), "-- M10 repository marker\n")?;
    write(&planted.join("SPEC.md"), "# M10 source input\n")?;
    let toolchain_path = root.join("lean-toolchain");
    let toolchain = fs::read_to_string(&toolchain_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M10 toolchain control",
            &toolchain_path,
            e,
        )
    })?;
    write(&planted.join("lean-toolchain"), &toolchain)?;
    write(&model.join("claims.json"), "{}\n")?;
    write(&model.join("reproducibility-plan.json"), "{}\n")?;

    let generated = run_command(
        Command::new(self_exe()?)
            .arg("manifest")
            .current_dir(&planted),
    )?;
    if !generated.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the real manifest generator rejected M10's control: {}",
                first_line(&format!("{}\n{}", generated.stdout, generated.stderr))
            ),
        ));
    }
    let control = run_command(
        Command::new(self_exe()?)
            .args(["manifest", "--check"])
            .current_dir(&planted),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED manifest copy already fails its check: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let manifest_path = planted.join("MANIFEST.json");
    let manifest_text = fs::read_to_string(&manifest_path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the M10 manifest", &manifest_path, e))?;
    let manifest = json::parse(CLAUSE, &manifest_text)?;
    let core_id = manifest
        .get("sourceManifestCoreIdentity")
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no source-core identity"))?;
    let later_id = manifest
        .get("generatedProofInputIdentity")
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no generated-input identity"))?;
    let pre_final_id = manifest
        .get("preFinalEnvironmentIdentity")
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no pre-final identity"))?;
    let core_body = manifest
        .get("sourceManifestCore")
        .map(Value::to_json)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no source-core body"))?;
    let generated_body = manifest
        .get("generatedProofInputBody")
        .map(Value::to_json)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no generated-input body"))?;
    let pre_final_body = manifest
        .get("preFinalEnvironmentBody")
        .map(Value::to_json)
        .ok_or_else(|| SpecError::new(CLAUSE, "M10 control has no pre-final body"))?;
    if core_body.contains(core_id)
        || generated_body.contains(later_id)
        || pre_final_body.contains(pre_final_id)
        || core_body.contains(later_id)
        || core_body.contains(pre_final_id)
        || generated_body.contains(pre_final_id)
    {
        return Err(SpecError::new(
            CLAUSE,
            "the production M10 control is already cyclic or backward-bound",
        ));
    }
    let anchor = format!("  \"sourceManifestCoreIdentity\": \"{core_id}\",");
    let replacement = format!("  \"sourceManifestCoreIdentity\": \"{later_id}\",");
    let mutant_text = manifest_text.replacen(&anchor, &replacement, 1);
    if mutant_text == manifest_text {
        return Err(SpecError::new(
            CLAUSE,
            "could not plant M10's backward stage-identity binding",
        ));
    }
    write(&manifest_path, &mutant_text)?;

    let mutant = run_command(
        Command::new(self_exe()?)
            .args(["manifest", "--check"])
            .current_dir(&planted),
    )?;
    Ok(!mutant.ok && mutant.stdout.contains("sourceManifestCoreIdentity differs"))
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
    if !schema::audit(&required, &schema::parse(&real), &schema::parse_gaps(&real)).is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            "the REAL bindings are already unbound, so M11's second half would pass \
             for the wrong reason",
        ));
    }

    let deleted = real.replace("-- authority-binding: GlobalOptimal\n", "");
    let names_unbound = schema::audit(
        &required,
        &schema::parse(&deleted),
        &schema::parse_gaps(&deleted),
    );

    let paraphrased = real.replacen(
        "              Foundation.CanonicalBytesLE releasedBytes competitorBytes)) :=\n  Iff.rfl",
        "              Foundation.CanonicalBytesLE releasedBytes competitorBytes)) := by\n  \
         simp [GlobalOptimal]",
        1,
    );
    let rejects_tactic = schema::audit(
        &required,
        &schema::parse(&paraphrased),
        &schema::parse_gaps(&paraphrased),
    );

    Ok(names_unbound
        .iter()
        .any(|f| f.starts_with("GlobalOptimal -- NO BINDING OR GAP"))
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
    let probe = probe_source(
        CLAUSE,
        root,
        &tmp.path().join(format!("M12_{tag}.lean")),
        &src,
    )?;
    if !probe.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the planted {tag} witness does not elaborate: {}",
                first_line(&probe.combined())
            ),
        ));
    }
    Ok(probe.combined())
}

// ---------------------------------------------------------------------------
// M13: a mutated vendored tree must break the binding the Lean theorem
//      `Wasm.profile_matches_pinned_revision` stands on.
//
// SPEC section 7.1 says that theorem means the model and map are identity-bound
// to the VENDORED revision. Lean cannot read `vendor/wasm-spec/`; it stands on
// the literals in `Wasm/Revision.lean` -- the digest of `SHA256SUMS`, the file
// count and the commit. A literal that had drifted from the tree would still
// elaborate, so the binding is only as good as the checker that recomputes it,
// and a checker that never fires is indistinguishable from one with nothing to
// find.
//
// Three faults, each planted on a COPY of the tree, each run through the REAL
// checker (`vendor::binding`) rather than a reimplementation of it:
//
//   * a flipped digest inside `SHA256SUMS` -- the manifest no longer describes
//     the file it lists, AND its own digest no longer matches the Lean literal;
//   * an appended line -- every per-file digest still checks out, so only the
//     digest of digests catches it. This is the mutation that would slip past
//     `sha256sum -c` alone;
//   * a deleted entry -- the file count no longer matches `fileCount`.
//
// The unmutated copy is the control: it must produce NO finding, so M13 cannot
// pass by failing for an unrelated reason (a bad copy, a missing file, a checker
// that rejects everything).
// ---------------------------------------------------------------------------
fn m13(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m13")?;
    let planted = tmp.path().join("wasm-spec");
    copy_tree(Path::new("vendor/wasm-spec"), &planted)?;

    let control = crate::vendor::binding(&planted, root)?;
    if !control.is_ok() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED copy of the vendored tree already fails the binding check, \
                 so M13 would pass for the wrong reason: {}",
                control.findings.join("; ")
            ),
        ));
    }
    if control.anchors_cited == 0 {
        return Err(SpecError::new(
            CLAUSE,
            "the binding check cites no vendored anchor, so its anchor half tests nothing",
        ));
    }

    let sums_path = planted.join("SHA256SUMS");
    let original = fs::read_to_string(&sums_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the planted digest manifest",
            &sums_path,
            e,
        )
    })?;

    // (a) a flipped digest: the manifest lies about a file it lists.
    let flipped = flip_first_digest(&original)?;
    write(&sums_path, &flipped)?;
    let corrupted = crate::vendor::binding(&planted, root)?;
    let rejects_flip = corrupted
        .findings
        .iter()
        .any(|f| f.starts_with("vendored file digest mismatch"))
        && corrupted
            .findings
            .iter()
            .any(|f| f.contains("have drifted apart"));

    // (b) an appended line: every per-file digest still checks out. Only the
    //     digest of digests notices, which is the whole point of recording it.
    write(&sums_path, &format!("{original}\n"))?;
    let appended = crate::vendor::binding(&planted, root)?;
    let rejects_append = appended.content_failures.is_empty()
        && appended
            .findings
            .iter()
            .any(|f| f.contains("have drifted apart"));

    // (c) a deleted entry: the vendored file count no longer matches Lean's.
    let shortened: String = original.lines().skip(1).map(|l| format!("{l}\n")).collect();
    write(&sums_path, &shortened)?;
    let deleted = crate::vendor::binding(&planted, root)?;
    let rejects_delete = deleted
        .findings
        .iter()
        .any(|f| f.contains("core3VendoredTree.fileCount"));

    // (d) a file the manifest does not list. This is the direction the checker
    //     MISSED, and an adversarial review demonstrated the consequence live:
    //     while `binding` walked only the manifest's own lines, 334 files were
    //     added to the vendored tree and `xtask vendor` went on reporting
    //     "40 files rechecked (0 digest failures)" and PASSING. Unlisted bytes
    //     changed no digest anywhere, so the claim that any vendored byte moves
    //     `SHA256SUMS` was false. `binding` now enumerates the directory; this
    //     plant is what keeps it doing so.
    write(&sums_path, &original)?;
    let smuggled = planted.join("document").join("core").join("SMUGGLED.rst");
    write(&smuggled, "planted content nothing has a digest for\n")?;
    let unlisted = crate::vendor::binding(&planted, root)?;
    let rejects_unlisted = unlisted
        .findings
        .iter()
        .any(|f| f.contains("not covered by the digest manifest"));
    fs::remove_file(&smuggled).ok();

    Ok(rejects_flip && rejects_append && rejects_delete && rejects_unlisted)
}

/// Flip one hex digit of the first digest line, keeping the line well formed so
/// the parser still accepts it. A malformed line would be rejected as a parse
/// error, which is a different failure from the one under test.
fn flip_first_digest(text: &str) -> Result<String> {
    for (index, line) in text.lines().enumerate() {
        if line.len() > 64 && line.as_bytes()[..64].iter().all(u8::is_ascii_hexdigit) {
            let first = &line[..1];
            let replacement = if first == "0" { "1" } else { "0" };
            let mutated = format!("{replacement}{}", &line[1..]);
            let mut out: Vec<String> = text.lines().map(String::from).collect();
            out[index] = mutated;
            return Ok(format!("{}\n", out.join("\n")));
        }
    }
    Err(SpecError::new(
        CLAUSE,
        "the planted digest manifest has no digest line to flip",
    ))
}

// ---------------------------------------------------------------------------
// M14: a fabricated Core coverage marker must be rejected.
//
// `xtask core` measures how much of the pinned Core 3.0 front end the Lean tree
// covers, and the number it prints is what an auditor will read. The whole value
// of that number rests on one property: the checklist is EXTRACTED from the
// vendored SpecTec sources, so a marker can claim an item only if the pinned
// grammar really defines it. Padding the number by inventing a marker must fail
// rather than inflate the total.
//
// The plant goes on a COPY of the Lean tree; `WasmGemmGnaf/` is never written.
// ---------------------------------------------------------------------------
fn m14(_root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m14")?;
    let planted_lean = tmp.path().join("lean");
    copy_tree(Path::new("WasmGemmGnaf"), &planted_lean)?;

    let spectec = Path::new("vendor/wasm-spec/specification/wasm-3.0");

    // The control: the unmutated copy must be accepted, so a rejection below
    // cannot be blamed on the copy itself.
    let control = crate::core::report(spectec, &planted_lean)?;
    if !control.is_ok() {
        return Err(SpecError::new(
            CLAUSE,
            "the UNMUTATED copy of the Lean tree already fails the Core coverage check, so \
             M14 would pass for the wrong reason",
        ));
    }
    let control_total: usize = control
        .parts
        .iter()
        .map(super::core::Coverage::covered)
        .sum();

    // (a) an invented opcode. No such production exists in the pinned grammar.
    let plant = planted_lean.join("PlantedCoverage.lean");
    write(
        &plant,
        "-- core-opcode: 0x0C TOTALLY.INVENTED\ntheorem plantedA : True := trivial\n",
    )?;
    let invented_opcode = crate::core::report(spectec, &planted_lean)?;
    let rejects_opcode = !invented_opcode.is_ok();

    // (b) an invented typing rule.
    write(
        &plant,
        "-- core-rule: Instr_ok/no-such-rule\ntheorem plantedB : True := trivial\n",
    )?;
    let invented_rule = crate::core::report(spectec, &planted_lean)?;
    let rejects_rule = !invented_rule.is_ok();

    // (c) an invented syntax production.
    write(
        &plant,
        "-- core-syntax: nosuchtype\ntheorem plantedC : True := trivial\n",
    )?;
    let invented_syntax = crate::core::report(spectec, &planted_lean)?;
    let rejects_syntax = !invented_syntax.is_ok();

    // (d) and the number must not have moved: a fabricated marker must not be
    //     able to raise the covered count even while it is being rejected.
    let planted_total: usize = invented_syntax
        .parts
        .iter()
        .map(super::core::Coverage::covered)
        .sum();
    let count_unmoved = planted_total == control_total;

    // (e) a REAL item claimed by a marker attached to nothing. An external audit
    //     objected that coverage "consists of comments anywhere in Lean files,
    //     with no connection to an elaborated declaration", and it was right of
    //     the first version. A floating comment must not count.
    write(
        &plant,
        "-- core-rule: Instr_ok/nop\n\n/- an ordinary block comment, not a declaration -/\n",
    )?;
    let floating = crate::core::report(spectec, &planted_lean)?;
    let rejects_floating =
        !floating.is_ok() && floating.parts.iter().any(|p| !p.unattached.is_empty());

    // (f) a REAL item claimed by a marker above a declaration the COMPILED
    //     environment does not have. The planted copy supplies the name; the
    //     real environment supplies the truth, so a marker over a renamed,
    //     deleted or commented-out case is caught.
    write(
        &plant,
        "-- core-rule: Instr_ok/nop\ndef thisNameIsNotInTheCompiledEnvironment : Nat := 0\n",
    )?;
    let ghost = crate::core::report_elaborated(Path::new("."), spectec, &planted_lean)?;
    let rejects_ghost = !ghost.is_ok() && ghost.parts.iter().any(|p| !p.unelaborated.is_empty());

    fs::remove_file(&plant).ok();

    Ok(rejects_opcode
        && rejects_rule
        && rejects_syntax
        && count_unmoved
        && rejects_floating
        && rejects_ghost)
}

// ---------------------------------------------------------------------------
// M15: a declaration carrying a required SPEC 15 NAME and the type `Nat`, bound
//      at `:= 0`, must be rejected.
//
// This is the exact shape an external audit named:
//
//   > The repository's reported 36/58 remains inflated. Its checker verifies
//   > names rather than exact proposition types; its own M12 test demonstrates
//   > that a matching-name `Nat := 0` is counted as discharged.
//
// It was right. `xtask claims required` asked `#print axioms` whether the name
// existed, so a `Nat := 0` under the right name passed. `M12` planted precisely
// that shape and, by construction, only ever tested the choice-taint rule on it.
//
// Two halves, as `M11` has:
//
//   * the ELABORATOR half. A signature binding stating SPEC section 7.3's
//     `decode_sound` and closed by `:= @<planted Nat>` must FAIL to
//     elaborate, with the same binding closed by `:= @Wasm.decode_sound`
//     as the control. Without the control a typo would make the mutant fail for
//     an unrelated reason and this falsifier would report PASS having tested
//     nothing.
//
//   * the WIRING half. The elaborator is only consulted if something asks it, so
//     on a COPY of the binding source the marker is deleted, the `:= @Name` is
//     replaced by a tactic, the marker is repointed at a name SPEC does not
//     require, the SPEC quotation is made stale, and an exact theorem-shaped
//     prose decoy is placed before the drifted fenced theorem -- and
//     `signature::audit` plus `required::apply_signatures` must reject each one.
//
// Every mutation is applied to a COPY; `WasmGemmGnaf/` is never written.
// ---------------------------------------------------------------------------

/// The Lean module carrying the SPEC 15 proposition bindings. M15 mutates a COPY
/// of its text; the file itself is never written.
const SIGNATURE_BINDINGS: &str = "WasmGemmGnaf/Conformance/RequiredSignatures.lean";

fn m15(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m15")?;

    // ---- the elaborator half ------------------------------------------------
    let control = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M15Control.lean"),
        &signature_binding("@WasmGemmGnaf.Wasm.decode_sound", ""),
    )?;
    if !control.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the REAL signature binding does not elaborate, so M15 would prove nothing: {}",
                first_line(&control.combined())
            ),
        ));
    }

    // The mutation: the required name, present, correctly spelled, type `Nat`.
    let mutant = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M15Mutant.lean"),
        &signature_binding(
            "@WasmGemmGnaf.Wasm.m15_planted_decode_sound",
            "namespace WasmGemmGnaf.Wasm\n\
             def m15_planted_decode_sound : Nat := 0\n\
             end WasmGemmGnaf.Wasm\n\n",
        ),
    )?;
    if mutant.success {
        return Ok(false);
    }
    // It must fail as a TYPE MISMATCH, not because the planted name is unknown:
    // an "unknown identifier" would mean the plant never entered the environment
    // and the binding rejected nothing.
    let rejects_nat =
        mutant.combined().contains("Type mismatch") || mutant.combined().contains("type mismatch");

    // ---- the wiring half ----------------------------------------------------
    let spec = fs::read_to_string(Path::new("SPEC.md"))
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new("SPEC.md"), e))?;
    let required = crate::required::required_names(&spec)?;
    let deviations = crate::signature::deviation_ids()?;
    let real = fs::read_to_string(Path::new(SIGNATURE_BINDINGS))
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new(SIGNATURE_BINDINGS), e))?;
    if !crate::signature::audit(
        &required,
        &crate::signature::parse(&real),
        &deviations,
        &spec,
    )
    .is_empty()
    {
        return Err(SpecError::new(
            CLAUSE,
            "the REAL signature bindings already fail their own audit, so M15's second \
             half would pass for the wrong reason",
        ));
    }

    const MARKER: &str = "-- spec-signature: Wasm.decode_sound\n";
    const CLOSURE: &str = "  @Wasm.decode_sound\n";

    // (a) the binding deleted: the name is credited by the environment and bound
    //     by nothing, which is the state the audit found the repository in.
    let deleted = real.replacen(MARKER, "", 1);
    if deleted == real {
        return Err(SpecError::new(
            CLAUSE,
            "could not delete the validation_progress marker",
        ));
    }
    let bindings = crate::signature::parse(&deleted);
    let exact = crate::signature::exact_names(&bindings);
    let rejects_deleted = !exact.contains(&"Wasm.decode_sound".to_string());

    // and the inventory must actually DEMOTE it, not merely notice.
    let mut demoted = crate::required::classify(
        &required,
        &required::flatten(&format!(
            "'WasmGemmGnaf.Wasm.decode_sound' does not depend on any axioms"
        )),
    );
    let credited_before = demoted.discharged;
    crate::required::apply_signatures(&mut demoted, &exact);
    let rejects_in_inventory = credited_before == 1
        && demoted.discharged == 0
        && demoted.unsigned == vec!["Wasm.decode_sound".to_string()];

    // (b) closed by a tactic. `by exact @Name` proves the same proposition today
    //     and accepts anything tomorrow; only `:= @Name` is definitional.
    let tactic = real.replacen(CLOSURE, "  by exact @Wasm.decode_sound\n", 1);
    if tactic == real {
        return Err(SpecError::new(
            CLAUSE,
            "could not replace the decode_sound closure",
        ));
    }
    let rejects_tactic = crate::signature::audit(
        &required,
        &crate::signature::parse(&tactic),
        &deviations,
        &spec,
    )
    .iter()
    .any(|f| f.contains("not by `:= @"));

    // (c) a marker naming something SPEC section 15 does not require.
    let invented = real.replacen(MARKER, "-- spec-signature: Wasm.not_in_spec_15\n", 1);
    let rejects_invented = crate::signature::audit(
        &required,
        &crate::signature::parse(&invented),
        &deviations,
        &spec,
    )
    .iter()
    .any(|f| f.contains("SPEC section 15 does not require it"));

    // (d) a stale SPEC quotation. SPEC.md is the source of the quoted block, so
    //     amending SPEC must break the binding rather than leave a stale
    //     quotation looking normative.
    let amended_spec = spec.replacen(
        "  Wasm.DeclarativeBinaryRelation bytes module",
        "  Wasm.DeclarativeBinaryRelation bytes module ∨ True",
        1,
    );
    if amended_spec == spec {
        return Err(SpecError::new(
            CLAUSE,
            "could not amend the SPEC 7.3 decode block",
        ));
    }
    let rejects_stale_quote = crate::signature::audit(
        &required,
        &crate::signature::parse(&real),
        &deviations,
        &amended_spec,
    )
    .iter()
    .any(|f| f.contains("does not quote it verbatim"));

    // (e) the ORIGINAL theorem text as ordinary prose before the amended fenced
    //     statement. A parser that searches all of SPEC.md accepts the decoy and
    //     misses the real drift; only a parser restricted to Lean fences rejects
    //     this attack.
    let original_block = crate::signature::spec_block(&spec, "Wasm.decode_sound")
        .ok_or_else(|| SpecError::new(CLAUSE, "SPEC has no fenced decode_sound theorem"))?;
    let prose_decoy_spec = format!("{original_block}\n\n{amended_spec}");
    let rejects_prose_decoy = crate::signature::audit(
        &required,
        &crate::signature::parse(&real),
        &deviations,
        &prose_decoy_spec,
    )
    .iter()
    .any(|f| f.contains("does not quote it verbatim"));

    Ok(rejects_nat
        && rejects_deleted
        && rejects_in_inventory
        && rejects_tactic
        && rejects_invented
        && rejects_stale_quote
        && rejects_prose_decoy)
}

/// A standalone signature binding of SPEC section 7.3's `decode_sound`,
/// closed by `closure`.
///
/// The proposition is SPEC's, written out rather than referenced, so the planted
/// file tests the same statement `Conformance/RequiredSignatures.lean` does. Only
/// the closure and the optional preamble differ between control and mutant.
fn signature_binding(closure: &str, preamble: &str) -> String {
    format!(
        "import WasmGemmGnaf\n\
         \n\
         set_option autoImplicit false\n\
         \n\
         open WasmGemmGnaf\n\
         \n\
         {preamble}\
         namespace M15Planted\n\
         \n\
         theorem planted_signature :\n\
         \x20   ∀ {{bytes : ByteArray}} {{module : Wasm.Module}},\n\
         \x20     Wasm.decode bytes = .ok module →\n\
         \x20     Wasm.DeclarativeBinaryRelation bytes module :=\n\
         \x20 {closure}\n\
         \n\
         end M15Planted\n"
    )
}

/// Copy a directory tree. Every mutation is applied to a COPY; the vendored
/// tree under verification is never written.
fn copy_tree(from: &Path, to: &Path) -> Result<()> {
    fs::create_dir_all(to)
        .map_err(|e| SpecError::io(CLAUSE, "cannot create the planted tree at", to, e))?;
    let entries = fs::read_dir(from)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the vendored tree at", from, e))?;
    for entry in entries {
        let entry =
            entry.map_err(|e| SpecError::io(CLAUSE, "cannot read an entry under", from, e))?;
        let source = entry.path();
        let target = to.join(entry.file_name());
        if source.is_dir() {
            copy_tree(&source, &target)?;
        } else {
            fs::copy(&source, &target)
                .map_err(|e| SpecError::io(CLAUSE, "cannot copy", &source, e))?;
        }
    }
    Ok(())
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
    text.lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("")
        .chars()
        .take(200)
        .collect()
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
        let path =
            std::env::temp_dir().join(format!("wgg-mutation-{tag}-{}-{nanos}", std::process::id()));
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
        assert!(
            !path.exists(),
            "the planted tree must not outlive the falsifier"
        );
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

    #[test]
    fn m17_calls_the_real_amendment_checker_and_rejects_all_four_drifts() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m17(root).expect("M17 runs"));
    }

    #[test]
    fn m18_rejects_the_malformed_opcode_275_shape() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m18(root).expect("M18 runs"));
    }

    #[test]
    fn m19_rejects_missing_generalized_supertype_validity() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m19(root).expect("M19 runs"));
    }

    #[test]
    fn m20_rejects_wrapped_core_type_group_indices() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m20(root).expect("M20 runs"));
    }

    #[test]
    fn m21_rejects_lossy_lane_store_successor_branching() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m21(root).expect("M21 runs"));
    }

    #[test]
    fn m22_rejects_broken_public_emitter() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m22(root).expect("M22 runs"));
    }

    #[test]
    fn m23_rejects_detached_module_byte_accounting() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m23(root).expect("M23 runs"));
    }

    #[test]
    fn m24_rejects_same_state_constant_initialization() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m24(root).expect("M24 runs"));
    }

    #[test]
    fn m25_rejects_mixed_recursive_suffix_scope_reset() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m25(root).expect("M25 runs"));
    }

    #[test]
    fn m26_rejects_public_costed_step_erasure_mismatch() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m26(root).expect("M26 runs"));
    }

    #[test]
    fn m27_rejects_public_compiler_status_epilogue_deletion() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m27(root).expect("M27 runs"));
    }

    #[test]
    fn m28_rejects_forged_public_evaluator_completion() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m28(root).expect("M28 runs"));
    }

    #[test]
    fn m29_rejects_malformed_byte_solved_float_target() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m29(root).expect("M29 runs"));
    }

    #[test]
    fn m30_rejects_disconnected_canonical_costed_explorer() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m30(root).expect("M30 runs"));
    }

    #[test]
    fn m31_rejects_one_page_short_harness_growth() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m31(root).expect("M31 runs"));
    }

    #[test]
    fn m32_rejects_implicit_select_bottom_loss() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m32(root).expect("M32 runs"));
    }

    #[test]
    fn m33_rejects_reducible_indexed_null_initializer_target() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m33(root).expect("M33 runs"));
    }

    #[test]
    fn m34_rejects_missing_computed_harness_abi_readiness() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m34(root).expect("M34 runs"));
    }

    #[test]
    fn m35_rejects_missing_local_value_type_validity() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m35(root).expect("M35 runs"));
    }

    #[test]
    fn m36_rejects_missing_recursive_heap_shape_coherence() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m36(root).expect("M36 runs"));
    }

    #[test]
    fn m37_rejects_omitted_compiled_status_assignment() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m37(root).expect("M37 runs"));
    }

    #[test]
    fn m38_rejects_perturbed_compiler_execution_charge() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask has a repository parent");
        assert!(m38(root).expect("M38 runs"));
    }
}

// ---------------------------------------------------------------------------
// M16: a reflection theorem whose declarative side is its executable side must
//      not be credited.
//
// This is the falsifier for the rule that four external audits asked for and no
// gate could enforce. Historically, `Wasm.decode_sound`,
// `Wasm.decode_complete`, and `Wasm.validate_bool_iff` had the right
// names, matching surface statements, and clean axiom closures while their
// proof terms exposed circular executable definitions. The public decoder pair
// is now repaired against independent `BmoduleA`; the legacy subset validator
// remains circular and uncredited. M16 plants the old defect so the rule cannot
// silently regress.
//
// Both halves are run against the REAL checker, `independence::report_over`,
// with planted tables. A falsifier that reimplemented the search would test its
// own string matching -- the mistake M2, M13, M14 and M15 were each written to
// avoid.
// ---------------------------------------------------------------------------
fn m16(root: &Path) -> Result<bool> {
    // The real table must still be ANSWERABLE by the compiled environment:
    // `report` errors when a `#print` goes unanswered, so an entry naming a
    // declaration that has been renamed or deleted turns this row red instead
    // of passing for want of a match. That is the failure mode this half is
    // for, and it is the one the check itself carried until this tranche --
    // `declarativeBinaryRelation_iff_encode` was listed unqualified and so was
    // never matched, because `.` is an identifier character.
    //
    // What this half deliberately does NOT do any more: assert that the real
    // table rejects one particular set of names. It used to assert exactly
    // `[decode_complete, decode_sound, validate_bool_iff]`, which made
    // the falsifier a snapshot of the defect rather than a test of the rule --
    // REPAIRING a circularity turned M16 red, which is precisely backwards.
    // `Wasm.decode_sound` and `Wasm.decode_complete` were repaired by being
    // re-pointed at `Wasm.Core`; the planted half below is what shows the rule
    // still fires, and it does so independently of how many names are currently
    // circular.
    let _real = crate::independence::report(root)?;

    // PLANTED CIRCULARITY. Each entry forbids a name the compiled environment
    // really does print for the declaration named: the proof term of
    // `Wasm.decode_sound` cites `Wasm.Core.decode_soundA`, and the definition of
    // `Wasm.DeclarativeBinaryRelation` cites `Wasm.Core.Binary.BmoduleA`. Both
    // must be found, one through the `proof term` path and one through the
    // `definition` path, so a checker that inspected only one of the two would
    // fail this half.
    const PLANTED: &[crate::independence::Entry] = &[
        crate::independence::Entry {
            required: "WasmGemmGnaf.Wasm.decode_sound",
            declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
            forbidden: &["WasmGemmGnaf.Wasm.Core.decode_soundA"],
            why: "planted: the proof term really does cite this name",
        },
        crate::independence::Entry {
            required: "WasmGemmGnaf.Wasm.decode_complete",
            declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
            forbidden: &["WasmGemmGnaf.Wasm.Core.Binary.BmoduleA"],
            why: "planted: the declarative definition really does cite this name",
        },
    ];
    let planted = crate::independence::report_over(root, PLANTED)?;
    let rejects_known = planted.rejected()
        == vec![
            "Wasm.decode_complete".to_string(),
            "Wasm.decode_sound".to_string(),
        ];

    // The control: the SAME declarations, with nothing forbidden, must produce
    // no finding. Without this the half above would also pass a checker that
    // rejects everything it is shown.
    const CONTROL: &[crate::independence::Entry] = &[crate::independence::Entry {
        required: "WasmGemmGnaf.Wasm.decode_sound",
        declarative: "WasmGemmGnaf.Wasm.DeclarativeBinaryRelation",
        forbidden: &[],
        why: "control: nothing is forbidden, so nothing may be found",
    }];
    let control = crate::independence::report_over(root, CONTROL)?;

    // And the demotion must actually happen: the rule `required` applies is
    // attacked directly, so emptying `apply_independence` turns M16 red.
    let mut report = crate::required::environment_report(root)?;
    let before = report.discharged;
    crate::required::apply_independence(&mut report, &["Wasm.decode_sound".to_string()]);
    let demoted =
        report.discharged + 1 == before && report.circular == vec!["Wasm.decode_sound".to_string()];

    Ok(rejects_known && control.is_ok() && demoted)
}

// ---------------------------------------------------------------------------
// M17: drift in the canonical authority-amendment set must be rejected.
//
// The amendment identity is computed by Lean, but its source digests, textual
// anchors, declaration names and register links are repository bytes that Lean
// cannot read.  Each plant below changes one of those bytes in a COPY and calls
// the REAL `amendment::binding`.  The unmodified copy is the control, so this
// falsifier cannot pass merely because copying the tree broke the checker.
// ---------------------------------------------------------------------------
fn m17(root: &Path) -> Result<bool> {
    let tmp = TempDir::new("m17")?;
    let planted = tmp.path().join("repo");
    copy_tree(&root.join("WasmGemmGnaf"), &planted.join("WasmGemmGnaf"))?;
    copy_tree(
        &root.join("vendor/wasm-spec"),
        &planted.join("vendor/wasm-spec"),
    )?;
    fs::create_dir_all(planted.join("model")).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot create M17 model directory at",
            &planted.join("model"),
            e,
        )
    })?;
    fs::copy(
        root.join("model/spec-deviations.json"),
        planted.join("model/spec-deviations.json"),
    )
    .map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot copy M17 deviation register from",
            &root.join("model/spec-deviations.json"),
            e,
        )
    })?;

    let control = crate::amendment::binding(&planted)?;
    if !control.is_ok() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED amendment-tree copy already fails its binding: {}",
                control.findings.join("; ")
            ),
        ));
    }

    let authority = planted.join("WasmGemmGnaf/Wasm/AuthorityAmendments.lean");
    let values = planted.join("WasmGemmGnaf/Wasm/Core/BinaryGrammar/ValuesAmended.lean");
    let register = planted.join("model/spec-deviations.json");

    let digest = mutation_rejected(
        &planted,
        &authority,
        "a83d9b3ea01740f86c966ad256d6b484779ac40722a9568de021514537506bc1",
        "083d9b3ea01740f86c966ad256d6b484779ac40722a9568de021514537506bc1",
    )?;
    let patch = mutation_rejected(
        &planted,
        &authority,
        "beforeAnchor := \"grammar BsN(N)\"",
        "beforeAnchor := \"grammar BsN_BROKEN(N)\"",
    )?;
    let declaration = mutation_rejected(
        &planted,
        &values,
        "inductive BsN' :",
        "inductive BsN_broken :",
    )?;
    let ledger = mutation_rejected(
        &planted,
        &register,
        "\"adoptedIntoSpec\": \"AMD-007\"",
        "\"adoptedIntoSpec\": \"AMD-X\"",
    )?;

    Ok(digest && patch && declaration && ledger)
}

// ---------------------------------------------------------------------------
// M18: AMD-012 must stay bound to the corrected opcode-275 I8x16 operand
// shape.  Planting the malformed pinned I16x8 shape in the exact amendment
// text must be rejected by the real amendment checker.
// ---------------------------------------------------------------------------
fn m18(root: &Path) -> Result<bool> {
    authority_amendment_mutation(
        root,
        "m18",
        "AMD-012",
        "(I8 X `16) RELAXED_DOT_ADD S\"",
        "(I16 X `8) RELAXED_DOT_ADD S\"",
    )
}

// ---------------------------------------------------------------------------
// M19: AMD-013 must retain the generalized-supertype `Typeuse_ok` premise.
// Removing that exact inserted line makes the recorded patch a no-op and must
// be rejected by the real amendment checker.
// ---------------------------------------------------------------------------
fn m19(root: &Path) -> Result<bool> {
    authority_amendment_mutation(
        root,
        "m19",
        "AMD-013",
        "\\n-- (Typeuse_ok: C |- typeuse : OK)*",
        "",
    )
}

// ---------------------------------------------------------------------------
// M20: the full Core type checker must reject a recursive type group whose
// flattened source indices would wrap modulo 2^32.  The declarative `Type_okA`
// relation carries the source-faithful `TypeGroupRangeOk` premise; deleting
// only the executable conjunct must make its real soundness proof fail.
//
// Both files are disposable copies elaborated against the repository's
// compiled dependencies.  The unmodified copy is the control, so a stale or
// missing dependency cannot make the mutant pass for an unrelated reason.
// ---------------------------------------------------------------------------
fn m20(root: &Path) -> Result<bool> {
    const VALIDATOR: &str = "WasmGemmGnaf/Wasm/Core/ValidateTypes.lean";
    const GUARD: &str = "  decide (TypeGroupRangeOk C td) &&";
    const MUTANT: &str = "  true &&";

    let source_path = root.join(VALIDATOR);
    let source = fs::read_to_string(&source_path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the M20 validator", &source_path, e))?;
    if source.matches(GUARD).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M20 expected exactly one executable type-group range guard in {VALIDATOR}"),
        ));
    }

    let tmp = TempDir::new("m20")?;
    let control_path = tmp.path().join("M20Control.lean");
    write(&control_path, &source)?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED ValidateTypes copy does not elaborate, so M20 would prove nothing: {}",
                first_line(&control.stderr)
            ),
        ));
    }

    let planted = source.replacen(GUARD, MUTANT, 1);
    let mutant_path = tmp.path().join("M20Mutant.lean");
    write(&mutant_path, &planted)?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;

    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("TypeGroupRangeOk") {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M20's mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// M21: lane-store failure and success are not exclusive in the pinned Core
// relation. The former compares the bit width `sz`, while the latter writes
// `sz / 8` bytes. The enumerator must therefore append both independently;
// changing that union back to an if/else drops a real `StepA.vstoreLaneVal`.
// ---------------------------------------------------------------------------
fn m21(root: &Path) -> Result<bool> {
    const SUCCESSORS: &str = "WasmGemmGnaf/Wasm/Core/WholeSuccessors.lean";
    const UNION: &str = "          failure ++ success";
    const LOSSY: &str = "          if address.value.val + ao.offset.val + sz.toNat > memory.bytes.length then\n            failure\n          else success";

    let source_path = root.join(SUCCESSORS);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M21 whole-machine successor enumerator",
            &source_path,
            e,
        )
    })?;
    if source.matches(UNION).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M21 expected exactly one independent lane-store successor union in {SUCCESSORS}"
            ),
        ));
    }

    let tmp = TempDir::new("m21")?;
    let control_path = tmp.path().join("M21Control.lean");
    write(&control_path, &source)?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED WholeSuccessors copy does not elaborate, so M21 would prove nothing: {}",
                first_line(&control.stderr)
            ),
        ));
    }

    let planted = source.replacen(UNION, LOSSY, 1);
    let mutant_path = tmp.path().join("M21Mutant.lean");
    write(&mutant_path, &planted)?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("vstoreLaneVal") {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M21's mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// M22: both public encoder boundaries must remain computational. Replacing
// `Wasm.encode` in CoreBackEnd and `Artifact.emit` in Emit with empty bytes must
// break their actual round-trip proof files. Each unmodified file is its own
// control, so neither mutant can pass on a broken build environment.
// ---------------------------------------------------------------------------
fn m22(root: &Path) -> Result<bool> {
    const CORE_BACKEND: &str = "WasmGemmGnaf/Wasm/CoreBackEnd.lean";
    const CORE_IMPLEMENTATION: &str =
        "def encode (module : Module) : ByteArray := Core.Binary.encodeA module.core";
    const CORE_BROKEN: &str = "def encode (_module : Module) : ByteArray := ByteArray.empty";
    const EMITTER: &str = "WasmGemmGnaf/Artifact/Emit.lean";
    const IMPLEMENTATION: &str =
        "def emit (module : Wasm.Module) : ByteArray := Wasm.encode module";
    const BROKEN: &str = "def emit (_module : Wasm.Module) : ByteArray := ByteArray.empty";

    let core_path = root.join(CORE_BACKEND);
    let core_source = fs::read_to_string(&core_path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the M22 Core backend", &core_path, e))?;
    if core_source.matches(CORE_IMPLEMENTATION).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M22 expected exactly one public encoder implementation in {CORE_BACKEND}"),
        ));
    }

    let source_path = root.join(EMITTER);
    let source = fs::read_to_string(&source_path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the M22 emitter", &source_path, e))?;
    if source.matches(IMPLEMENTATION).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M22 expected exactly one public emitter implementation in {EMITTER}"),
        ));
    }

    let tmp = TempDir::new("m22")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let core_control_path = tmp.path().join("M22CoreControl.lean");
    write(&core_control_path, &core_source)?;
    let core_control = run_command(
        Command::new("lean")
            .arg(&core_control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !core_control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED CoreBackEnd copy does not elaborate, so M22 would prove \
                 nothing: {}",
                first_line(&format!("{}\n{}", core_control.stdout, core_control.stderr))
            ),
        ));
    }

    let core_planted = core_source.replacen(CORE_IMPLEMENTATION, CORE_BROKEN, 1);
    let core_mutant_path = tmp.path().join("M22CoreMutant.lean");
    write(&core_mutant_path, &core_planted)?;
    let core_mutant = run_command(
        Command::new("lean")
            .arg(&core_mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if core_mutant.ok {
        return Ok(false);
    }
    let core_diagnostic = format!("{}\n{}", core_mutant.stdout, core_mutant.stderr);
    let rejects_core_source = core_diagnostic.contains("Core.Binary.encodeA")
        && !core_diagnostic.contains("unknown identifier");
    if !rejects_core_source {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M22's Wasm.encode mutant failed outside the round-trip proof chain: {}",
                first_line(&core_diagnostic)
            ),
        ));
    }

    // Lean recovers from the first failed declaration in a file, so a broken
    // `toBytes_encode` can leave a synthetic declaration available to the later
    // theorem. Copy the real final theorem and proof as a second control, then
    // expose the mutated encoder in its conclusion. This requires the actual
    // `encode_decode_roundtrip` proof term itself to reject empty bytes.
    const ROUNDTRIP_HEAD: &str = "theorem encode_decode_roundtrip";
    let roundtrip_start = core_source
        .find(ROUNDTRIP_HEAD)
        .ok_or_else(|| SpecError::new(CLAUSE, "M22 could not find Wasm.encode_decode_roundtrip"))?;
    let roundtrip_tail = &core_source[roundtrip_start..];
    let roundtrip_end = roundtrip_tail
        .find("\n\nend WasmGemmGnaf.Wasm")
        .ok_or_else(|| SpecError::new(CLAUSE, "M22 could not bound the round-trip theorem"))?;
    let real_roundtrip = &roundtrip_tail[..roundtrip_end];
    let copied_roundtrip =
        real_roundtrip.replacen(ROUNDTRIP_HEAD, "theorem m22_encode_decode_roundtrip", 1);
    let roundtrip_module = |theorem: &str| {
        format!(
            "import WasmGemmGnaf.Wasm.CoreBackEnd\n\n\
             set_option autoImplicit false\n\n\
             namespace WasmGemmGnaf.Wasm\n\n\
             {theorem}\n\n\
             end WasmGemmGnaf.Wasm\n"
        )
    };
    let roundtrip_control = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M22RoundtripControl.lean"),
        &roundtrip_module(&copied_roundtrip),
    )?;
    if !roundtrip_control.success {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the copied Wasm.encode_decode_roundtrip control does not elaborate: {}",
                first_line(&roundtrip_control.combined())
            ),
        ));
    }
    let empty_roundtrip =
        copied_roundtrip.replacen("decode (encode module)", "decode ByteArray.empty", 1);
    if empty_roundtrip == copied_roundtrip {
        return Err(SpecError::new(
            CLAUSE,
            "M22 could not expose the empty encoder in encode_decode_roundtrip",
        ));
    }
    let roundtrip_mutant = probe_source(
        CLAUSE,
        root,
        &tmp.path().join("M22RoundtripMutant.lean"),
        &roundtrip_module(&empty_roundtrip),
    )?;
    let roundtrip_diagnostic = roundtrip_mutant.combined();
    let rejects_core_roundtrip = !roundtrip_mutant.success
        && (roundtrip_diagnostic.contains("Type mismatch")
            || roundtrip_diagnostic.contains("type mismatch"))
        && !roundtrip_diagnostic.contains("unknown identifier");

    let control_path = tmp.path().join("M22ArtifactControl.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED Artifact.Emit copy does not elaborate, so M22 would prove nothing: {}",
                first_line(&control.stderr)
            ),
        ));
    }

    let planted = source.replacen(IMPLEMENTATION, BROKEN, 1);
    let mutant_path = tmp.path().join("M22ArtifactMutant.lean");
    write(&mutant_path, &planted)?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("decode_emit")
        && !diagnostic.contains("encode_decode_roundtrip")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M22's mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(rejects_core_source && rejects_core_roundtrip)
}

// ---------------------------------------------------------------------------
// M23: the exact aggregate must obtain moduleBytes from the emitted byte array,
// not from an unrelated constant.  The real projection theorem is retained in
// a copied source file, so changing only the defining conjunct must make that
// proof stop elaborating.  The unmodified file is the control.
// ---------------------------------------------------------------------------
fn m23(root: &Path) -> Result<bool> {
    const AGGREGATE: &str = "WasmGemmGnaf/Cost/Aggregate.lean";
    const EXACT: &str = "cost.static.moduleBytes = bytes.size ∧";
    const BROKEN: &str = "cost.static.moduleBytes = 0 ∧";

    let source_path = root.join(AGGREGATE);
    let source = fs::read_to_string(&source_path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the M23 aggregate", &source_path, e))?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M23 expected exactly one module-byte conjunct in {AGGREGATE}"),
        ));
    }

    let tmp = TempDir::new("m23")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M23Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified aggregate copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M23Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("module_bytes_exact")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M23 mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M24: AMD-014 must thread the post-expression state through public constant
// initialization. Restoring the pinned same-state premise must break the real
// executable-to-relational initializer soundness proof retained in the file.
// ---------------------------------------------------------------------------
fn m24(root: &Path) -> Result<bool> {
    const INITIALIZER: &str = "WasmGemmGnaf/Wasm/Core/InstantiationAmended.lean";
    const THREADED: &str = "Eval_exprEraseA state expression evaluated [value] →";
    const PINNED: &str = "Eval_exprEraseA state expression state [value] →";

    let source_path = root.join(INITIALIZER);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M24 amended initializer",
            &source_path,
            e,
        )
    })?;
    if source.matches(THREADED).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M24 expected exactly one state-threaded global premise in {INITIALIZER}"),
        ));
    }

    let tmp = TempDir::new("m24")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M24Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified AMD-014 initializer copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M24Mutant.lean");
    write(&mutant_path, &source.replacen(THREADED, PINNED, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("evalGlobals_sound")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M24 mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M25: AMD-015 keeps the executable ordinary-cons arm aligned with the sole
// amended recursive-type relation. Removing only its suffix-scope check must
// break the real soundness proof that constructs `Rectype_okA.cons`.
// ---------------------------------------------------------------------------
fn m25(root: &Path) -> Result<bool> {
    const VALIDATOR: &str = "WasmGemmGnaf/Wasm/Core/ValidateTypes.lean";
    const SCOPE_CHECK: &str =
        "        (RecType.recr (SubTypes.ofList sts)).noRebasedRecSupers &&\n";

    let source_path = root.join(VALIDATOR);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M25 amended type validator",
            &source_path,
            e,
        )
    })?;
    if source.matches(SCOPE_CHECK).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M25 expected exactly one AMD-015 suffix-scope check in {VALIDATOR}"),
        ));
    }

    let tmp = TempDir::new("m25")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M25Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified AMD-015 validator copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M25Mutant.lean");
    write(&mutant_path, &source.replacen(SCOPE_CHECK, "", 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("checkRectypeListA_sound")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Invalid projection")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M25 mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M26: the public costed reduction must consume exactly the Harness event that
//      `CostedEvent.erase` exposes. Replacing that premise by another valid
//      Harness event must break the real structural erasure proof.
// ---------------------------------------------------------------------------
fn m26(root: &Path) -> Result<bool> {
    // The public `CostedReduces` and its structural `erase` proof live in
    // `Wasm/Evaluate.lean`; `Wasm/CoreErasure.lean` only restates the SPEC
    // name over them.
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Evaluate.lean";
    const EXACT_STEP: &str = "      (step : Core.Harness.StepA initial costed.erase next) :\n";
    const WRONG_STEP: &str = "      (step : Core.Harness.StepA initial (.initialize []) next) :\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M26 public erasure module",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT_STEP).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M26 expected exactly one public costed-step premise in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m26")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M26Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified public erasure copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M26Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT_STEP, WRONG_STEP, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("CostedReduces.erase")
        && !diagnostic.contains("costed_erase_iff_plain_run")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M26 mutant failed for an unrelated reason: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M27: the public direct compiler must retain the private status-local epilogue.
// Changing the real lowering in a complete source copy must break the real
// kernel-checked lowering equation in that same file.
// ---------------------------------------------------------------------------
fn m27(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/GNAF/Compile.lean";
    const EXACT: &str =
        "def bodyCode (e : CompileEnv) (scr : Nat) (p : Plan) : List Wasm.Core.Instr :=\n  code e 0 scr p ++ [localGet e.statusLocal, wrapI64]\n";
    const BROKEN: &str =
        "def bodyCode (e : CompileEnv) (scr : Nat) (p : Plan) : List Wasm.Core.Instr :=\n  code e 0 scr p\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M27 public compiler",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M27 expected exactly one status epilogue lowering in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m27")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M27Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified direct compiler copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M27Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("bodyCode_has_status_epilogue")
        && !diagnostic.contains("type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("rfl")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M27 mutant failed outside the lowering equation: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M28: a system evaluation is related only when the sole public evaluator
// actually returns it. Replacing that computation by reflexivity must break
// the real extensional soundness proof in the same complete source copy.
// ---------------------------------------------------------------------------
fn m28(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Universal/Evaluate.lean";
    const EXACT: &str = "  Universal.evaluate S bytes = .complete evaluation\n";
    const FORGED: &str = "  EvaluationResult.complete evaluation = .complete evaluation\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M28 public evaluator",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M28 expected exactly one canonical evaluator relation in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m28")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M28Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified public evaluator copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M28Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, FORGED, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("system_evaluation_rel_sound")
        && !diagnostic.contains("evaluateFinite_complete_profileValid")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M28 mutant failed outside evaluator reflection: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M29: raw `FN` contains constructor terms excluded by the pinned `fN` syntax
// sort. Making the amended byte-solved-result premise vacuous must break the
// real kernel theorem that extracts well-formedness from `load-num-val`.
// ---------------------------------------------------------------------------
fn m29(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/Execution.lean";
    const EXACT: &str = "  | .amended => Num_.wf type value = true\n";
    const BROKEN: &str = "  | .amended => True\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M29 public execution relation",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M29 expected exactly one amended byte-solved numeric premise in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m29")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M29Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified public execution copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M29Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("loadNumVal_result_wf")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M29 mutant failed outside the byte-solved well-formedness theorem: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M30: the Universal checker must call the sole canonical public costed
// explorer. Replacing that call by unconditional failure must break the real
// per-input and whole-system completeness proofs in the same source copy.
// ---------------------------------------------------------------------------
fn m30(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Universal/Evaluate.lean";
    const EXACT: &str = "      match htree : S.machine.exploreAllCosted S.problem.maxSteps\n          initialization.initial with\n";
    const BROKEN: &str = "      match htree :\n          (Wasm.CostedTreeResult.initializationFailure Wasm.invalidModuleInitialization :\n            CostedTreeResult P S.problem.maxSteps initialization.initial) with\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M30 canonical Universal evaluator",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M30 expected exactly one operative canonical explorer call in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m30")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M30Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified Universal evaluator copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M30Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("execution_checker_complete_within_sublevel")
        && !diagnostic.contains("system_evaluation_rel_complete")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("contradiction")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M30 mutant failed outside canonical evaluator completeness: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M31: the Harness must grow to the exact page ceiling of the complete raw
// window.  Reducing that target by one page must break the real theorem that
// the subsequent Core splice is available.
// ---------------------------------------------------------------------------
fn m31(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/HarnessExecution.lean";
    const EXACT: &str = "  requiredPages (request.rawPtr.val + request.rawLen.val)\n";
    const BROKEN: &str = "  requiredPages (request.rawPtr.val + request.rawLen.val) - 1\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M31 Harness relation",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M31 expected exactly one operative raw target-page equation in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m31")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M31Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified Harness copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M31Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("growMemoryForRaw_splice_available")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("tactic 'change' failed")
        && !diagnostic.contains("Tactic `change` failed")
        && !diagnostic.contains("maximum recursion depth has been reached")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M31 mutant failed outside the raw-splice availability proof: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M32: implicit select must accept the stack-polymorphic BOT operand inferred
// after `unreachable`. Restoring the narrower num/vector-only test must break
// the real two-instruction completeness witness.
// ---------------------------------------------------------------------------
fn m32(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/ValidateInstr.lean";
    // The amended checker's implicit-select test is the one followed by the
    // amended `subOfA` comparison; the legacy `checkInstr` arm above it uses
    // plain `subOf`, so this two-line anchor is unique to `checkInstrA`.
    const EXACT: &str =
        "if (ValType.nvb t₁ && ValType.nvb t₂) &&\n                      (subOfA C t₁ t₂ || subOfA C t₂ t₁) then\n";
    const BROKEN: &str =
        "if (t₁.isNumOrVec && t₂.isNumOrVec) &&\n                      (subOfA C t₁ t₂ || subOfA C t₂ t₁) then\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M32 full amended checker completeness source",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M32 expected exactly one amended implicit-select BOT test in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m32")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M32Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified full validator completeness copy does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M32Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("unreachable_select_checkSeqA")
        && !diagnostic.contains("checkSeqA_complete")
        && !diagnostic.contains("Tactic `rfl` failed")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M32 mutant failed outside implicit-select completeness: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M33: a reducible indexed `ref.null` must not be accepted as a second fresh
// initialization target.  Disconnecting the relational constructor from the
// ordinary executable candidate must break its real target-functionality proof.
// ---------------------------------------------------------------------------
fn m33(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/HarnessExecution.lean";
    const EXACT: &str = "      initializationCandidate? request =\n        some (.beforeEntry\n          { request := request, memoryAddr := memory, gemmAddr := gemm } core) →\n";
    const BROKEN: &str =
        "      initializationCandidate? request = initializationCandidate? request →\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M33 Harness initialization relation",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M33 expected exactly one executable-candidate premise in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m33")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M33Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified Harness initialization control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M33Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("InitializesA.target_functional")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
        && !diagnostic.contains("unsolved goals")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M33 mutant failed outside initialization target functionality: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M34: public Harness requests must carry the ordinary computations required
// by their selected callable and raw-memory endpoint. Replacing either checked
// predicate by `True` must break the production extraction/refutation proofs.
// ---------------------------------------------------------------------------
fn m34(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/HarnessExecution.lean";
    const GEMM_EXACT: &str = "def GemmFunctionReady (h : Harness) (store : Store) : Prop :=\n  (store.funcs[h.gemmAddr]?).bind (fun function => expandDt function.type) =\n    some (.func\n      (ValTypes.ofList [.num .i32, .num .i32])\n      (ValTypes.ofList [.num .i32]))\n";
    const GEMM_BROKEN: &str =
        "def GemmFunctionReady (_h : Harness) (_store : Store) : Prop := True\n";
    const INSTALL_EXACT: &str = "def RawInstallReady (h : Harness) (state : State) : Prop :=\n  (installRaw? h state).isSome = true\n";
    const INSTALL_BROKEN: &str =
        "def RawInstallReady (_h : Harness) (_state : State) : Prop := True\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M34 Harness ABI readiness source",
            &source_path,
            e,
        )
    })?;
    if source.matches(GEMM_EXACT).count() != 1 || source.matches(INSTALL_EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M34 expected one callable and one raw-install predicate in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m34")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let run_source = |name: &str, text: &str| -> Result<crate::gate::Ran> {
        let path = tmp.path().join(name);
        write(&path, text)?;
        run_command(
            Command::new("lean")
                .arg(&path)
                .env("LEAN_PATH", &lean_path)
                .current_dir(root),
        )
    };

    let control = run_source("M34Control.lean", &source)?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified Harness ABI readiness control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    for (name, exact, broken, expected) in [
        (
            "M34GemmMutant.lean",
            GEMM_EXACT,
            GEMM_BROKEN,
            "exists_function",
        ),
        (
            "M34InstallMutant.lean",
            INSTALL_EXACT,
            INSTALL_BROKEN,
            "exists_result",
        ),
    ] {
        let mutant = run_source(name, &source.replacen(exact, broken, 1))?;
        if mutant.ok {
            return Ok(false);
        }
        let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
        if !diagnostic.contains(expected)
            && !diagnostic.contains("not_gemmFunctionReady_of_missing")
            && !diagnostic.contains("not_rawInstallReady_of_memory_zero_missing")
            && !diagnostic.contains("unsolved goals")
            && !diagnostic.contains("Application type mismatch")
            && !diagnostic.contains("application type mismatch")
            && !diagnostic.contains("Type mismatch")
            && !diagnostic.contains("type mismatch")
            && !diagnostic.contains("Tactic `rewrite` failed")
            && !diagnostic.contains("Tactic `cases` failed")
            && !diagnostic.contains("`simp` made no progress")
        {
            return Err(SpecError::new(
                CLAUSE,
                format!(
                    "M34 mutant failed outside computed ABI readiness: {}",
                    first_line(&diagnostic)
                ),
            ));
        }
        if diagnostic.contains("unknown identifier") {
            return Ok(false);
        }
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// M35: both amended local-validation constructors must retain ordinary value-
// type validity. Defaultability alone admits an out-of-range non-null
// reference local and breaks the real extraction and rejection theorems.
// ---------------------------------------------------------------------------
fn m35(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/Validation/ModulesCombinedAmended.lean";
    const VALIDITY: &str = "      Valtype_okA C l.valtype →\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M35 amended local-validation relation",
            &source_path,
            e,
        )
    })?;
    if source.matches(VALIDITY).count() != 2 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M35 expected two local value-type premises in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m35")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M35Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified amended local-validation control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M35Mutant.lean");
    write(&mutant_path, &source.replace(VALIDITY, ""))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("valtype_ok")
        && !diagnostic.contains("rejects_out_of_range_ref_local")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
        && !diagnostic.contains("No goals to be solved")
        && !diagnostic.contains("Tactic `assumption` failed")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M35 mutant failed outside local value-type validity: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M36: a rolled recursive variable must retain the exact outer composite
// shape stored at its `C.RECS` entry.  Removing the operative STRUCT edge must
// break the production REC-to-ANY bridge used by rolled type validity.
// ---------------------------------------------------------------------------
fn m36(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/Wasm/Core/Validation/SubtypingAmended.lean";
    const REC_STRUCT: &str =
        "  /-- AMD-022: a recursive variable retains the exact STRUCT shape stored at\n      its `C.RECS` entry. -/\n  | rec_struct {C : Context} {i : Nat} {fin : Option Final} {sups : TypeUses}\n      {fts : FieldTypes} :\n      C.recs[i]? = some (.sub fin sups (.struct fts)) →\n      Heaptype_subA C (.use (.recu i)) (.abs .struct)\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M36 amended heap-subtyping relation",
            &source_path,
            e,
        )
    })?;
    if source.matches(REC_STRUCT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M36 expected one operative REC-to-STRUCT rule in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m36")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M36Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified amended heap-subtyping control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M36Mutant.lean");
    write(&mutant_path, &source.replacen(REC_STRUCT, "", 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("rec_struct_any")
        && !diagnostic.contains("rec_struct")
        && !diagnostic.contains("Invalid field")
        && !diagnostic.contains("unknown constant")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M36 mutant failed outside recursive heap-shape coherence: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// M37: deleting the operative setStatus extraction must break the real
// source/lowering status correspondence used by compiler refinement.
// ---------------------------------------------------------------------------
fn m37(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/GNAF/CompileScalarRuntime.lean";
    const EXACT: &str = "  | .setStatus status => [status.code]\n";
    const BROKEN: &str = "  | .setStatus _ => []\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M37 scalar compiler runtime bridge",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M37 expected one operative setStatus extraction in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m37")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M37Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified scalar compiler runtime control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M37Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("apply_statusAssignments")
        && !diagnostic.contains("supportedStatus")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
        && !diagnostic.contains("simp made no progress")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M37 mutant failed outside source/status correspondence: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

// ---------------------------------------------------------------------------
// M38: perturbing one real execution-cost coordinate must break the
// coordinatewise equality with the independently defined source formula.
// ---------------------------------------------------------------------------
fn m38(root: &Path) -> Result<bool> {
    const SOURCE: &str = "WasmGemmGnaf/GNAF/CompileCost.lean";
    const EXACT: &str = "      dispatchSteps := 5\n";
    const BROKEN: &str = "      dispatchSteps := 6\n";

    let source_path = root.join(SOURCE);
    let source = fs::read_to_string(&source_path).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read the M38 exact compiler cost module",
            &source_path,
            e,
        )
    })?;
    if source.matches(EXACT).count() != 1 {
        return Err(SpecError::new(
            CLAUSE,
            format!("M38 expected one execution dispatch coordinate in {SOURCE}"),
        ));
    }

    let tmp = TempDir::new("m38")?;
    let lean_path = root.join(".lake/build/lib/lean");
    let control_path = tmp.path().join("M38Control.lean");
    write(&control_path, &source)?;
    let control = run_command(
        Command::new("lean")
            .arg(&control_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if !control.ok {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the unmodified exact compiler cost control does not elaborate: {}",
                first_line(&format!("{}\n{}", control.stdout, control.stderr))
            ),
        ));
    }

    let mutant_path = tmp.path().join("M38Mutant.lean");
    write(&mutant_path, &source.replacen(EXACT, BROKEN, 1))?;
    let mutant = run_command(
        Command::new("lean")
            .arg(&mutant_path)
            .env("LEAN_PATH", &lean_path)
            .current_dir(root),
    )?;
    if mutant.ok {
        return Ok(false);
    }
    let diagnostic = format!("{}\n{}", mutant.stdout, mutant.stderr);
    if !diagnostic.contains("compose_formula_eq_certifiedCost")
        && !diagnostic.contains("omega could not prove")
        && !diagnostic.contains("unsolved goals")
        && !diagnostic.contains("Application type mismatch")
        && !diagnostic.contains("application type mismatch")
        && !diagnostic.contains("Type mismatch")
        && !diagnostic.contains("type mismatch")
    {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "M38 mutant failed outside exact compiler cost composition: {}",
                first_line(&diagnostic)
            ),
        ));
    }
    Ok(!diagnostic.contains("unknown identifier"))
}

fn authority_amendment_mutation(
    root: &Path,
    tag: &str,
    amendment: &str,
    old: &str,
    new: &str,
) -> Result<bool> {
    let tmp = TempDir::new(tag)?;
    let planted = tmp.path().join("repo");
    copy_tree(&root.join("WasmGemmGnaf"), &planted.join("WasmGemmGnaf"))?;
    copy_tree(
        &root.join("vendor/wasm-spec"),
        &planted.join("vendor/wasm-spec"),
    )?;
    fs::create_dir_all(planted.join("model")).map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot create authority-mutation model directory at",
            &planted.join("model"),
            e,
        )
    })?;
    fs::copy(
        root.join("model/spec-deviations.json"),
        planted.join("model/spec-deviations.json"),
    )
    .map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot copy authority-mutation deviation register from",
            &root.join("model/spec-deviations.json"),
            e,
        )
    })?;

    let control = crate::amendment::binding(&planted)?;
    if !control.is_ok() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "the UNMUTATED {amendment} copy already fails its binding: {}",
                control.findings.join("; ")
            ),
        ));
    }

    let authority = planted.join("WasmGemmGnaf/Wasm/AuthorityAmendments.lean");
    mutation_rejected(&planted, &authority, old, new)
}

fn mutation_rejected(root: &Path, path: &Path, old: &str, new: &str) -> Result<bool> {
    let original = fs::read_to_string(path)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the mutation control", path, e))?;
    let planted = original.replacen(old, new, 1);
    if planted == original {
        return Err(SpecError::new(
            CLAUSE,
            format!("could not plant mutation `{old}` in {}", path.display()),
        ));
    }
    write(path, &planted)?;
    let result = crate::amendment::binding(root);
    write(path, &original)?;
    match result {
        Ok(binding) => Ok(!binding.is_ok()),
        Err(err) => Err(SpecError::new(
            CLAUSE,
            format!("mutation made the checker error instead of reject: {err}"),
        )),
    }
}
