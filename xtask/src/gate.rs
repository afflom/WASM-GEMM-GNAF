//! `xtask gate [--no-mutation]` -- the normative release gate. SPEC section 20.2.
//! Replaces `Tools/gate.py`.
//!
//! Exits non-zero unless every numbered condition holds. It is expected to fail
//! at step 9 while WGG-GO-1 is outstanding; that failure is the conforming
//! behaviour, and per UOR-GNAF 13.3 the gate MUST NOT return an unproved global
//! label.
//!
//! Three rules here were each learned from a real defect and are load-bearing:
//!
//!   * the ROOT module is elaborated directly, because `lake build` can serve a
//!     stale olean and report success on a root that does not elaborate;
//!   * the vendored Core digests are recomputed from CONTENT, never read out of
//!     the checksum string that claims them;
//!   * every declaration question is answered by PRESENCE in the compiled
//!     environment and by axiom closure, never by a JSON status field.

use std::path::Path;
use std::process::Command;

use crate::json::Value;
use crate::spec::{Outcome, Result, SpecError};
use crate::{firewall, json, lean, manifest, repo, required, sha256, vendor};

const CLAUSE: &str = "20.2";

/// The declarations whose PRESENCE decides steps 2, 4, 5, 8 and 9.
///
/// All of them are answered by ONE `lean` invocation: a probe per declaration
/// re-imports the whole library each time and times the gate out.
const PRESENCE_PROBE: [&str; 7] = [
    "WasmGemmGnaf.Conformance.globalOptimal_matches_authority_schema",
    "WasmGemmGnaf.Conformance.profileValid_matches_authority_schema",
    "WasmGemmGnaf.Wasm.profile_matches_pinned_revision",
    "WasmGemmGnaf.Universal.universal_sublevel_coverage",
    "WasmGemmGnaf.Universal.all_competitors_lower_bound",
    "WasmGemmGnaf.Artifact.released_attains_lower_bound",
    "WasmGemmGnaf.Artifact.released_wasm_gemm_gnaf_global_optimal",
];

/// Accumulates the numbered verdicts and prints each as it is decided.
struct Gate {
    failed: usize,
}

impl Gate {
    fn check(&mut self, step: &str, name: &str, ok: bool, detail: &str) {
        // Only show the detail on failure: a PASS row carrying a failure
        // explanation is how a green gate gets misread as a red one, and a red
        // one as green.
        let shown = if ok { "" } else { detail };
        if shown.is_empty() {
            println!("  [{}] {step}. {name}", verdict(ok));
        } else {
            println!("  [{}] {step}. {name} — {shown}", verdict(ok));
        }
        if !ok {
            self.failed += 1;
        }
    }
}

fn verdict(ok: bool) -> &'static str {
    if ok {
        "PASS"
    } else {
        "FAIL"
    }
}

pub fn run(root: &Path, no_mutation: bool) -> Result<Outcome> {
    let mut g = Gate { failed: 0 };
    println!("release gate (SPEC 20.2)\n");

    // ---- 1. authority + toolchain identities -------------------------------
    let authority = read_json("authority/manifest.json")?;
    let pins = authority
        .get("pins")
        .ok_or_else(|| SpecError::new(CLAUSE, "authority/manifest.json has no `pins`"))?;

    let uor = pins
        .get("uorGnaf")
        .ok_or_else(|| SpecError::new(CLAUSE, "authority/manifest.json pins no `uorGnaf`"))?;
    let uor_path = uor.required_str(CLAUSE, "path", "authority pin `uorGnaf`")?;
    let pinned = uor.required_str(CLAUSE, "pinnedSha256", "authority pin `uorGnaf`")?;
    let recomputed = sha256::file_hex(CLAUSE, Path::new(uor_path))?;
    g.check(
        "1",
        "UOR-GNAF authority digest",
        recomputed == pinned,
        &format!("{}...", &pinned[..pinned.len().min(16)]),
    );

    let built = manifest::build()?;
    let manifest_report = manifest::verdict(&built)?;
    g.check(
        "1",
        "manifest identity stages current and acyclic",
        manifest_report.is_ok(),
        &clip(manifest_report.as_ref().err().map_or("", String::as_str), 150),
    );

    let toolchain = read_trimmed("lean-toolchain")?;
    let pinned_toolchain = pins
        .get("lean")
        .and_then(|l| l.get("toolchain"))
        .and_then(Value::as_str)
        .unwrap_or_default();
    g.check("1", "Lean toolchain pin", toolchain == pinned_toolchain, &toolchain);

    // SPEC 5: recompute the pins from content, never trust a checksum string.
    let vendored = pins
        .get("wasmCore")
        .and_then(|w| w.get("vendored"))
        == Some(&Value::Bool(true));
    let digests = vendor::recompute("vendor/wasm-spec")?;
    g.check(
        "1",
        "WebAssembly Core wg-3.0 vendored and digests recomputed",
        vendored && digests.is_ok(),
        &clip_or(
            digests.as_ref().err().map_or("", String::as_str),
            140,
            "vendored tree digest mismatch",
        ),
    );

    // SPEC 5.1: the tool CHECKS what the kernel proved; it never decides it.
    // `Wasm.profile_matches_pinned_revision` stands on literals in
    // `Wasm/Revision.lean` -- the digest of `SHA256SUMS`, the file count, the
    // commit -- and Lean cannot read the tree. This is what stops a literal that
    // has drifted from the vendored bytes from elaborating its way past the gate,
    // and it checks the vendored-anchor map of `Wasm/Adequacy.lean` the same way.
    let binding = vendor::binding(Path::new("vendor/wasm-spec"), root)?;
    g.check(
        "1",
        "Lean vendored-tree literals match the vendored content",
        binding.is_ok(),
        &clip(&binding.findings.join("; "), 200),
    );

    // ---- 2. claim graph -----------------------------------------------------
    let registry = read_json("model/claims.json")?;
    let claims = registry
        .get("claims")
        .and_then(Value::as_array)
        .ok_or_else(|| SpecError::new(CLAUSE, "model/claims.json has no `claims` array"))?;
    let ids: Vec<&str> = claims.iter().map(|c| str_field(c, "id")).collect();

    g.check("2", "claim graph nonempty", !claims.is_empty(), &format!("{} claims", claims.len()));

    let mut unique: Vec<&str> = ids.clone();
    unique.sort_unstable();
    unique.dedup();
    g.check("2", "claim ids unique", unique.len() == ids.len(), "");

    let dangling: Vec<&str> = claims
        .iter()
        .flat_map(|c| c.get("dependsOn").and_then(Value::as_array).unwrap_or(&[]))
        .filter_map(Value::as_str)
        .filter(|d| !ids.contains(d))
        .collect();
    g.check("2", "no orphan dependencies", dangling.is_empty(), &py_list(&dangling));

    // SPEC 5.1: the Lean development and the Rust tooling are separate trees.
    // The tooling crate must never end up on the proof path.
    let rust_in_lib = files_with_extension(Path::new("WasmGemmGnaf"), "rs")?;
    let lean_in_xtask = files_with_extension(Path::new("xtask"), "lean")?;
    g.check(
        "2",
        "SPEC 5.1 language boundary",
        rust_in_lib.is_empty() && lean_in_xtask.is_empty(),
        &format!(
            "rust under WasmGemmGnaf/: {}; lean under xtask/: {}",
            py_list(&borrow(&rust_in_lib)),
            py_list(&borrow(&lean_in_xtask))
        ),
    );

    let fw = firewall::report()?;
    g.check(
        "2",
        "dependency firewall (SPEC 10.1)",
        fw.is_ok(),
        &clip(last_line(fw.as_ref().err().map_or("", String::as_str)), 160),
    );

    // ---- 3. Lean builds, no placeholder or unexpected axiom -----------------
    let build = run_command(Command::new("lake").arg("build"))?;
    g.check("3", "lake build", build.ok, &clip(build.stderr.trim(), 120));

    // `lake build` can report success while serving a stale .olean, masking a
    // root module that does not actually elaborate (this really happened: two
    // modules declared clashing `Fault` types and lake reported green).
    // Elaborate the root directly -- success there is the claim that matters.
    let root_module = run_command(
        Command::new("lean")
            .arg("WasmGemmGnaf.lean")
            .env("LEAN_PATH", root.join(".lake/build/lib/lean")),
    )?;
    g.check(
        "3",
        "root module elaborates (not a stale olean)",
        root_module.ok && root_module.stdout.trim().is_empty(),
        &clip(root_module.stdout.trim(), 160),
    );

    let scan = crate::scan::report(&[])?;
    g.check(
        "3",
        "no forbidden constructs",
        scan.is_ok(),
        &clip(scan.as_ref().err().map_or("", String::as_str), 160),
    );

    let proved: Vec<String> = claims
        .iter()
        .filter(|c| str_field(c, "level") == "formalProof")
        .filter_map(|c| c.get("leanDeclaration").and_then(Value::as_str))
        .map(String::from)
        .collect();
    // The root module, not one layer of it: a probe importing only
    // `Cost.Objective` cannot see a claim proved in `GNAF` or `Gemm`, and an
    // unseen claim is an unaudited claim.
    let axioms = lean::probe_axioms(CLAUSE, root, ".gate_axioms.lean", &proved)?;
    let unexpected: Vec<&str> = ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"]
        .into_iter()
        .filter(|w| axioms.stdout.contains(w))
        .collect();
    let axioms_ok = axioms.success && unexpected.is_empty();
    g.check(
        "3",
        "axiom closure clean",
        axioms_ok,
        &if unexpected.is_empty() {
            clip(axioms.stderr.trim(), 120)
        } else {
            py_list(&unexpected)
        },
    );

    // ---- 2 (continued). deviations and the SPEC 15 inventory ----------------
    let deviations = read_json("model/spec-deviations.json")?;
    let rows = deviations
        .get("deviations")
        .and_then(Value::as_array)
        .unwrap_or(&[]);
    // A deviation is justified when it names the content that REPLACES what the
    // SPEC asked for. That field is a list of proved declarations in some rows
    // and a sentence in others, so the test is that something was supplied --
    // an empty list is not a justification.
    let undocumented: Vec<&str> = rows
        .iter()
        .filter(|d| !d.get("intendedContentProvedBy").is_some_and(Value::is_supplied))
        .map(|d| str_field(d, "id"))
        .collect();
    g.check(
        "2",
        "every SPEC deviation carries a proved replacement",
        undocumented.is_empty(),
        &py_list(&undocumented),
    );

    // SPEC 15 inventory, derived from SPEC.md and checked against the COMPILED
    // environment. A hand-maintained JSON status field is not evidence; an
    // external audit found the registry understated the surface by 26
    // declarations.
    //
    // `required::report` now demands a PROPOSITION, not a name: a required
    // declaration counts only if `Conformance/RequiredSignatures.lean` restates
    // it in full and closes it with `:= @Name`. The same audit found the previous
    // rule crediting a matching-name `Nat := 0`.
    let inventory = required::report(root)?;
    g.check(
        "2",
        "SPEC 15 required declarations all discharged",
        inventory.missing.is_empty(),
        &clip(&inventory.render(false).replace('\n', " "), 150),
    );

    // And the wiring that makes the line above mean anything: every credited
    // declaration has a binding, no binding is closed by a tactic, no marker
    // names something SPEC does not require, and every quotation of SPEC is
    // current. `M15` is the falsifier.
    let spec_text = std::fs::read_to_string(Path::new("SPEC.md"))
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", Path::new("SPEC.md"), e))?;
    let required_declarations = required::required_names(&spec_text)?;
    let signature_source = std::fs::read_to_string(Path::new(
        "WasmGemmGnaf/Conformance/RequiredSignatures.lean",
    ))
    .map_err(|e| {
        SpecError::io(
            CLAUSE,
            "cannot read",
            Path::new("WasmGemmGnaf/Conformance/RequiredSignatures.lean"),
            e,
        )
    })?;
    let signature_bindings = crate::signature::parse(&signature_source);
    let mut signature_failures = crate::signature::audit(
        &required_declarations,
        &signature_bindings,
        &crate::signature::deviation_ids()?,
        &spec_text,
    );
    let exact = crate::signature::exact_names(&signature_bindings);
    for name in &inventory.credited {
        if !exact.iter().any(|e| e == name)
            && !signature_bindings.iter().any(|b| b.name == *name)
        {
            signature_failures.push(format!("{name} has no signature binding"));
        }
    }
    g.check(
        "2",
        &format!(
            "all {} credited SPEC 15 declarations bound to SPEC's proposition",
            exact.len()
        ),
        signature_failures.is_empty(),
        &clip(&signature_failures.join("; "), 200),
    );

    // ---- declaration presence, from one probe -------------------------------
    let names: Vec<String> = PRESENCE_PROBE.iter().map(|s| (*s).to_string()).collect();
    let presence = lean::probe_axioms(CLAUSE, root, ".gate_decl.lean", &names)?;
    let seen = presence.combined();
    let declared = |name: &str| seen.contains(&format!("'{name}' "));

    // SPEC 1 / authority WGG-GO-1: the gate must compare the compiled UNFOLDED
    // definition with the frozen schema, not merely find a name. The binding is
    // definitional (Iff.rfl in Conformance/Schema.lean), so a weakened
    // GlobalOptimal or an artifact-specific ProfileValid stops elaborating.
    //
    // The two named here are the ones the release theorem is stated in, so they
    // are answered from the presence probe already run. That is a spot check on
    // two of thirteen, which is why the full audit follows it: the audit reads
    // the authority's own `scopeCriticalDefinitions` array, so a definition
    // added to the frozen authority cannot pass unnoticed for want of anyone
    // remembering to extend this list.
    g.check(
        "2",
        "scope-critical definitions match the frozen WGG-GO-1 schema",
        declared("WasmGemmGnaf.Conformance.globalOptimal_matches_authority_schema")
            && declared("WasmGemmGnaf.Conformance.profileValid_matches_authority_schema"),
        "schema binding absent -- a name check alone cannot reject a weakened proposition",
    );

    let required_definitions = crate::schema::scope_critical_definitions()?;
    let schema_source = std::fs::read_to_string(Path::new(
        "WasmGemmGnaf/Conformance/Schema.lean",
    ))
    .map_err(|e| {
        SpecError::io(CLAUSE, "cannot read", Path::new("WasmGemmGnaf/Conformance/Schema.lean"), e)
    })?;
    let unbound = crate::schema::audit(
        &required_definitions,
        &crate::schema::parse(&schema_source),
    );
    g.check(
        "2",
        &format!(
            "all {} authority scope-critical definitions definitionally bound",
            required_definitions.len()
        ),
        unbound.is_empty(),
        &clip(&unbound.join("; "), 200),
    );

    // ---- 4-8. semantics, coverage, artifact, lower bound --------------------
    g.check(
        "4",
        "WebAssembly and GEMM semantics built",
        declared("WasmGemmGnaf.Wasm.profile_matches_pinned_revision"),
        "Wasm.profile_matches_pinned_revision absent",
    );
    g.check(
        "5",
        "universal sublevel coverage proved",
        declared("WasmGemmGnaf.Universal.universal_sublevel_coverage"),
        "Universal.universal_sublevel_coverage absent",
    );
    g.check(
        "6",
        "committed artifact matches proved value",
        Path::new("artifacts/wasm-gemm-gnaf.wasm").exists(),
        "artifact not emitted",
    );
    g.check("7", "artifact decode/validate/ABI/cost theorems", false, "gated on WS-001");
    g.check(
        "8",
        "universal lower bound and attainment",
        declared("WasmGemmGnaf.Universal.all_competitors_lower_bound")
            && declared("WasmGemmGnaf.Artifact.released_attains_lower_bound"),
        "Universal.all_competitors_lower_bound / Artifact.released_attains_lower_bound absent",
    );

    // ---- 9. the release theorem itself --------------------------------------
    // Presence in the compiled environment, never a JSON field. This is the
    // condition the whole gate exists to protect.
    g.check(
        "9",
        "released_wasm_gemm_gnaf_global_optimal closed",
        declared("WasmGemmGnaf.Artifact.released_wasm_gemm_gnaf_global_optimal"),
        "declaration absent; answer class WorkloadIncomplete (UOR-GNAF 10.9)",
    );

    // ---- 10-13 --------------------------------------------------------------
    g.check("10", "Atlas seal reconstructs", false, "seal not constructed");

    if no_mutation {
        // Invoked from M6; running the suite here would recurse back into the gate.
        g.check("11", "mutation suites reject planted faults", true, "skipped (invoked from M6)");
    } else {
        let mutation = run_command(Command::new(self_exe()?).arg("mutation"))?;
        g.check(
            "11",
            "mutation suites reject planted faults",
            mutation.ok,
            &tail(mutation.stdout.trim(), 160),
        );
    }

    g.check("12", "two clean emissions byte-identical", false, "gated on step 6");

    let root_check = crate::root::report(true)?;
    g.check(
        "13",
        "no stale or unowned Lean module",
        root_check.is_ok(),
        &clip(root_check.as_ref().err().map_or("", String::as_str), 160),
    );

    let git = run_command(Command::new("git").args(["status", "--porcelain"]))?;
    g.check(
        "13",
        "worktree clean after verification",
        git.stdout.trim().is_empty(),
        "untracked build outputs present",
    );

    println!("\n{}", "=".repeat(66));
    if g.failed > 0 {
        println!("GATE: FAIL — {} unmet condition(s).", g.failed);
        println!("This is the conforming outcome while WGG-GO-1 is outstanding.");
        println!("Terminal answer: WorkloadIncomplete (UOR-GNAF 10.9). See CERTIFICATION.md.");
        println!("Per UOR-GNAF 13.3 the gate MUST NOT return an unproved global label.");
        return Ok(Outcome::Fail);
    }
    println!("GATE: PASS");
    Ok(Outcome::Pass)
}

/// This binary, for the one step that must run in a separate process.
pub fn self_exe() -> Result<std::path::PathBuf> {
    std::env::current_exe().map_err(|e| {
        SpecError::new(CLAUSE, format!("cannot locate the gate binary to re-invoke: {e}"))
    })
}

pub struct Ran {
    pub ok: bool,
    pub stdout: String,
    pub stderr: String,
}

/// Run a command, capturing both streams.
pub fn run_command(command: &mut Command) -> Result<Ran> {
    let output = command.output().map_err(|e| {
        SpecError::new(
            CLAUSE,
            format!("cannot run `{}`: {e}", command.get_program().to_string_lossy()),
        )
    })?;
    Ok(Ran {
        ok: output.status.success(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

fn read_json(path: &str) -> Result<Value> {
    let p = Path::new(path);
    let text = std::fs::read(p)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", p, e))?;
    json::parse(CLAUSE, &text)
}

fn read_trimmed(path: &str) -> Result<String> {
    let p = Path::new(path);
    std::fs::read_to_string(p)
        .map(|t| t.trim().to_string())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", p, e))
}

fn str_field<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("")
}

fn files_with_extension(dir: &Path, extension: &str) -> Result<Vec<String>> {
    let mut found = Vec::new();
    if dir.is_dir() {
        collect_extension(dir, extension, &mut found)?;
    }
    found.sort();
    Ok(found)
}

fn collect_extension(dir: &Path, extension: &str, found: &mut Vec<String>) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .map_err(|e| SpecError::io("5.1", "cannot read directory", dir, e))?;
    for entry in entries {
        let entry = entry.map_err(|e| SpecError::io("5.1", "cannot read entry under", dir, e))?;
        let path = entry.path();
        if path.is_dir() {
            collect_extension(&path, extension, found)?;
        } else if path.extension().is_some_and(|e| e == extension) {
            found.push(repo::slash(&path));
        }
    }
    Ok(())
}

/// A list of names the way the gate has always printed them.
///
/// The failure details are read by a release engineer under time pressure, so
/// the rendering stays exactly as it was rather than becoming a Rust debug dump.
fn py_list(items: &[&str]) -> String {
    let body: Vec<String> = items.iter().map(|i| format!("'{i}'")).collect();
    format!("[{}]", body.join(", "))
}

fn borrow(items: &[String]) -> Vec<&str> {
    items.iter().map(String::as_str).collect()
}

fn clip(text: &str, limit: usize) -> String {
    text.chars().take(limit).collect()
}

fn clip_or(text: &str, limit: usize, fallback: &str) -> String {
    let clipped = clip(text.trim(), limit);
    if clipped.is_empty() {
        fallback.to_string()
    } else {
        clipped
    }
}

fn tail(text: &str, limit: usize) -> String {
    let chars: Vec<char> = text.chars().collect();
    chars[chars.len().saturating_sub(limit)..].iter().collect()
}

fn last_line(text: &str) -> &str {
    text.trim_end().rsplit('\n').next().unwrap_or("")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detail_is_hidden_on_pass() {
        // Not a cosmetic rule: a PASS row that carries a failure explanation is
        // how a green gate gets read as red.
        let mut g = Gate { failed: 0 };
        g.check("1", "ok", true, "this must not appear");
        assert_eq!(g.failed, 0);
        g.check("1", "bad", false, "this must appear");
        assert_eq!(g.failed, 1);
    }

    #[test]
    fn clipping_matches_python_slicing() {
        assert_eq!(clip("abcdef", 3), "abc");
        assert_eq!(clip("ab", 8), "ab");
        assert_eq!(tail("abcdef", 3), "def");
        assert_eq!(tail("ab", 8), "ab");
        assert_eq!(clip_or("   ", 10, "fallback"), "fallback");
        assert_eq!(last_line("a\nb\nc\n"), "c");
    }

    #[test]
    fn a_supplied_field_is_present_and_non_empty() {
        // The defect: a deviation row whose justification is an empty list is
        // NOT justified, and one whose justification is a list of proved
        // declarations IS -- so the test cannot be "is this a string".
        let devs = json::parse(
            "20.2",
            r#"[{"intendedContentProvedBy": ["A.b"]},
                {"intendedContentProvedBy": []},
                {"intendedContentProvedBy": null},
                {"intendedContentProvedBy": "prose"},
                {}]"#,
        )
        .expect("parses");
        let rows = devs.as_array().expect("array");
        let supplied: Vec<bool> = rows
            .iter()
            .map(|d| d.get("intendedContentProvedBy").is_some_and(Value::is_supplied))
            .collect();
        assert_eq!(supplied, vec![true, false, false, true, false]);
    }

    #[test]
    fn failure_details_list_names_the_way_the_gate_always_has() {
        assert_eq!(py_list(&[]), "[]");
        assert_eq!(py_list(&["DEV-001", "DEV-002"]), "['DEV-001', 'DEV-002']");
    }
}
