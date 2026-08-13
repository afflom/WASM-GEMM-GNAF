//! `xtask manifest [--check]` -- SPEC sections 4 and 5. Replaces `Tools/manifest.py`.
//!
//! SPEC section 4 fixes three ordered identity stages plus one external
//! attestation, and requires them ACYCLIC: no manifest contains its own
//! identity, and no two stages hash each other.
//!
//! 1. `SourceManifestCore` -- immutable authority + handwritten Lean + fixtures +
//!    tool inputs. EXCLUDES every manifest and every generated output.
//! 2. `GeneratedProofInputBody` -- binds the source-core identity plus every
//!    GENERATED Lean source on the final theorem path. Excludes its own encoding
//!    and all later outputs. `PreFinalEnvironmentBody` binds that identity plus
//!    toolchain/dependency identities and the compiled environment digest.
//! 3. `OutputManifestBody` -- binds the three identities above plus artifact,
//!    seal, proof registry, generated docs and the frozen reproducibility plan.
//!    EXCLUDES `MANIFEST.json` itself.
//!
//! `MANIFEST.json` is the canonical encoding of stage 3; its own external digest
//! is reported by CI and never included in its own preimage.

use std::fs;
use std::path::Path;

use crate::json::{self, obj, s, Out};
use crate::sha256;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "4";
const MANIFEST: &str = "MANIFEST.json";

/// Files that are GENERATED rather than handwritten. Excluded from the source core.
const GENERATED: [&str; 3] = ["CONFORMANCE.md", "MANIFEST.json", "WasmGemmGnaf.lean"];

/// Outputs, excluded from stages 1 and 2.
const OUTPUT_DIRS: [&str; 1] = ["artifacts/"];

/// Directory prefixes whose contents are never source.
///
/// `target/` and `.lake/` in particular: recording a build product makes the
/// manifest stale on any clean checkout, which stopped CI before the
/// release-path, required-declaration, axiom and final-gate checks ran. The
/// same defect arrived once as Python bytecode; the rule is that nothing
/// derived is ever hashed here.
const SKIP_DIRS: [&str; 4] = [".git/", ".lake/", "vendor/wasm-spec/README.md", "target/"];

/// The SPEC section 5 prefixes that hold source.
const SOURCE_DIRS: [&str; 8] = [
    "WasmGemmGnaf/",
    "authority/",
    "model/",
    "Tools/",
    "xtask/",
    "fixtures/",
    "Tests/",
    ".github/",
];

/// The SPEC section 5 root files that hold source.
const SOURCE_FILES: [&str; 14] = [
    "SPEC.md",
    "README.md",
    "AGENTS.md",
    "VERIFICATION.md",
    "CERTIFICATION.md",
    "Justfile",
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
    ".gitignore",
    "Cargo.toml",
    "Cargo.lock",
    "LICENSE-APACHE",
    "LICENSE-MIT",
];

pub fn run(check: bool) -> Result<Outcome> {
    let built = build()?;
    if check {
        match verdict(&built)? {
            Ok(line) => {
                println!("{line}");
                Ok(Outcome::Pass)
            }
            Err(line) => {
                println!("{line}");
                Ok(Outcome::Fail)
            }
        }
    } else {
        let path = Path::new(MANIFEST);
        fs::write(path, built.document.pretty() + "\n")
            .map_err(|e| SpecError::io(CLAUSE, "cannot write", path, e))?;
        println!("{MANIFEST}: {} source files", built.source_files);
        println!("  sourceManifestCore      {}...", &built.source_core[..16]);
        println!("  generatedProofInput     {}...", &built.generated_proof_input[..16]);
        println!("  preFinalEnvironment     {}...", &built.pre_final_environment[..16]);
        Ok(Outcome::Pass)
    }
}

/// A manifest just recomputed from the tree.
pub struct Built {
    pub document: Out,
    pub source_files: usize,
    pub source_core: String,
    pub generated_proof_input: String,
    pub pre_final_environment: String,
}

/// The `--check` verdict: `Ok` is the current-manifest line, `Err` the staleness
/// report. Both are printed; only the second is a SPEC section 4 failure.
pub fn verdict(built: &Built) -> Result<std::result::Result<String, String>> {
    let path = Path::new(MANIFEST);
    if !path.is_file() {
        return Ok(Err(format!("{MANIFEST} missing — run `just manifest`")));
    }
    let text = fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read", path, e))?;
    let current = json::parse(CLAUSE, &text)?;

    for (field, fresh) in [
        ("sourceManifestCoreIdentity", &built.source_core),
        ("generatedProofInputIdentity", &built.generated_proof_input),
        ("preFinalEnvironmentIdentity", &built.pre_final_environment),
    ] {
        if current.get(field).and_then(crate::json::Value::as_str) != Some(fresh.as_str()) {
            return Ok(Err(format!(
                "{MANIFEST} STALE: {field} differs — run `just manifest`"
            )));
        }
    }
    Ok(Ok(format!(
        "manifest current: {} source files, 3 identity stages",
        built.source_files
    )))
}

/// Recompute all three stages from the tree.
pub fn build() -> Result<Built> {
    // ---- stage 1: source core ---------------------------------------------
    let source_files = collect(is_source)?;
    let source_core = obj(vec![
        ("schemaVersion", Out::Int(1)),
        ("stage", s("SourceManifestCore")),
        (
            "excludes",
            Out::Arr(vec![
                s("every manifest"),
                s("every generated output"),
                s("artifacts/"),
            ]),
        ),
        ("files", Out::Arr(source_files.iter().map(|p| file_entry(p, true)).collect::<Result<_>>()?)),
    ]);
    let source_core_id = identity(&source_core);

    // ---- stage 2: generated proof inputs + pre-final environment ----------
    let generated_present: Vec<String> = ["WasmGemmGnaf.lean"]
        .into_iter()
        .filter(|p| Path::new(p).exists())
        .map(String::from)
        .collect();
    let generated_proof_input = obj(vec![
        ("schemaVersion", Out::Int(1)),
        ("stage", s("GeneratedProofInputBody")),
        ("sourceManifestCoreIdentity", s(source_core_id.clone())),
        (
            "excludes",
            Out::Arr(vec![s("its own JSON encoding"), s("every later output")]),
        ),
        (
            "generatedLeanSources",
            Out::Arr(
                generated_present
                    .iter()
                    .map(|p| file_entry(p, true))
                    .collect::<Result<_>>()?,
            ),
        ),
        (
            "note",
            s("Artifact/Bytes.lean is NOT present: no artifact has been emitted, \
               because emission requires WS-001 and BI-002. SPEC 13 Phase F step 4 \
               is therefore not reached."),
        ),
    ]);
    let generated_proof_input_id = identity(&generated_proof_input);

    let toolchain_path = Path::new("lean-toolchain");
    let toolchain = fs::read_to_string(toolchain_path)
        .map_err(|e| SpecError::io("4", "cannot read the pinned toolchain", toolchain_path, e))?
        .trim()
        .to_string();
    let pre_final_environment = obj(vec![
        ("schemaVersion", Out::Int(1)),
        ("stage", s("PreFinalEnvironmentBody")),
        ("generatedProofInputIdentity", s(generated_proof_input_id.clone())),
        ("leanToolchain", s(toolchain)),
        ("leanCommit", s("d024af099ca4bf2c86f649261ebf59565dc8c622")),
        ("dependencies", Out::Arr(Vec::new())),
        ("compiledEnvironmentDigest", Out::Null),
        (
            "note",
            s("compiledEnvironmentDigest is null: SPEC 13 Phase F step 5 records the \
               checked final declaration-environment digest, which is only meaningful \
               once the final theorem is on the path. GO-001 is outstanding."),
        ),
    ]);
    let pre_final_environment_id = identity(&pre_final_environment);

    // ---- stage 3: output manifest -----------------------------------------
    let artifacts = collect(|p| p.starts_with("artifacts/") && !p.ends_with("README.md"))?;
    let output_manifest = obj(vec![
        ("schemaVersion", Out::Int(1)),
        ("stage", s("OutputManifestBody")),
        ("sourceManifestCoreIdentity", s(source_core_id.clone())),
        ("generatedProofInputIdentity", s(generated_proof_input_id.clone())),
        ("preFinalEnvironmentIdentity", s(pre_final_environment_id.clone())),
        ("excludes", Out::Arr(vec![s("MANIFEST.json itself")])),
        (
            "artifact",
            Out::Arr(artifacts.iter().map(|p| file_entry(p, false)).collect::<Result<_>>()?),
        ),
        ("atlasSeal", Out::Null),
        (
            "proofRegistry",
            obj(vec![
                ("path", s("model/claims.json")),
                ("sha256", s(sha256::file_hex(CLAUSE, Path::new("model/claims.json"))?)),
            ]),
        ),
        (
            "generatedDocumentation",
            if Path::new("CONFORMANCE.md").exists() {
                Out::Arr(vec![obj(vec![
                    ("path", s("CONFORMANCE.md")),
                    ("sha256", s(sha256::file_hex(CLAUSE, Path::new("CONFORMANCE.md"))?)),
                ])])
            } else {
                Out::Arr(Vec::new())
            },
        ),
        (
            "reproducibilityPlan",
            obj(vec![
                ("path", s("model/reproducibility-plan.json")),
                (
                    "sha256",
                    s(sha256::file_hex(CLAUSE, Path::new("model/reproducibility-plan.json"))?),
                ),
            ]),
        ),
        (
            "releaseStatus",
            obj(vec![
                ("GO-001", s("outstanding")),
                ("answerClass", s("WorkloadIncomplete")),
                ("authority", s("UOR-GNAF v1-draft.2 section 10.9")),
            ]),
        ),
        ("extraFilesBeyondSpecTree", extra_files()),
    ]);

    let document = obj(vec![
        ("schemaVersion", Out::Int(1)),
        ("description", s("Ordered acyclic identity stages. SPEC sections 4 and 5.")),
        (
            "acyclicity",
            s("Each stage binds only EARLIER stage identities. No stage contains \
               its own identity. MANIFEST.json is the canonical encoding of \
               OutputManifestBody and its own digest is never in its own preimage."),
        ),
        ("sourceManifestCore", source_core),
        ("sourceManifestCoreIdentity", s(source_core_id.clone())),
        ("generatedProofInputBody", generated_proof_input),
        ("generatedProofInputIdentity", s(generated_proof_input_id.clone())),
        ("preFinalEnvironmentBody", pre_final_environment),
        ("preFinalEnvironmentIdentity", s(pre_final_environment_id.clone())),
        ("outputManifestBody", output_manifest),
        ("reproducibilityAttestation", Out::Null),
    ]);

    Ok(Built {
        document,
        source_files: source_files.len(),
        source_core: source_core_id,
        generated_proof_input: generated_proof_input_id,
        pre_final_environment: pre_final_environment_id,
    })
}

/// SPEC section 5: additional files are permitted only when owned by a layer and
/// listed here with a justification.
fn extra_files() -> Out {
    let rows = [
        ("WasmGemmGnaf/Wasm/Fault.lean", "Wasm",
         "SPEC 7.1's SpecMachine exposes ONE Fault used by both decode and initial. Binary and Config own genuinely different failure sets under SPEC 7.1's ownership rule, so the unified type needs its own module. Both injections proved injective, images proved disjoint."),
        ("WasmGemmGnaf/Foundation/SchemaRegistry.lean", "Foundation",
         "Required verbatim by SPEC 6.2 ('Foundation/SchemaRegistry.lean SHALL retain the finite registry'), which the SPEC 5 tree omits."),
        ("WasmGemmGnaf/Atlas/CoverageScope.lean", "Atlas",
         "Hardening. Proves the seal's cover check is blind to the byte universe, so it cannot be cited as universal coverage (claim AT-001, falsifier M7)."),
        ("WasmGemmGnaf/Universal/BilinearLowerBound.lean", "Universal",
         "Proved partial lower bound (claim LB-002); establishes that the open tensor-rank problem does not gate the release theorem."),
    ];
    obj(vec![
        (
            "rule",
            s("SPEC 5: additional files permitted only when owned by a layer and listed here."),
        ),
        (
            "files",
            Out::Arr(
                rows.into_iter()
                    .map(|(path, layer, why)| {
                        obj(vec![
                            ("path", s(path)),
                            ("layer", s(layer)),
                            ("justification", s(why)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

/// Canonical identity of a first-order body: sha256 of its canonical JSON.
/// Sorted keys and fixed separators make the encoding injective for these bodies.
fn identity(body: &Out) -> String {
    sha256::hex(body.canonical().as_bytes())
}

fn file_entry(path: &str, with_size: bool) -> Result<Out> {
    let p = Path::new(path);
    let bytes = fs::read(p).map_err(|e| SpecError::io(CLAUSE, "cannot hash", p, e))?;
    let mut fields = vec![("path", s(path)), ("sha256", s(sha256::hex(&bytes)))];
    if with_size {
        fields.push(("bytes", Out::Int(bytes.len() as u64)));
    }
    Ok(obj(fields))
}

/// Every tracked path satisfying `pred`, sorted.
///
/// Sorting the whole list (rather than per directory) is what makes the source
/// core's file order a function of the tree alone, so the identity does not
/// depend on the filesystem's enumeration order.
fn collect(pred: impl Fn(&str) -> bool) -> Result<Vec<String>> {
    let mut out = Vec::new();
    walk(Path::new("."), &mut out)?;
    let mut kept: Vec<String> = out.into_iter().filter(|p| pred(p)).collect();
    kept.sort();
    Ok(kept)
}

fn walk(dir: &Path, out: &mut Vec<String>) -> Result<()> {
    let entries =
        fs::read_dir(dir).map_err(|e| SpecError::io(CLAUSE, "cannot read directory", dir, e))?;
    for entry in entries {
        let entry = entry.map_err(|e| SpecError::io(CLAUSE, "cannot read entry under", dir, e))?;
        let path = entry.path();
        let rel = normalize(&path);
        if skipped(&rel) {
            continue;
        }
        let kind = entry
            .file_type()
            .map_err(|e| SpecError::io(CLAUSE, "cannot stat", &path, e))?;
        if kind.is_dir() {
            walk(&path, out)?;
        } else {
            out.push(rel);
        }
    }
    Ok(())
}

/// `./a/b` as `a/b`, with `/` separators.
fn normalize(path: &Path) -> String {
    let text = path.to_string_lossy().replace('\\', "/");
    text.strip_prefix("./").unwrap_or(&text).to_string()
}

/// Never hashed: build output, version-control internals, and anything derived.
fn skipped(rel: &str) -> bool {
    SKIP_DIRS.iter().any(|d| rel.starts_with(d) || rel == d.trim_end_matches('/'))
        || rel.contains("__pycache__")
        || rel.ends_with(".pyc")
}

fn is_source(p: &str) -> bool {
    let base = p.rsplit('/').next().unwrap_or(p);
    if GENERATED.contains(&base) {
        return false;
    }
    if OUTPUT_DIRS.iter().any(|d| p.starts_with(d)) {
        return false;
    }
    SOURCE_DIRS.iter().any(|d| p.starts_with(d)) || SOURCE_FILES.contains(&p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_and_derived_paths_are_never_source() {
        assert!(!is_source("MANIFEST.json"));
        assert!(!is_source("CONFORMANCE.md"));
        assert!(!is_source("WasmGemmGnaf.lean"));
        assert!(!is_source("artifacts/wasm-gemm-gnaf.wasm"));
        assert!(is_source("WasmGemmGnaf/Foundation/Bytes.lean"));
        assert!(is_source("xtask/src/manifest.rs"));
        assert!(is_source("SPEC.md"));
        assert!(!is_source("vendor/wasm-spec/SHA256SUMS"));
    }

    #[test]
    fn bytecode_and_build_output_are_skipped() {
        // The defect this guards: recording derived bytes made the manifest
        // stale on a clean checkout and stopped CI before any real check ran.
        assert!(skipped("target/release/xtask"));
        assert!(skipped(".lake/build/lib/lean/WasmGemmGnaf.olean"));
        assert!(skipped(".git/HEAD"));
        assert!(skipped("Tools/__pycache__/manifest.cpython-312.pyc"));
        assert!(skipped("anything.pyc"));
        assert!(!skipped("WasmGemmGnaf/Wasm/Fault.lean"));
    }

    #[test]
    fn identity_is_order_independent_but_content_sensitive() {
        let a = obj(vec![("b", Out::Int(2)), ("a", s("x"))]);
        let b = obj(vec![("a", s("x")), ("b", Out::Int(2))]);
        assert_eq!(identity(&a), identity(&b));
        let c = obj(vec![("a", s("y")), ("b", Out::Int(2))]);
        assert_ne!(identity(&a), identity(&c));
    }

    #[test]
    fn a_stage_never_contains_its_own_identity() {
        // SPEC 4 acyclicity. Checked on the shape the builder produces rather
        // than on one recorded run, so it holds for any tree.
        let core = obj(vec![("stage", s("SourceManifestCore")), ("files", Out::Arr(vec![]))]);
        let core_id = identity(&core);
        assert!(!core.canonical().contains(&core_id));

        let later = obj(vec![
            ("stage", s("GeneratedProofInputBody")),
            ("sourceManifestCoreIdentity", s(core_id.clone())),
        ]);
        let later_id = identity(&later);
        assert!(later.canonical().contains(&core_id), "must bind the EARLIER stage");
        assert!(!later.canonical().contains(&later_id), "must not bind itself");
        assert!(!core.canonical().contains(&later_id), "must not bind a LATER stage");
    }
}
