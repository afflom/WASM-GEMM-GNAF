//! `xtask amendment` -- the tool half of the grammar-amendment identity binding.
//! SPEC sections 7.3 and 24 (`AMD-005`, `DEV-006`).
//!
//! SPEC section 5.1 draws the line this file sits on. `xtask` CHECKS whether the
//! kernel has discharged an obligation; it never DECIDES one.
//! `Wasm/Core/ProfileAmendment.lean` proves everything about the amendment that
//! Lean can state about itself: that the pinned judgments are contained in the
//! amended ones, that the amended ones are strictly wider, that the arity
//! discipline survives, and that the recorded flags are exactly those theorems.
//! What Lean cannot do is read a file. `core3InstrSeqAmendment` names the
//! vendored SpecTec source the defect is IN and records its SHA-256, and a
//! literal that had drifted from the bytes on disk would still elaborate. This
//! is what stops that.
//!
//! Six findings, each one a way the recorded amendment could stop describing the
//! repository:
//!
//! 1. the recorded per-file digest is not the digest of the file on disk;
//! 2. it is not the digest `vendor/wasm-spec/SHA256SUMS` lists for that file,
//!    so the amendment would sit outside the tree `xtask vendor` walks;
//! 3. the recorded pinned commit is not the vendored tree's, or the recorded
//!    upstream repair commit IS -- i.e. the pin was advanced after all;
//! 4. the pinned source does not contain the judgment the record names, so the
//!    record would point at a production that is not there;
//! 5. the amended Lean module does not declare the relation the record names;
//! 6. the amended Lean module carries a Core 3.0 coverage marker, which SPEC
//!    section 7.3 forbids: the pinned rule inventory must not be inflated by an
//!    amendment.

use std::path::Path;

use crate::sha256;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "7.3";

/// Where the Lean literals live, relative to the repository root.
const REVISION_MODULE: &str = "WasmGemmGnaf/Wasm/Revision.lean";
/// Where the amended judgment lives, relative to the repository root.
const AMENDED_MODULE: &str = "WasmGemmGnaf/Wasm/Core/Validation/InstructionsAmended.lean";
/// The vendored tree root, as `Wasm/Revision.lean` records it.
const VENDOR_ROOT: &str = "vendor/wasm-spec/";
/// The deviation register.
const DEVIATIONS: &str = "model/spec-deviations.json";

/// What the recorded amendment and the tree say, side by side.
pub struct Binding {
    /// `core3InstrSeqAmendment.deviationId`.
    pub deviation_id: String,
    /// `core3InstrSeqAmendment.amendmentId`.
    pub amendment_id: String,
    /// `core3InstrSeqAmendment.pinnedSource`.
    pub pinned_source: String,
    /// `core3InstrSeqAmendmentSourceSha256`.
    pub lean_source_digest: String,
    /// SHA-256 of the pinned source, recomputed from the bytes on disk.
    pub recomputed_source_digest: String,
    /// The digest `SHA256SUMS` lists for the same file.
    pub manifest_source_digest: String,
    /// `core3RevisionCommit`.
    pub lean_commit: String,
    /// The contents of `vendor/wasm-spec/PINNED-COMMIT`.
    pub vendored_commit: String,
    /// `core3InstrSeqRepairCommit` -- recorded, and deliberately not pinned.
    pub repair_commit: String,
    /// `core3InstrSeqAmendment.judgment`.
    pub judgment: String,
    /// `core3InstrSeqAmendment.amendedRelation`.
    pub amended_relation: String,
    /// Coverage markers found in the amended module. SPEC 7.3: must be zero.
    pub markers_in_amended_module: usize,
    /// Every reason this binding is not sound. Empty means it holds.
    pub findings: Vec<String>,
}

impl Binding {
    pub fn is_ok(&self) -> bool {
        self.findings.is_empty()
    }

    pub fn render(&self) -> String {
        let mut out = vec![
            format!("grammar amendment {} ({})", self.amendment_id, self.deviation_id),
            format!("  pinned source: {}", self.pinned_source),
            format!("    digest recomputed from content: {}", self.recomputed_source_digest),
            format!("    Lean core3InstrSeqAmendmentSourceSha256: {}", self.lean_source_digest),
            format!("    SHA256SUMS lists: {}", self.manifest_source_digest),
            format!("  judgment amended: {}", self.judgment),
            format!("  amended relation: {}", self.amended_relation),
            format!(
                "  coverage markers in the amended module: {} (SPEC 7.3 requires 0)",
                self.markers_in_amended_module
            ),
            format!(
                "  pinned commit: {} (Lean core3RevisionCommit {})",
                self.vendored_commit, self.lean_commit
            ),
            format!("  upstream repair commit, recorded and NOT pinned: {}", self.repair_commit),
        ];
        for finding in &self.findings {
            out.push(format!("  FAIL {finding}"));
        }
        out.join("\n")
    }
}

pub fn run() -> Result<Outcome> {
    let binding = binding(Path::new("."))?;
    println!("{}", binding.render());
    Ok(if binding.is_ok() { Outcome::Pass } else { Outcome::Fail })
}

/// Compare the recorded amendment with the vendored tree and the Lean sources
/// under `root`. `root` is a parameter so the mutation suite can point this at
/// a COPY with a planted fault.
pub fn binding(root: &Path) -> Result<Binding> {
    let revision_path = root.join(REVISION_MODULE);
    let revision = crate::repo::read_lossy(CLAUSE, &revision_path)?;

    let record = record_body(&revision).ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            format!(
                "{}: no `def core3InstrSeqAmendment : GrammarAmendmentBody :=` record to check",
                revision_path.display()
            ),
        )
    })?;

    let deviation_id = required_field(&record, "deviationId", &revision_path)?;
    let amendment_id = required_field(&record, "amendmentId", &revision_path)?;
    let pinned_source = required_field(&record, "pinnedSource", &revision_path)?;
    let judgment = required_field(&record, "judgment", &revision_path)?;
    let amended_relation = required_field(&record, "amendedRelation", &revision_path)?;

    let lean_source_digest = string_literal(&revision, "core3InstrSeqAmendmentSourceSha256")
        .ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                format!(
                    "{}: no `def core3InstrSeqAmendmentSourceSha256 : String := \"...\"`",
                    revision_path.display()
                ),
            )
        })?;
    let repair_commit =
        string_literal(&revision, "core3InstrSeqRepairCommit").ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                format!("{}: no `def core3InstrSeqRepairCommit` literal", revision_path.display()),
            )
        })?;
    let lean_commit = string_literal(&revision, "core3RevisionCommit").ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            format!("{}: no `def core3RevisionCommit` literal", revision_path.display()),
        )
    })?;

    let mut findings: Vec<String> = Vec::new();

    // 1. the recorded source lies inside the vendored tree and hashes to the
    //    recorded digest.
    if !pinned_source.starts_with(VENDOR_ROOT) {
        findings.push(format!(
            "the recorded pinned source {pinned_source} is not under {VENDOR_ROOT}, so no \
             vendored digest covers it"
        ));
    }
    let source_path = root.join(&pinned_source);
    let recomputed_source_digest = match std::fs::read(&source_path) {
        Ok(bytes) => sha256::hex(&bytes),
        Err(_) => {
            findings.push(format!(
                "the recorded pinned source {pinned_source} cannot be read; the amendment names \
                 a file the tree does not have"
            ));
            String::new()
        }
    };
    if !recomputed_source_digest.is_empty() && recomputed_source_digest != lean_source_digest {
        findings.push(format!(
            "core3InstrSeqAmendmentSourceSha256 is {lean_source_digest} but {pinned_source} \
             hashes to {recomputed_source_digest}"
        ));
    }

    // 2. and it is the digest the vendored manifest lists for the same file.
    let relative = pinned_source.strip_prefix(VENDOR_ROOT).unwrap_or(&pinned_source).to_string();
    let sums_path = root.join(VENDOR_ROOT).join("SHA256SUMS");
    let sums = crate::repo::read_lossy(CLAUSE, &sums_path)?;
    let manifest_source_digest = manifest_digest_of(&sums, &relative).unwrap_or_default();
    if manifest_source_digest.is_empty() {
        findings.push(format!(
            "{} lists no digest for {relative}, so the amended source is outside the tree \
             `xtask vendor` walks",
            sums_path.display()
        ));
    } else if manifest_source_digest != lean_source_digest {
        findings.push(format!(
            "core3InstrSeqAmendmentSourceSha256 is {lean_source_digest} but SHA256SUMS lists \
             {manifest_source_digest} for {relative}"
        ));
    }

    // 3. the pin is the pin, and the repair commit is not it.
    let pinned_commit_path = root.join(VENDOR_ROOT).join("PINNED-COMMIT");
    let vendored_commit = crate::repo::read_lossy(CLAUSE, &pinned_commit_path)?.trim().to_string();
    if vendored_commit != lean_commit {
        findings.push(format!(
            "the vendored PINNED-COMMIT is {vendored_commit} but core3RevisionCommit is \
             {lean_commit}"
        ));
    }
    if repair_commit == lean_commit {
        findings.push(format!(
            "core3InstrSeqRepairCommit equals the pin ({lean_commit}): SPEC 7.3 records the \
             defect instead of advancing the pin, so these must differ"
        ));
    }
    if repair_commit.len() != 40 || !repair_commit.bytes().all(|b| b.is_ascii_hexdigit()) {
        findings.push(format!(
            "core3InstrSeqRepairCommit {repair_commit} is not a forty-digit commit identifier"
        ));
    }

    // 4. the pinned source really contains the production the record names.
    if !recomputed_source_digest.is_empty() {
        let text = crate::repo::read_lossy(CLAUSE, &source_path)?;
        if !text.contains(&judgment) {
            findings.push(format!(
                "the recorded judgment `{judgment}` does not occur in {pinned_source}: the \
                 amendment points at a production the pinned source does not define"
            ));
        }
    }

    // 5. the amended module declares the relation the record names.
    let amended_path = root.join(AMENDED_MODULE);
    let amended = crate::repo::read_lossy(CLAUSE, &amended_path)?;
    let short = amended_relation.rsplit('.').next().unwrap_or(&amended_relation).to_string();
    if !amended.contains(&format!("inductive {short} :")) {
        findings.push(format!(
            "{} does not declare `{short}`, which core3InstrSeqAmendment records as the amended \
             relation",
            amended_path.display()
        ));
    }

    // 6. and it inflates no coverage inventory.
    let markers_in_amended_module = amended
        .lines()
        .filter(|line| {
            let t = line.trim_start();
            t.starts_with("-- core-syntax:")
                || t.starts_with("-- core-rule:")
                || t.starts_with("-- core-opcode:")
                || t.starts_with("-- core-exec:")
                || t.starts_with("-- core-aux:")
        })
        .count();
    if markers_in_amended_module != 0 {
        findings.push(format!(
            "{} carries {markers_in_amended_module} Core 3.0 coverage marker(s); SPEC 7.3 \
             forbids the amendment from inflating the pinned rule inventory",
            amended_path.display()
        ));
    }

    // 7. the deviation register records both identifiers.
    let register_path = root.join(DEVIATIONS);
    let register = crate::repo::read_lossy(CLAUSE, &register_path)?;
    for id in [&deviation_id, &amendment_id] {
        if !register.contains(&format!("\"{id}\"")) {
            findings.push(format!(
                "{} does not record {id}, which core3InstrSeqAmendment names",
                register_path.display()
            ));
        }
    }

    Ok(Binding {
        deviation_id,
        amendment_id,
        pinned_source,
        lean_source_digest,
        recomputed_source_digest,
        manifest_source_digest,
        lean_commit,
        vendored_commit,
        repair_commit,
        judgment,
        amended_relation,
        markers_in_amended_module,
        findings,
    })
}

/// The body of `def core3InstrSeqAmendment : GrammarAmendmentBody := { ... }`,
/// as source text.
fn record_body(src: &str) -> Option<String> {
    let at = src.find("def core3InstrSeqAmendment : GrammarAmendmentBody :=")?;
    let rest = &src[at..];
    let open = rest.find('{')?;
    let mut depth = 0usize;
    for (index, ch) in rest[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(rest[open..open + index + 1].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// The string literal of a `<field> :=` structure field, which may sit on the
/// next line. A field whose value is an identifier rather than a literal (the
/// record shares `core3RevisionCommit` that way) returns `None`.
fn field_string(record: &str, field: &str) -> Option<String> {
    let at = record.find(&format!("{field} :="))?;
    let rest = &record[at + field.len() + " :=".len()..];
    // Only look as far as the next field, so a missing literal cannot silently
    // pick up the following field's value.
    let stop = rest.find(" := ").unwrap_or(rest.len());
    let window = &rest[..stop];
    let open = window.find('"')?;
    let body = &window[open + 1..];
    let close = body.find('"')?;
    Some(body[..close].to_string())
}

fn required_field(record: &str, field: &str, path: &Path) -> Result<String> {
    field_string(record, field).ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            format!("{}: core3InstrSeqAmendment records no `{field}` literal", path.display()),
        )
    })
}

/// The literal of a `def <name> : String := "..."`.
fn string_literal(src: &str, name: &str) -> Option<String> {
    let at = src.find(&format!("def {name} : String :="))?;
    let rest = &src[at..];
    let open = rest.find('"')?;
    let body = &rest[open + 1..];
    let close = body.find('"')?;
    Some(body[..close].to_string())
}

/// The digest `SHA256SUMS` lists for one relative path, in either coreutils
/// form.
fn manifest_digest_of(sums: &str, relative: &str) -> Option<String> {
    for line in sums.lines() {
        let line = line.trim_end();
        let (digest, rest) = line.split_once(' ')?;
        if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
            continue;
        }
        let Some(name) = rest.strip_prefix(' ').or_else(|| rest.strip_prefix('*')) else {
            continue;
        };
        if name.trim_start_matches("./") == relative {
            return Some(digest.to_string());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;

    /// A minimal tree with the shape `binding` reads, so the tests exercise the
    /// real checker rather than a reimplementation of it.
    fn plant(name: &str, source_body: &str, digest_literal: &str, repair: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!("wgg-amendment-{name}"));
        let _ = fs::remove_dir_all(&root);
        let spec_dir = root.join("vendor/wasm-spec/specification/wasm-3.0");
        fs::create_dir_all(&spec_dir).unwrap();
        fs::create_dir_all(root.join("WasmGemmGnaf/Wasm/Core/Validation")).unwrap();
        fs::create_dir_all(root.join("model")).unwrap();

        let rel = "specification/wasm-3.0/2.3-validation.instructions.spectec";
        fs::write(spec_dir.join("2.3-validation.instructions.spectec"), source_body).unwrap();
        let real = sha256::hex(source_body.as_bytes());
        fs::write(
            root.join("vendor/wasm-spec/SHA256SUMS"),
            format!("{real}  ./{rel}\n"),
        )
        .unwrap();
        fs::write(
            root.join("vendor/wasm-spec/PINNED-COMMIT"),
            "9d36019973201a19f9c9ebb0f10828b2fe2374aa\n",
        )
        .unwrap();
        fs::write(
            root.join("WasmGemmGnaf/Wasm/Core/Validation/InstructionsAmended.lean"),
            "inductive Instrs_ok' : Context -> List Instr -> InstrType -> Prop where\n",
        )
        .unwrap();
        fs::write(
            root.join("model/spec-deviations.json"),
            "{ \"deviations\": [\"DEV-006\"], \"amendments\": [\"AMD-005\"] }\n",
        )
        .unwrap();
        fs::write(
            root.join(REVISION_MODULE),
            format!(
                "def core3RevisionCommit : String :=\n  \
                 \"9d36019973201a19f9c9ebb0f10828b2fe2374aa\"\n\n\
                 def core3InstrSeqAmendmentSourceSha256 : String :=\n  \"{digest_literal}\"\n\n\
                 def core3InstrSeqRepairCommit : String :=\n  \"{repair}\"\n\n\
                 def core3InstrSeqAmendment : GrammarAmendmentBody :=\n  \
                 {{ deviationId := \"DEV-006\"\n    \
                 amendmentId := \"AMD-005\"\n    \
                 specSection := \"7.3\"\n    \
                 pinnedCommit := core3RevisionCommit\n    \
                 pinnedSource :=\n      \"vendor/wasm-spec/{rel}\"\n    \
                 pinnedSourceSha256 := core3InstrSeqAmendmentSourceSha256\n    \
                 judgment := \"Instrs_ok/seq\"\n    \
                 amendedRelation := \"WasmGemmGnaf.Wasm.Core.Instrs_ok'\"\n    \
                 upstreamIssue := 2194\n    \
                 upstreamPullRequest := 2197\n    \
                 upstreamRepairCommit := core3InstrSeqRepairCommit\n    \
                 pinAdvanced := false\n    \
                 noRegression := true\n    \
                 strictlyWider := true\n    \
                 arityPreserved := true }}\n"
            ),
        )
        .unwrap();
        root
    }

    const BODY: &str = "rule Instrs_ok/seq:\n  C |- instr_1 instr_2* : t_1* -> t_3*\n";

    #[test]
    fn a_faithful_record_passes() {
        let root = plant(
            "ok",
            BODY,
            &sha256::hex(BODY.as_bytes()),
            "bd4633aced30b720ff62b44cf00c03ece792f008",
        );
        let b = binding(&root).unwrap();
        assert!(b.is_ok(), "clean tree reported {:?}", b.findings);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_drifted_source_digest_is_a_finding() {
        let root = plant(
            "drift",
            BODY,
            "0000000000000000000000000000000000000000000000000000000000000000",
            "bd4633aced30b720ff62b44cf00c03ece792f008",
        );
        let b = binding(&root).unwrap();
        assert!(!b.is_ok(), "a drifted digest literal passed");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn advancing_the_pin_to_the_repair_is_a_finding() {
        let root = plant(
            "advanced",
            BODY,
            &sha256::hex(BODY.as_bytes()),
            "9d36019973201a19f9c9ebb0f10828b2fe2374aa",
        );
        let b = binding(&root).unwrap();
        assert!(!b.is_ok(), "recording the pin as the repair commit passed");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_judgment_the_source_does_not_define_is_a_finding() {
        let body = "rule Instrs_ok/empty:\n";
        let root = plant(
            "judgment",
            body,
            &sha256::hex(body.as_bytes()),
            "bd4633aced30b720ff62b44cf00c03ece792f008",
        );
        let b = binding(&root).unwrap();
        assert!(!b.is_ok(), "a judgment absent from the pinned source passed");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_coverage_marker_in_the_amended_module_is_a_finding() {
        let root = plant(
            "marker",
            BODY,
            &sha256::hex(BODY.as_bytes()),
            "bd4633aced30b720ff62b44cf00c03ece792f008",
        );
        fs::write(
            root.join("WasmGemmGnaf/Wasm/Core/Validation/InstructionsAmended.lean"),
            "-- core-rule: Instrs_ok/seq\ninductive Instrs_ok' : Context -> List Instr -> InstrType -> Prop where\n",
        )
        .unwrap();
        let b = binding(&root).unwrap();
        assert!(!b.is_ok(), "a coverage marker in the amended module passed");
        let _ = fs::remove_dir_all(&root);
    }
}
