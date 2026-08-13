//! Vendored-authority digests, recomputed from CONTENT. SPEC section 5.
//!
//! SPEC section 5 requires offline verification to recompute pins from the bytes
//! on disk rather than trust a checksum string. `authority/manifest.json` states
//! that the WebAssembly Core tree is vendored and names `SHA256SUMS` as its
//! digest manifest -- but a manifest that is only ever read, never recomputed,
//! attests to nothing. This reads every listed file and hashes it.
//!
//! The Python gate shelled out to `sha256sum -c`. Doing it here removes a
//! dependency on a coreutils build from the release-verification path, which
//! SPEC section 4 wants free of anything fetched or assumed.

use std::path::Path;

use crate::sha256;
use crate::spec::{Result, SpecError};

const CLAUSE: &str = "5";

/// Recheck every digest in `<dir>/SHA256SUMS` against the file's content.
///
/// `Ok` is the clean summary; `Err` lists the failures in the same shape
/// `sha256sum -c --quiet` reports them, so a red gate reads the same as before.
pub fn recompute(dir: &str) -> Result<std::result::Result<String, String>> {
    let sums = Path::new(dir).join("SHA256SUMS");
    let text = std::fs::read_to_string(&sums).map_err(|e| {
        SpecError::io(CLAUSE, "cannot read the vendored digest manifest", &sums, e)
    })?;

    let mut failures = Vec::new();
    let mut checked = 0usize;

    for line in text.lines() {
        let line = line.trim_end();
        if line.is_empty() {
            continue;
        }
        let Some((expected, name)) = split_entry(line) else {
            return Err(SpecError::new(
                CLAUSE,
                format!("{}: unparseable digest line `{line}`", sums.display()),
            ));
        };
        checked += 1;
        let path = Path::new(dir).join(name.trim_start_matches("./"));
        match std::fs::read(&path) {
            Ok(bytes) => {
                if sha256::hex(&bytes) != expected {
                    failures.push(format!("{name}: FAILED"));
                }
            }
            Err(_) => failures.push(format!("{name}: FAILED open or read")),
        }
    }

    if checked == 0 {
        return Err(SpecError::new(
            CLAUSE,
            format!("{}: lists no vendored file to recompute", sums.display()),
        ));
    }
    if failures.is_empty() {
        Ok(Ok(format!("{checked} vendored digests recomputed from content")))
    } else {
        Ok(Err(failures.join("\n")))
    }
}

/// `<hex>  <name>` or `<hex> *<name>`, as coreutils writes them.
fn split_entry(line: &str) -> Option<(&str, &str)> {
    split_entry_wide(line, 64)
}

/// One `<digest>  <name>` line, in either coreutils form, at an exact digest
/// width: 64 hex digits for a SHA-256 line of `SHA256SUMS`, 40 for a git blob
/// object id in `BLOBS`. The width is checked rather than inferred so a
/// truncated digest is a parse error instead of a silent short compare.
fn split_entry_wide(line: &str, width: usize) -> Option<(&str, &str)> {
    let (digest, rest) = line.split_once(' ')?;
    if digest.len() != width || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let name = rest.strip_prefix(' ').or_else(|| rest.strip_prefix('*'))?;
    (!name.is_empty()).then_some((digest, name))
}

// ---------------------------------------------------------------------------
// The Lean binding: `xtask vendor`
//
// SPEC section 5.1 draws the line this half of the file sits on. `xtask` CHECKS
// whether the kernel has discharged an obligation; it never DECIDES one. The
// Lean theorem `Wasm.profile_matches_pinned_revision` stands on the literals in
// `Wasm/Revision.lean` -- the pinned commit, the vendored file count and the
// digest of `vendor/wasm-spec/SHA256SUMS`. Lean cannot read the tree, so a
// literal that has drifted from the bytes on disk would still elaborate. This
// is what stops that: it recomputes the digest of digests from CONTENT and
// fails when the literal no longer describes the tree.
//
// It also checks the transcription record the other way round: every vendored
// anchor cited by `Wasm/Adequacy.lean`'s `vendorAnchor?` must be a label that
// the vendored reStructuredText actually DEFINES, so an invented rule
// identifier cannot sit in the conformance map unnoticed.
//
// What it deliberately does NOT claim, and prints so on every run: the vendored
// sources state most rule bodies as unexpanded SpecTec macro references, whose
// `.watsup` definitions are not in the vendored file set. A label check is a
// check on rule IDENTITY, not on rule CONTENT.
// ---------------------------------------------------------------------------

/// Where the Lean literals live, relative to the repository root.
const REVISION_MODULE: &str = "WasmGemmGnaf/Wasm/Revision.lean";
/// Where the vendored-anchor map lives, relative to the repository root.
const ADEQUACY_MODULE: &str = "WasmGemmGnaf/Wasm/Adequacy.lean";

/// What the vendored tree and the Lean literals say, side by side.
pub struct Binding {
    /// Files listed in `SHA256SUMS`, and rechecked against their content.
    pub files_listed: usize,
    /// Per-file digest mismatches, in `sha256sum -c` shape.
    pub content_failures: Vec<String>,
    /// SHA-256 of `SHA256SUMS`, recomputed from the bytes on disk.
    pub recomputed_manifest_digest: String,
    /// `core3VendorManifestSha256`, read out of `Wasm/Revision.lean`.
    pub lean_manifest_digest: String,
    /// Files listed in `BLOBS`, rechecked as git blob object ids.
    pub blobs_listed: usize,
    /// Vendored files whose bytes are not the pinned blob.
    pub blob_failures: Vec<String>,
    /// SHA-256 of `BLOBS`, recomputed from the bytes on disk.
    pub recomputed_blob_digest: String,
    /// `core3VendorBlobManifestSha256`, read out of `Wasm/Revision.lean`.
    pub lean_blob_digest: String,
    /// `core3VendoredTree.fileCount`, read out of `Wasm/Revision.lean`.
    pub lean_file_count: usize,
    /// `core3RevisionCommit`, read out of `Wasm/Revision.lean`.
    pub lean_commit: String,
    /// The contents of `vendor/wasm-spec/PINNED-COMMIT`.
    pub vendored_commit: String,
    /// reStructuredText labels the vendored tree defines.
    pub labels_defined: usize,
    /// Of those, the ones shaped like a rule label.
    pub rule_labels_defined: usize,
    /// Distinct anchors `vendorAnchor?` cites.
    pub anchors_cited: usize,
    /// Cited anchors that the vendored tree defines.
    pub anchors_found: usize,
    /// Cited anchors that it does not.
    pub anchors_missing: Vec<String>,
    /// Unexpanded SpecTec `${rule: ...}` / `$${rule: ...}` references found.
    pub spectec_macro_references: usize,
    /// Every reason this binding is not sound. Empty means it holds.
    pub findings: Vec<String>,
}

impl Binding {
    pub fn is_ok(&self) -> bool {
        self.findings.is_empty()
    }

    /// The lines `xtask vendor` prints. `list` adds the coverage arithmetic and
    /// the SpecTec disclosure.
    pub fn render(&self, list: bool) -> String {
        let mut out = vec![
            format!(
                "vendored tree: {} files rechecked from content ({} digest failures)",
                self.files_listed,
                self.content_failures.len()
            ),
            format!("  manifest digest recomputed: {}", self.recomputed_manifest_digest),
            format!("  Lean core3VendorManifestSha256: {}", self.lean_manifest_digest),
            format!(
                "  pinned blob ids recomputed: {} files ({} not the pinned blob)",
                self.blobs_listed,
                self.blob_failures.len()
            ),
            format!("  blob manifest digest recomputed: {}", self.recomputed_blob_digest),
            format!("  Lean core3VendorBlobManifestSha256: {}", self.lean_blob_digest),
            format!(
                "  Lean core3VendoredTree.fileCount: {} (manifest lists {})",
                self.lean_file_count, self.files_listed
            ),
            format!(
                "  pinned commit: {} (Lean core3RevisionCommit {})",
                self.vendored_commit, self.lean_commit
            ),
            format!(
                "  vendored anchors cited by Wasm/Adequacy.lean: {} of {} found",
                self.anchors_found, self.anchors_cited
            ),
        ];
        for anchor in &self.anchors_missing {
            out.push(format!("  UNDEFINED ANCHOR {anchor}"));
        }
        if list {
            out.push(format!(
                "  vendored labels defined: {} ({} rule-shaped)",
                self.labels_defined, self.rule_labels_defined
            ));
            out.push(format!(
                "  COVERAGE GAP: the enumeration cites {} distinct anchors of the {} \
                 rule-shaped labels the vendored tree defines; it is a declared SUBSET \
                 of the pinned rule set, not proved to be all of it",
                self.anchors_cited, self.rule_labels_defined
            ));
            out.push(format!(
                "  SCOPE LIMIT: {} unexpanded SpecTec rule references (`${{rule: ...}}`) \
                 remain in the vendored sources; their `.watsup` definitions are not \
                 vendored, so this checks rule IDENTITY, never rule CONTENT",
                self.spectec_macro_references
            ));
        }
        for finding in &self.findings {
            out.push(format!("  FAIL {finding}"));
        }
        out.join("\n")
    }
}

/// Compare the vendored tree under `vendor_dir` with the Lean literals in the
/// modules under `lean_root`.
///
/// Both are parameters so the mutation suite can point this at a COPY of the
/// vendored tree. A falsifier that reimplements the comparison would test its
/// own arithmetic; this one runs the real checker against a planted tree.
pub fn binding(vendor_dir: &Path, lean_root: &Path) -> Result<Binding> {
    let sums_path = vendor_dir.join("SHA256SUMS");
    let sums = std::fs::read(&sums_path).map_err(|e| {
        SpecError::io(CLAUSE, "cannot read the vendored digest manifest", &sums_path, e)
    })?;
    let sums_text = String::from_utf8_lossy(&sums).into_owned();

    let mut findings: Vec<String> = Vec::new();

    // 1. every listed file still hashes to its listed digest.
    let mut content_failures = Vec::new();
    let mut files_listed = 0usize;
    let mut listed_names: Vec<String> = Vec::new();
    for line in sums_text.lines() {
        let line = line.trim_end();
        if line.is_empty() {
            continue;
        }
        let Some((expected, name)) = split_entry(line) else {
            return Err(SpecError::new(
                CLAUSE,
                format!("{}: unparseable digest line `{line}`", sums_path.display()),
            ));
        };
        files_listed += 1;
        listed_names.push(name.trim_start_matches("./").to_string());
        let path = vendor_dir.join(name.trim_start_matches("./"));
        match std::fs::read(&path) {
            Ok(bytes) => {
                if sha256::hex(&bytes) != expected {
                    content_failures.push(format!("{name}: FAILED"));
                }
            }
            Err(_) => content_failures.push(format!("{name}: FAILED open or read")),
        }
    }

    // 1b. the manifest covers the WHOLE tree, not merely itself.
    //
    // This direction was missing and an adversarial review demonstrated the
    // consequence live: with the checker walking only the manifest's own lines,
    // 334 files were added to `vendor/wasm-spec/` and `xtask vendor` went on
    // reporting "40 files rechecked from content (0 digest failures)" and
    // PASSING. A file present in the tree but absent from the manifest changed
    // no digest anywhere, so the sentence in `Wasm/Revision.lean` claiming that
    // "changing any vendored byte changes SHA256SUMS" was false as written.
    //
    // Enumerating the directory and requiring the two sets to agree closes it in
    // both directions: an unlisted file is now a finding, and so is a listed
    // file that has been deleted.
    let mut present: Vec<String> = Vec::new();
    collect_relative(vendor_dir, vendor_dir, &mut present)?;
    present.retain(|p| p != "SHA256SUMS" && p != "BLOBS");
    present.sort();
    let mut unlisted: Vec<&String> =
        present.iter().filter(|p| !listed_names.iter().any(|l| l == *p)).collect();
    unlisted.sort();
    for path in &unlisted {
        findings.push(format!(
            "vendored file not covered by the digest manifest: {path} -- it can be changed \
             without changing any recorded digest"
        ));
    }
    let mut vanished: Vec<&String> =
        listed_names.iter().filter(|l| !present.iter().any(|p| p == *l)).collect();
    vanished.sort();
    for path in &vanished {
        findings.push(format!("digest manifest lists a file the tree does not have: {path}"));
    }
    if files_listed == 0 {
        return Err(SpecError::new(
            CLAUSE,
            format!("{}: lists no vendored file to recompute", sums_path.display()),
        ));
    }
    for failure in &content_failures {
        findings.push(format!("vendored file digest mismatch: {failure}"));
    }

    // 2. the digest of digests, recomputed from the manifest's own bytes.
    let recomputed_manifest_digest = sha256::hex(&sums);

    let revision_path = lean_root.join(REVISION_MODULE);
    let revision = crate::repo::read_lossy(CLAUSE, &revision_path)?;
    let lean_manifest_digest = string_literal(&revision, "core3VendorManifestSha256")
        .ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                format!(
                    "{}: no `def core3VendorManifestSha256 : String := \"...\"` to check the \
                     vendored tree against",
                    revision_path.display()
                ),
            )
        })?;
    let lean_commit = string_literal(&revision, "core3RevisionCommit").ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            format!("{}: no `def core3RevisionCommit` literal", revision_path.display()),
        )
    })?;
    let lean_file_count = field_nat(&revision, "fileCount").ok_or_else(|| {
        SpecError::new(
            CLAUSE,
            format!("{}: `core3VendoredTree` records no `fileCount`", revision_path.display()),
        )
    })?;

    if recomputed_manifest_digest != lean_manifest_digest {
        findings.push(format!(
            "the Lean literal `core3VendorManifestSha256` is {lean_manifest_digest}, but \
             {} hashes to {recomputed_manifest_digest}: the vendored tree and the theorem \
             have drifted apart",
            sums_path.display()
        ));
    }
    if files_listed != lean_file_count {
        findings.push(format!(
            "the Lean literal `core3VendoredTree.fileCount` is {lean_file_count}, but \
             {} lists {files_listed} files",
            sums_path.display()
        ));
    }

    // 2b. every vendored file is the GIT BLOB the pinned commit's tree names.
    //
    // `SHA256SUMS` is a file this repository wrote: recomputing it proves the
    // tree has not changed since we recorded it, NOT that the tree is the one
    // commit `core3RevisionCommit` names. `BLOBS` closes that gap, because a git
    // blob id is `sha1("blob " ++ len ++ "\0" ++ content)` -- a function of the
    // bytes alone -- and it is exactly the identity the pinned tree lists each
    // file under. Recomputing it needs no network and no `git`.
    let blobs_path = vendor_dir.join("BLOBS");
    let blobs = std::fs::read(&blobs_path).map_err(|e| {
        SpecError::io(CLAUSE, "cannot read the vendored blob manifest", &blobs_path, e)
    })?;
    let blobs_text = String::from_utf8_lossy(&blobs).into_owned();
    let mut blob_failures = Vec::new();
    let mut blobs_listed = 0usize;
    for line in blobs_text.lines() {
        let line = line.trim_end();
        if line.is_empty() {
            continue;
        }
        let Some((expected, name)) = split_entry_wide(line, 40) else {
            return Err(SpecError::new(
                CLAUSE,
                format!("{}: unparseable blob line `{line}`", blobs_path.display()),
            ));
        };
        blobs_listed += 1;
        let path = vendor_dir.join(name.trim_start_matches("./"));
        match std::fs::read(&path) {
            Ok(bytes) => {
                if crate::sha1::blob_hex(&bytes) != expected {
                    blob_failures.push(format!("{name}: FAILED"));
                }
            }
            Err(_) => blob_failures.push(format!("{name}: FAILED open or read")),
        }
    }
    if blobs_listed == 0 {
        return Err(SpecError::new(
            CLAUSE,
            format!("{}: lists no vendored blob to recompute", blobs_path.display()),
        ));
    }
    for failure in &blob_failures {
        findings.push(format!("vendored file is not the pinned blob: {failure}"));
    }

    let recomputed_blob_digest = sha256::hex(&blobs);
    let lean_blob_digest = string_literal(&revision, "core3VendorBlobManifestSha256")
        .ok_or_else(|| {
            SpecError::new(
                CLAUSE,
                format!(
                    "{}: no `def core3VendorBlobManifestSha256 : String := \"...\"`; without \
                     it nothing in Lean stands on the pinned blob identities",
                    revision_path.display()
                ),
            )
        })?;
    if recomputed_blob_digest != lean_blob_digest {
        findings.push(format!(
            "the Lean literal `core3VendorBlobManifestSha256` is {lean_blob_digest}, but \
             {} hashes to {recomputed_blob_digest}",
            blobs_path.display()
        ));
    }

    // 3. the vendored commit and the Lean commit are one commit.
    let commit_path = vendor_dir.join("PINNED-COMMIT");
    let vendored_commit = std::fs::read_to_string(&commit_path)
        .map(|t| t.trim().to_string())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the vendored commit", &commit_path, e))?;
    if vendored_commit != lean_commit {
        findings.push(format!(
            "{} says {vendored_commit}, the Lean literal `core3RevisionCommit` says \
             {lean_commit}",
            commit_path.display()
        ));
    }

    // 4. every anchor the conformance map cites is a label the tree DEFINES.
    let adequacy_path = lean_root.join(ADEQUACY_MODULE);
    let adequacy = crate::repo::read_lossy(CLAUSE, &adequacy_path)?;
    let mut anchors = vendor_anchors(&adequacy);
    anchors.sort();
    anchors.dedup();
    if anchors.is_empty() {
        return Err(SpecError::new(
            CLAUSE,
            format!(
                "{}: `def vendorAnchor?` cites no vendored anchor, so this check would \
                 pass for want of anything to check",
                adequacy_path.display()
            ),
        ));
    }

    let (labels, spectec_macro_references) = vendored_labels(&vendor_dir.join("document"))?;
    let rule_labels_defined = labels.iter().filter(|l| is_rule_label(l)).count();
    let mut anchors_missing: Vec<String> = anchors
        .iter()
        .filter(|a| !labels.iter().any(|l| l == *a))
        .cloned()
        .collect();
    anchors_missing.sort();
    for anchor in &anchors_missing {
        findings.push(format!(
            "`vendorAnchor?` cites `{anchor}`, which the vendored tree does not define as \
             a label"
        ));
    }

    Ok(Binding {
        files_listed,
        content_failures,
        recomputed_manifest_digest,
        lean_manifest_digest,
        blobs_listed,
        blob_failures,
        recomputed_blob_digest,
        lean_blob_digest,
        lean_file_count,
        lean_commit,
        vendored_commit,
        labels_defined: labels.len(),
        rule_labels_defined,
        anchors_cited: anchors.len(),
        anchors_found: anchors.len() - anchors_missing.len(),
        anchors_missing,
        spectec_macro_references,
        findings,
    })
}

pub fn run(list: bool) -> Result<crate::spec::Outcome> {
    let binding = binding(Path::new("vendor/wasm-spec"), Path::new("."))?;
    println!("{}", binding.render(list));
    Ok(if binding.is_ok() { crate::spec::Outcome::Pass } else { crate::spec::Outcome::Fail })
}

/// The string literal of `def <name> : String :=\n  "..."`.
///
/// Deliberately naive: it looks for the definition keyword and takes the next
/// double-quoted run. A Lean development that spelled the literal some other way
/// would fail to parse here rather than be silently skipped, which is the safe
/// direction -- `binding` turns `None` into an error, never into a pass.
fn string_literal(src: &str, name: &str) -> Option<String> {
    let at = src.find(&format!("def {name} : String :="))?;
    let rest = &src[at..];
    let open = rest.find('"')?;
    let body = &rest[open + 1..];
    let close = body.find('"')?;
    Some(body[..close].to_string())
}

/// The natural-number literal of a `<name> := <n>` structure field.
fn field_nat(src: &str, name: &str) -> Option<usize> {
    let at = src.find(&format!("{name} := "))?;
    let rest = &src[at + name.len() + " := ".len()..];
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// Every anchor cited by `def vendorAnchor?`, in source order.
///
/// The block is delimited by its own shape: the arms are the run of lines
/// beginning `  | .` that follows the definition keyword. Reading only that run
/// keeps an unrelated `=> some "..."` elsewhere in the module out of the result.
fn vendor_anchors(src: &str) -> Vec<String> {
    let Some(at) = src.find("def vendorAnchor? :") else {
        return Vec::new();
    };
    let mut anchors = Vec::new();
    for line in src[at..].lines().skip(1) {
        if !line.starts_with("  | .") {
            if line.trim().is_empty() {
                continue;
            }
            break;
        }
        if let Some(rest) = line.split_once("=> some \"") {
            if let Some(end) = rest.1.find('"') {
                anchors.push(rest.1[..end].to_string());
            }
        }
    }
    anchors
}

/// Every reStructuredText label the vendored sources DEFINE, and how many
/// unexpanded SpecTec rule references they still carry.
fn vendored_labels(dir: &Path) -> Result<(Vec<String>, usize)> {
    let mut labels = Vec::new();
    let mut macros = 0usize;
    let mut files = Vec::new();
    collect_files(dir, &mut files)?;
    files.sort();
    for path in files {
        let Ok(bytes) = std::fs::read(&path) else { continue };
        let text = String::from_utf8_lossy(&bytes);
        macros += text.matches("${rule:").count();
        for line in text.lines() {
            let Some(rest) = line.strip_prefix(".. _") else { continue };
            let Some(label) = rest.strip_suffix(':') else { continue };
            if !label.is_empty() && !label.contains(' ') {
                labels.push(label.to_string());
            }
        }
    }
    labels.sort();
    labels.dedup();
    Ok((labels, macros))
}

fn collect_files(dir: &Path, found: &mut Vec<std::path::PathBuf>) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the vendored directory", dir, e))?;
    for entry in entries {
        let entry =
            entry.map_err(|e| SpecError::io(CLAUSE, "cannot read an entry under", dir, e))?;
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, found)?;
        } else {
            found.push(path);
        }
    }
    Ok(())
}

/// Every file under `dir`, as a path relative to `base`, with `/` separators.
///
/// This is the half of the binding that was missing: without enumerating the
/// tree, a checker that walks only the digest manifest cannot see a file the
/// manifest does not mention.
fn collect_relative(base: &Path, dir: &Path, found: &mut Vec<String>) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the vendored directory", dir, e))?;
    for entry in entries {
        let entry =
            entry.map_err(|e| SpecError::io(CLAUSE, "cannot read an entry under", dir, e))?;
        let path = entry.path();
        if path.is_dir() {
            collect_relative(base, &path, found)?;
        } else if let Ok(rel) = path.strip_prefix(base) {
            let mut parts: Vec<String> = Vec::new();
            for component in rel.components() {
                parts.push(component.as_os_str().to_string_lossy().into_owned());
            }
            found.push(parts.join("/"));
        }
    }
    Ok(())
}

/// A label shaped like a normative rule: the five prefixes the pinned Core
/// sources use for binary, validation, execution, syntax and allocation rules.
fn is_rule_label(label: &str) -> bool {
    ["valid-", "binary-", "exec-", "syntax-", "alloc-"]
        .iter()
        .any(|p| label.starts_with(p))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_both_coreutils_forms() {
        let hex = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
        assert_eq!(split_entry(&format!("{hex}  ./LICENSE")), Some((hex, "./LICENSE")));
        assert_eq!(split_entry(&format!("{hex} *./LICENSE")), Some((hex, "./LICENSE")));
        assert_eq!(split_entry("short  ./LICENSE"), None);
        assert_eq!(split_entry(&format!("{hex}  ")), None);
    }

    #[test]
    fn reads_the_lean_literals() {
        let src = "def core3RevisionCommit : String :=\n  \"9d36\"\n\n\
                   def core3VendorManifestSha256 : String :=\n  \"a343\"\n\n\
                   def core3VendoredTree : VendoredTreeBody :=\n\
                   \x20 { root := \"vendor/wasm-spec/\"\n\
                   \x20   fileCount := 40\n\
                   \x20   manifestSha256 := core3VendorManifestSha256 }\n";
        assert_eq!(string_literal(src, "core3VendorManifestSha256").as_deref(), Some("a343"));
        assert_eq!(string_literal(src, "core3RevisionCommit").as_deref(), Some("9d36"));
        assert_eq!(field_nat(src, "fileCount"), Some(40));
        assert_eq!(string_literal(src, "absent"), None);
    }

    #[test]
    fn reads_only_the_anchor_block() {
        let src = "def vendorAnchor? : PinnedCoreRuleId → Option String\n\
                   \x20 | .decodeModule => some \"binary-module\"\n\
                   \x20 | .validNop => some \"valid-nop\"\n\
                   \x20 | .rejectAtomicRmw => none\n\
                   \n\
                   def elsewhere : Option String := some \"not-an-anchor\"\n";
        assert_eq!(vendor_anchors(src), vec!["binary-module", "valid-nop"]);
        assert!(vendor_anchors("no such definition").is_empty());
    }

    #[test]
    fn rule_shaped_labels_are_recognised() {
        assert!(is_rule_label("valid-nop"));
        assert!(is_rule_label("alloc-module"));
        assert!(!is_rule_label("index-instructions"));
    }

    /// A scratch tree that is removed on drop. Nothing here is ever written
    /// into the repository.
    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn new(tag: &str) -> Self {
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.subsec_nanos())
                .unwrap_or(0);
            let path = std::env::temp_dir()
                .join(format!("wgg-vendor-{tag}-{}-{nanos}", std::process::id()));
            std::fs::create_dir_all(&path).expect("scratch");
            Scratch(path)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// Build a minimal vendored tree and Lean root that the binding accepts,
    /// with `anchor` cited by the conformance map and `defined` defined by the
    /// vendored source.
    fn fixture(scratch: &Scratch, anchor: &str, defined: &str) -> (std::path::PathBuf, std::path::PathBuf) {
        let vendor_dir = scratch.0.join("vendor");
        let core = vendor_dir.join("document").join("core");
        std::fs::create_dir_all(&core).expect("core");
        std::fs::write(core.join("instructions.rst"), format!(".. _{defined}:\n\ntext\n"))
            .expect("rst");
        std::fs::write(vendor_dir.join("PINNED-COMMIT"), "deadbeef\n").expect("commit");
        std::fs::write(vendor_dir.join("LICENSE"), "licence\n").expect("licence");
        let listed = sha256::hex(b"licence\n");
        std::fs::write(vendor_dir.join("SHA256SUMS"), format!("{listed}  ./LICENSE\n"))
            .expect("sums");
        let sums_digest = sha256::hex(&std::fs::read(vendor_dir.join("SHA256SUMS")).expect("read"));

        let lean_root = scratch.0.join("lean");
        let wasm = lean_root.join("WasmGemmGnaf").join("Wasm");
        std::fs::create_dir_all(&wasm).expect("wasm");
        std::fs::write(
            wasm.join("Revision.lean"),
            format!(
                "def core3RevisionCommit : String :=\n  \"deadbeef\"\n\n\
                 def core3VendorManifestSha256 : String :=\n  \"{sums_digest}\"\n\n\
                 def core3VendoredTree : VendoredTreeBody :=\n\
                 \x20 {{ fileCount := 1 }}\n"
            ),
        )
        .expect("revision");
        std::fs::write(
            wasm.join("Adequacy.lean"),
            format!(
                "def vendorAnchor? : PinnedCoreRuleId → Option String\n\
                 \x20 | .one => some \"{anchor}\"\n"
            ),
        )
        .expect("adequacy");
        (vendor_dir, lean_root)
    }

    #[test]
    fn a_matching_tree_binds() {
        let scratch = Scratch::new("ok");
        let (vendor_dir, lean_root) = fixture(&scratch, "valid-nop", "valid-nop");
        let report = binding(&vendor_dir, &lean_root).expect("binds");
        assert!(report.is_ok(), "{:?}", report.findings);
        assert_eq!(report.anchors_cited, 1);
        assert_eq!(report.anchors_found, 1);
    }

    #[test]
    fn an_anchor_the_tree_does_not_define_is_rejected() {
        // The gap-3 half: an invented rule identifier in the conformance map
        // must not pass merely because it is well spelled.
        let scratch = Scratch::new("anchor");
        let (vendor_dir, lean_root) = fixture(&scratch, "valid-invented", "valid-nop");
        let report = binding(&vendor_dir, &lean_root).expect("binds");
        assert!(!report.is_ok());
        assert_eq!(report.anchors_found, 0);
        assert_eq!(report.anchors_missing, vec!["valid-invented".to_string()]);
        assert!(report.findings.iter().any(|f| f.contains("does not define as a label")));
    }

    #[test]
    fn a_drifted_lean_digest_is_rejected() {
        // The half no per-file check can catch: `SHA256SUMS` still describes
        // every file it lists, but is no longer the manifest Lean recorded.
        let scratch = Scratch::new("drift");
        let (vendor_dir, lean_root) = fixture(&scratch, "valid-nop", "valid-nop");
        let sums = vendor_dir.join("SHA256SUMS");
        let text = std::fs::read_to_string(&sums).expect("read");
        std::fs::write(&sums, format!("{text}\n")).expect("append");

        let report = binding(&vendor_dir, &lean_root).expect("binds");
        assert!(report.content_failures.is_empty(), "every listed file still checks out");
        assert!(report.findings.iter().any(|f| f.contains("have drifted apart")));
    }

    #[test]
    fn a_disagreeing_commit_is_rejected() {
        let scratch = Scratch::new("commit");
        let (vendor_dir, lean_root) = fixture(&scratch, "valid-nop", "valid-nop");
        std::fs::write(vendor_dir.join("PINNED-COMMIT"), "0000000\n").expect("commit");
        let report = binding(&vendor_dir, &lean_root).expect("binds");
        assert!(report.findings.iter().any(|f| f.contains("core3RevisionCommit")));
    }
}
