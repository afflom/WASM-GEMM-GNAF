//! `xtask amendment` -- bind the complete release-semantics amendment set to
//! the byte-identical pinned Core 3.0 authority tree.
//!
//! Lean gives `Wasm.core3AuthorityAmendmentSet` a canonical identity and binds
//! that identity into the profile semantics. Lean cannot read repository files,
//! so this checker parses the first-order records, checks every textual patch
//! against the vendored bytes and manifest, checks the tree and registry
//! bindings, and locates every coverage-neutral amended Lean declaration.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use crate::json::Value;
use crate::sha256;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "7.3";
const AUTHORITY_MODULE: &str = "WasmGemmGnaf/Wasm/AuthorityAmendments.lean";
const REVISION_MODULE: &str = "WasmGemmGnaf/Wasm/Revision.lean";
const LEAN_ROOT: &str = "WasmGemmGnaf";
const VENDOR_ROOT: &str = "vendor/wasm-spec/";
const AUTHORITY_SOURCE_ROOT: &str = "vendor/wasm-spec/specification/wasm-3.0/";
const DEVIATIONS: &str = "model/spec-deviations.json";
const EXPECTED_AMENDMENTS: [&str; 8] = [
    "AMD-005", "AMD-007", "AMD-008", "AMD-009", "AMD-010", "AMD-011", "AMD-012", "AMD-013",
];
const EXPECTED_DEVIATIONS: [&str; 8] = [
    "DEV-006", "DEV-007", "DEV-008", "DEV-009", "DEV-010", "DEV-011", "DEV-012", "DEV-013",
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct PatchRecord {
    source_path: String,
    source_sha256: String,
    before_anchor: String,
    after_anchor: String,
    removed_text: String,
    inserted_text: String,
    effect: String,
    affected_symbols: Vec<String>,
    amended_declarations: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AmendmentRecord {
    lean_name: String,
    deviation_id: String,
    amendment_id: String,
    spec_section: String,
    pinned_commit: String,
    patches: Vec<PatchRecord>,
    upstream_references: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatchBinding {
    pub amendment_id: String,
    pub source_path: String,
    pub recorded_digest: String,
    pub recomputed_digest: String,
    pub manifest_digest: String,
}

/// The source-visible facts checked for the canonical amendment set.
pub struct Binding {
    pub amendment_ids: Vec<String>,
    pub deviation_ids: Vec<String>,
    pub patches: Vec<PatchBinding>,
    pub lean_commit: String,
    pub vendored_commit: String,
    pub amended_declarations: usize,
    pub markers_in_amended_modules: usize,
    pub findings: Vec<String>,
}

impl Binding {
    pub fn is_ok(&self) -> bool {
        self.findings.is_empty()
    }

    pub fn render(&self) -> String {
        let mut out = vec![
            format!(
                "authority amendment set: {} amendment(s), {} exact patch operation(s)",
                self.amendment_ids.len(),
                self.patches.len()
            ),
            format!("  amendments: {}", self.amendment_ids.join(", ")),
            format!("  deviations: {}", self.deviation_ids.join(", ")),
            format!(
                "  pinned commit: {} (Lean core3RevisionCommit {})",
                self.vendored_commit, self.lean_commit
            ),
            format!(
                "  amended declarations found: {}",
                self.amended_declarations
            ),
            format!(
                "  coverage markers in their source modules: {} (SPEC 7.3 requires 0)",
                self.markers_in_amended_modules
            ),
        ];
        for patch in &self.patches {
            out.push(format!(
                "  {} {} [{}]",
                patch.amendment_id, patch.source_path, patch.recorded_digest
            ));
        }
        for finding in &self.findings {
            out.push(format!("  FAIL {finding}"));
        }
        out.join("\n")
    }
}

pub fn run() -> Result<Outcome> {
    let binding = binding(Path::new("."))?;
    println!("{}", binding.render());
    Ok(if binding.is_ok() {
        Outcome::Pass
    } else {
        Outcome::Fail
    })
}

/// Compare `Wasm.core3AuthorityAmendmentSet` with the vendored tree and the
/// repository sources under `root`. The root parameter lets tests plant faults
/// in a disposable copy.
pub fn binding(root: &Path) -> Result<Binding> {
    let authority_path = root.join(AUTHORITY_MODULE);
    let authority = crate::repo::read_lossy(CLAUSE, &authority_path)?;
    let tokens = lex(&authority).map_err(|message| {
        SpecError::new(CLAUSE, format!("{}: {message}", authority_path.display()))
    })?;

    let source_prefix = parse_authority_source_prefix(&tokens, &authority_path)?;
    let amendment_names =
        parse_identifier_list_def(&tokens, "core3AuthorityAmendments", &authority_path)?;
    let (tree_expr, set_amendments) = parse_amendment_set(&tokens, &authority_path)?;

    let revision_path = root.join(REVISION_MODULE);
    let revision = crate::repo::read_lossy(CLAUSE, &revision_path)?;
    let revision_tokens = lex(&revision).map_err(|message| {
        SpecError::new(CLAUSE, format!("{}: {message}", revision_path.display()))
    })?;
    let lean_commit = parse_string_def(&revision_tokens, "core3RevisionCommit", &revision_path)?;

    let pinned_commit_path = root.join(VENDOR_ROOT).join("PINNED-COMMIT");
    let vendored_commit = crate::repo::read_lossy(CLAUSE, &pinned_commit_path)?
        .trim()
        .to_string();
    let sums_path = root.join(VENDOR_ROOT).join("SHA256SUMS");
    let sums = crate::repo::read_lossy(CLAUSE, &sums_path)?;

    let mut findings = Vec::new();
    if source_prefix != AUTHORITY_SOURCE_ROOT {
        findings.push(format!(
            "authoritySource expands to `{source_prefix}`, not `{AUTHORITY_SOURCE_ROOT}`"
        ));
    }
    if tree_expr != ["VendoredTreeBody.identity", "core3VendoredTree"] {
        findings.push(format!(
            "core3AuthorityAmendmentSet.vendoredTreeId is `{}`, not \
             `VendoredTreeBody.identity core3VendoredTree`",
            tree_expr.join(" ")
        ));
    }
    if set_amendments != "core3AuthorityAmendments" {
        findings.push(format!(
            "core3AuthorityAmendmentSet.amendments names `{set_amendments}`, not \
             `core3AuthorityAmendments`"
        ));
    }
    if lean_commit != vendored_commit {
        findings.push(format!(
            "PINNED-COMMIT is {vendored_commit}, but core3RevisionCommit is {lean_commit}"
        ));
    }

    let mut records = Vec::new();
    for name in &amendment_names {
        records.push(parse_amendment_def(
            &tokens,
            name,
            &source_prefix,
            &authority_path,
        )?);
    }

    let amendment_ids: Vec<String> = records.iter().map(|a| a.amendment_id.clone()).collect();
    let deviation_ids: Vec<String> = records.iter().map(|a| a.deviation_id.clone()).collect();
    if amendment_ids != EXPECTED_AMENDMENTS {
        findings.push(format!(
            "canonical amendment order is [{}], expected [{}]",
            amendment_ids.join(", "),
            EXPECTED_AMENDMENTS.join(", ")
        ));
    }
    if deviation_ids != EXPECTED_DEVIATIONS {
        findings.push(format!(
            "canonical deviation order is [{}], expected [{}]",
            deviation_ids.join(", "),
            EXPECTED_DEVIATIONS.join(", ")
        ));
    }
    if !all_distinct(amendment_names.iter().map(String::as_str)) {
        findings.push("core3AuthorityAmendments contains a duplicate declaration name".into());
    }
    if !all_distinct(amendment_ids.iter().map(String::as_str)) {
        findings.push("core3AuthorityAmendments contains a duplicate amendmentId".into());
    }
    if !all_distinct(deviation_ids.iter().map(String::as_str)) {
        findings.push("core3AuthorityAmendments contains a duplicate deviationId".into());
    }

    let registry_path = root.join(DEVIATIONS);
    let registry_text = crate::repo::read_lossy(CLAUSE, &registry_path)?;
    let registry = crate::json::parse(CLAUSE, &registry_text)?;
    check_registry(&registry, &records, &registry_path, &mut findings);

    let declarations = declared_names(root)?;
    let mut declaration_files = BTreeSet::new();
    let mut amended_declarations = BTreeSet::new();
    let mut patch_bindings = Vec::new();

    for amendment in &records {
        if amendment.pinned_commit != "core3RevisionCommit" {
            findings.push(format!(
                "{}.pinnedCommit is `{}`, not `core3RevisionCommit`",
                amendment.lean_name, amendment.pinned_commit
            ));
        }
        if amendment.spec_section != "4 and 7.3" {
            findings.push(format!(
                "{} records specSection `{}`, expected `4 and 7.3`",
                amendment.amendment_id, amendment.spec_section
            ));
        }
        if amendment.patches.is_empty() {
            findings.push(format!(
                "{} records no patch operation",
                amendment.amendment_id
            ));
        }
        if amendment.upstream_references.is_empty() {
            findings.push(format!(
                "{} records no upstream reference",
                amendment.amendment_id
            ));
        }

        for (patch_index, patch) in amendment.patches.iter().enumerate() {
            let label = format!("{} patch {}", amendment.amendment_id, patch_index + 1);
            let source_path = root.join(&patch.source_path);
            let source_bytes = match std::fs::read(&source_path) {
                Ok(bytes) => bytes,
                Err(_) => {
                    findings.push(format!(
                        "{label} source `{}` cannot be read",
                        patch.source_path
                    ));
                    Vec::new()
                }
            };
            let recomputed_digest = if source_bytes.is_empty() {
                String::new()
            } else {
                sha256::hex(&source_bytes)
            };
            let relative = patch
                .source_path
                .strip_prefix(VENDOR_ROOT)
                .unwrap_or(&patch.source_path);
            let manifest_digest = manifest_digest_of(&sums, relative).unwrap_or_default();

            if !patch.source_path.starts_with(AUTHORITY_SOURCE_ROOT) {
                findings.push(format!(
                    "{label} source `{}` is outside `{AUTHORITY_SOURCE_ROOT}`",
                    patch.source_path
                ));
            }
            if !is_sha256(&patch.source_sha256) {
                findings.push(format!(
                    "{label} sourceSha256 `{}` is not lowercase SHA-256",
                    patch.source_sha256
                ));
            }
            if !recomputed_digest.is_empty() && recomputed_digest != patch.source_sha256 {
                findings.push(format!(
                    "{label} records digest {} but `{}` hashes to {}",
                    patch.source_sha256, patch.source_path, recomputed_digest
                ));
            }
            if manifest_digest.is_empty() {
                findings.push(format!(
                    "SHA256SUMS lists no digest for `{relative}` ({label})"
                ));
            } else if manifest_digest != patch.source_sha256 {
                findings.push(format!(
                    "{label} records digest {} but SHA256SUMS lists {}",
                    patch.source_sha256, manifest_digest
                ));
            }

            if let Ok(source_text) = std::str::from_utf8(&source_bytes) {
                check_patch_text(patch, source_text, &label, &mut findings);
            } else if !source_bytes.is_empty() {
                findings.push(format!("{label} source is not UTF-8 SpecTec text"));
            }

            if patch.affected_symbols.is_empty() {
                findings.push(format!("{label} names no affected authority symbol"));
            }
            if patch.amended_declarations.is_empty() {
                findings.push(format!("{label} names no amended Lean declaration"));
            }
            for declaration in &patch.amended_declarations {
                amended_declarations.insert(declaration.clone());
                match declarations.get(declaration) {
                    None => findings.push(format!(
                        "{label} names `{declaration}`, but no such Lean declaration exists"
                    )),
                    Some(paths) if paths.len() != 1 => findings.push(format!(
                        "{label} names `{declaration}`, but it is declared in {} source files",
                        paths.len()
                    )),
                    Some(paths) => {
                        declaration_files.insert(paths[0].clone());
                    }
                }
            }

            patch_bindings.push(PatchBinding {
                amendment_id: amendment.amendment_id.clone(),
                source_path: patch.source_path.clone(),
                recorded_digest: patch.source_sha256.clone(),
                recomputed_digest,
                manifest_digest,
            });
        }
    }

    let mut markers_in_amended_modules = 0usize;
    for path in declaration_files {
        let text = crate::repo::read_lossy(CLAUSE, &path)?;
        let count = coverage_markers(&text);
        markers_in_amended_modules += count;
        if count != 0 {
            findings.push(format!(
                "{} carries {count} Core coverage marker(s); amendment declarations are \
                 coverage-neutral",
                path.display()
            ));
        }
    }

    Ok(Binding {
        amendment_ids,
        deviation_ids,
        patches: patch_bindings,
        lean_commit,
        vendored_commit,
        amended_declarations: amended_declarations.len(),
        markers_in_amended_modules,
        findings,
    })
}

fn check_patch_text(patch: &PatchRecord, source: &str, label: &str, findings: &mut Vec<String>) {
    if patch.before_anchor.is_empty() {
        findings.push(format!("{label} has an empty beforeAnchor"));
        return;
    }
    // SpecTec records are stored without layout indentation.  Compare the
    // exact line text after removing only leading/trailing horizontal layout;
    // do not collapse internal whitespace or tokens.
    let source = normalize_spectec(source);
    let before_anchor = normalize_spectec(&patch.before_anchor);
    let after_anchor = normalize_spectec(&patch.after_anchor);
    let removed_text = normalize_spectec(&patch.removed_text);
    let inserted_text = normalize_spectec(&patch.inserted_text);
    let candidates: Vec<(usize, usize)> = occurrences(&source, &before_anchor)
        .into_iter()
        .filter_map(|before| {
            let start = before + before_anchor.len();
            if after_anchor.is_empty() {
                Some((before, source.len()))
            } else {
                occurrences(&source[start..], &after_anchor)
                    .first()
                    .map(|after| (before, start + after))
            }
        })
        .collect();
    if candidates.len() != 1 {
        findings.push(format!(
            "{label} anchors select {} region(s), not exactly one",
            candidates.len()
        ));
        return;
    }
    let region_start = candidates[0].0 + before_anchor.len();
    let region_end = candidates[0].1;
    let region = &source[region_start..region_end];

    match patch.effect.as_str() {
        "add" => {
            // Adding a field sometimes replaces the old closing punctuation,
            // so `.add` may legitimately carry a nonempty removedText.
            if inserted_text.is_empty() {
                findings.push(format!("{label} is `.add` but insertedText is empty"));
            }
        }
        "replace" | "narrow" | "widen" => {
            if removed_text.is_empty() || inserted_text.is_empty() {
                findings.push(format!(
                    "{label} is `.{}` but does not record both removedText and insertedText",
                    patch.effect
                ));
            }
            if removed_text == inserted_text {
                findings.push(format!("{label} records a no-op textual replacement"));
            }
        }
        other => findings.push(format!("{label} records unknown effect `.{other}`")),
    }

    if !removed_text.is_empty() {
        let removed = occurrences(region, &removed_text);
        // A single authority operation may touch several productions while
        // leaving their `rule ...:` headers unchanged (AMD-011).  In that
        // case the recorded exact changed lines form an ordered subsequence,
        // not one contiguous byte block.
        if removed.len() != 1 && !ordered_line_subsequence(region, &removed_text) {
            findings.push(format!(
                "{label} removedText occurs {} time(s) and its exact lines are not an ordered \
                 subsequence between the anchors",
                removed.len()
            ));
        }
    }
    if !inserted_text.is_empty() && !occurrences(region, &inserted_text).is_empty() {
        findings.push(format!(
            "{label} insertedText is already present between the pinned anchors"
        ));
    }
}

fn ordered_line_subsequence(haystack: &str, needle: &str) -> bool {
    let lines: Vec<&str> = haystack.lines().collect();
    let mut cursor = 0usize;
    for wanted in needle.lines() {
        let Some(offset) = lines[cursor..].iter().position(|line| *line == wanted) else {
            return false;
        };
        cursor += offset + 1;
    }
    true
}

fn normalize_spectec(text: &str) -> String {
    text.lines()
        .map(|line| line.trim_matches([' ', '\t', '\r']))
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn check_registry(
    registry: &Value,
    records: &[AmendmentRecord],
    path: &Path,
    findings: &mut Vec<String>,
) {
    let Some(deviations) = registry.get("deviations").and_then(Value::as_array) else {
        findings.push(format!("{} has no `deviations` array", path.display()));
        return;
    };
    let Some(amendments) = registry.get("amendments").and_then(Value::as_array) else {
        findings.push(format!("{} has no `amendments` array", path.display()));
        return;
    };

    for record in records {
        let ds: Vec<&Value> = deviations
            .iter()
            .filter(|v| v.get("id").and_then(Value::as_str) == Some(&record.deviation_id))
            .collect();
        if ds.len() != 1 {
            findings.push(format!(
                "{} records {} deviation row(s) for {} (expected one)",
                path.display(),
                ds.len(),
                record.deviation_id
            ));
        } else if ds[0].get("adoptedIntoSpec").and_then(Value::as_str) != Some(&record.amendment_id)
        {
            findings.push(format!(
                "{} does not bind {}.adoptedIntoSpec to {}",
                path.display(),
                record.deviation_id,
                record.amendment_id
            ));
        }

        let as_: Vec<&Value> = amendments
            .iter()
            .filter(|v| v.get("id").and_then(Value::as_str) == Some(&record.amendment_id))
            .collect();
        if as_.len() != 1 {
            findings.push(format!(
                "{} records {} amendment row(s) for {} (expected one)",
                path.display(),
                as_.len(),
                record.amendment_id
            ));
        } else if as_[0].get("deviation").and_then(Value::as_str) != Some(&record.deviation_id) {
            findings.push(format!(
                "{} does not bind {}.deviation to {}",
                path.display(),
                record.amendment_id,
                record.deviation_id
            ));
        }
    }
}

fn coverage_markers(text: &str) -> usize {
    text.lines()
        .filter(|line| {
            let t = line.trim_start();
            t.starts_with("-- core-syntax:")
                || t.starts_with("-- core-rule:")
                || t.starts_with("-- core-opcode:")
                || t.starts_with("-- core-exec:")
                || t.starts_with("-- core-aux:")
        })
        .count()
}

fn occurrences(haystack: &str, needle: &str) -> Vec<usize> {
    if needle.is_empty() {
        return Vec::new();
    }
    haystack.match_indices(needle).map(|(i, _)| i).collect()
}

fn is_sha256(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn all_distinct<'a>(mut items: impl Iterator<Item = &'a str>) -> bool {
    let mut seen = BTreeSet::new();
    items.all(|item| seen.insert(item))
}

fn manifest_digest_of(sums: &str, relative: &str) -> Option<String> {
    for line in sums.lines() {
        let line = line.trim_end();
        let Some((digest, rest)) = line.split_once(' ') else {
            continue;
        };
        if !is_sha256(digest) {
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

// -------------------------------------------------------------------------
// Lean declaration discovery

fn declared_names(root: &Path) -> Result<BTreeMap<String, Vec<PathBuf>>> {
    let mut names: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
    for path in crate::repo::lean_files(CLAUSE, &root.join(LEAN_ROOT))? {
        let source = crate::repo::read_lossy(CLAUSE, &path)?;
        let stripped = crate::lean::strip(&source);
        let mut namespaces: Vec<String> = Vec::new();
        for line in stripped.lines() {
            let line = line.trim();
            if let Some(rest) = line.strip_prefix("namespace ") {
                if let Some(name) = first_lean_name(rest) {
                    namespaces.push(name.to_string());
                }
                continue;
            }
            if let Some(rest) = line.strip_prefix("end ") {
                if let Some(name) = first_lean_name(rest) {
                    if namespaces
                        .last()
                        .is_some_and(|open| open == name || open.rsplit('.').next() == Some(name))
                    {
                        namespaces.pop();
                    }
                }
                continue;
            }
            let Some(local) = declaration_name(line) else {
                continue;
            };
            let mut parts = namespaces.clone();
            parts.push(local.to_string());
            names.entry(parts.join(".")).or_default().push(path.clone());
        }
    }
    Ok(names)
}

fn declaration_name(line: &str) -> Option<&str> {
    let mut line = line.trim_start();
    for modifier in ["private", "protected", "noncomputable", "unsafe", "partial"] {
        if let Some(rest) = line.strip_prefix(modifier) {
            if rest.starts_with(char::is_whitespace) {
                line = rest.trim_start();
                break;
            }
        }
    }
    for kind in [
        "def",
        "abbrev",
        "opaque",
        "theorem",
        "lemma",
        "structure",
        "inductive",
        "class",
    ] {
        let Some(rest) = line.strip_prefix(kind) else {
            continue;
        };
        if rest.starts_with(char::is_whitespace) {
            return first_lean_name(rest.trim_start());
        }
    }
    None
}

fn first_lean_name(s: &str) -> Option<&str> {
    let end = s
        .find(|c: char| {
            !(c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '\'' || c == '$')
        })
        .unwrap_or(s.len());
    (end != 0).then(|| &s[..end])
}

// -------------------------------------------------------------------------
// Small parser for the first-order Lean data literals in AuthorityAmendments

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Ident(String),
    String(String),
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Assign,
}

fn lex(source: &str) -> std::result::Result<Vec<Token>, String> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0usize;
    let mut block_depth = 0usize;
    while i < chars.len() {
        if block_depth != 0 {
            if i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '-' {
                block_depth += 1;
                i += 2;
            } else if i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '/' {
                block_depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        if i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '-' {
            block_depth = 1;
            i += 2;
            continue;
        }
        if i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '-' {
            i += 2;
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }
        match chars[i] {
            '{' => {
                tokens.push(Token::LBrace);
                i += 1;
            }
            '}' => {
                tokens.push(Token::RBrace);
                i += 1;
            }
            '[' => {
                tokens.push(Token::LBracket);
                i += 1;
            }
            ']' => {
                tokens.push(Token::RBracket);
                i += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                i += 1;
            }
            ':' if i + 1 < chars.len() && chars[i + 1] == '=' => {
                tokens.push(Token::Assign);
                i += 2;
            }
            '"' => {
                i += 1;
                let mut value = String::new();
                let mut closed = false;
                while i < chars.len() {
                    match chars[i] {
                        '"' => {
                            i += 1;
                            closed = true;
                            break;
                        }
                        '\\' => {
                            i += 1;
                            if i >= chars.len() {
                                return Err("unterminated escape in string literal".into());
                            }
                            match chars[i] {
                                'n' => value.push('\n'),
                                'r' => value.push('\r'),
                                't' => value.push('\t'),
                                '\\' => value.push('\\'),
                                '"' => value.push('"'),
                                c => return Err(format!("unsupported Lean string escape `\\{c}`")),
                            }
                            i += 1;
                        }
                        c => {
                            value.push(c);
                            i += 1;
                        }
                    }
                }
                if !closed {
                    return Err("unterminated string literal".into());
                }
                tokens.push(Token::String(value));
            }
            _ => {
                let start = i;
                while i < chars.len()
                    && !chars[i].is_whitespace()
                    && !matches!(chars[i], '{' | '}' | '[' | ']' | ',' | '"')
                    && !(chars[i] == ':' && i + 1 < chars.len() && chars[i + 1] == '=')
                    && !(chars[i] == '/' && i + 1 < chars.len() && chars[i + 1] == '-')
                    && !(chars[i] == '-' && i + 1 < chars.len() && chars[i + 1] == '-')
                {
                    i += 1;
                }
                if start == i {
                    return Err(format!("cannot tokenize character `{}`", chars[i]));
                }
                tokens.push(Token::Ident(chars[start..i].iter().collect()));
            }
        }
    }
    if block_depth != 0 {
        return Err("unterminated block comment".into());
    }
    Ok(tokens)
}

struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    context: String,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token], pos: usize, context: impl Into<String>) -> Self {
        Self {
            tokens,
            pos,
            context: context.into(),
        }
    }

    fn error(&self, message: impl Into<String>) -> SpecError {
        SpecError::new(CLAUSE, format!("{}: {}", self.context, message.into()))
    }

    fn token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn bump(&mut self) -> Option<&Token> {
        let token = self.tokens.get(self.pos);
        if token.is_some() {
            self.pos += 1;
        }
        token
    }

    fn expect(&mut self, want: &Token) -> Result<()> {
        if self.token() == Some(want) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.error(format!("expected {want:?}, found {:?}", self.token())))
        }
    }

    fn ident(&mut self) -> Result<String> {
        let token = self.bump().cloned();
        match token {
            Some(Token::Ident(s)) => Ok(s),
            other => Err(self.error(format!("expected identifier, found {other:?}"))),
        }
    }

    fn string(&mut self) -> Result<String> {
        let token = self.bump().cloned();
        match token {
            Some(Token::String(s)) => Ok(s),
            other => Err(self.error(format!("expected string literal, found {other:?}"))),
        }
    }

    fn string_list(&mut self) -> Result<Vec<String>> {
        self.expect(&Token::LBracket)?;
        let mut out = Vec::new();
        while self.token() != Some(&Token::RBracket) {
            out.push(self.string()?);
            if self.token() == Some(&Token::Comma) {
                self.pos += 1;
            } else if self.token() != Some(&Token::RBracket) {
                return Err(self.error("expected comma or closing bracket in string list"));
            }
        }
        self.expect(&Token::RBracket)?;
        Ok(out)
    }
}

fn def_rhs(tokens: &[Token], name: &str, path: &Path) -> Result<usize> {
    let mut hits = Vec::new();
    let mut i = 0usize;
    while i + 1 < tokens.len() {
        if tokens[i] == Token::Ident("def".into()) && tokens[i + 1] == Token::Ident(name.into()) {
            let mut j = i + 2;
            while j < tokens.len() && tokens[j] != Token::Assign {
                if tokens[j] == Token::Ident("def".into()) {
                    break;
                }
                j += 1;
            }
            if j < tokens.len() && tokens[j] == Token::Assign {
                hits.push(j + 1);
            }
        }
        i += 1;
    }
    match hits.as_slice() {
        [rhs] => Ok(*rhs),
        [] => Err(SpecError::new(
            CLAUSE,
            format!("{}: no `def {name}` literal", path.display()),
        )),
        _ => Err(SpecError::new(
            CLAUSE,
            format!("{}: `def {name}` occurs more than once", path.display()),
        )),
    }
}

fn parse_string_def(tokens: &[Token], name: &str, path: &Path) -> Result<String> {
    let rhs = def_rhs(tokens, name, path)?;
    Parser::new(tokens, rhs, format!("{}: def {name}", path.display())).string()
}

fn parse_authority_source_prefix(tokens: &[Token], path: &Path) -> Result<String> {
    let rhs = def_rhs(tokens, "authoritySource", path)?;
    let mut p = Parser::new(tokens, rhs, format!("{}: authoritySource", path.display()));
    let prefix = p.string()?;
    if p.ident()? != "++" || p.ident()? != "leaf" {
        return Err(p.error("expected the exact expression `\"...\" ++ leaf`"));
    }
    Ok(prefix)
}

fn parse_identifier_list_def(tokens: &[Token], name: &str, path: &Path) -> Result<Vec<String>> {
    let rhs = def_rhs(tokens, name, path)?;
    let mut p = Parser::new(tokens, rhs, format!("{}: def {name}", path.display()));
    p.expect(&Token::LBracket)?;
    let mut out = Vec::new();
    while p.token() != Some(&Token::RBracket) {
        out.push(p.ident()?);
        if p.token() == Some(&Token::Comma) {
            p.pos += 1;
        } else if p.token() != Some(&Token::RBracket) {
            return Err(p.error("expected comma or closing bracket in amendment list"));
        }
    }
    p.expect(&Token::RBracket)?;
    Ok(out)
}

fn parse_amendment_set(tokens: &[Token], path: &Path) -> Result<(Vec<String>, String)> {
    let rhs = def_rhs(tokens, "core3AuthorityAmendmentSet", path)?;
    let mut p = Parser::new(
        tokens,
        rhs,
        format!("{}: core3AuthorityAmendmentSet", path.display()),
    );
    p.expect(&Token::LBrace)?;
    let mut tree = None;
    let mut amendments = None;
    while p.token() != Some(&Token::RBrace) {
        let field = p.ident()?;
        p.expect(&Token::Assign)?;
        match field.as_str() {
            "vendoredTreeId" => tree = Some(vec![p.ident()?, p.ident()?]),
            "amendments" => amendments = Some(p.ident()?),
            _ => return Err(p.error(format!("unknown amendment-set field `{field}`"))),
        }
    }
    p.expect(&Token::RBrace)?;
    Ok((
        tree.ok_or_else(|| p.error("missing vendoredTreeId"))?,
        amendments.ok_or_else(|| p.error("missing amendments"))?,
    ))
}

fn parse_amendment_def(
    tokens: &[Token],
    name: &str,
    source_prefix: &str,
    path: &Path,
) -> Result<AmendmentRecord> {
    let rhs = def_rhs(tokens, name, path)?;
    let mut p = Parser::new(tokens, rhs, format!("{}: def {name}", path.display()));
    p.expect(&Token::LBrace)?;
    let mut deviation_id = None;
    let mut amendment_id = None;
    let mut spec_section = None;
    let mut pinned_commit = None;
    let mut patches = None;
    let mut upstream_references = None;
    while p.token() != Some(&Token::RBrace) {
        let field = p.ident()?;
        p.expect(&Token::Assign)?;
        match field.as_str() {
            "deviationId" => deviation_id = Some(p.string()?),
            "amendmentId" => amendment_id = Some(p.string()?),
            "specSection" => spec_section = Some(p.string()?),
            "pinnedCommit" => pinned_commit = Some(p.ident()?),
            "patches" => patches = Some(parse_patch_list(&mut p, source_prefix)?),
            "upstreamReferences" => upstream_references = Some(p.string_list()?),
            _ => return Err(p.error(format!("unknown amendment field `{field}`"))),
        }
    }
    p.expect(&Token::RBrace)?;
    Ok(AmendmentRecord {
        lean_name: name.to_string(),
        deviation_id: deviation_id.ok_or_else(|| p.error("missing deviationId"))?,
        amendment_id: amendment_id.ok_or_else(|| p.error("missing amendmentId"))?,
        spec_section: spec_section.ok_or_else(|| p.error("missing specSection"))?,
        pinned_commit: pinned_commit.ok_or_else(|| p.error("missing pinnedCommit"))?,
        patches: patches.ok_or_else(|| p.error("missing patches"))?,
        upstream_references: upstream_references
            .ok_or_else(|| p.error("missing upstreamReferences"))?,
    })
}

fn parse_patch_list(p: &mut Parser<'_>, source_prefix: &str) -> Result<Vec<PatchRecord>> {
    p.expect(&Token::LBracket)?;
    let mut out = Vec::new();
    while p.token() != Some(&Token::RBracket) {
        out.push(parse_patch(p, source_prefix)?);
        if p.token() == Some(&Token::Comma) {
            p.pos += 1;
        } else if p.token() != Some(&Token::RBracket) {
            return Err(p.error("expected comma or closing bracket in patch list"));
        }
    }
    p.expect(&Token::RBracket)?;
    Ok(out)
}

fn parse_patch(p: &mut Parser<'_>, source_prefix: &str) -> Result<PatchRecord> {
    p.expect(&Token::LBrace)?;
    let mut source_path = None;
    let mut source_sha256 = None;
    let mut before_anchor = None;
    let mut after_anchor = None;
    let mut removed_text = None;
    let mut inserted_text = None;
    let mut effect = None;
    let mut affected_symbols = None;
    let mut amended_declarations = None;
    while p.token() != Some(&Token::RBrace) {
        let field = p.ident()?;
        p.expect(&Token::Assign)?;
        match field.as_str() {
            "sourcePath" => {
                source_path = Some(match p.token() {
                    Some(Token::String(_)) => p.string()?,
                    Some(Token::Ident(name)) if name == "authoritySource" => {
                        p.pos += 1;
                        format!("{source_prefix}{}", p.string()?)
                    }
                    other => {
                        return Err(p.error(format!(
                            "sourcePath must be a literal or authoritySource literal, found {other:?}"
                        )))
                    }
                })
            }
            "sourceSha256" => source_sha256 = Some(p.string()?),
            "beforeAnchor" => before_anchor = Some(p.string()?),
            "afterAnchor" => after_anchor = Some(p.string()?),
            "removedText" => removed_text = Some(p.string()?),
            "insertedText" => inserted_text = Some(p.string()?),
            "effect" => {
                let e = p.ident()?;
                effect = Some(e.strip_prefix('.').unwrap_or(&e).to_string());
            }
            "affectedAuthoritySymbols" => affected_symbols = Some(p.string_list()?),
            "amendedLeanDeclarations" => amended_declarations = Some(p.string_list()?),
            _ => return Err(p.error(format!("unknown patch field `{field}`"))),
        }
    }
    p.expect(&Token::RBrace)?;
    Ok(PatchRecord {
        source_path: source_path.ok_or_else(|| p.error("missing sourcePath"))?,
        source_sha256: source_sha256.ok_or_else(|| p.error("missing sourceSha256"))?,
        before_anchor: before_anchor.ok_or_else(|| p.error("missing beforeAnchor"))?,
        after_anchor: after_anchor.ok_or_else(|| p.error("missing afterAnchor"))?,
        removed_text: removed_text.ok_or_else(|| p.error("missing removedText"))?,
        inserted_text: inserted_text.ok_or_else(|| p.error("missing insertedText"))?,
        effect: effect.ok_or_else(|| p.error("missing effect"))?,
        affected_symbols: affected_symbols
            .ok_or_else(|| p.error("missing affectedAuthoritySymbols"))?,
        amended_declarations: amended_declarations
            .ok_or_else(|| p.error("missing amendedLeanDeclarations"))?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    const COMMIT: &str = "9d36019973201a19f9c9ebb0f10828b2fe2374aa";

    fn plant(name: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!("wgg-authority-amendments-{name}"));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join(AUTHORITY_SOURCE_ROOT)).unwrap();
        fs::create_dir_all(root.join("WasmGemmGnaf/Wasm/Core")).unwrap();
        fs::create_dir_all(root.join("model")).unwrap();

        fs::write(
            root.join(REVISION_MODULE),
            format!("def core3RevisionCommit : String := \"{COMMIT}\"\n"),
        )
        .unwrap();
        fs::write(
            root.join(VENDOR_ROOT).join("PINNED-COMMIT"),
            format!("{COMMIT}\n"),
        )
        .unwrap();

        let mut sums = String::new();
        let mut authority = String::from(
            "private def authoritySource (leaf : String) : String :=\n  \
             \"vendor/wasm-spec/specification/wasm-3.0/\" ++ leaf\n\n",
        );
        let mut names = Vec::new();
        let mut deviations = Vec::new();
        let mut amendments = Vec::new();
        let mut declarations = String::from("namespace Test\n");

        for (i, (amendment, deviation)) in EXPECTED_AMENDMENTS
            .iter()
            .zip(EXPECTED_DEVIATIONS.iter())
            .enumerate()
        {
            let leaf = format!("source-{i}.spectec");
            let relative = format!("specification/wasm-3.0/{leaf}");
            let body = format!("BEFORE-{i}\nOLD-{i}\nAFTER-{i}\n");
            fs::write(root.join(VENDOR_ROOT).join(&relative), &body).unwrap();
            let digest = sha256::hex(body.as_bytes());
            sums.push_str(&format!("{digest}  ./{relative}\n"));

            let def_name = format!("amendment{i}");
            names.push(def_name.clone());
            authority.push_str(&format!(
                "def {def_name} : AuthorityAmendmentBody :=\n  \
                 {{ deviationId := \"{deviation}\"\n    \
                 amendmentId := \"{amendment}\"\n    \
                 specSection := \"4 and 7.3\"\n    \
                 pinnedCommit := core3RevisionCommit\n    \
                 patches := [{{ sourcePath := authoritySource \"{leaf}\"\n      \
                 sourceSha256 := \"{digest}\"\n      \
                 beforeAnchor := \"BEFORE-{i}\"\n      \
                 afterAnchor := \"AFTER-{i}\"\n      \
                 removedText := \"OLD-{i}\"\n      \
                 insertedText := \"NEW-{i}\"\n      \
                 effect := .replace\n      \
                 affectedAuthoritySymbols := [\"symbol-{i}\"]\n      \
                 amendedLeanDeclarations := [\"Test.D{i}\"] }}]\n    \
                 upstreamReferences := [\"https://example.test/{amendment}\"] }}\n\n"
            ));
            declarations.push_str(&format!("def D{i} : Nat := {i}\n"));
            deviations.push(format!(
                "{{\"id\":\"{deviation}\",\"adoptedIntoSpec\":\"{amendment}\"}}"
            ));
            amendments.push(format!(
                "{{\"id\":\"{amendment}\",\"deviation\":\"{deviation}\"}}"
            ));
        }
        declarations.push_str("end Test\n");
        authority.push_str(&format!(
            "def core3AuthorityAmendments : List AuthorityAmendmentBody := [{}]\n\n\
             def core3AuthorityAmendmentSet : AuthorityAmendmentSetBody :=\n  \
             {{ vendoredTreeId := VendoredTreeBody.identity core3VendoredTree\n    \
             amendments := core3AuthorityAmendments }}\n",
            names.join(", ")
        ));

        fs::write(root.join(VENDOR_ROOT).join("SHA256SUMS"), sums).unwrap();
        fs::write(root.join(AUTHORITY_MODULE), authority).unwrap();
        fs::write(
            root.join("WasmGemmGnaf/Wasm/Core/Repairs.lean"),
            declarations,
        )
        .unwrap();
        fs::write(
            root.join(DEVIATIONS),
            format!(
                "{{\"deviations\":[{}],\"amendments\":[{}]}}\n",
                deviations.join(","),
                amendments.join(",")
            ),
        )
        .unwrap();
        root
    }

    fn rejected(root: &Path) -> bool {
        binding(root).map_or(true, |b| !b.is_ok())
    }

    fn mutate(path: &Path, old: &str, new: &str) {
        let source = fs::read_to_string(path).unwrap();
        assert!(
            source.contains(old),
            "fixture did not contain mutation target `{old}`"
        );
        fs::write(path, source.replacen(old, new, 1)).unwrap();
    }

    #[test]
    fn faithful_complete_set_passes() {
        let root = plant("ok");
        let b = binding(&root).unwrap();
        assert!(b.is_ok(), "clean tree reported {:?}", b.findings);
        assert_eq!(b.amendment_ids, EXPECTED_AMENDMENTS);
        assert_eq!(b.patches.len(), EXPECTED_AMENDMENTS.len());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn source_digest_drift_is_rejected() {
        let root = plant("digest");
        mutate(
            &root.join(AUTHORITY_MODULE),
            &sha256::hex(b"BEFORE-0\nOLD-0\nAFTER-0\n"),
            &"0".repeat(64),
        );
        assert!(rejected(&root));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn anchor_or_removed_text_drift_is_rejected() {
        for (name, old, new) in [
            (
                "anchor",
                "beforeAnchor := \"BEFORE-0\"",
                "beforeAnchor := \"MISSING\"",
            ),
            (
                "removed",
                "removedText := \"OLD-0\"",
                "removedText := \"NOT-THERE\"",
            ),
        ] {
            let root = plant(name);
            mutate(&root.join(AUTHORITY_MODULE), old, new);
            assert!(rejected(&root), "{name} mutation passed");
            let _ = fs::remove_dir_all(root);
        }
    }

    #[test]
    fn empty_inserted_text_is_rejected() {
        let root = plant("inserted");
        mutate(
            &root.join(AUTHORITY_MODULE),
            "insertedText := \"NEW-0\"",
            "insertedText := \"\"",
        );
        assert!(rejected(&root));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn wrong_pin_or_tree_identity_is_rejected() {
        for (name, old, new) in [
            (
                "pin",
                "pinnedCommit := core3RevisionCommit",
                "pinnedCommit := otherCommit",
            ),
            (
                "tree",
                "VendoredTreeBody.identity core3VendoredTree",
                "VendoredTreeBody.identity otherTree",
            ),
        ] {
            let root = plant(name);
            mutate(&root.join(AUTHORITY_MODULE), old, new);
            assert!(rejected(&root), "{name} mutation passed");
            let _ = fs::remove_dir_all(root);
        }
    }

    #[test]
    fn incomplete_set_or_register_is_rejected() {
        let root = plant("set");
        let last_amendment = format!("amendment{}]", EXPECTED_AMENDMENTS.len() - 1);
        mutate(&root.join(AUTHORITY_MODULE), &last_amendment, "]");
        assert!(rejected(&root));
        let _ = fs::remove_dir_all(root);

        let root = plant("register");
        mutate(
            &root.join(DEVIATIONS),
            "\"adoptedIntoSpec\":\"AMD-005\"",
            "\"adoptedIntoSpec\":\"AMD-X\"",
        );
        assert!(rejected(&root));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn missing_declaration_or_coverage_marker_is_rejected() {
        let declarations = "WasmGemmGnaf/Wasm/Core/Repairs.lean";
        let root = plant("declaration");
        mutate(&root.join(declarations), "def D0", "def Gone");
        assert!(rejected(&root));
        let _ = fs::remove_dir_all(root);

        let root = plant("marker");
        let path = root.join(declarations);
        let source = fs::read_to_string(&path).unwrap();
        fs::write(path, format!("-- core-rule: invented\n{source}")).unwrap();
        let b = binding(&root).unwrap();
        assert!(!b.is_ok());
        assert_eq!(b.markers_in_amended_modules, 1);
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn lean_string_escapes_are_decoded() {
        let tokens = lex("def x := \"a\\nb\\\\c\\\"d\"").unwrap();
        assert_eq!(
            tokens.last(),
            Some(&Token::String("a\nb\\c\"d".to_string()))
        );
    }
}
