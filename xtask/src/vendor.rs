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
    let (digest, rest) = line.split_once(' ')?;
    if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let name = rest.strip_prefix(' ').or_else(|| rest.strip_prefix('*'))?;
    (!name.is_empty()).then_some((digest, name))
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
}
