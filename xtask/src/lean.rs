//! Lean source handling: the comment/string stripper, the line-level
//! declaration predicates, and the `#print axioms` probe runner.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::spec::{Result, SpecError};

/// Blank out comments and string bodies, preserving line structure.
///
/// This is the part of the forbidden-construct scan that carries the whole
/// check. A plain text search for `sorry` fires on the doc comments that
/// explain the ban -- several modules legitimately mention it -- and a gate
/// that reports its own documentation as a violation gets switched off, which
/// is the same failure as a gate that never fires.
///
/// Handles nested `/- ... -/` (so `/-- ... -/` doc comments too), `--` line
/// comments, and string literals with backslash escapes. Every removed
/// character becomes a space and every newline survives, so line numbers and
/// the "is this at the start of a line" tests downstream stay meaningful.
pub fn strip(src: &str) -> String {
    let c: Vec<char> = src.chars().collect();
    let n = c.len();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;
    let mut depth = 0usize;

    let two = |i: usize, a: char, b: char| i + 1 < n && c[i] == a && c[i + 1] == b;

    while i < n {
        if depth == 0 && two(i, '/', '-') {
            depth = 1;
            i += 2;
            out.push_str("  ");
            continue;
        }
        if depth > 0 {
            if two(i, '/', '-') {
                depth += 1;
                i += 2;
                out.push_str("  ");
                continue;
            }
            if two(i, '-', '/') {
                depth -= 1;
                i += 2;
                out.push_str("  ");
                continue;
            }
            out.push(if c[i] == '\n' { '\n' } else { ' ' });
            i += 1;
            continue;
        }
        if two(i, '-', '-') {
            while i < n && c[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        if c[i] == '"' {
            out.push(' ');
            i += 1;
            while i < n && c[i] != '"' {
                if c[i] == '\\' && i + 1 < n {
                    out.push_str("  ");
                    i += 2;
                    continue;
                }
                out.push(if c[i] == '\n' { '\n' } else { ' ' });
                i += 1;
            }
            if i < n {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        out.push(c[i]);
        i += 1;
    }
    out
}

/// Split on `\n`, `\r\n` or a lone `\r`, with no trailing empty line -- the
/// behaviour the Python tools got from `str.splitlines()`.
pub fn splitlines(s: &str) -> Vec<&str> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let (mut start, mut i) = (0usize, 0usize);
    while i < b.len() {
        match b[i] {
            b'\n' => {
                out.push(&s[start..i]);
                i += 1;
                start = i;
            }
            b'\r' => {
                out.push(&s[start..i]);
                i += if i + 1 < b.len() && b[i + 1] == b'\n' {
                    2
                } else {
                    1
                };
                start = i;
            }
            _ => i += 1,
        }
    }
    if start < b.len() {
        out.push(&s[start..]);
    }
    out
}

fn is_ident_tail(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

/// Does the line use one of the banned placeholder tokens as a token, rather
/// than mentioning it inside a longer identifier?
///
/// A `.` before the token also disqualifies it, so a qualified name such as
/// `Foo.admit` is not a placeholder.
pub fn has_placeholder(line: &str) -> bool {
    const BANNED: [&str; 3] = ["sorry", "admit", "native_decide"];
    let c: Vec<char> = line.chars().collect();
    for kw in BANNED {
        let k: Vec<char> = kw.chars().collect();
        if c.len() < k.len() {
            continue;
        }
        for start in 0..=(c.len() - k.len()) {
            if c[start..start + k.len()] != k[..] {
                continue;
            }
            let before_ok = start == 0 || !(is_ident_tail(c[start - 1]) || c[start - 1] == '.');
            let end = start + k.len();
            let after_ok = end == c.len() || !is_ident_tail(c[end]);
            if before_ok && after_ok {
                return true;
            }
        }
    }
    false
}

/// `axiom` opening a declaration on this line.
pub fn is_axiom_decl(line: &str) -> bool {
    match line.trim_start().strip_prefix("axiom") {
        Some(rest) => rest.starts_with(char::is_whitespace),
        None => false,
    }
}

/// `unsafe`/`partial` opening a `def`, `abbrev`, `instance` or `theorem`.
pub fn is_unsafe_or_partial_decl(line: &str) -> bool {
    let head = line.trim_start();
    for modifier in ["unsafe", "partial"] {
        if let Some(rest) = head.strip_prefix(modifier) {
            if let Some(after) = require_space(rest) {
                if ["def", "abbrev", "instance", "theorem"]
                    .iter()
                    .any(|d| after.starts_with(d))
                {
                    return true;
                }
            }
        }
    }
    false
}

/// `noncomputable def|abbrev|instance <name>` -- returns the keyword and name.
pub fn noncomputable_decl(line: &str) -> Option<(&'static str, String)> {
    let rest = line.trim_start().strip_prefix("noncomputable")?;
    let after = require_space(rest)?;
    for kind in ["def", "abbrev", "instance"] {
        if let Some(tail) = after.strip_prefix(kind) {
            let Some(named) = require_space(tail) else {
                continue;
            };
            let name: String = named.chars().take_while(|c| !c.is_whitespace()).collect();
            if !name.is_empty() {
                return Some((kind, name));
            }
        }
    }
    None
}

/// The module an `import` line names, if the line is an import.
pub fn import_target(line: &str) -> Option<&str> {
    let rest = line.trim_start().strip_prefix("import")?;
    let after = require_space(rest)?;
    let end = after
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
        .unwrap_or(after.len());
    (end > 0).then(|| &after[..end])
}

/// Consume at least one whitespace character, as a regex `\s+` would.
fn require_space(s: &str) -> Option<&str> {
    let trimmed = s.trim_start();
    (trimmed.len() < s.len()).then_some(trimmed)
}

/// A `line.strip()[:80]` excerpt, for quoting the offending source.
pub fn excerpt(line: &str) -> String {
    line.trim().chars().take(80).collect()
}

/// The result of elaborating a probe file.
pub struct Probe {
    pub stdout: String,
    pub stderr: String,
    pub success: bool,
}

impl Probe {
    /// Everything Lean said, on either stream.
    pub fn combined(&self) -> String {
        format!("{}{}", self.stdout, self.stderr)
    }
}

/// Write a `#print axioms` probe, elaborate it against the compiled
/// environment, and delete it.
///
/// SPEC section 19: the decisive audit inspects the compiled environment, not
/// the source text. There is no way to ask that question without Lean, and
/// linking Lean's API from Rust would put this tooling crate on the proof path,
/// so the probe is elaborated by the `lean` binary with `LEAN_PATH` pointed at
/// the build output -- the same route the Python tools took.
pub fn probe_axioms(
    clause: &'static str,
    root: &Path,
    probe_file: &str,
    declarations: &[String],
) -> Result<Probe> {
    let mut src = String::from("import WasmGemmGnaf\n");
    for decl in declarations {
        src.push_str("#print axioms ");
        src.push_str(decl);
        src.push('\n');
    }
    probe_source(clause, root, &PathBuf::from(probe_file), &src)
}

/// Elaborate an arbitrary probe against the compiled environment, then delete it.
///
/// The falsifier suite needs this: a planted mutation must be elaborated
/// somewhere that is NOT the repository, so `path` is a caller's choice rather
/// than a fixed name in the tree.
pub fn probe_source(clause: &'static str, root: &Path, path: &Path, src: &str) -> Result<Probe> {
    fs::write(path, src).map_err(|e| SpecError::io(clause, "cannot write probe", path, e))?;

    let outcome = Command::new("lean")
        .arg(path)
        .env("LEAN_PATH", root.join(".lake/build/lib/lean"))
        .output();

    // Delete the probe whatever happened: a leftover `.lean` in the root would
    // be picked up by the next `just root-check` as an unowned module.
    let _ = fs::remove_file(path);

    let outcome = outcome.map_err(|e| {
        SpecError::new(
            clause,
            format!(
                "cannot run `lean` to audit the compiled environment: {e}. \
                 The axiom closure is decided by the compiled environment, so this \
                 check cannot be answered from source alone -- install the pinned \
                 toolchain and run `lake build` first."
            ),
        )
    })?;

    Ok(Probe {
        stdout: String::from_utf8_lossy(&outcome.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&outcome.stderr).into_owned(),
        success: outcome.status.success(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn doc_comment_mentioning_sorry_is_invisible() {
        let src =
            "/-- SPEC 19 bans `sorry` on the proof path. -/\ntheorem good : True := trivial\n";
        let code = strip(src);
        assert!(!splitlines(&code).iter().any(|l| has_placeholder(l)));
    }

    #[test]
    fn real_sorry_fires() {
        let src = "theorem bad : True := by sorry\n";
        let code = strip(src);
        assert!(splitlines(&code).iter().any(|l| has_placeholder(l)));
    }

    #[test]
    fn nested_block_comments_close_once() {
        let src = "/- outer /- inner -/ still comment sorry -/\ntheorem t : True := trivial\n";
        let code = strip(src);
        assert!(!splitlines(&code).iter().any(|l| has_placeholder(l)));
    }

    #[test]
    fn line_comment_and_string_are_blanked() {
        assert!(!has_placeholder(&strip("def f := g -- sorry")));
        assert!(!has_placeholder(&strip("def msg := \"sorry\"")));
    }

    #[test]
    fn escaped_quote_does_not_end_the_string() {
        assert!(!has_placeholder(&strip("def m := \"a\\\" sorry \"")));
    }

    #[test]
    fn line_structure_survives_stripping() {
        let src = "line1\n/- two\nthree -/\nline4 sorry\n";
        let code = strip(src);
        let lines = splitlines(&code);
        assert_eq!(lines.len(), 4);
        assert!(has_placeholder(lines[3]));
        assert!(!has_placeholder(lines[1]));
    }

    #[test]
    fn qualified_name_is_not_a_placeholder() {
        assert!(!has_placeholder("exact Foo.admit"));
        assert!(!has_placeholder("def sorryFree := 1"));
        assert!(!has_placeholder("def notsorry := 1"));
        assert!(has_placeholder("  admit"));
    }

    #[test]
    fn declaration_predicates() {
        assert!(is_axiom_decl("  axiom foo : True"));
        assert!(!is_axiom_decl("  axioms foo"));
        assert!(!is_axiom_decl("-- axiom foo"));
        assert!(is_unsafe_or_partial_decl("partial def loop := loop"));
        assert!(is_unsafe_or_partial_decl("  unsafe instance i : I := {}"));
        assert!(!is_unsafe_or_partial_decl("partially def x := 1"));
        assert_eq!(
            noncomputable_decl("noncomputable def decider : D := c"),
            Some(("def", "decider".to_string()))
        );
        assert_eq!(noncomputable_decl("def decider : D := c"), None);
        assert_eq!(
            import_target("import WasmGemmGnaf.Atlas.Seal"),
            Some("WasmGemmGnaf.Atlas.Seal")
        );
        assert_eq!(import_target("importWasmGemmGnaf"), None);
    }

    #[test]
    fn splitlines_matches_python() {
        assert_eq!(splitlines(""), Vec::<&str>::new());
        assert_eq!(splitlines("a\n"), vec!["a"]);
        assert_eq!(splitlines("a\nb"), vec!["a", "b"]);
        assert_eq!(splitlines("a\r\nb"), vec!["a", "b"]);
    }
}
