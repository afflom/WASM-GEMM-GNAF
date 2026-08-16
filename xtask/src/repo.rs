//! Repository root discovery and the deterministic `.lean` walk.

use std::fs;
use std::path::{Path, PathBuf};

use crate::spec::{Result, SpecError};

/// Locate the repository root by walking up from the current directory looking
/// for the two files that identify this tree: `lakefile.lean` (the Lean build)
/// and `SPEC.md` (the normative document every checker cites).
///
/// The Python tools derived the root from `__file__`. Deriving it from the
/// working directory instead means the same binary works from a `git worktree`
/// or an unpacked release tarball, which is how offline verification runs.
pub fn find_root() -> Result<PathBuf> {
    let start = std::env::current_dir()
        .map_err(|e| SpecError::new("5", format!("cannot read the working directory: {e}")))?;
    let mut dir = start.as_path();
    loop {
        if dir.join("lakefile.lean").is_file() && dir.join("SPEC.md").is_file() {
            return Ok(dir.to_path_buf());
        }
        match dir.parent() {
            Some(p) => dir = p,
            None => {
                return Err(SpecError::new(
                    "5",
                    format!(
                        "no repository root at or above {}: expected a directory holding both \
                         lakefile.lean and SPEC.md",
                        start.display()
                    ),
                ))
            }
        }
    }
}

/// Move to the repository root so that every path this tool prints is relative
/// to it, exactly as the Python tools did with `os.chdir(ROOT)`.
pub fn enter_root() -> Result<PathBuf> {
    let root = find_root()?;
    std::env::set_current_dir(&root)
        .map_err(|e| SpecError::io("5", "cannot enter repository root", &root, e))?;
    Ok(root)
}

/// Every `.lean` file under `dir`, in a deterministic order: directories and
/// files sorted by name, parents before children.
///
/// Paths come back exactly as they would be joined from `dir`, so a caller that
/// passes a relative `WasmGemmGnaf` gets `WasmGemmGnaf/Foundation/Bytes.lean`.
pub fn lean_files(clause: &'static str, dir: &Path) -> Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    walk(clause, dir, &mut found)?;
    Ok(found)
}

fn walk(clause: &'static str, dir: &Path, found: &mut Vec<PathBuf>) -> Result<()> {
    let entries =
        fs::read_dir(dir).map_err(|e| SpecError::io(clause, "cannot read directory", dir, e))?;

    let mut files = Vec::new();
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| SpecError::io(clause, "cannot read entry under", dir, e))?;
        let path = entry.path();
        let kind = entry
            .file_type()
            .map_err(|e| SpecError::io(clause, "cannot stat", &path, e))?;
        if kind.is_dir() {
            dirs.push(path);
        } else if path.extension().is_some_and(|e| e == "lean") {
            files.push(path);
        }
    }
    files.sort();
    dirs.sort();

    found.extend(files);
    for d in dirs {
        walk(clause, &d, found)?;
    }
    Ok(())
}

/// Read a source file, replacing invalid UTF-8 rather than failing, mirroring
/// Python's `open(p, errors="replace")`.
pub fn read_lossy(clause: &'static str, path: &Path) -> Result<String> {
    let bytes = fs::read(path).map_err(|e| SpecError::io(clause, "cannot read", path, e))?;
    Ok(String::from_utf8_lossy(&bytes).into_owned())
}

/// Path with `/` separators, for matching against SPEC-declared prefixes.
pub fn slash(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}
