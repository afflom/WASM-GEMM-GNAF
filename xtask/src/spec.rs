//! Errors that name the SPEC clause they violate.
//!
//! A red gate has to say WHICH promise broke. An error that only says
//! "No such file or directory" tells a release engineer nothing about whether
//! the tree is non-conforming or the tool was invoked wrongly, so every failure
//! path here carries the SPEC section that motivated the check.

use std::fmt;
use std::path::Path;

/// A tooling failure, tagged with the SPEC clause it relates to.
#[derive(Debug)]
pub struct SpecError {
    clause: &'static str,
    message: String,
}

impl SpecError {
    pub fn new(clause: &'static str, message: impl Into<String>) -> Self {
        SpecError { clause, message: message.into() }
    }

    /// Wrap an I/O failure against a path, keeping the SPEC clause.
    pub fn io(clause: &'static str, what: &str, path: &Path, err: std::io::Error) -> Self {
        SpecError::new(clause, format!("{} {}: {}", what, path.display(), err))
    }
}

impl fmt::Display for SpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SPEC {}: {}", self.clause, self.message)
    }
}

impl std::error::Error for SpecError {}

pub type Result<T> = std::result::Result<T, SpecError>;

/// The verdict of one checker. `Fail` means the tree violates the SPEC clause
/// the checker enforces -- it is a conforming answer, not a tool error, so it
/// travels separately from [`SpecError`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Pass,
    Fail,
}

impl Outcome {
    pub fn code(self) -> i32 {
        match self {
            Outcome::Pass => 0,
            Outcome::Fail => 1,
        }
    }
}
