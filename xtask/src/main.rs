//! Release-gate checkers for WASM-GEMM-GNAF.
//!
//! This crate is TOOLING. It is not part of the Lean proof path: nothing under
//! `WasmGemmGnaf/` depends on it, and it is never imported by the library. It
//! reads the tree, questions the compiled Lean environment, and reports whether
//! the promises in `SPEC.md` hold.
//!
//! Every failure names the SPEC section it enforces, so a red gate says WHICH
//! promise broke rather than merely that something did.

mod amendment;
mod axioms;
mod core;
mod docs;
mod firewall;
mod gate;
mod independence;
mod json;
mod lean;
mod manifest;
mod mutation;
mod releasepath;
mod repo;
mod required;
mod root;
mod scan;
mod schema;
mod sha1;
mod sha256;
mod signature;
mod spec;
mod vendor;

use std::process::ExitCode;

use spec::{Outcome, Result, SpecError};

const USAGE: &str = "\
xtask -- release-gate checkers for WASM-GEMM-GNAF

USAGE:
    xtask <command> [options]

SOURCE CHECKS (read the tree)
    sources scan [PATH...]     Forbidden constructs, comments and strings excluded
                               (SPEC 19). Defaults to WasmGemmGnaf/.
    sources firewall           The competitor universe must not import the artifact,
                               the selector or a conclusion (SPEC 10.1).
    sources root [--check]     Regenerate the root import module from the layer tree;
                               --check fails if it is stale or a module is unowned
                               (SPEC 5).
    sources releasepath        No noncomputable definition on the release path
                               (SPEC 19 / 6.3).
    vendor [--list]            The vendored WebAssembly Core tree, recomputed from
                               CONTENT (SPEC 5), against the literals the Lean
                               theorem `Wasm.profile_matches_pinned_revision` stands
                               on: the digest of SHA256SUMS, the file count, the
                               pinned commit, and every vendored rule anchor cited by
                               `Wasm/Adequacy.lean`. --list adds the coverage
                               arithmetic and the SpecTec scope limit.
    amendment                  The recorded grammar amendment (SPEC 7.3, AMD-005 /
                               DEV-006), checked against the tree: the digest of the
                               vendored SpecTec source the defect is in, the entry
                               SHA256SUMS lists for it, that the pin was NOT advanced
                               to upstream's repair, that the amended Lean module
                               declares the recorded relation, and that it carries no
                               Core 3.0 coverage marker.
    core [--list]              How much of the PINNED Core 3.0 front end the Lean
                               tree covers (SPEC 7.1). The checklist is EXTRACTED
                               from the vendored SpecTec sources -- every opcode
                               production, typing rule and syntax production --
                               and Lean claims an item with a `-- core-opcode:` /
                               `-- core-rule:` / `-- core-syntax:` marker. A
                               marker naming something the sources do not define
                               is a hard failure. --list names what is missing.

ENVIRONMENT CHECKS (question the compiled Lean environment)
    claims required [--list] [--check]
                               SPEC 15's required declarations, with SPEC 4's ban on
                               choice-tainted executable witnesses enforced.
                               --list names what is outstanding; --check exits
                               non-zero if anything is.
    claims list                The claim registry with each claim's level and status
                               (SPEC 17.1).
    axioms                     Axiom closure of every formalProof claim (SPEC 19).
    schema                     Every `scopeCriticalDefinitions` entry of the frozen
                               WGG-GO-1 authority is bound to its fully spelled-out
                               body by a definitional proof (SPEC 1). The authority
                               JSON supplies the list; Lean's elaborator compares
                               the bodies.
    signature                  Every SPEC 15 declaration the environment credits is
                               bound to SPEC's PROPOSITION, restated in full and
                               closed by `:= @Name`, in
                               WasmGemmGnaf/Conformance/RequiredSignatures.lean.
                               SPEC.md supplies the list; Lean's elaborator compares
                               the types. Without this, a declaration with the right
                               name and type `Nat` counts as discharged.

GENERATORS (write a tracked file, deterministically)
    manifest [--check]         The ordered acyclic identity stages, as MANIFEST.json
                               (SPEC 4/5). --check fails if it is stale.
    docs                       CONFORMANCE.md from model/claims.json (SPEC 17.3).

RELEASE
    gate [--no-mutation]       The normative release gate: SPEC 20.2's thirteen
                               conditions. --no-mutation is for the M6 falsifier,
                               which would otherwise recurse back into this suite.
    mutation                   Planted falsifiers M1-M15 (SPEC 18). Every mutation is
                               applied to a COPY, never to the repository.

Requires `lake build` first for the environment checks.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match dispatch(&args) {
        Ok(outcome) => ExitCode::from(outcome.code() as u8),
        Err(err) => {
            eprintln!("xtask: {err}");
            ExitCode::from(2)
        }
    }
}

fn dispatch(args: &[String]) -> Result<Outcome> {
    let Some(command) = args.first().map(String::as_str) else {
        print!("{USAGE}");
        return Ok(Outcome::Fail);
    };
    let rest = &args[1..];

    // Every checker reports paths relative to the repository root, exactly as
    // the SPEC names them, so run from there whatever the caller's directory.
    let root = repo::enter_root()?;

    match command {
        "sources" => {
            let Some(sub) = rest.first().map(String::as_str) else {
                return Err(SpecError::new(
                    "19",
                    "`xtask sources` needs a check: scan, firewall, root or releasepath",
                ));
            };
            let opts = &rest[1..];
            match sub {
                "scan" => {
                    let targets: Vec<String> =
                        opts.iter().filter(|a| !a.starts_with("--")).cloned().collect();
                    scan::run(&targets)
                }
                "firewall" => firewall::run(),
                "root" => root::run(has(opts, "--check")),
                "releasepath" => releasepath::run(),
                other => Err(unknown("sources", other)),
            }
        }
        "claims" => {
            let Some(sub) = rest.first().map(String::as_str) else {
                return Err(SpecError::new("15", "`xtask claims` needs a check: required"));
            };
            let opts = &rest[1..];
            match sub {
                "required" => required::run(&root, has(opts, "--list"), has(opts, "--check")),
                "list" => required::list_registry(),
                other => Err(unknown("claims", other)),
            }
        }
        "axioms" => axioms::run(&root),
        "schema" => schema::run(&root),
        "signature" => signature::run(&root),
        "vendor" => vendor::run(has(rest, "--list")),
        "amendment" => amendment::run(),
        "core" => core::run(&root, has(rest, "--list"), has(rest, "--check")),
        "independence" => independence::run(&root),
        "manifest" => manifest::run(has(rest, "--check")),
        "docs" => docs::run(has(rest, "--check")),
        "gate" => gate::run(&root, has(rest, "--no-mutation")),
        "mutation" => mutation::run(&root),
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            Ok(Outcome::Pass)
        }
        other => Err(unknown("xtask", other)),
    }
}

fn has(args: &[String], flag: &str) -> bool {
    args.iter().any(|a| a == flag)
}

fn unknown(group: &str, name: &str) -> SpecError {
    SpecError::new(
        "20.2",
        format!("`{group}` has no check named `{name}`; run `xtask help` for the gate's checks"),
    )
}
