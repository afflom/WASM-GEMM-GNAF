# `just vv` is the normative release gate (SPEC.md section 20.2).
default: vv

# Every checker, generator and falsifier is the `xtask` Rust binary. It has no
# dependencies, so building it is offline and reproducible -- SPEC section 4
# forbids network-fetched inputs in release verification.
xtask := "cargo run --quiet --release -p xtask --"

# The whole gate. Expected to FAIL at step 9 while WGG-GO-1 is outstanding.
vv: tools root-check firewall manifest-check releasepath build vendor core required signature schema claims axioms docs-check
    @{{xtask}} gate

bootstrap:
    @lean --version && lake --version && cargo --version

# Build the gate checkers. Every recipe below that runs a check depends on this,
# so no check can silently run against a stale binary.
tools:
    @cargo build --release --quiet

build:
    lake build

test: tools
    lake build
    cargo test --release --quiet

prove:
    lake build

# SPEC 17.1: the claim LEVEL is load-bearing, so it is printed beside the status.
claims: tools
    @{{xtask}} claims list

# SPEC 19: axiom closure of every formalProof claim, over the COMPILED environment.
axioms: tools
    @{{xtask}} axioms

artifact-check:
    @test -f artifacts/wasm-gemm-gnaf.wasm || (echo "artifact absent: gated on WS-001/LB-001" && exit 1)

emit:
    @echo "emit: gated on WS-001 (mechanized Core 3.0 semantics)" && exit 1

# SPEC 18: every decisive gate must reject a planted fault. Each mutation is
# applied to a COPY; the repository is never modified.
mutation: tools
    @{{xtask}} mutation

reproduce:
    @echo "reproduce: gated on emit" && exit 1

# SPEC 17.3: CONFORMANCE.md embeds a LIVE inventory over the whole Lean tree, so
# it goes stale whenever a module is added -- not only when a claim changes.
# `reproducible.yml` asserted this in CI only, so staleness was found one push
# too late. This fails locally first.
docs-check: tools
    @{{xtask}} docs --check

# SPEC 17.3: CONFORMANCE.md, regenerated deterministically from the registry.
docs: tools
    @{{xtask}} docs

# SPEC 19: forbidden constructs, with comments and string literals excluded.
scan: tools
    @{{xtask}} sources scan

# Regenerate the root import module from the layer tree.
root: tools
    @{{xtask}} sources root

# Fail if the root import is stale or any module belongs to no SPEC 5 layer.
root-check: tools
    @{{xtask}} sources root --check

# SPEC 10.1: the competitor universe must not import the artifact or a conclusion.
firewall: tools
    @{{xtask}} sources firewall

# SPEC 4/5: regenerate the ordered acyclic identity manifest.
manifest: tools
    @{{xtask}} manifest

manifest-check: tools
    @{{xtask}} manifest --check

# SPEC 19/6.3: no noncomputable definition on the release path.
releasepath: tools
    @{{xtask}} sources releasepath

# SPEC 5: the vendored WebAssembly Core tree, recomputed from CONTENT, against
# the literals `Wasm.profile_matches_pinned_revision` stands on. Lean cannot read
# the tree; this is what stops a drifted literal from elaborating past the gate.
vendor: tools
    @{{xtask}} vendor --list

# SPEC 7.1: how much of the PINNED Core 3.0 front end the Lean tree covers. The
# checklist is EXTRACTED from the vendored SpecTec sources -- every opcode
# production, typing rule, syntax production and execution rule -- so it cannot
# be edited to flatter the repository.
#
# `--check` FAILS on incomplete coverage. It did not, and an external audit was
# right that a coverage number which cannot fail is not a gate: `just vv` ran the
# bare form, so 166 of 1206 passed silently.
core: tools
    @{{xtask}} core --check

# SPEC 15: required declarations, checked against the compiled environment.
required: tools
    @{{xtask}} claims required --list

# SPEC 1: every scopeCriticalDefinitions entry of the frozen WGG-GO-1 authority
# is bound to its fully spelled-out body by Iff.rfl / rfl. The authority JSON is
# the source of the list; the Lean elaborator is the comparator.
schema: tools
    @lake build WasmGemmGnaf.Conformance.Schema
    @{{xtask}} schema

# SPEC 15: every required declaration the environment credits is bound to SPEC's
# PROPOSITION -- restated in full, closed by `:= @Name`, so the comparison is
# definitional. SPEC.md is the source of the list; the Lean elaborator is the
# comparator.
#
# Without this, `just required` checked a NAME. An external audit demonstrated
# the consequence with this repository's own M12: a declaration called
# `Gemm.valid_input_finite` with type `Nat` and body `0` was counted discharged.
signature: tools
    @lake build WasmGemmGnaf.Conformance.RequiredSignatures
    @{{xtask}} signature
