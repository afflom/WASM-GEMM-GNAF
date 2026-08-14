/-
# SPEC §15 status pointer

This module proves no SPEC obligation.  `SPEC.md` is the normative contract,
`CERTIFICATION.md` is the repository's terminal answer, and the generated
`CONFORMANCE.md` together with `just required` reports the live declaration
inventory.  Exact totals are deliberately not copied into this comment because
a hand-maintained count can drift from the compiled environment.

## Current public-Core boundary

The public `Wasm.Module` is a representable amended Core 3.0 module:
representability is witnessed by `Wasm.Core.Binary.BmoduleA`.  The public
`Wasm.decode` and `Wasm.DeclarativeBinaryRelation` use the amended decoder and
that amended grammar, and `Wasm.decode_sound` / `Wasm.decode_complete` establish
their exact agreement.

`Wasm.encode` is a computational encoder on that public representable carrier.
`Wasm.encode_decode_roundtrip` and `Artifact.decode_emit` prove that decoding the
encoder's chosen output returns the same public module.  This is only an
encode/decode round trip.  It does not assert byte uniqueness, identify selected
or committed release bytes, provide a GEMM implementation, or construct a
`Universal.SystemEvaluation`.

The legacy `Wasm.Subset` validator, execution relation, fuel explorer, costed
machine, compiler target, and module-level witnesses do not discharge the
corresponding public amended-Core obligations.  In particular, no subset byte or
evaluation witness is release evidence.

## Open release chain

The public amended-Core validator biconditional, whole-machine successor
enumeration, preservation/progress, bounded all-branch exploration, and exact
SPEC §7.5 event accounting remain open.  The direct public-Core GNAF compiler,
all four SPEC §8.2 arithmetic modes, execution refinement, and exact resource and
cost proofs also remain open.

Consequently `Universal.system_evaluation_rel_sound` and
`Universal.system_evaluation_rel_complete` are not closed for a byte-indexed
public-Core evaluator.  `GO-008` remains open: there is no emitted semantically
correct public-Core GEMM equipped with the exact released costed evaluation.
`Artifact.released_bytes_equal_selection`,
`Artifact.committed_literal_equal_selection`, attainment,
`Universal.universal_sublevel_coverage`,
`Universal.all_competitors_lower_bound`, and the other SPEC §15
`Artifact.released_*` obligations remain open.  The repository declares no
release-scoped `Universal.GlobalOptimal` result and no
`Artifact.released_wasm_gemm_gnaf_global_optimal` theorem.

The conforming terminal answer therefore remains `WorkloadIncomplete`.  The
generic argmin and other conditional infrastructure do not instantiate the
release claim.
-/
import WasmGemmGnaf.Theorems.WasmModel
import WasmGemmGnaf.Theorems.GemmTotal
import WasmGemmGnaf.Theorems.CostModel
import WasmGemmGnaf.Theorems.AtlasLaws
import WasmGemmGnaf.Theorems.Release

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

/-- Marker declaration.  `Status.lean` is a status pointer, not a source of
mathematical results. -/
theorem spec15_ledger_is_documentation : True := trivial

end WasmGemmGnaf.Theorems
