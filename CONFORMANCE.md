# Conformance

**Inventory:** 297 Lean modules, 183,053 lines, 6,561 proved theorems.
Generated live; prose documents cite this table rather than repeating counts.

Generated from `model/claims.json` by `just docs`. Do not edit by hand.

Claim levels are load-bearing (SPEC 17.1). Only `formalProof` supports the
words "proved", "theorem", or "globally optimal".

## Claims

| ID | Level | Status | Statement | Lean declaration |
| --- | --- | --- | --- | --- |
| `CO-001` | formalProof | discharged | Every one of the 36 charged artifact coordinates is bounded by the canonical score. | `WasmGemmGnaf.Cost.coordinate_le_score` |
| `CO-002` | formalProof | discharged | Module bytes are bounded by the canonical score (size half of properness). | `WasmGemmGnaf.Cost.moduleBytes_le_score` |
| `CO-003` | formalProof | discharged | The canonical objective is monotone under componentwise cost order. | `WasmGemmGnaf.Cost.CanonicalObjective.monotone` |
| `CO-004` | formalProof | discharged | Sequential cost composition is associative; sums on cumulative coordinates, maxima on the three peaks. | `WasmGemmGnaf.Cost.sequentialCompose_assoc` |
| `CO-005` | formalProof | discharged | The 36-element artifact coordinate index is completely covered by its enumeration. | `WasmGemmGnaf.Cost.ArtifactCoordinate.mem_all` |
| `CO-007` | formalProof | discharged | For the exact public amended-Core aggregate predicate of SPEC 9.1, the static moduleBytes coordinate equals... | `WasmGemmGnaf.Cost.module_bytes_exact` |
| `LF-001` | authority | verified | Lean toolchain is leanprover/lean4:v4.30.0 at commit d024af099ca4bf2c86f649261ebf59565dc8c622. | `—` |
| `LF-002` | authority | verified | UOR-GNAF authority is UOR-GNAF-v1-draft.2.md with SHA-256 5c342373b2ff809bfd607c413cafd0582d32bb097544c6597... | `—` |
| `WS-001` | open | outstanding | Mechanized WebAssembly Core 3.0 semantics (GC, exception handling, fixed SIMD, tail calls) with decode_soun... | `—` |
| `UV-001` | open | outstanding | Universal sublevel coverage over all same-profile byte modules, with no coverage hypothesis. | `—` |
| `LB-001` | open | outstanding | A universal lower bound F on total charged cost over every correct feasible same-profile module, attained b... | `—` |
| `GO-001` | open | outstanding | released_wasm_gemm_gnaf_global_optimal : GlobalOptimal Release.wasmProfile Release.gemmProblem Release.cost... | `—` |
| `AT-001` | formalProof | discharged | Two Atlas states/cores with equal recorded searchPartitions, candidateFacts key identities, and partitionCo... | `WasmGemmGnaf.Atlas.universalCoverCompleteCheck_scope_blind` |
| `AT-002` | open | outstanding | Atlas.seal_implies_universal_coverage: a sealed state implies universal sublevel coverage over all profile-... | `—` |
| `LB-002` | formalProof | discharged | Every modeled bilinear 3x3 scheme satisfying ChargedOps and OutputsAreRankThree has total charged operation... | `WasmGemmGnaf.Universal.BilinearScheme.chargedOps_lower_bound` |
| `GO-002` | formalProof | discharged | The current legacy-carrier GlobalOptimal has an unrestricted outer ByteArray quantifier and equals GlobalOp... | `WasmGemmGnaf.Universal.globalOptimal_iff_over_all` |
| `GO-003` | formalProof | discharged | Any proof of the current legacy-carrier GlobalOptimal implies its released bytes satisfy that carrier's com... | `WasmGemmGnaf.Universal.globalOptimal_lower_bound_fires` |
| `UV-002` | formalProof | discharged | Within the current legacy SystemEvaluation carrier, byte strings inside a module-size bound are finitely en... | `WasmGemmGnaf.Universal.sublevel_bytes_enumerated` |
| `UV-006` | open | outstanding | SPEC 10.3: possible_winner_within_sublevel for an evaluated public amended-Core competitor under the releas... | `—` |
| `UV-005` | formalProof | discharged | SPEC 10.4: partition_cover_complete -- every byte string a root partition cell denotes is resolved by one o... | `WasmGemmGnaf.Universal.partition_cover_complete` |
| `CM-002` | formalProof | discharged | The legacy subset DecodeFault and InstantiateFault constructors are disjoint. | `WasmGemmGnaf.Wasm.Subset.Fault.decoding_ne_instantiation` |
| `LB-003` | formalProof | discharged | For a finite input type, if every input contributes at least k to a natural-valued cost function, the full... | `WasmGemmGnaf.Universal.sum_ge_card_mul` |
| `LB-004` | formalProof | discharged | A scalar lower bound L strictly below a released score S does not by itself imply every score above L is al... | `WasmGemmGnaf.Universal.lower_bound_below_released_is_not_optimality` |
| `BI-001` | formalProof | discharged | GNAF.compile emits a public representable Wasm.Module that passes the combined amended Core 3.0 validator f... | `WasmGemmGnaf.GNAF.compile_validates` |
| `BI-002` | open | outstanding | The GNAF compiler can emit a module implementing the FULL released GEMM problem (all four arithmetic modes... | `—` |
| `BI-003` | formalProof | discharged | The concrete gemmWitness plan satisfies Plan.inReleasedSubset = true. | `WasmGemmGnaf.GNAF.gemmWitness_inReleasedSubset` |
| `AT-003` | formalProof | discharged | Atlas.semanticClosure is contained in every semantically closed body containing its seed body. | `WasmGemmGnaf.Atlas.semantic_closure_least` |
| `AT-004` | formalProof | discharged | For every coherent Atlas state body, incremental accumulation equals full rebuild in that state's own scope. | `WasmGemmGnaf.Atlas.incremental_eq_full_rebuild` |
| `CM-003` | buildEvidence | verified | MANIFEST.json realises SPEC 4's three ordered identity stages, acyclically: no stage contains its own ident... | `—` |
| `GO-004` | formalProof | discharged | For the current legacy-subset Setting/SystemEvaluation carrier, if the admissible set is nonempty and the d... | `WasmGemmGnaf.Universal.exists_globalOptimal_of_nonempty` |
| `GO-005` | open | outstanding | Universal.system_evaluation_rel_functional holds for two evaluations of the same bytes under the public ame... | `—` |
| `GO-006` | open | outstanding | NONEMPTINESS: one concrete byte sequence with proofs of ProfileValid, SemanticCorrect and SemanticWithinRes... | `—` |
| `GO-007` | open | outstanding | EXHIBITION: the committed release literal equals the byte sequence selected by the argmin. | `—` |
| `GM-002` | formalProof | discharged | For every valid raw invocation, Gemm.reference returns a reference result. | `WasmGemmGnaf.Gemm.reference_total` |
| `BI-004` | formalProof | discharged | The GNAF plan language can express writing a computed value into memory. | `WasmGemmGnaf.GNAF.storeReg_reads_back` |
| `BI-005` | formalProof | discharged | After Plan evaluation, reading four bytes at gemmWitness's declared C base yields its declared alpha*A*B +... | `WasmGemmGnaf.GNAF.gemmWitness_writes_C` |
| `UV-003` | formalProof | discharged | Universal.system_evaluation_rel_complete proves that public profile validity, semantic correctness, and sem... | `WasmGemmGnaf.Universal.system_evaluation_rel_complete` |
| `UV-007` | formalProof | discharged | Universal.system_evaluation_rel_sound reflects a completed result of the sole executable public amended-Cor... | `WasmGemmGnaf.Universal.system_evaluation_rel_sound` |
| `GO-008` | open | outstanding | Universal.SystemEvaluationRel is inhabited for an emitted, semantically correct public Core GEMM module und... | `—` |
| `CO-006` | open | outstanding | The released cost table contains exactly one row for every enabled amended Core 3.0 execution and harness e... | `—` |
| `WS-002` | open | outstanding | The public amended Core costed explorer is sound and complete for every bounded branch and returns a canoni... | `—` |
| `BI-006` | open | outstanding | Every branch of the compiled GEMM baseline terminates within the released 2^320 step bound, so exploreAllCo... | `—` |
| `GO-009` | open | outstanding | A module that is BOTH evaluable (SystemEvaluation inhabited) AND SemanticCorrect for the release GEMM problem. | `—` |
| `BI-007` | formalProof | discharged | The GNAF plan language can express input-dependent computation: reading a descriptor field from memory into... | `WasmGemmGnaf.GNAF.loopReg_trips_from_memory` |
| `BI-008` | formalProof | discharged | The GNAF plan language expresses an INPUT-DEPENDENT GEMM: one TypedPlan, GNAF.gemmKernel, loads m, n and k... | `WasmGemmGnaf.GNAF.gemmKernel_writes_C` |
| `CM-004` | buildEvidence | verified | CI verifies the exact-SHA build: the authority digest step runs from the directory the checksum file names. | `—` |
| `CM-005` | buildEvidence | verified | The SPEC 15 inventory is derived from SPEC.md and checked against the compiled environment, not from a hand... | `—` |
| `WS-003` | open | outstanding | Release.wasmProfile is backed by the completed pinned Core 3.0 semantics rather than the i32 witness profil... | `—` |
| `WS-004` | formalProof | discharged | Wasm.profile_matches_pinned_revision binds every enabled vendored Core 3.0 rule exactly once to the release... | `WasmGemmGnaf.Wasm.profile_matches_pinned_revision` |
| `CM-006` | buildEvidence | verified | The Lean literals Wasm.profile_matches_pinned_revision stands on are recomputed from the vendored CONTENT:... | `—` |
| `CM-007` | open | outstanding | Implement and enforce the complete SPEC 17.2 per-claim row schema, canonical proposition and scope identiti... | `—` |
| `UV-004` | formalProof | discharged | Provide a constructive duplicate-free enumeration of every lawful raw invocation, a global choice-free Fint... | `WasmGemmGnaf.Universal.input_enumerator_complete` |
| `WS-005` | formalProof | discharged | A 53-byte Core 3.0 ABI-shape witness is accepted by the amended decoder as Wasm.Core.releaseBaselineModule... | `WasmGemmGnaf.Release.coreArtifact_validUnder` |
| `WS-006` | formalProof | discharged | Artifact.emit computationally encodes every representable public amended-Core Wasm.Module, and the public a... | `WasmGemmGnaf.Artifact.decode_emit` |
| `WS-007` | formalProof | discharged | For every representable public amended-Core Wasm.Module, decoding the computational Wasm.encode output retu... | `WasmGemmGnaf.Wasm.encode_decode_roundtrip` |
| `WS-008` | formalProof | discharged | Cost labels over the public typed amended-Core harness erase exactly to the plain public run, with the amen... | `WasmGemmGnaf.Wasm.costed_erase_iff_plain_run` |
| `WS-009` | formalProof | discharged | The public amended-Core read relation restores the source grammar's implicit well-formedness side condition... | `WasmGemmGnaf.Wasm.mem_successors_iff_step` |
| `WS-010` | open | outstanding | For every representable public amended-Core module, the public executable validation Boolean is true exactl... | `—` |
| `WS-011` | open | outstanding | Every representable, declaratively valid public amended-Core module configuration that instantiates that mo... | `—` |
| `BI-009` | formalProof | discharged | No total map from the legacy release path's instructions to the pinned Core 3.0 instructions preserves i32... | `WasmGemmGnaf.GNAF.no_i32const_preserving_map` |
| `BI-010` | open | outstanding | Every finite public Wasm.Run of GNAF.compile on a CheckedPlan and lawful raw invocation is accepted by the... | `—` |
| `BI-011` | open | outstanding | For every cost-labelled public execution of GNAF.compile, the sequentially composed initialization and exec... | `—` |

## Axiom closure

Every `formalProof` claim's transitive axioms, from `#print axioms`:

- `CO-001` — `propext`, `Quot.sound`
- `CO-002` — `propext`, `Quot.sound`
- `CO-003` — none
- `CO-004` — `propext`
- `CO-005` — `propext`
- `CO-007` — `propext`, `Quot.sound`
- `AT-001` — `propext`, `Classical.choice`, `Quot.sound`
- `LB-002` — `propext`, `Quot.sound`
- `GO-002` — `propext`, `Classical.choice`, `Quot.sound`
- `GO-003` — `propext`, `Classical.choice`, `Quot.sound`
- `UV-002` — `propext`, `Classical.choice`, `Quot.sound`
- `UV-005` — `propext`, `Classical.choice`, `Quot.sound`
- `CM-002` — none
- `LB-003` — `propext`, `Quot.sound`
- `LB-004` — none
- `BI-001` — `propext`, `Classical.choice`, `Quot.sound`
- `BI-003` — none
- `AT-003` — `propext`, `Quot.sound`
- `AT-004` — `propext`, `Classical.choice`, `Quot.sound`
- `GO-004` — `propext`, `Classical.choice`, `Quot.sound`
- `GM-002` — `propext`, `Classical.choice`, `Quot.sound`
- `BI-004` — `propext`, `Quot.sound`
- `BI-005` — `propext`, `Quot.sound`
- `UV-003` — `propext`, `Classical.choice`, `Quot.sound`
- `UV-007` — `propext`, `Classical.choice`, `Quot.sound`
- `BI-007` — `propext`
- `BI-008` — `propext`, `Quot.sound`
- `WS-004` — `propext`, `Classical.choice`, `Quot.sound`
- `UV-004` — `propext`, `Quot.sound`
- `WS-005` — `propext`, `Classical.choice`, `Quot.sound`
- `WS-006` — `propext`, `Classical.choice`, `Quot.sound`
- `WS-007` — `propext`, `Classical.choice`, `Quot.sound`
- `WS-008` — `propext`, `Classical.choice`, `Quot.sound`
- `WS-009` — `propext`, `Classical.choice`, `Quot.sound`
- `BI-009` — `propext`, `Quot.sound`

Permitted: `propext`, `Quot.sound`, `Classical.choice` (Lean core logical
axioms, SPEC 4). Any `sorryAx` or project-declared axiom fails the gate.

## Refuted framings

Recorded so they are not silently re-asserted:

- **REFUTED** (medium) — Closure requires exact minimal-program-size lower bounds, an open circuit-complexity problem.
  - Weight-one module bytes creates a minimal-total-cost obligation, not a minimal-program-size one; asymptotic circuit lower bounds are the wrong authority.

## Outstanding obligations

21 outstanding. Terminal answer for `GO-001`: `WorkloadIncomplete`
(UOR-GNAF v1-draft.2 section 10.9). See `CERTIFICATION.md`.

- `WS-001` (O-6) — Mechanized WebAssembly Core 3.0 semantics (GC, exception handling, fixed SIMD, tail calls) with deco
- `UV-001` (O-5) — Universal sublevel coverage over all same-profile byte modules, with no coverage hypothesis.
- `LB-001` (O-5) — A universal lower bound F on total charged cost over every correct feasible same-profile module, att
- `GO-001` (—) — released_wasm_gemm_gnaf_global_optimal : GlobalOptimal Release.wasmProfile Release.gemmProblem Relea
- `AT-002` (O-5) — Atlas.seal_implies_universal_coverage: a sealed state implies universal sublevel coverage over all p
- `UV-006` (O-6) — SPEC 10.3: possible_winner_within_sublevel for an evaluated public amended-Core competitor under the
- `BI-002` (O-6) — The GNAF compiler can emit a module implementing the FULL released GEMM problem (all four arithmetic
- `GO-005` (O-6) — Universal.system_evaluation_rel_functional holds for two evaluations of the same bytes under the pub
- `GO-006` (O-6) — NONEMPTINESS: one concrete byte sequence with proofs of ProfileValid, SemanticCorrect and SemanticWi
- `GO-007` (O-5) — EXHIBITION: the committed release literal equals the byte sequence selected by the argmin.
- `GO-008` (O-6) — Universal.SystemEvaluationRel is inhabited for an emitted, semantically correct public Core GEMM mod
- `CO-006` (O-6) — The released cost table contains exactly one row for every enabled amended Core 3.0 execution and ha
- `WS-002` (—) — The public amended Core costed explorer is sound and complete for every bounded branch and returns a
- `BI-006` (O-6) — Every branch of the compiled GEMM baseline terminates within the released 2^320 step bound, so explo
- `GO-009` (O-6) — A module that is BOTH evaluable (SystemEvaluation inhabited) AND SemanticCorrect for the release GEM
- `WS-003` (O-6) — Release.wasmProfile is backed by the completed pinned Core 3.0 semantics rather than the i32 witness
- `CM-007` (O-6) — Implement and enforce the complete SPEC 17.2 per-claim row schema, canonical proposition and scope i
- `WS-010` (O-6) — For every representable public amended-Core module, the public executable validation Boolean is true
- `WS-011` (O-6) — Every representable, declaratively valid public amended-Core module configuration that instantiates
- `BI-010` (O-6) — Every finite public Wasm.Run of GNAF.compile on a CheckedPlan and lawful raw invocation is accepted
- `BI-011` (O-6) — For every cost-labelled public execution of GNAF.compile, the sequentially composed initialization a
