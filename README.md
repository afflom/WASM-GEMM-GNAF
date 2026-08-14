# WASM-GEMM-GNAF

A Lean 4 mechanization targeting a kernel-checked global-optimality theorem for a
committed WebAssembly GEMM binary, under the pinned UOR-GNAF authority.

## Status

> Global optimality is the release theorem required by `SPEC.md`; it has not been
> established. No current test, benchmark, candidate search, or partial proof may
> be cited as that theorem.

That paragraph is mandated verbatim by `SPEC.md` §21 for the pre-closure state and
must not be edited while the state holds.

The repository's exact terminal answer for the requested claim is
`WorkloadIncomplete` — a branch of the UOR-GNAF §10.9 total answer carrier, and the
branch its §13.3 *requires* when the argmin proof is not closed. The full obligation
ledger, including framings narrowed or refuted by adversarial review, is in
[CERTIFICATION.md](CERTIFICATION.md).

`just vv` fails on the recorded open prerequisites and on gate step 9, where the
final declaration is absent. That is the correct behavior. A green gate in this
state would mean the gate had been weakened or the proof had genuinely closed.

## What is proved

Kernel-checked in Lean 4.30.0, sorry-free; the live inventory is the first line of
[CONFORMANCE.md](CONFORMANCE.md). Permitted formal-proof closure is `propext`,
`Quot.sound`, and Prop-level `Classical.choice`, named individually per
`SPEC.md` §4. Three input-enumeration declarations currently reach
`Classical.choice` as executable witnesses; they are therefore recorded as
uncredited and outstanding, not counted as formal proof.

| Declaration | Content |
| --- | --- |
| `Universal.exists_globalOptimal_of_nonempty` | generic finite-argmin existence for an explicitly nonempty, decidable instantiated universe |
| `Universal.systemEvaluation_subsingleton` | uniqueness inside the current legacy-subset evaluation carrier when one exists |
| `Cost.coordinate_le_score` | each of the 36 charged coordinates is ≤ the canonical score |
| `Cost.CanonicalObjective.monotone` | componentwise ≤ implies score ≤ |
| `Wasm.mem_successors_iff_step` | the legacy `Wasm.Subset` successor enumerator is its subset `Step` relation |
| `Wasm.encode_decode_roundtrip` | canonical binary round-trip for every representable public amended-Core `Wasm.Module` |
| `Wasm.costed_run_iff_plain_run` | legacy `Wasm.Subset` cost instrumentation is transparent |
| `Atlas.semantic_closure_least` | least closure, and it equals the derivation closure |
| `Atlas.incremental_eq_full_rebuild` | incremental accumulation = full rebuild for coherent unscoped state bodies |
| `Atlas.universalCoverCompleteCheck_scope_blind` | the seal cannot stand in for coverage |

`coordinate_le_score` is load-bearing twice over: it makes every score sublevel
finite, and it bounds minimizers to a finite carrier so the argmin exists.

## What is not proved, and what that now means

The generic finite-argmin lemma is proved under explicit nonemptiness and
decision hypotheses. It does not instantiate the released public-Core universe,
construct its evaluation, cover its cost sublevel, select release bytes, or
identify a committed artifact. Release-scope optimality, coverage/lower-bound,
selection, and byte identification therefore remain open:

| | |
| --- | --- |
| `UV-001` / `LB-001` | complete release-universe coverage or an attained universal lower bound |
| `GO-006` | nonemptiness — one concrete module with proofs of the three extensional predicates (SPEC §13 Phase B) |
| `GO-007` | identification — the committed literal equals the selected bytes |
| `WS-001` | full public Core validation/execution/successor/progress/cost closure |
| `BI-002` | the compiler covers all four arithmetic modes, not only modular-`u32` |

Nothing outstanding is stubbed, axiomatized, or assumed as the required
proposition. Exact release declarations are absent where omitted; present
weaker/amended or choice-tainted declarations are explicitly uncredited, and
the registry records the obligations as `open`.

## Scope of the word "optimal"

Every use of "globally optimal" in this repository refers to the exact abstract
UOR-Wasm cost objective defined in `SPEC.md` §9 — a weight-one sum over 36 charged
coordinates. **It is not a claim about physical latency on any engine or
processor.** Core WebAssembly specifies behavior, not host latency. No benchmark,
throughput measurement, or cross-engine run can discharge it.

## Pinned authorities

| Authority | Pin | Verified |
| --- | --- | --- |
| UOR-GNAF | `UOR-GNAF-v1-draft.2.md`, SHA-256 `5c34…200a` | ✅ by content |
| Lean | `leanprover/lean4:v4.30.0`, commit `d024af09…c622` | ✅ by toolchain |
| WebAssembly Core | wg-3.0, commit `9d360199…74aa` | ✅ vendored, 374 files, by content |
| Repository baseline | `fdd58db98edf5b0a28c04bada3e78cef99adece4` | ✅ |

Digests are recomputed from file content by the release checks (`just vendor` and
`just vv`), never trusted as strings.

## Layout

| Path | What it is |
| --- | --- |
| `SPEC.md` | the normative implementation contract |
| `CERTIFICATION.md` | the terminal answer and obligation ledger |
| `authority/` | pinned immutable authorities and the frozen `WGG-GO-1` proposition |
| `WasmGemmGnaf/Cost/` | cost vectors and the canonical proper objective |
| `WasmGemmGnaf/Foundation/` | canonical identity, ordering, result algebra |
| `model/claims.json` | the claim registry; every claim carries its level |

## Claim discipline

Claim levels are load-bearing (`SPEC.md` §17.1). Only `formalProof` supports the
words "proved", "theorem", or "globally optimal". `authority`, `buildEvidence`,
`measurement`, and `open` do not, and no test or benchmark promotes a claim across
that line.

## Licence

Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
