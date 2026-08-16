# Certification outcome — WGG-GO-1

Answer class: **`WorkloadIncomplete`** (UOR-GNAF v1-draft.2 §10.9 total answer carrier)

This document is the repository's exact terminal answer for the requested claim.
It is not a status report, a roadmap, or a promise. Under the pinned authority it
is a *conforming terminal result*: UOR-GNAF §10.9 makes `WorkloadIncomplete` a
branch of the total answer type, and §13.3 requires it here rather than a label:

> Computational difficulty does not weaken exactness. A machine MAY return an
> honest weaker claim; it MUST NOT return an unproved global label.

SPEC.md §1 states the same rule for this repository:

> If the universal proof cannot be closed, the correct repository outcome is
> `incomplete`; weakening the universe, silently strengthening the machine,
> omitting cost, or changing the public wording is forbidden.

Accordingly **the requested proposition is not weakened**. The authority target
quantifies over all finite byte sequences and charges every objective coordinate
at weight one. The repository does not currently provide its release
instantiation or the required `Release.artifactBytes`.

---

## 1. RequestedClaimScope

The requested claim target is exactly
`authority/global-optimality-WGG-GO-1.json`:

```
GlobalOptimal
  Release.wasmProfile
  Release.gemmProblem
  Release.costObjective
  Release.artifactBytes
```

with the quantifier in conjunct 7 ranging over **all** finite byte sequences that
decode and validate under the pinned profile — not GNAF plans, not registered
kernels, not attention-indexed candidates. `Release.artifactBytes` is deliberately
absent until a computable public-Core compiler, selection, and committed artifact
exist.

## 2. Obligation ledger

UOR-GNAF §19.3 fixes the required evidence for this claim class:

| Obligation | Required evidence | Status |
|---|---|---|
| Global scalar optimum | complete admission, **attainment**, and **exhaustive / proof-complete / no-improver coverage *or* a universal lower bound attained** | **OUTSTANDING** |

Decomposed against SPEC §10:

| # | Sub-obligation | Status |
|---|---|---|
| O-1 | Competitor universe defined extensionally over all byte strings | authority target fixed; public-Core release migration outstanding |
| O-2 | Sublevel is finite and decidable | abstract finiteness infrastructure exists; exact released admission/decision outstanding |
| O-3 | Complete admission (`SystemEvaluationRel` sound/complete/functional) | outstanding, gated on O-6 |
| O-4 | Attainment: shipped bytes' exact score computed | outstanding, gated on O-6 |
| O-5 | **Universal lower bound `F`, attained** | **OUTSTANDING — no known technique** |
| O-6 | Mechanized Wasm Core 3.0 semantics (GC, EH, SIMD, tail calls) | outstanding — engineering; see §2.1 |
| O-7 | Non-degenerate public-Core release evaluation (`GO-008`) and exact per-event cost table (`CO-006`) | **OUTSTANDING**; legacy subset seam evidence is non-release-applicable |

Release gate step 9 fails. It is *supposed* to fail. See §6.

### 2.1 O-6 is larger than the module count suggests

A large module and theorem count (see `CONFORMANCE.md` for the live inventory) can
create a misleading impression of proximity. Three scope facts, all discovered by
audit rather than reported by construction, bound what has actually been built:

**The public Core spine is partly mechanized, but the release chain is not
closed.** `Wasm.Module` now carries a Core module with an amended declarative
binary witness. The public decoder and computational encoder are proved sound,
complete and round-tripping against that same relation, and `Artifact.emit` uses
that encoder. The corrected declarative validation hierarchy and the executable
validator's soundness are kernel checked. Full validator completeness, exact
whole-machine successor enumeration, typed progress, and the complete SPEC §7.5
event-cost correspondence remain open. The older `Wasm.Subset` machine is retained
only as legacy support; none of its byte/evaluation witnesses is release evidence.

**The compiler still cannot emit the required public artifact.** `GNAF.compile`
returns `Wasm.Subset.Module`, not the public Core carrier, and its current target
does not implement all four SPEC §8.2 arithmetic modes. The direct, bounded Core
compiler and its refinement/resource/cost proofs are the open `BI-010`/`BI-002`
work. Consequently there is no released Core GEMM byte string on which to attain
an upper bound, construct the exact sublevel, or instantiate the abstract argmin.

**There is no release theorem or release evaluation witness.** The former
subset-only `witnessBytes`/`baselineBytes` and `SystemEvaluation` theorem cones
were removed after audit: they quantified over the wrong module, decoder, event,
and cost carriers. `GO-008` is open. The repository therefore states no
`Universal.GlobalOptimal` result at the SPEC §9 release scope, conditional or
otherwise, and it does not substitute a legacy witness to make the antecedent
inhabited.

`GNAF.compile_validates` is *not* vacuous — it holds for every `CheckedPlan` — and
the in-subset results are no longer unwitnessed either: `GNAF.gemmWitness` is a
concrete `1×1×1` modular-`u32` GEMM plan that classifies the raw ABI header,
dispatches on the layout class, runs the blocked traversal and the `i`/`j` loop
nest, accumulates the `k` reduction under the modular contract, sets the status
word, stores the product into the declared `C` region and publishes it. It is
proved in `Plan.inReleasedSubset`, type checked, compiled, validated and free of
`unreachable`; its accumulator is proved to hold exactly `(A·B) mod 2^32`; and
`GNAF.gemmWitness_writes_C` reads the `C` region back little-endian at the stored
width and gets `alpha · A · B + beta · C mod 2^32` for the `alpha` and `beta`
this descriptor declares (`BI-003` and `BI-005`, both discharged; `BI-004` is
the store constructor's own load-after-store law). The witness therefore *writes*
its result: the earlier limitation — that SPEC §11.1's plan language had no
constructor moving a register into memory — no longer holds, `Plan.storeReg` is
that constructor and `GNAF.storeReg_reads_back` is its load-after-store law.

Three things this still does not reach, recorded on `BI-003`: the descriptor
declares `alpha = 1` and `beta = 0` and the plan carries no scaling node, so it
is that instance of `C ← alpha · op(A) · op(B) + beta · C` and not the general
form; the statement is about `Plan.eval`, not about the emitted Wasm, which is
`compile_refines` and is omitted; and it is one `1×1×1` modular-`u32` shape, not
the scalar-kind × mode × transpose × layout-class family `BI-002` still records
as outstanding. Phase B is thus begun, not achieved.

## 2.2 External audit findings (accepted)

An external audit at commit `c44a06d` found the following. All were verified and
all are accepted; several were missed by this repository's own auditing.

**The inventory materially understated the proof surface.** At commit `c44a06d`,
`model/claims.json` showed 10 outstanding rows while the then-58-name SPEC §15
list yielded 22 discharged and 36 outstanding. `just required` now derives the
live inventory from SPEC.md and queries the compiled environment; its current
counts are intentionally not copied into this historical paragraph. Gate steps
4, 5, 8 and 9 test declaration presence instead of reading a status field. A
hand-maintained JSON status is not evidence.

**CI had never established the exact-SHA build.** `verify.yml` ran
`sha256sum -c authority/uor-gnaf.sha256` from the repository root, but the
checksum file names the authority *without* a directory prefix, so the step failed
and the workflow stopped **before `lake build`**. Neither the build nor the axiom
closure had been established by CI at any commit. Fixed.

**The decider was noncomputable and its completeness was circular; it is now
deleted.** `Release.evaluateClassically` assumed `Nonempty (SystemEvaluation …)`
and extracted a witness by `Classical.choice`; `Release.decider` wrapped it. It
decoded, validated, enumerated and executed nothing, and the completeness theorem
took an existing evaluation as an *argument* rather than proving one exists. SPEC
§19 excludes noncomputable definitions from the product/proof path. Both
definitions, every theorem stated against them, and the `Theorems.release_*` and
`Artifact.exists_globalOptimal_of_baseline_semantics` results that depended on
them have been **removed from the repository** — not relabelled, not retained
behind a checker, and not replaced by a substitute evaluator over the witness
semantics. `UV-003` is **open**, `just releasepath` passes, and no classical
stand-in for the implemented explorer remains.

**The release profile is the i32 witness profile.** `Release.wasmProfile` is
`Wasm.unitWitnessProfile`, and its cost table is `canonicalCostTableUnits` rather
than SPEC §7.5's `Release.wasmCostTableBody`. The syntactic `∀ ByteArray` in
`GlobalOptimal` therefore does not yet range over the authority-required Core 3.0
competitor universe. Recorded as `WS-003`.

**The emitter cannot refine the plan.** `Compile.lean`'s `storeReg`/`loadReg`
clauses bind width as `_` and always emit full-word `storeW`/`loadW`, so the
emitted code does not respect the declared width `storeReg_reads_back` states.
The ABI installs raw bytes at the supplied pointer while compilation treats cell
`i` as an `i32` at absolute address `4*i` with no repacking. Abstract `loopReg`
snapshots its bound once; emitted code re-reads the extent each test. The shipped
baseline still compiles `gemmWitnessChecked`, not `gemmKernel`. So every
`gemmKernel_*` theorem is about `Plan.eval` only, and `compile_refines`,
`compile_cost_exact` and the termination bound are legitimately open. Recorded as
`BI-008`.

**Crux delta of the previous commit: zero.** `BI-007` was real progress on the
abstract plan language, but it closed no executable evaluator, no compiled
baseline, no universal coverage, no lower bound, no selected artifact and no final
theorem. That assessment is correct and is recorded here rather than argued with.

## 3. What is discharged

Kernel-checked under Lean 4.30.0; the live inventory is the first line of
`CONFORMANCE.md`. Zero `sorry`, zero `admit`, zero project-declared `axiom`, zero
`native_decide`, zero `partial`/`unsafe`/`noncomputable` on the proof path.

Layers built: `Foundation`, `Wasm`, `Gemm`, `Cost`, `GNAF`, `Universal`, `Atlas`,
`Artifact`, `Theorems`, `Conformance`.

Load-bearing results:

| Declaration | Content |
|---|---|
| `Wasm.decode_sound`, `Wasm.decode_complete` | public amended-Core decoder equivalence with `BmoduleA` |
| `Wasm.encode_decode_roundtrip`, `Artifact.decode_emit` | computational public Core encoding and exact decode/emit round trip |
| `Core.Binary.BmoduleA.wf_of` | every amended binary derivation produces a syntactically well-formed Core module |
| `Core.Validate.validate_sound` | the current executable Core validator implies the corrected declarative hierarchy |
| `Core.Context.decHeaptypeSubN_complete_of_sourceTypeNodeA` | amended heap-subtype decision completeness on an explicitly certified ranked source graph |
| `Core.Types_okA.storedTypeSupersRankedA` | the first source type-section rank certificate, with non-wrapping group ranges |
| `Cost.coordinate_le_score` | every one of the 36 charged coordinates is ≤ the canonical score |
| `Cost.moduleBytes_le_score` | module size is bounded by the score (size half of properness) |
| `Cost.CanonicalObjective.monotone` | componentwise ≤ implies score ≤ |
| `Core.vstoreLaneVal_mem_directSuccessors` | the exact lane-store success branch remains enumerable even when the pinned OOB branch overlaps it |
| `Universal.exists_globalOptimal_of_nonempty` | generic classical argmin existence under its explicit nonempty/decision hypotheses — §3.1 |
| `Atlas.semantic_closure_least` | least closure, and it *equals* the derivation closure |
| `Atlas.incremental_eq_full_rebuild` | incremental accumulation = full rebuild for coherent state bodies in their own scope; exact AMD-003 required-name theorem |
| `Atlas.universalCoverCompleteCheck_scope_blind` | **hardening** — see §3.2 |

`coordinate_le_score` is the hinge: it is what makes every score sublevel finite,
and it is what SPEC §10.3's coverage construction rests on.

### 3.1 Generic argmin existence is proved; release instantiation is open

`Universal.exists_globalOptimal_of_nonempty` is a valid abstract theorem: under
its explicit nonempty admissible-set and decision hypotheses, the natural-valued
objective and canonical byte order yield an argmin. It is infrastructure, not a
proof of the SPEC §9 released WebAssembly objective. The repository has no
public-Core decider satisfying those hypotheses, no semantically correct emitted
Core GEMM with an exact `SystemEvaluation`, and no selected committed byte string.

`Universal.systemEvaluation_subsingleton` shows uniqueness only inside the
current legacy-subset evaluation carrier once an evaluation exists; it neither
constructs one nor discharges public-Core relation functionality. The deleted
legacy subset evaluation must not be used to inhabit the release premise.

The release residue therefore still includes both:

- `GO-006`/`GO-008`: construct one public-Core emitted GEMM that is profile valid,
  semantically correct, resource feasible, and equipped with the exact released
  all-branch evaluation; and
- `GO-007`/`WGG-GO-1`: prove the SPEC §9 total-cost lower-bound/coverage and
  canonical selection clauses, and identify the committed bytes with that
  selection.

Axiom closure by `#print axioms`: `propext`, `Quot.sound`, and
`Classical.choice`, named individually as SPEC §4 requires. Choice is permitted
only for Prop-level results. The compiled audit also finds it in the Type-valued
input-enumeration witnesses `Gemm.valid_input_finite`,
`Gemm.raw_input_finite`, and `Universal.input_enumerator_complete`; those three
are therefore uncredited and `UV-004` remains open. No `sorryAx`.

### 3.2 Hardening: the seal cannot stand in for coverage

An adversarial audit found the most attractive route to a false global-optimality
claim in this repository, and it was closed by **strengthening**, not by softening
any wording.

`Atlas.universalCoverCompleteCheck` — the seal's universal-cover checker — verifies
*bookkeeping consistency*: that the recorded cover matches the recorded candidate
facts. It never quantifies over the byte universe, and it is satisfiable by a cover
that records nothing at all. Left implicit, a reader could take a passing seal as
evidence of universal coverage.

`Atlas.universalCoverCompleteCheck_scope_blind` now makes this kernel-checked: the
check is a function of exactly the recorded `searchPartitions`, `candidateFacts`
identities, and `partitionCoverRoot`. Two states agreeing on those agree on the
check, whatever byte strings exist. **Therefore no proposition quantified over
`ByteArray` follows from the seal check.**

This is why `Atlas.seal_implies_universal_coverage` (a SPEC §15 required
declaration) is **absent** rather than derived: deriving it from this check would
be unsound. Claim `AT-002` records the absence; falsifier `M7` fails if anyone
later supplies it without a real proof, or removes the blindness lemma that makes
the absence principled. This is exactly the UOR-GNAF §18 non-claim that *index
presence or provenance alone proves eligibility, correctness, or optimality*.

### 3.3 Hardening: the forbidden-construct scan

The source scan initially matched any identifier containing `sorry`, so it
false-positived on `Conformance/AxiomAudit.lean`'s `sorryAx` constructor — which
exists precisely in order to *reject* that axiom. A gate that cries wolf gets
disabled, so the pattern was tightened to token boundaries. It is now clean on the
real tree and still catches a planted `theorem p : True := by sorry`.

The decisive audit remains `#print axioms` over the compiled environment
(`just axioms`), per SPEC §19; the text scan is defence in depth.

Authority pins verified by content, not by trusting a string:

| Authority | Status |
|---|---|
| UOR-GNAF v1-draft.2 | SHA-256 `5c34…200a` — **matches the SPEC §4 pin exactly** |
| Lean toolchain | `v4.30.0`, commit `d024af09…c622` — **matches the SPEC §4 pin exactly** |
| WebAssembly Core wg-3.0 `9d360199…74aa` | vendored and content-digest checked; registered AMD/DEV repairs remain explicit and mutation-tested |

## 4. Why O-5 is outstanding

This section was adversarially reviewed. Earlier framings were narrowed or
withdrawn where the formal statements did not support them.

### 4.1 What is *not* the obstruction

**What the bilinear lemma actually proves.** `LB-002`
(`Universal.BilinearScheme.chargedOps_lower_bound`) formalizes one restricted
accounting fact. For a modeled bilinear scheme with `r` products, A-side supports
`p_k ≥ 1`, B-side supports `w_k ≥ 1`, and reconstruction support totaling at least
27, total charged operations satisfy

```
T ≥ r + 18
```

The naive rank-27 scheme witnesses equality at 45 charged operations. This shows
the formula is sharp at that point, not that naive is minimal among lower-rank
schemes. For `r = 19..23` the theorem gives only `T ≥ 37..41`, so it does not prove
that resolving the open tensor-rank interval is irrelevant to the release optimum.
Laderman's particular 23-product/98-addition construction costs 121, but that
example does not exclude a different lower-rank construction.

**Not asymptotic circuit lower bounds.** Weight-one module bytes creates a
minimal-*total-cost* obligation, not a minimal-program-size one, so the open
problem of superlinear circuit lower bounds for explicit functions is the wrong
authority to invoke. **Refuted, medium confidence.**

**Abstract finiteness is not constructive enumeration.** A bounded byte carrier is
finite as a proposition. The release-scope duplicate-free executable enumeration,
input witnesses, evaluator decision, and exact coverage theorem remain open; the
choice-tainted input enumerators are explicitly uncredited.

### 4.2 What *is* the obstruction

One binding route is the UOR-GNAF §19.3 disjunct: **a universal lower bound,
attained.** Under that route closure requires both of:

1. a proved floor `F` on the *total charged cost* of every correct, feasible,
   same-profile WebAssembly module over the complete raw-invocation domain; and
2. shipped bytes whose exact score **equals** `F`.

Neither half is proved here. Proof-complete partition or no-improver coverage are
the alternative routes listed in §5.

**No exhaustive or analytic certificate is present.** Properness yields bounded
sublevels once the public evaluator and exact cost model exist, but this repository
does not yet provide the constructive public-carrier enumeration/decision theorem
or a complete checked partition. Nor does it provide an analytic lower bound tight
at the shipped bytes. Claims about physical infeasibility are not used as proof and
receive no registry credit.

**A further complication, recorded because it is easy to miss.** Under
charge-everything accounting over a *finite* input domain, the optimum may not be
an arithmetic algorithm at all. Dispatch is charged, so shape-specialized kernels
are penalized; and for narrow scalar kinds a lookup table can undercut arithmetic
on `staticDataBytes` against `sumScalarOps`. The argmin is a discrete trade-off
across 36 coordinates, not an algebraic invariant. Tensor-rank accounting alone
therefore neither identifies the optimum nor supplies the all-module lower bound.

**Residual uncertainty, stated honestly.** The `LB-002` floor covers only its
modeled bilinear schemes; non-bilinear programs and arbitrary WebAssembly modules
are outside that theorem. O-5 is not proved impossible, and no generic hardness
result may dismiss this bounded profile. It is filed as an outstanding obligation
with no known discharge, never as an impossibility theorem.

## 5. What would discharge O-5

Recorded so the ledger is falsifiable rather than rhetorical:

- an analytic lower-bound theorem on total charged cost over the full domain,
  tight enough that a constructible module attains it; **or**
- a proof-complete symbolic partition (SPEC §10.4 `dominated`) covering the sublevel
  without per-module enumeration; **or**
- a `no-improver` coverage argument in the UOR-GNAF §19.3 sense.

Any of these, plus O-6, closes the claim. Absent all of them the answer stays
`WorkloadIncomplete`.

## 6. What must not happen

Per UOR-GNAF §18, these remain explicit **non-claims**, and none may be presented
as discharging WGG-GO-1:

- that incomplete saturation, search, autotuning, benchmarking, or learned
  selection proves an optimum;
- that an internal plan optimum proves the containing complete system globally
  optimal;
- that a restricted-universe optimum applies to an omitted parent universe;
- that **correctness may be weakened because complete optimization is expensive**.

Specifically forbidden here: narrowing the competitor universe to GNAF plans and
renaming the result; dropping a cost coordinate to make a floor reachable;
restricting the input domain to make the sum tractable; or asserting
`released_wasm_gemm_gnaf_global_optimal` with any hypothesis attached. Each would
produce a different, weaker proposition wearing the release theorem's name.

Each authority schema name is now mechanically accounted rather than silently
omitted. `WasmGemmGnaf/Conformance/Schema.lean` closes exact entries
definitionally, so a narrowed quantifier, dropped conjunct, added hypothesis, or
substituted scoped predicate stops elaborating. Definitions still using a legacy
carrier are marked as explicit uncredited gaps; `just schema` prints the public
schema OPEN while any remain. The inventory itself is read from
`authority/global-optimality-WGG-GO-1.json`, not transcribed here.

## 7. Reproducing this outcome

```
just claims     # registry: WGG-GO-1 present, status incomplete
just axioms     # axiom closure of every proved declaration
just schema     # exact bindings plus explicit uncredited schema gaps
just vv         # full gate; FAILS on open prerequisites and the absent step-9 theorem
```

`just vv` failing is the correct observable behavior of a conforming repository in
this state. A green `just vv` here would mean the gate had been weakened.
