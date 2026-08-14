/-
  Theorems: the cost algebra and the proper-objective bounds.

  This module is an INDEX.  Every declaration restates a proposition already
  proved in `WasmGemmGnaf/Cost/` and closes it by `exact`-ing the original, so
  SPEC §15's required-name list is checkable against full statements in one
  place.

  ## Exact SPEC §15 declarations discharged here

  | SPEC §15 name                        | discharged by                          |
  |--------------------------------------|----------------------------------------|
  | `Cost.transition_accounting_positive`| `Theorems.transition_accounting_positive` |
  | `Cost.objective_sublevel_finite`     | `Theorems.objective_sublevel_finite`   |

  `Theorems.module_bytes_exact` is a proved projection from the repository's
  parameterized `Cost.ExactAggregateCost`.  SPEC §9.1 instead binds the public
  profile, bytes, and `Wasm.Module`, and derives decoding, validation, and static
  charges from those objects.  No bridge from that public-Core predicate is
  proved, so the required `Cost.module_bytes_exact` remains outstanding.

  ## Additional proved results indexed here (not on the §15 list)

  * `coordinate_le_score` and `proper_coordinate_le_score` — SPEC §9.2's
    properness hinge: every one of the 36 charged coordinates is bounded by the
    score.  This is what makes every score sublevel finite, and is what the
    coverage construction of SPEC §10.3 would rest on.
  * `canonical_objective_monotone` and `proper_objective_monotone` — SPEC §9.3
    monotonicity of the score under the componentwise cost order.
  * The SPEC §9.1 sequential-composition laws: `sequentialCompose_zero_left`,
    `sequentialCompose_zero_right`, `sequentialCompose_assoc`,
    `sequentialCompose_le_left`, `sequentialCompose_le_right`,
    `sequentialCompose_mono`, and the positivity bound
    `total_sequentialCompose_ge`.  Sums on cumulative coordinates, maxima on the
    three peaks; associativity is what makes trace cost independent of how the
    trace is bracketed.
  * `sublevelEnumeration_length` — the sublevel enumeration is exactly the
    finite product of the 36 coordinate ranges `{0, …, u}`.
  * `exact_aggregate_unique`, `raw_charge_le_dynamicSum`,
    `raw_charge_le_dynamicMax` — accounting facts for the repository's
    parameterized aggregate predicate that sit beside `module_bytes_exact`:
    the exact aggregate determines the whole
    cost vector, and no raw invocation's charge escapes either aggregate.
  * `transition_accounting_strict` — the strict form of positive accounting.

  ## Scope of `module_bytes_exact` (anti-vacuity note)

  `Cost.ExactAggregateCost` takes `decodes : Prop`, `decodeSteps`,
  `validationSteps` and `staticDataBytes` as *parameters* rather than computing
  them from a mechanized Core 3.0 decoder and validator (see the doc comment on
  the definition in `Cost/Aggregate.lean`).  So `module_bytes_exact` says: **if**
  a cost vector is exact for given bytes under that predicate, **then** its
  `moduleBytes` coordinate is literally `bytes.size`.  It does not by itself
  establish that any particular released artifact's cost vector is exact — that
  needs a baseline, and is `O-4`/`O-6`.

  ## SPEC §15 Cost declaration outstanding

  `Cost.module_bytes_exact` remains outstanding at the public-Core proposition.
  The exact released artifact and competitor application are also open under
  `O-3`, `O-4`, and `O-5`, as recorded in `Theorems/Status.lean`.
-/
import WasmGemmGnaf.Cost.Vector
import WasmGemmGnaf.Cost.Event
import WasmGemmGnaf.Cost.Aggregate
import WasmGemmGnaf.Cost.Objective
import WasmGemmGnaf.Cost.Proper

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

open WasmGemmGnaf.Cost

/-! ## SPEC §9.1: the sequential composition algebra -/

/-- The zero cost vector is a left unit for sequential composition. -/
theorem sequentialCompose_zero_left (v : DynamicVector) :
    sequentialCompose DynamicVector.zero v = v :=
  Cost.sequentialCompose_zero_left v

/-- The zero cost vector is a right unit for sequential composition. -/
theorem sequentialCompose_zero_right (v : DynamicVector) :
    sequentialCompose v DynamicVector.zero = v :=
  Cost.sequentialCompose_zero_right v

/-- **SPEC §9.1.**  Sequential composition is associative: sums on the
cumulative coordinates, maxima on the three peaks.  Trace cost therefore does
not depend on how the trace is bracketed. -/
theorem sequentialCompose_assoc (a b c : DynamicVector) :
    sequentialCompose (sequentialCompose a b) c
      = sequentialCompose a (sequentialCompose b c) :=
  Cost.sequentialCompose_assoc a b c

/-- Composition never loses the first operand's charge. -/
theorem sequentialCompose_le_left (a b : DynamicVector) :
    DynamicVector.ComponentwiseLE a (sequentialCompose a b) :=
  Cost.sequentialCompose_le_left a b

/-- Composition never loses the second operand's charge. -/
theorem sequentialCompose_le_right (a b : DynamicVector) :
    DynamicVector.ComponentwiseLE b (sequentialCompose a b) :=
  Cost.sequentialCompose_le_right a b

/-- **SPEC §9.1.**  Sequential composition is monotone in both arguments. -/
theorem sequentialCompose_mono {a a' b b' : DynamicVector}
    (ha : DynamicVector.ComponentwiseLE a a')
    (hb : DynamicVector.ComponentwiseLE b b') :
    DynamicVector.ComponentwiseLE (sequentialCompose a b) (sequentialCompose a' b') :=
  Cost.sequentialCompose_mono ha hb

/-- Positive accounting: composing a charge onto a running cost increases the
running total by at least the additive part of that charge. -/
theorem total_sequentialCompose_ge (a b : DynamicVector) :
    a.total + b.additiveTotal ≤ (sequentialCompose a b).total :=
  Cost.total_sequentialCompose_ge a b

/-- **SPEC §15, `Cost.transition_accounting_positive`.**  Composing a charged
event onto a running cost raises the running total by at least the weight that
event claims: no charged transition is absorbed for free. -/
theorem transition_accounting_positive (v : DynamicVector) (e : Event) :
    v.total + e.weight ≤ (sequentialCompose v e.charge).total :=
  Cost.transition_accounting_positive v e

/-- The strict form: every charged transition strictly increases the running
total, so a nonterminating run cannot hold its charge constant. -/
theorem transition_accounting_strict (v : DynamicVector) (e : Event) :
    v.total < (sequentialCompose v e.charge).total :=
  Cost.transition_accounting_strict v e

/-! ## The repository's parameterized aggregate

`ExactAggregateCost bytes decodes decodeSteps validationSteps staticDataBytes
repetitions dynamicFor cost` takes decodability and the three static quantities
as parameters.  It is weaker than SPEC §9.1's public-Core predicate, which binds
them to a profile and module.  The results below are conditional statements
about this repository predicate and do not bridge that gap. -/

/-- A projection from the repository's parameterized aggregate predicate: a
cost vector exact under its supplied parameters records `bytes.size`.  This is
not the public-Core SPEC §15 discharge. -/
theorem module_bytes_exact {Raw : Type} [Foundation.Fintype Raw]
    {bytes : ByteArray} {decodes : Prop}
    {decodeSteps validationSteps staticDataBytes repetitions : Nat}
    {dynamicFor : Raw → DynamicVector} {cost : CompleteSystemCost}
    (h : ExactAggregateCost bytes decodes decodeSteps validationSteps
      staticDataBytes repetitions dynamicFor cost) :
    cost.static.moduleBytes = bytes.size :=
  Cost.module_bytes_exact h

/-- Exactness determines the whole cost vector, not just its size coordinate:
two vectors exact for the same data are equal.  This is what stops
`module_bytes_exact` from being satisfiable by a vector that is honest about
size and free everywhere else. -/
theorem exact_aggregate_unique {Raw : Type} [Foundation.Fintype Raw]
    {bytes : ByteArray} {decodes : Prop}
    {decodeSteps validationSteps staticDataBytes repetitions : Nat}
    {dynamicFor : Raw → DynamicVector} {cost cost' : CompleteSystemCost}
    (h : ExactAggregateCost bytes decodes decodeSteps validationSteps
      staticDataBytes repetitions dynamicFor cost)
    (h' : ExactAggregateCost bytes decodes decodeSteps validationSteps
      staticDataBytes repetitions dynamicFor cost') :
    cost = cost' :=
  Cost.exact_unique h h'

/-- Full-domain accounting: every raw invocation's charge appears in the
aggregated dynamic sum, so no input is charged off the books. -/
theorem raw_charge_le_dynamicSum {Raw : Type} [Foundation.Fintype Raw]
    {bytes : ByteArray} {decodes : Prop}
    {decodeSteps validationSteps staticDataBytes repetitions : Nat}
    {dynamicFor : Raw → DynamicVector} {cost : CompleteSystemCost}
    (h : ExactAggregateCost bytes decodes decodeSteps validationSteps
      staticDataBytes repetitions dynamicFor cost) (a : Raw) :
    DynamicVector.ComponentwiseLE (dynamicFor a) cost.dynamicSum :=
  Cost.raw_charge_le_dynamicSum h a

/-- Full-domain accounting for the peak coordinates: every raw invocation's
charge is under the aggregated dynamic maximum. -/
theorem raw_charge_le_dynamicMax {Raw : Type} [Foundation.Fintype Raw]
    {bytes : ByteArray} {decodes : Prop}
    {decodeSteps validationSteps staticDataBytes repetitions : Nat}
    {dynamicFor : Raw → DynamicVector} {cost : CompleteSystemCost}
    (h : ExactAggregateCost bytes decodes decodeSteps validationSteps
      staticDataBytes repetitions dynamicFor cost) (a : Raw) :
    DynamicVector.ComponentwiseLE (dynamicFor a) cost.dynamicMax :=
  Cost.raw_charge_le_dynamicMax h a

/-! ## SPEC §9.2: every coordinate is bounded by the score -/

/-- **SPEC §9.2, `coordinate_le_score`.**  For the canonical all-weights-one
objective every one of the 36 charged coordinates is bounded by the score.  This
is the property that makes every score sublevel finite. -/
theorem coordinate_le_score (c : ArtifactVector) :
    ∀ co : ArtifactCoordinate, co.value c ≤ CanonicalObjective.score c :=
  Cost.coordinate_le_score c

/-- The same bound for an arbitrary proper objective, not only the canonical
one: no proper objective leaves any charged coordinate free. -/
theorem proper_coordinate_le_score {Profile Problem : Type} {P : Profile} {G : Problem}
    (objective : ProperObjective P G) (c : CompleteSystemCost) (co : ArtifactCoordinate) :
    co.value c ≤ objective.score c :=
  ProperObjective.coordinate_le_score objective c co

/-- Module size is bounded by the score: the size half of properness. -/
theorem moduleBytes_le_score (c : ArtifactVector) :
    c.static.moduleBytes ≤ CanonicalObjective.score c :=
  Cost.moduleBytes_le_score c

/-! ## SPEC §9.3: monotonicity -/

/-- **SPEC §9.3.**  The canonical score is monotone for the componentwise
order. -/
theorem canonical_objective_monotone {a b : ArtifactVector}
    (h : ComponentwiseLE a b) :
    CanonicalObjective.score a ≤ CanonicalObjective.score b :=
  Cost.CanonicalObjective.monotone h

/-- **SPEC §9.3, `Cost.ProperObjective.monotone`.**  Every proper objective is
monotone for the componentwise order. -/
theorem proper_objective_monotone {Profile Problem : Type} {P : Profile} {G : Problem}
    (objective : ProperObjective P G) {a b : CompleteSystemCost}
    (h : ComponentwiseLE a b) : objective.score a ≤ objective.score b :=
  ProperObjective.monotone objective h

/-- Weighted evaluation is monotone for any objective body, which is the general
fact the two statements above specialise. -/
theorem evaluate_monotone (body : ObjectiveBody) {a b : ArtifactVector}
    (h : ComponentwiseLE a b) : evaluate body a ≤ evaluate body b :=
  Cost.evaluate_monotone body h

/-! ## SPEC §9.3: sublevel finiteness -/

/-- **SPEC §15, `Cost.objective_sublevel_finite`.**  Every score sublevel of a
proper objective is finite: `sublevelEnumeration u` is an explicit finite list
containing every cost vector whose score is at most `u`.

The proof is the injection into the finite product of the 36 coordinate ranges
`{0, …, u}`: each coordinate of a sublevel member is bounded by `u` by
`proper_coordinate_le_score`, and the coordinate map is a retraction, so no
sublevel member escapes the enumeration. -/
theorem objective_sublevel_finite {Profile Problem : Type} {P : Profile} {G : Problem}
    (objective : ProperObjective P G) (u : Nat)
    (c : CompleteSystemCost) (h : objective.score c ≤ u) :
    c ∈ sublevelEnumeration u :=
  Cost.objective_sublevel_finite objective u c h

/-- The sublevel enumeration is exactly the finite product of the 36 coordinate
ranges `{0, …, u}`, so the finiteness above is an explicit cardinality, not a
mere existence claim. -/
theorem sublevelEnumeration_length (u : Nat) :
    (sublevelEnumeration u).length = (u + 1) ^ 36 :=
  Cost.sublevelEnumeration_length u

/-- Any coordinatewise-bounded cost vector is enumerated, independently of any
objective. -/
theorem mem_sublevelEnumeration {u : Nat} {c : ArtifactVector}
    (h : ∀ co : ArtifactCoordinate, co.value c ≤ u) :
    c ∈ sublevelEnumeration u :=
  Cost.mem_sublevelEnumeration h

end WasmGemmGnaf.Theorems
