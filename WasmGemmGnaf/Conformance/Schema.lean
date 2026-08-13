/-
  Exact schema binding for the scope-critical definitions.

  SPEC §1 and `authority/global-optimality-WGG-GO-1.json` require the conformance
  gate to compare the *compiled, unfolded* declaration bodies against the frozen
  authority schema, and say plainly that recording the implementation's own
  proposition without that comparison is insufficient.

  A name check cannot do that: a weaker or conditional proposition under the right
  name passes it. What follows spells each scope-critical definition out in full
  and closes the equivalence by `Iff.rfl` (propositions) or `rfl` (data), so the
  binding is *definitional*. If anyone narrows a quantifier, drops a conjunct,
  adds a hypothesis, swaps the competitor domain for a scoped predicate, or edits
  a field out of a record, these stop elaborating.

  THE LIST IS NOT MAINTAINED HERE.  `authority/global-optimality-WGG-GO-1.json`
  lists the `scopeCriticalDefinitions`; `xtask schema` reads that array and fails
  naming any entry with no binding below.  The JSON is therefore the source of the
  list and the Lean elaborator is the comparator, which is what the audit asked
  for: no hand-maintained checklist decides coverage, and no string comparison
  decides agreement.  The array currently holds fourteen names — one more than the
  count that has been quoted in review — which is precisely why nothing downstream
  transcribes it.

  Each binding is announced by an `authority-binding:` line carrying the exact
  name the authority JSON uses.  That marker is what the tool matches; the
  theorem under it is what Lean checks.

  This is the machine-checked half of the authority gate rule. `just required`
  supplies the inventory half.
-/
import WasmGemmGnaf.Universal.Sublevel
import WasmGemmGnaf.Gemm.Reference

set_option autoImplicit false

namespace WasmGemmGnaf.Conformance

open Universal

-- SPEC §8.3's representability bound on the raw carrier is written as an
-- explicit binder on the theorems that need it, not as a section variable. A
-- section variable attaches silently to bindings that do not need it, and a
-- hypothesis nobody asked for is exactly what these theorems exist to forbid.
variable {P : Wasm.Profile}

/-! ## 1. The decisive predicate -/

/--
**`GlobalOptimal` matches the frozen `WGG-GO-1` schema.**

Every conjunct of SPEC §1 is written out here rather than referenced. The
competitor quantifier is `∀ competitorBytes : ByteArray` in *both* clauses, with
no scope predicate; the lower-bound clause is the conjunction SPEC §1 gives, not
an implication; and the tie-break clause carries `CanonicalBytesLE`.

`Iff.rfl` is the whole proof, which is the point: it holds only while the
definition is *definitionally* this proposition.
-/
-- authority-binding: GlobalOptimal
theorem globalOptimal_matches_authority_schema [Foundation.Fintype (Gemm.RawInvocation P)]
    (S : Setting P) (D : Decider S)
    (O : Cost.ProperObjective P S.problem) (releasedBytes : ByteArray) :
    GlobalOptimal S D O releasedBytes ↔
      (ProfileValid P releasedBytes ∧
       SemanticCorrect S releasedBytes ∧
       SemanticWithinResources S releasedBytes ∧
       ∃ releasedEval : SystemEvaluation S releasedBytes,
         SystemEvaluationRel S D releasedBytes releasedEval ∧
         Correct releasedEval ∧
         Feasible releasedEval ∧
         (∀ competitorBytes : ByteArray,
            ProfileValid P competitorBytes →
            SemanticCorrect S competitorBytes →
            SemanticWithinResources S competitorBytes →
            ∀ competitorEval : SystemEvaluation S competitorBytes,
              SystemEvaluationRel S D competitorBytes competitorEval ∧
              O.score releasedEval.cost ≤ O.score competitorEval.cost) ∧
         (∀ competitorBytes : ByteArray,
            ProfileValid P competitorBytes →
            SemanticCorrect S competitorBytes →
            SemanticWithinResources S competitorBytes →
            ∀ competitorEval : SystemEvaluation S competitorBytes,
              SystemEvaluationRel S D competitorBytes competitorEval →
              O.score releasedEval.cost = O.score competitorEval.cost →
              Foundation.CanonicalBytesLE releasedBytes competitorBytes)) :=
  Iff.rfl

/-! ## 2. The extensional competitor predicates (SPEC §10.1) -/

/-- **`ProfileValid` matches the frozen schema.**  SPEC §17.2 requires the gate to
reject an artifact-specific `ProfileValid`; this pins it to the four extensional
conditions of SPEC §10.1 and nothing else. -/
-- authority-binding: Universal.ProfileValid
theorem profileValid_matches_authority_schema
    (profile : Wasm.Profile) (bytes : ByteArray) :
    ProfileValid profile bytes ↔
      (∃ module : Wasm.Module,
        Wasm.decode bytes = .ok module ∧
        Universal.validateUnder profile module = true ∧
        module.imports = [] ∧
        Universal.HasExactGemmExports profile module) :=
  Iff.rfl

/--
**`SemanticCorrect` matches the frozen schema.**

Unfolded through `SemanticCorrectAt`, `IsMaximalExecution` and
`StartsCostedInvocation`, because that is where the strength lives: the raw
quantifier is over *every* `Gemm.RawInvocation P`, the execution quantifier over
*every* inhabitant of `Wasm.MaximalExecution initial`, and the existential half
is present — so the predicate cannot be satisfied by an empty run relation.
-/
-- authority-binding: Universal.SemanticCorrect
theorem semanticCorrect_matches_authority_schema
    (S : Setting P) (bytes : ByteArray) :
    SemanticCorrect S bytes ↔
      ∀ raw : Gemm.RawInvocation P,
        ((∃ initialization : InitializationObservation P,
           ∃ initial : Wasm.Config,
           ∃ execution : Wasm.MaximalExecution initial,
             (∃ module : Wasm.Module,
               Wasm.decode bytes = .ok module ∧
               Universal.validateUnder P module = true ∧
               S.machine.initialGemmInvocationCosted module
                   (Universal.toWasmInvocation raw) = .ok initialization ∧
               initialization.initial = initial) ∧
             IsMaximalExecutionFrom initial execution) ∧
         ∀ (initialization : InitializationObservation P)
           (initial : Wasm.Config) (execution : Wasm.MaximalExecution initial),
           ((∃ module : Wasm.Module,
               Wasm.decode bytes = .ok module ∧
               Universal.validateUnder P module = true ∧
               S.machine.initialGemmInvocationCosted module
                   (Universal.toWasmInvocation raw) = .ok initialization ∧
               initialization.initial = initial) ∧
            IsMaximalExecutionFrom initial execution) →
           ∃ observation : Wasm.ExecutionObservation,
             HasFiniteObservation execution observation ∧
             S.problem.Accepts raw observation) :=
  Iff.rfl

/--
**`SemanticWithinResources` matches the frozen schema.**

Both halves: no *valid prefix* reaches `maxSteps + 1` — the budget is enforced on
prefixes, so an execution cannot buy time by never becoming maximal — and every
maximal execution is charged componentwise inside the problem's limit, with the
initialization charge sequentially composed in rather than dropped.
-/
-- authority-binding: Universal.SemanticWithinResources
theorem semanticWithinResources_matches_authority_schema
    (S : Setting P) (bytes : ByteArray) :
    SemanticWithinResources S bytes ↔
      ∀ raw : Gemm.RawInvocation P,
        ((¬ ∃ initialization : InitializationObservation P,
            ∃ initial : Wasm.Config,
            ∃ pre : RelationalPrefix initial (S.problem.maxSteps + 1),
              (∃ module : Wasm.Module,
                Wasm.decode bytes = .ok module ∧
                Universal.validateUnder P module = true ∧
                S.machine.initialGemmInvocationCosted module
                    (Universal.toWasmInvocation raw) = .ok initialization ∧
                initialization.initial = initial) ∧ pre.Valid) ∧
         (∀ (initialization : InitializationObservation P)
            (initial : Wasm.Config) (execution : Wasm.MaximalExecution initial),
            ((∃ module : Wasm.Module,
                Wasm.decode bytes = .ok module ∧
                Universal.validateUnder P module = true ∧
                S.machine.initialGemmInvocationCosted module
                    (Universal.toWasmInvocation raw) = .ok initialization ∧
                initialization.initial = initial) ∧
             IsMaximalExecutionFrom initial execution) →
            ∃ costed : CostedExecutionObservation S.semantics initial,
              CostedAs (S := S) execution costed ∧
              Cost.DynamicVector.ComponentwiseLE
                (Cost.sequentialCompose initialization.cost costed.cost)
                S.problem.limit)) :=
  Iff.rfl

/-! ## 3. The evaluation record and its relation -/

/--
**`SystemEvaluation` matches the frozen schema, field for field.**

Structure eta makes the reconstruction definitional, so the binding pins the
*exact* field list: adding a field breaks the constructor application, removing
one breaks the projection, and weakening a field's type breaks the ascription.
`perInput` is total over the raw carrier and `observationsComplete` covers every
maximal execution — neither may be narrowed to a sampled or reachable subset.
-/
-- authority-binding: Universal.SystemEvaluation
theorem systemEvaluation_matches_authority_schema [Foundation.Fintype (Gemm.RawInvocation P)]
    (S : Setting P) (bytes : ByteArray) (E : SystemEvaluation S bytes) :
    E = SystemEvaluation.mk
      (module := (E.module : Wasm.Module))
      (decodeEq := (E.decodeEq : Wasm.decode bytes = .ok E.module))
      (perInput := (E.perInput :
        ∀ raw : Gemm.RawInvocation P, InputEvaluation S E.module raw))
      (observationsComplete := (E.observationsComplete :
        ∀ raw : Gemm.RawInvocation P, (E.perInput raw).CoversEveryMaximalExecution))
      (cost := (E.cost : Cost.CompleteSystemCost))
      (costExact := (E.costExact :
        Cost.ExactAggregateCost bytes (Wasm.decode bytes = .ok E.module)
          (P.body.costTableBody.decodeCost bytes)
          (S.semantics.validationSteps E.module)
          (S.semantics.staticDataBytes E.module)
          S.problem.workloadRepetitions
          (fun raw => (E.perInput raw).resourceVector) E.cost)) :=
  rfl

/-- **`SystemEvaluationRel` matches the frozen schema.**  It is decided by the
*decider* on the bytes alone: `D.evaluate` receives no artifact, no selector and
no conclusion, so the relation cannot be tuned to the released bytes. -/
-- authority-binding: Universal.SystemEvaluationRel
theorem systemEvaluationRel_matches_authority_schema [Foundation.Fintype (Gemm.RawInvocation P)]
    (S : Setting P) (D : Decider S) (bytes : ByteArray)
    (evaluation : SystemEvaluation S bytes) :
    SystemEvaluationRel S D bytes evaluation ↔
      D.evaluate bytes = .complete evaluation :=
  Iff.rfl

/-- **`Correct` matches the frozen schema.**  Over *every* raw invocation and
*every* recorded costed observation of it, with the nonemptiness conjunct
retained: a trap, an uncaught exception or a stuck state appears as a recorded
observation the reference relation rejects, so it falsifies this. -/
-- authority-binding: Universal.Correct
theorem correct_matches_authority_schema [Foundation.Fintype (Gemm.RawInvocation P)]
    {S : Setting P} {bytes : ByteArray} (evaluation : SystemEvaluation S bytes) :
    Correct evaluation ↔
      ∀ raw : Gemm.RawInvocation P,
        (evaluation.perInput raw).observations.elements ≠ [] ∧
        ∀ observation ∈ (evaluation.perInput raw).observations.elements,
          S.problem.Accepts raw observation.observation :=
  Iff.rfl

/-- **`Feasible` matches the frozen schema.**  The bound is on `resourceVector`,
which is the initialization charge composed with the componentwise maximum over
every recorded branch — the worst permitted execution, not a chosen one. -/
-- authority-binding: Universal.Feasible
theorem feasible_matches_authority_schema [Foundation.Fintype (Gemm.RawInvocation P)]
    {S : Setting P} {bytes : ByteArray} (evaluation : SystemEvaluation S bytes) :
    Feasible evaluation ↔
      ∀ raw : Gemm.RawInvocation P,
        Cost.DynamicVector.ComponentwiseLE
          (evaluation.perInput raw).resourceVector S.problem.limit :=
  Iff.rfl

/-! ## 4. The objective (SPEC §9.3) -/

/--
**`Cost.ProperObjective` matches the frozen schema, field for field.**

`sublevelBound` is the conjunct that makes the objective *proper*: every score
sublevel is contained in a declared componentwise resource bound. An objective
that dropped it — leaving code size, execution, memory or advice free — would
still typecheck as a record but would no longer reconstruct here.
-/
-- authority-binding: Cost.ProperObjective
theorem properObjective_matches_authority_schema
    {Profile Problem : Type} {Pr : Profile} {G : Problem}
    (O : Cost.ProperObjective Pr G) :
    O = Cost.ProperObjective.mk
      (body := (O.body : Cost.ObjectiveBody))
      (bodyValid := (O.bodyValid : Cost.EveryCoordinateWeightPositive O.body))
      (boundOfScore := (O.boundOfScore : Nat → Cost.ResourceBounds))
      (sublevelBound := (O.sublevelBound :
        ∀ {c : Cost.CompleteSystemCost} {u : Nat},
          Cost.evaluate O.body c ≤ u → Cost.Within (O.boundOfScore u) c)) :=
  rfl

/-- **`Cost.ProperObjective.score` matches the frozen schema.**  The score is the
*whole* charged vector evaluated against the objective body — not a projection
onto one coordinate, and not a function of anything else. -/
-- authority-binding: Cost.ProperObjective.score
theorem properObjective_score_matches_authority_schema
    {Profile Problem : Type} {Pr : Profile} {G : Problem}
    (O : Cost.ProperObjective Pr G) (cost : Cost.CompleteSystemCost) :
    O.score cost = Cost.evaluate O.body cost :=
  rfl

/-! ## 5. The canonical tie-break order (SPEC §9.1) -/

/-- **`CanonicalBytesLE` matches the frozen schema.**  It is the unsigned
lexicographic order on the byte *lists*, so the tie-break is decided by content
alone. -/
-- authority-binding: CanonicalBytesLE
theorem canonicalBytesLE_matches_authority_schema (left right : ByteArray) :
    Foundation.CanonicalBytesLE left right ↔
      Foundation.UnsignedLexicographicLE left.toList right.toList :=
  Iff.rfl

/-- The order it delegates to, spelled out at the recursive step: a proper prefix
is smaller, and otherwise the first differing byte decides as an unsigned
natural. Written out so `CanonicalBytesLE` cannot be silently redirected to a
different comparison under the same name. -/
theorem unsignedLexicographicLE_step (a b : UInt8) (as bs : List UInt8) :
    Foundation.UnsignedLexicographicLE (a :: as) (b :: bs) ↔
      (a.toNat < b.toNat ∨
        (a.toNat = b.toNat ∧ Foundation.UnsignedLexicographicLE as bs)) :=
  Iff.rfl

/-! ## 6. The reference relation and the two indices (SPEC §8) -/

/--
**`Gemm.Reference.Accepts` matches the frozen schema.**

Unfolded through `ReferenceSemanticAccepts`. A trapped or uncaught-exception
observation has no `returned` outcome and is rejected; the entry store must be
exactly what the harness installed; the final ABI-visible store must be exactly
what the reference prescribes at *every* index; and the write-containment
conjunct is checked against the problem's own sanctioned regions, not the
candidate's.
-/
-- authority-binding: Gemm.Reference.Accepts
theorem gemmReferenceAccepts_matches_authority_schema
    (problem : Gemm.Problem P) (raw : Gemm.RawInvocation P)
    (observation : Wasm.ExecutionObservation) :
    Gemm.Reference.Accepts problem raw observation ↔
      ((∃ entry final : Gemm.Store,
          Gemm.semanticFor problem raw observation =
            .returned (Gemm.referenceStatus raw.body) entry final ∧
          (∀ i, entry i = Gemm.entryObservable raw.body i) ∧
          (∀ i, final i = Gemm.referenceObservableStore raw.body i)) ∧
       Wasm.CandidateCallMemoryWritesWithin observation (Gemm.windowOf P raw.body)
         (problem.SanctionedWriteRegions raw
           (Gemm.semanticFor problem raw observation))) :=
  Iff.rfl

/-- **`Wasm.Profile` matches the frozen schema.**  A first-order body plus a
proof that it is lawful, and nothing else: the lawfulness is never stored as
data, so no profile can carry a private field the competitor universe cannot
see. -/
-- authority-binding: Wasm.Profile
theorem wasmProfile_matches_authority_schema (profile : Wasm.Profile) :
    profile = Wasm.Profile.mk
      (body := (profile.body : Wasm.ProfileBody))
      (lawful := (profile.lawful : Wasm.ProfileLawful profile.body)) :=
  rfl

/-- **`Gemm.Problem` matches the frozen schema.**  A first-order body plus a
proof that it is the pinned canonical WGNG-v1 body. The lawfulness field is what
stops a problem instance from being weakened to suit an artifact. -/
-- authority-binding: Gemm.Problem
theorem gemmProblem_matches_authority_schema (problem : Gemm.Problem P) :
    problem = Gemm.Problem.mk
      (body := (problem.body : Gemm.ProblemBody P.body))
      (lawful := (problem.lawful : Gemm.ProblemLawful P.body problem.body)) :=
  rfl

/-! ## 7. Consequences the audit reads directly -/

/-- **The competitor domain is unrestricted.**  Extracted so the property the
audit cares about — that the quantifier ranges over every finite byte sequence —
is checkable on its own, without unfolding the whole proposition. -/
theorem globalOptimal_competitor_domain_unrestricted [Foundation.Fintype (Gemm.RawInvocation P)]
    (S : Setting P) (D : Decider S)
    (O : Cost.ProperObjective P S.problem) {releasedBytes : ByteArray}
    (h : GlobalOptimal S D O releasedBytes) :
    ∀ competitorBytes : ByteArray,
      ProfileValid P competitorBytes →
      SemanticCorrect S competitorBytes →
      SemanticWithinResources S competitorBytes →
      ∀ competitorEval : SystemEvaluation S competitorBytes,
        SystemEvaluationRel S D competitorBytes competitorEval ∧
        O.score (Classical.choose h.2.2.2).cost ≤ O.score competitorEval.cost := by
  have hs := Classical.choose_spec h.2.2.2
  exact hs.2.2.2.1

end WasmGemmGnaf.Conformance
