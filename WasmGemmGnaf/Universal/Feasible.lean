/-
  `Universal.Feasible`: the evaluator-side resource predicate.
  Normative source: SPEC.md section 10.1.

  "Resource feasibility therefore measures every bounded terminal execution
  independently of semantic correctness."

  Dependency firewall (SPEC §10.1): this file imports only
  `Universal/Competitor.lean`.  It does not import `GNAF`, `Atlas`, `Artifact`,
  `Universal/LowerBound`, `Universal/Argmin`, or `Theorems`.

  Every declaration in this file is either a definition or a proved theorem.
-/
import WasmGemmGnaf.Universal.Competitor
import WasmGemmGnaf.Universal.Correct
import WasmGemmGnaf.Wasm.PublicSuccessors

set_option autoImplicit false

namespace WasmGemmGnaf.Universal

variable {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]

/-- **SPEC §10.1**, `Universal.Feasible`.

The quantifier is over *every* raw invocation.  `resourceVector` is the
initialization charge composed with the componentwise maximum over every
recorded branch, so this bounds the worst permitted execution of the invocation,
not a chosen one. -/
def Feasible {S : Setting P} {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) : Prop :=
  ∀ raw : Gemm.RawInvocation P,
    Cost.DynamicVector.ComponentwiseLE
      (evaluation.perInput raw).resourceVector S.problem.limit

/-- A feasible evaluation pays for initialization inside the limit: the
initialization charge of every input is bounded. -/
theorem feasible_initialization_le {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : Feasible evaluation)
    (raw : Gemm.RawInvocation P) :
    Cost.DynamicVector.ComponentwiseLE
      (evaluation.perInput raw).initialization.cost S.problem.limit := by
  have hexact := (evaluation.perInput raw).resourceExact
  refine Cost.DynamicVector.componentwiseLE_trans ?_ (h raw)
  rw [hexact]
  exact Cost.sequentialCompose_le_left _ _

/-- A feasible evaluation pays for the worst recorded branch inside the limit. -/
theorem feasible_branchMax_le {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : Feasible evaluation)
    (raw : Gemm.RawInvocation P) :
    Cost.DynamicVector.ComponentwiseLE
      (Cost.maxOverCosts
        ((evaluation.perInput raw).observations.elements.map (·.cost)))
      S.problem.limit := by
  have hexact := (evaluation.perInput raw).resourceExact
  refine Cost.DynamicVector.componentwiseLE_trans ?_ (h raw)
  rw [hexact]
  exact Cost.sequentialCompose_le_right _ _

/-- Every *individual* recorded branch of a feasible evaluation is inside the
limit.  This is the sense in which feasibility measures every bounded terminal
execution, not just an average or a selected one. -/
theorem feasible_observation_le {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : Feasible evaluation)
    (raw : Gemm.RawInvocation P)
    {o : CostedExecutionObservation P (evaluation.perInput raw).initial}
    (ho : o ∈ (evaluation.perInput raw).observations.elements) :
    Cost.DynamicVector.ComponentwiseLE o.cost S.problem.limit := by
  refine Cost.DynamicVector.componentwiseLE_trans ?_ (feasible_branchMax_le h raw)
  exact Cost.le_maxOverCosts (List.mem_map_of_mem ho)

/-- Initialization composed with any recorded branch stays inside the limit —
the exact shape SPEC §10.1's `SemanticWithinResourcesAt` charges. -/
theorem feasible_compose_le {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : Feasible evaluation)
    (raw : Gemm.RawInvocation P)
    {o : CostedExecutionObservation P (evaluation.perInput raw).initial}
    (ho : o ∈ (evaluation.perInput raw).observations.elements) :
    Cost.DynamicVector.ComponentwiseLE
      (Cost.sequentialCompose (evaluation.perInput raw).initialization.cost o.cost)
      S.problem.limit := by
  refine Cost.DynamicVector.componentwiseLE_trans ?_ (h raw)
  rw [(evaluation.perInput raw).resourceExact]
  exact Cost.sequentialCompose_mono_right _
    (Cost.le_maxOverCosts (List.mem_map_of_mem ho))

/-- `Feasible` is pointwise in the raw invocation: no cross-input amortization
is available. -/
theorem feasible_pointwise {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : Feasible evaluation)
    (raw : Gemm.RawInvocation P) :
    Cost.DynamicVector.ComponentwiseLE
      (evaluation.perInput raw).resourceVector S.problem.limit :=
  h raw

/-! ## Extensional reflection -/

/-- The resource charge of every maximal public-Core execution is bounded by
an evaluator-side feasible result.  Coverage identifies the execution with a
recorded costed branch; `resourceExact` then makes that branch part of the
componentwise maximum rather than a selected path. -/
theorem maximal_charge_of_feasible {S : Setting P} {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes)
    (hfeasible : Feasible evaluation) (raw : Gemm.RawInvocation P)
    (initialization : InitializationObservation P) (initial : Wasm.Config)
    (execution : Wasm.MaximalExecution initial)
    (hmax : IsMaximalExecution S bytes raw initialization execution) :
    ∃ costed : CostedExecutionObservation P initial,
      CostedAs (S := S) execution costed ∧
      Cost.DynamicVector.ComponentwiseLE
        (Cost.sequentialCompose initialization.cost costed.cost)
        S.problem.limit := by
  obtain ⟨hstarts, _⟩ := hmax
  obtain ⟨module, hdecode, _, hinitial, hinitialConfig⟩ := hstarts
  have hmodule : module = evaluation.module :=
    profileValid_module_unique hdecode evaluation.decodeEq
  subst module
  let input := evaluation.perInput raw
  have hinit : initialization = input.initialization := by
    rw [input.initialEq] at hinitial
    exact (Except.ok.inj hinitial).symm
  subst initialization
  have hinitialEq : initial = input.initial := hinitialConfig.symm.trans input.initialConfigEq
  cases hinitialEq
  cases execution with
  | finite observation run maximal =>
      obtain ⟨costed, hmem, hfinite⟩ := evaluation.observationsComplete raw
        (.finite observation run maximal)
      have hcostedAs :
          CostedAs (S := S) (.finite observation run maximal) costed := by
        unfold CostedAs Wasm.MaximalExecution.CostedAs
        cases hfinite
        congr
      exact ⟨costed, hcostedAs, feasible_compose_le hfeasible raw hmem⟩
  | diverges events configs starts steps =>
      obtain ⟨_, _, hfalse⟩ := evaluation.observationsComplete raw
        (.diverges events configs starts steps)
      exact False.elim hfalse

/-- Once the executable tree checker has ruled out an overrun prefix, evaluator
feasibility is exactly the extensional resource predicate.  The no-overrun
premise is deliberately the checker's concrete relational conclusion, not a
coverage assumption over byte strings. -/
theorem semanticWithinResources_of_feasible_and_noOverrun
    {S : Setting P} {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) (hfeasible : Feasible evaluation)
    (hnoOverrun : ∀ raw : Gemm.RawInvocation P,
      ¬ ∃ initialization : InitializationObservation P,
        ∃ initial : Wasm.Config,
        ∃ pre : RelationalPrefix initial (S.problem.maxSteps + 1),
          StartsCostedInvocation S bytes raw initialization initial ∧ pre.Valid) :
    SemanticWithinResources S bytes := by
  intro raw
  exact ⟨hnoOverrun raw,
    maximal_charge_of_feasible evaluation hfeasible raw⟩

/-- Extensional resource conformance bounds every recorded branch of a
profile-valid complete evaluation.  Recorded costs are exact functions of the
public event trace, so an extensional witness for the same observation has the
same dynamic vector. -/
theorem feasible_of_semanticWithinResources
    {S : Setting P} {bytes : ByteArray}
    (hprofile : ProfileValid P bytes) (evaluation : SystemEvaluation S bytes)
    (hresources : SemanticWithinResources S bytes) : Feasible evaluation := by
  intro raw
  let input := evaluation.perInput raw
  have hstart : StartsCostedInvocation S bytes raw input.initialization input.initial := by
    obtain ⟨module, hdecode, hvalidate, _, _⟩ := hprofile
    have hmodule : module = evaluation.module :=
      profileValid_module_unique hdecode evaluation.decodeEq
    subst module
    exact ⟨evaluation.module, evaluation.decodeEq, hvalidate, input.initialEq,
      input.initialConfigEq⟩
  have hbranch : ∀ costed ∈ input.observations.elements,
      Cost.DynamicVector.ComponentwiseLE
        (Cost.sequentialCompose input.initialization.cost costed.cost)
        S.problem.limit := by
    intro costed _hcosted
    obtain ⟨other, hsame, hle⟩ := (hresources raw).2 input.initialization
      input.initial
      (.finite costed.observation costed.execution
        costed.execution.isTerminalObservation)
      ⟨hstart, trivial⟩
    have hobservation : costed.observation = other.observation := by
      unfold CostedAs Wasm.MaximalExecution.CostedAs at hsame
      have hsome : some costed.observation = some other.observation :=
        congrArg
          (fun execution =>
            match execution with
            | .finite observation _ _ => some observation
            | .diverges _ _ _ _ => none)
          hsame
      exact Option.some.inj hsome
    have hcost : costed.cost = other.cost := by
      exact (costed.functional_of_observation
        Wasm.Core.Harness.StepA.target_functional other hobservation).2.2
    simpa [hcost] using hle
  have hinitial : Cost.DynamicVector.ComponentwiseLE
      input.initialization.cost S.problem.limit := by
    exact Cost.DynamicVector.componentwiseLE_trans
      (Cost.sequentialCompose_le_left _ _)
      (hbranch input.observations.head (by
        simp [Foundation.NonemptyCanonicalFrontier.elements]))
  rw [input.resourceExact]
  apply Cost.sequentialCompose_maxOverCosts_le hinitial
  intro v hv
  obtain ⟨costed, hcosted, rfl⟩ := List.mem_map.mp hv
  exact hbranch costed hcosted

/-- A completed public tree rules out every prefix one step beyond its exact
bound, even when the same fresh start is reached through an extensionally
presented initialization witness. -/
theorem SystemEvaluation.noOverrunStarts
    {S : Setting P} {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) (raw : Gemm.RawInvocation P) :
    ¬ ∃ initialization : InitializationObservation P,
      ∃ initial : Wasm.Config,
      ∃ pre : RelationalPrefix initial (S.problem.maxSteps + 1),
        StartsCostedInvocation S bytes raw initialization initial ∧ pre.Valid := by
  rintro ⟨initialization, initial, pre, hstarts, hpre⟩
  let input := evaluation.perInput raw
  obtain ⟨decoded, hdecode, _, hinitial, hinitialConfig⟩ := hstarts
  have hmodule : decoded = evaluation.module :=
    profileValid_module_unique hdecode evaluation.decodeEq
  subst decoded
  have hinit : initialization = input.initialization := by
    rw [input.initialEq] at hinitial
    exact (Except.ok.inj hinitial).symm
  subst initialization
  have hinitialEq : initial = input.initial :=
    hinitialConfig.symm.trans input.initialConfigEq
  cases hinitialEq
  obtain ⟨coverage, _⟩ := input.treeComplete
  exact coverage.noOverrun ⟨pre, hpre⟩

/-- On profile-valid public bytes, evaluator feasibility is exactly the
extensional all-execution resource predicate. -/
theorem feasible_iff_semanticWithinResources
    {S : Setting P} {bytes : ByteArray}
    (hprofile : ProfileValid P bytes) (evaluation : SystemEvaluation S bytes) :
    Feasible evaluation ↔ SemanticWithinResources S bytes := by
  constructor
  · intro hfeasible
    exact semanticWithinResources_of_feasible_and_noOverrun evaluation hfeasible
      evaluation.noOverrunStarts
  · exact feasible_of_semanticWithinResources hprofile evaluation

/-- `Correct` and `Feasible` are independent predicates over the same
evaluation: neither is stated in terms of the other.  Their conjunction is
recorded here so the two reflection equivalences of SPEC §10.1 have a single
name to target. -/
def CorrectAndFeasible {S : Setting P} {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) : Prop :=
  Correct evaluation ∧ Feasible evaluation

/-- The conjunction projects to each component. -/
theorem correctAndFeasible_left {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : CorrectAndFeasible evaluation) :
    Correct evaluation := h.1

/-- The conjunction projects to each component. -/
theorem correctAndFeasible_right {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes} (h : CorrectAndFeasible evaluation) :
    Feasible evaluation := h.2

end WasmGemmGnaf.Universal
