/-
  Executable public-Core evaluation.

  This layer turns the byte-independent public machine operations carried by a
  `Universal.Setting` into the exact per-input object of SPEC section 10.1.  It
  does not select an artifact and imports no GNAF, Atlas, Artifact, lower-bound
  or argmin module.
-/
import WasmGemmGnaf.Universal.Feasible

set_option autoImplicit false

namespace WasmGemmGnaf.Universal

variable {P : Wasm.Profile}

/-! ## Public profile checking -/

/-- The exact-export predicate as a Boolean over the public Core AST. -/
def hasExactGemmExportsB (P : Wasm.Profile) (module : Wasm.Module) : Bool :=
  Wasm.Core.Module.satisfiesExport module.core
      { name := "memory", kind := .memory } &&
  Wasm.Core.Module.satisfiesExport module.core
      { name := "gemm", kind := .function Wasm.gemmFuncType } &&
  module.core.exports.all (fun entry =>
    Wasm.Core.nameMatches "gemm" entry.name ||
      Wasm.Core.nameMatches "memory" entry.name)

/-- The executable export test reflects the extensional export proposition
used by `ProfileValid`. -/
theorem hasExactGemmExportsB_eq_true_iff (P : Wasm.Profile)
    (module : Wasm.Module) :
    hasExactGemmExportsB P module = true ↔ HasExactGemmExports P module := by
  simp only [hasExactGemmExportsB, HasExactGemmExports, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, and_assoc]

/-- Closed result algebra for the public decoder/validator/profile test.  Every
failure retains the concrete module or decoder fault that caused it. -/
inductive ProfileCheckResult
  | complete (module : Wasm.Module)
  | decodeFailure (fault : Wasm.CoreDecodeFault)
  | validationFailure (module : Wasm.Module)
  | importFailure (module : Wasm.Module)
  | exportFailure (module : Wasm.Module)

/-- The finite public profile checker used before raw-input exploration. -/
def profileChecker (P : Wasm.Profile) (bytes : ByteArray) : ProfileCheckResult :=
  match Wasm.decode bytes with
  | .error fault => .decodeFailure fault
  | .ok module =>
      if Wasm.validateUnder P module then
        if module.core.imports.isEmpty then
          if hasExactGemmExportsB P module then .complete module
          else .exportFailure module
        else .importFailure module
      else .validationFailure module

/-- A completed public profile check is exactly `ProfileValid`; no profile
condition is supplied by a caller. -/
theorem profileChecker_complete_iff (P : Wasm.Profile) (bytes : ByteArray)
    (module : Wasm.Module) :
    profileChecker P bytes = .complete module ↔
      Wasm.decode bytes = .ok module ∧
      Wasm.validateUnder P module = true ∧
      module.core.imports = [] ∧
      HasExactGemmExports P module := by
  cases hdecode : Wasm.decode bytes with
  | error fault =>
      simp [profileChecker, hdecode]
  | ok decoded =>
      by_cases hvalidate : Wasm.validateUnder P decoded = true
      · by_cases himports : decoded.core.imports = []
        · by_cases hexports : HasExactGemmExports P decoded
          · simp [profileChecker, hdecode, hvalidate, himports, hexports,
              hasExactGemmExportsB_eq_true_iff, List.isEmpty_iff]
            rintro rfl
            exact ⟨hvalidate, himports, hexports⟩
          · simp [profileChecker, hdecode, hvalidate, himports, hexports,
              hasExactGemmExportsB_eq_true_iff, List.isEmpty_iff]
            rintro rfl _ _
            exact hexports
        · simp [profileChecker, hdecode, hvalidate, himports,
            hasExactGemmExportsB_eq_true_iff, List.isEmpty_iff]
          rintro rfl _ himports' _
          exact himports himports'
      · simp [profileChecker, hdecode, hvalidate,
          hasExactGemmExportsB_eq_true_iff, List.isEmpty_iff]
        rintro rfl hvalidate' _ _
        exact hvalidate hvalidate'

/-- The checker-level formulation of public profile validity. -/
theorem profileChecker_complete_exists_iff (P : Wasm.Profile)
    (bytes : ByteArray) :
    (∃ module, profileChecker P bytes = .complete module) ↔
      ProfileValid P bytes := by
  constructor
  · rintro ⟨module, hcheck⟩
    exact ⟨module, (profileChecker_complete_iff P bytes module).mp hcheck⟩
  · rintro ⟨module, hprofile⟩
    exact ⟨module, (profileChecker_complete_iff P bytes module).mpr hprofile⟩

/-- The closed result algebra of checking one raw invocation.  A successful
result contains the exact `InputEvaluation`; every other constructor retains
the public machine's concrete failure witness. -/
inductive ExecutionCheckResult (S : Setting P) (module : Wasm.Module)
    (raw : Gemm.RawInvocation P)
  | complete (evaluation : InputEvaluation S module raw)
  | initializationFailure (report : Foundation.FailureReport)
  | nonterminal (initial : Wasm.Config)
      (overrun : NonterminalPrefix initial (S.problem.maxSteps + 1))

namespace ExecutionCheckResult

/-- The decidable success tag used when folding the checker over the finite raw
input carrier.  It inspects only the result constructor. -/
def isComplete {S : Setting P} {module : Wasm.Module}
    {raw : Gemm.RawInvocation P} : ExecutionCheckResult S module raw → Bool
  | .complete _ => true
  | .initializationFailure _ => false
  | .nonterminal _ _ => false

/-- Extract the completed input evaluation.  The proof argument rules out both
failure constructors constructively, so no choice operator is involved. -/
def getComplete {S : Setting P} {module : Wasm.Module}
    {raw : Gemm.RawInvocation P} (result : ExecutionCheckResult S module raw)
    (hcomplete : result.isComplete = true) : InputEvaluation S module raw :=
  match result with
  | .complete evaluation => evaluation
  | .initializationFailure _ => False.elim (Bool.noConfusion hcomplete)
  | .nonterminal _ _ => False.elim (Bool.noConfusion hcomplete)

/-- `getComplete` is definitionally the payload of the successful constructor. -/
theorem eq_complete_getComplete {S : Setting P} {module : Wasm.Module}
    {raw : Gemm.RawInvocation P} (result : ExecutionCheckResult S module raw)
    (hcomplete : result.isComplete = true) :
    result = .complete (result.getComplete hcomplete) := by
  cases result with
  | complete evaluation => rfl
  | initializationFailure report =>
      change false = true at hcomplete
      exact False.elim (Bool.noConfusion hcomplete)
  | nonterminal initial overrun =>
      change false = true at hcomplete
      exact False.elim (Bool.noConfusion hcomplete)

end ExecutionCheckResult

/-- A completed public tree covers every maximal execution by construction.
The proof is projected from the strengthened public `CostedCoverage`; it is not
an extra certificate supplied by a Universal caller. -/
theorem InputEvaluation.coversEveryMaximalExecution
    {S : Setting P} {module : Wasm.Module} {raw : Gemm.RawInvocation P}
    (evaluation : InputEvaluation S module raw) :
    evaluation.CoversEveryMaximalExecution := by
  obtain ⟨coverage, _⟩ := evaluation.treeComplete
  intro execution
  cases execution with
  | finite observation run maximal =>
      obtain ⟨costed, hmem, hmatch⟩ :=
        coverage.maximal (.finite observation run maximal)
      exact ⟨costed, hmem, hmatch⟩
  | diverges events configs starts steps =>
      obtain ⟨_, _, hfalse⟩ :=
        coverage.maximal (.diverges events configs starts steps)
      exact False.elim hfalse

/-- The exact initialization charge followed by the componentwise worst public
branch charge. -/
def checkedInputResource
    (initialization : InitializationObservation P)
    (observations : Foundation.NonemptyCanonicalFrontier
      (CostedExecutionObservation P initialization.initial)) :
    Cost.DynamicVector :=
  Cost.sequentialCompose initialization.cost
    (Cost.maxOverCosts (observations.elements.map (·.cost)))

/-- **SPEC §10.1/§15**, the executable checker for one public-Core raw
invocation.  It performs fresh initialization and then invokes the bounded
all-successor costed explorer at the problem's exact step limit. -/
def executionChecker (S : Setting P) (module : Wasm.Module)
    (raw : Gemm.RawInvocation P) : ExecutionCheckResult S module raw :=
  match hinitial : Wasm.initialGemmInvocationCosted P module (toWasmInvocation raw) with
  | .error report => .initializationFailure report
  | .ok initialization =>
      match htree : S.machine.exploreAllCosted S.problem.maxSteps
          initialization.initial with
      | .complete observations coverage =>
          .complete
            { initial := initialization.initial
              initialization := initialization
              initialConfigEq := rfl
              initialEq := hinitial
              observations := observations
              treeComplete := ⟨coverage, htree⟩
              resourceVector := checkedInputResource initialization observations
              resourceExact := rfl }
      | .nonterminalPrefix overrun => .nonterminal initialization.initial overrun
      | .initializationFailure report => .initializationFailure report

/-- **SPEC §15, `Universal.execution_checker_sound`.**  A completed checker
answer is tied to the exact public initializer and exact bounded all-branch
explorer; neither equality is supplied by the caller or stored in the checker. -/
theorem execution_checker_sound {S : Setting P} {module : Wasm.Module}
    {raw : Gemm.RawInvocation P} {evaluation : InputEvaluation S module raw}
    (hcheck : executionChecker S module raw = .complete evaluation) :
    Wasm.initialGemmInvocationCosted P module (toWasmInvocation raw) =
        .ok evaluation.initialization ∧
      ∃ coverage,
        S.machine.exploreAllCosted S.problem.maxSteps evaluation.initial =
          .complete evaluation.observations coverage := by
  have _checkerReturnedEvaluation := hcheck
  exact ⟨evaluation.initialEq, evaluation.treeComplete⟩

/-- **SPEC §15, `Universal.execution_checker_complete_within_sublevel`.**
Whenever the public initializer succeeds and the bounded all-successor tree
returns a completed frontier at the problem limit, the executable checker
returns the corresponding exact input evaluation.  This is the local checker
boundary used for every input of a score sublevel; no program-equivalence or
termination oracle appears. -/
theorem execution_checker_complete_within_sublevel
    {S : Setting P} {module : Wasm.Module} {raw : Gemm.RawInvocation P}
    {initialization : InitializationObservation P}
    {observations : Foundation.NonemptyCanonicalFrontier
      (CostedExecutionObservation P initialization.initial)}
    {coverage : CostedCoverage P S.problem.maxSteps
      initialization.initial observations}
    (hinitial : Wasm.initialGemmInvocationCosted P module
        (toWasmInvocation raw) = .ok initialization)
    (htree : S.machine.exploreAllCosted S.problem.maxSteps initialization.initial =
      .complete observations coverage) :
    ∃ evaluation : InputEvaluation S module raw,
      executionChecker S module raw = .complete evaluation := by
  unfold executionChecker
  split
  · next report heq =>
    rw [heq] at hinitial
    contradiction
  · next checkedInitialization heq =>
    split
    · next checkedObservations checkedCoverage treeEq =>
      exact ⟨
        { initial := checkedInitialization.initial
          initialization := checkedInitialization
          initialConfigEq := rfl
          initialEq := heq
          observations := checkedObservations
          treeComplete := ⟨checkedCoverage, treeEq⟩
          resourceVector := checkedInputResource checkedInitialization checkedObservations
          resourceExact := rfl }, rfl⟩
    · next overrun treeEq =>
      have hinitEq : checkedInitialization = initialization := by
        rw [heq] at hinitial
        exact Except.ok.inj hinitial
      subst checkedInitialization
      rw [treeEq] at htree
      contradiction
    · next report treeEq =>
      have hinitEq : checkedInitialization = initialization := by
        rw [heq] at hinitial
        exact Except.ok.inj hinitial
      subst checkedInitialization
      rw [treeEq] at htree
      contradiction

/-! ## Choice-free aggregation over every raw invocation -/

section EveryInput

variable [Foundation.Fintype (Gemm.RawInvocation P)]

/-- Run the exact per-input checker over the complete constructive enumeration
of raw invocations.  The Boolean is true precisely when every invocation
returned its proof-carrying `complete` constructor. -/
def allInputsComplete (S : Setting P) (module : Wasm.Module) : Bool :=
  (Foundation.Fintype.elems (Gemm.RawInvocation P)).all
    (fun raw => (executionChecker S module raw).isComplete)

/-- Pointwise successful checker equations close the finite all-input fold.
This is the constructive aggregation direction used by whole-system
completeness: the proof traverses the canonical finite enumeration and never
selects a witness with `Classical.choice`. -/
theorem allInputsComplete_of_executionChecker_complete
    {S : Setting P} {module : Wasm.Module}
    (hcomplete : ∀ raw : Gemm.RawInvocation P,
      ∃ evaluation : InputEvaluation S module raw,
        executionChecker S module raw = .complete evaluation) :
    allInputsComplete S module = true := by
  apply List.all_eq_true.mpr
  intro raw _
  obtain ⟨evaluation, hevaluation⟩ := hcomplete raw
  simp [hevaluation, ExecutionCheckResult.isComplete]

/-- A successful all-input fold exposes the success equation at any requested
raw invocation, using finite-enumerator coverage. -/
theorem executionChecker_isComplete_of_allInputsComplete
    {S : Setting P} {module : Wasm.Module}
    (hcomplete : allInputsComplete S module = true)
    (raw : Gemm.RawInvocation P) :
    (executionChecker S module raw).isComplete = true := by
  exact List.all_eq_true.mp hcomplete raw (Foundation.Fintype.mem_elems raw)

/-- The per-input family extracted from a successful fold.  This is executable
dependent elimination of checker results, not `Classical.choice`. -/
def checkedInputOfAll {S : Setting P} {module : Wasm.Module}
    (hcomplete : allInputsComplete S module = true)
    (raw : Gemm.RawInvocation P) : InputEvaluation S module raw :=
  let result := executionChecker S module raw
  result.getComplete
    (executionChecker_isComplete_of_allInputsComplete hcomplete raw)

/-- Every extracted input is exactly the payload returned by its checker. -/
theorem executionChecker_checkedInputOfAll
    {S : Setting P} {module : Wasm.Module}
    (hcomplete : allInputsComplete S module = true)
    (raw : Gemm.RawInvocation P) :
    executionChecker S module raw =
      .complete (checkedInputOfAll hcomplete raw) := by
  exact ExecutionCheckResult.eq_complete_getComplete _ _

end EveryInput

/-! ## Constructive whole-domain checking -/

section WholeDomain

variable [Foundation.Fintype (Gemm.RawInvocation P)]

/-- The first raw invocation whose proof-carrying checker did not return its
`complete` constructor.  This structural scan neither compares proof-carrying
raw values nor invokes choice. -/
def firstIncomplete (S : Setting P) (module : Wasm.Module) :
    List (Gemm.RawInvocation P) → Option (Gemm.RawInvocation P)
  | [] => none
  | raw :: rest =>
      if (executionChecker S module raw).isComplete then
        firstIncomplete S module rest
      else
        some raw

/-- Absence of a failing raw invocation is exactly the Boolean all-success
fold over the same explicit list. -/
theorem firstIncomplete_eq_none_iff (S : Setting P) (module : Wasm.Module) :
    ∀ raws : List (Gemm.RawInvocation P),
      firstIncomplete S module raws = none ↔
        raws.all (fun raw => (executionChecker S module raw).isComplete) = true := by
  intro raws
  induction raws with
  | nil => simp [firstIncomplete]
  | cons raw rest ih =>
      simp only [firstIncomplete, List.all_cons, Bool.and_eq_true]
      cases hcheck : (executionChecker S module raw).isComplete <;>
        simp [hcheck, ih]

/-- Every returned counterexample is a genuine non-complete checker result. -/
theorem firstIncomplete_eq_some_isComplete_false
    (S : Setting P) (module : Wasm.Module) :
    ∀ {raws : List (Gemm.RawInvocation P)} {raw : Gemm.RawInvocation P},
      firstIncomplete S module raws = some raw →
        (executionChecker S module raw).isComplete = false := by
  intro raws
  induction raws with
  | nil => simp [firstIncomplete]
  | cons head rest ih =>
      intro raw hfound
      simp only [firstIncomplete] at hfound
      cases hcheck : (executionChecker S module head).isComplete with
      | false =>
          simp [hcheck] at hfound
          subst raw
          exact hcheck
      | true =>
          simp [hcheck] at hfound
          exact ih hfound

end WholeDomain

/-! ## Exact whole-system aggregation -/

section Aggregate

variable [Foundation.Fintype (Gemm.RawInvocation P)]

/-- Extensional correctness and resource conformance expose exactly the
premises needed by the canonical public explorer on one raw invocation: a
fresh successful initialization, finiteness of every maximal execution from
that start, and exclusion of a prefix one step past the public bound.  The
module is the unique result of the public profile checker. -/
theorem semanticInput_explorerPremises {S : Setting P} {bytes : ByteArray}
    (hprofile : ProfileValid P bytes)
    (hcorrect : SemanticCorrect S bytes)
    (hresources : SemanticWithinResources S bytes)
    (raw : Gemm.RawInvocation P) :
    ∃ module : Wasm.Module,
      ∃ initialization : InitializationObservation P,
      profileChecker P bytes = .complete module ∧
      Wasm.initialGemmInvocationCosted P module (toWasmInvocation raw) =
        .ok initialization ∧
      (∃ observation : Wasm.ExecutionObservation,
        Wasm.FiniteExecution initialization.initial observation) ∧
      (∀ execution : Wasm.MaximalExecution initialization.initial,
        ∃ observation,
          HasFiniteObservation execution observation) ∧
      ¬ ∃ pre : RelationalPrefix initialization.initial
          (S.problem.maxSteps + 1), pre.Valid := by
  obtain ⟨module, hprofileCheck⟩ :=
    (profileChecker_complete_exists_iff P bytes).mpr hprofile
  obtain ⟨witnessInitialization, witnessInitial, witnessExecution, hmaximal⟩ :=
    (hcorrect raw).1
  obtain ⟨witnessObservation, hwitnessFinite, _⟩ :=
    (hcorrect raw).2 witnessInitialization witnessInitial witnessExecution hmaximal
  obtain ⟨hstarts, _⟩ := hmaximal
  obtain ⟨witnessModule, hwitnessDecode, _, hwitnessInitialization,
    hwitnessInitial⟩ := hstarts
  have hcheckedDecode : Wasm.decode bytes = .ok module :=
    (profileChecker_complete_iff P bytes module).mp hprofileCheck |>.1
  have hmodule : witnessModule = module :=
    profileValid_module_unique hwitnessDecode hcheckedDecode
  subst witnessModule
  refine ⟨module, witnessInitialization, hprofileCheck,
    hwitnessInitialization, ?_, ?_, ?_⟩
  ·
    cases witnessExecution with
    | finite finiteObservation run maximal =>
        have runObservation :
            Wasm.FiniteExecution witnessInitial witnessObservation :=
          hwitnessFinite ▸ run
        exact ⟨witnessObservation, hwitnessInitial.symm ▸ runObservation⟩
    | diverges events configs starts steps =>
        exact False.elim hwitnessFinite
  · intro execution
    have hstart : StartsCostedInvocation S bytes raw witnessInitialization
        witnessInitialization.initial := by
      exact ⟨module, hcheckedDecode,
        (profileChecker_complete_iff P bytes module).mp hprofileCheck |>.2.1,
        hwitnessInitialization, rfl⟩
    obtain ⟨observation, hfinite, _⟩ :=
      (hcorrect raw).2 witnessInitialization witnessInitialization.initial
        execution ⟨hstart, trivial⟩
    exact ⟨observation, hfinite⟩
  · rintro ⟨pre, hvalid⟩
    apply (hresources raw).1
    exact ⟨witnessInitialization, witnessInitialization.initial, pre,
      ⟨module, hcheckedDecode,
        (profileChecker_complete_iff P bytes module).mp hprofileCheck |>.2.1,
        hwitnessInitialization, rfl⟩, hvalid⟩

/-- The unique complete-system vector determined by public bytes, their public
module, the positive workload multiplicity, and every checked raw input. -/
def checkedSystemCost (S : Setting P) (bytes : ByteArray) (module : Wasm.Module)
    (perInput : ∀ raw : Gemm.RawInvocation P, InputEvaluation S module raw) :
    Cost.CompleteSystemCost :=
  { static :=
      { moduleBytes := bytes.size
        decodeSteps := Wasm.decodeCost P.costTableBody bytes
        validationSteps := Wasm.validationCost P.costTableBody module
        staticDataBytes := Wasm.instantiatedStaticBytes P module }
    dynamicSum :=
      Cost.scale S.problem.workloadRepetitions
        (Cost.fullDomainSum (fun raw => (perInput raw).resourceVector))
    dynamicMax :=
      Cost.fullDomainMax (fun raw => (perInput raw).resourceVector) }

/-- The constructed vector satisfies every conjunct of SPEC §9.1's public
`ExactAggregateCost`; no static coordinate is caller supplied. -/
theorem checkedSystemCost_exact (S : Setting P) (bytes : ByteArray)
    (module : Wasm.Module)
    (perInput : ∀ raw : Gemm.RawInvocation P, InputEvaluation S module raw)
    (hdecode : Wasm.decode bytes = .ok module) :
    Cost.ExactAggregateCost P bytes module S.problem.workloadRepetitions
      (fun raw => (perInput raw).resourceVector)
      (checkedSystemCost S bytes module perInput) := by
  exact ⟨S.problem.workloadRepetitionsPositive, hdecode, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Assemble a public `SystemEvaluation` from the executable per-input checker
outputs and their all-maximal-branch coverage.  Cost aggregation is recomputed
here, after coverage, so an input checker cannot inject a different artifact
cost. -/
def assembleSystemEvaluation (S : Setting P) (bytes : ByteArray)
    (module : Wasm.Module) (hdecode : Wasm.decode bytes = .ok module)
    (perInput : ∀ raw : Gemm.RawInvocation P, InputEvaluation S module raw) :
    SystemEvaluation S bytes :=
  { module := module
    decodeEq := hdecode
    perInput := perInput
    observationsComplete := fun raw => (perInput raw).coversEveryMaximalExecution
    cost := checkedSystemCost S bytes module perInput
    costExact := checkedSystemCost_exact S bytes module perInput hdecode }

/-! ## The finite public evaluator -/

/-- Canonical site for a rejected public profile check.  The constructor of
`ProfileCheckResult` retains the detailed cause during computation; the public
result algebra records the stable failure category at this boundary. -/
def publicProfileFailureSite : Foundation.CanonicalObjectId where
  schemaVersion := 1
  domain := .generic
  typeTag := Foundation.Bytes.pack []
  canonicalBodyBytes := Foundation.Bytes.pack []

/-- Stable public failure report for a rejected decoder/validator/profile
check.  Codes distinguish decoder, validator, imports and exports without
claiming a host diagnostic string. -/
def publicProfileFailure (code : Nat) : Foundation.FailureReport where
  site := publicProfileFailureSite
  code := code
  context := []

/-- The implemented finite decoder, validator, raw-input fold and public
all-branch checker.  A successful result is assembled solely from the payloads
returned by the per-input checker. -/
def evaluateFinite (S : Setting P) (bytes : ByteArray) : EvaluationResult S bytes :=
  match hprofile : profileChecker P bytes with
  | .decodeFailure _ => .profileFailure (publicProfileFailure 1)
  | .validationFailure _ => .profileFailure (publicProfileFailure 2)
  | .importFailure _ => .profileFailure (publicProfileFailure 3)
  | .exportFailure _ => .profileFailure (publicProfileFailure 4)
  | .complete module =>
      if hcomplete : allInputsComplete S module = true then
        let perInput := checkedInputOfAll hcomplete
        let hdecode := (profileChecker_complete_iff P bytes module).mp hprofile |>.1
        .complete (assembleSystemEvaluation S bytes module hdecode perInput)
      else
        match hfound : firstIncomplete S module
            (Foundation.Fintype.elems (Gemm.RawInvocation P)) with
        | none =>
            False.elim (hcomplete ((firstIncomplete_eq_none_iff S module _).mp hfound))
        | some raw =>
            match hcheck : executionChecker S module raw with
            | .initializationFailure report => .initializationFailure raw report
            | .nonterminal initial overrun => .nonterminal raw initial overrun
            | .complete _ =>
                have hfalse := firstIncomplete_eq_some_isComplete_false S module hfound
                False.elim (by
                  simp only [hcheck, ExecutionCheckResult.isComplete] at hfalse
                  exact Bool.noConfusion hfalse)

/-- **SPEC §10.1**, the sole public whole-system evaluator.  It is the finite
computation above, not a callback stored in a release or partition object. -/
def evaluate (S : Setting P) (bytes : ByteArray) : EvaluationResult S bytes :=
  evaluateFinite S bytes

/-- A token selecting the sole public evaluator.  It has no function field, so
callers cannot replace the semantics used by `SystemEvaluationRel`. -/
structure Decider (_S : Setting P) where

namespace Decider

/-- Method spelling retained for downstream objective/partition APIs; the
token is ignored and the canonical evaluator is called directly. -/
def evaluate {S : Setting P} (_decider : Decider S) (bytes : ByteArray) :
    EvaluationResult S bytes :=
  Universal.evaluate S bytes

end Decider

/-- **SPEC §10.1**, relation to the result of the sole public evaluator. -/
def SystemEvaluationRel (S : Setting P) (_D : Decider S) (bytes : ByteArray)
    (evaluation : SystemEvaluation S bytes) : Prop :=
  Universal.evaluate S bytes = .complete evaluation

/-- A completed finite evaluator result can only come through the public
decoder/validator/import/export success arm. -/
theorem evaluateFinite_complete_profileValid {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes}
    (h : evaluateFinite S bytes = .complete evaluation) :
    ProfileValid P bytes := by
  unfold evaluateFinite at h
  split at h
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · next module hprofile =>
      exact (profileChecker_complete_exists_iff P bytes).mp ⟨module, hprofile⟩

/-- Every completed result of the implemented finite evaluator reflects both
extensional semantic correctness and extensional resource conformance.  The
only premise is the evaluator's own result equation. -/
theorem evaluateFinite_complete_reflects {S : Setting P} {bytes : ByteArray}
    {evaluation : SystemEvaluation S bytes}
    (h : evaluateFinite S bytes = .complete evaluation) :
    (Correct evaluation ↔ SemanticCorrect S bytes) ∧
      (Feasible evaluation ↔ SemanticWithinResources S bytes) := by
  have hprofile := evaluateFinite_complete_profileValid h
  exact ⟨correct_iff_semanticCorrect hprofile evaluation,
    feasible_iff_semanticWithinResources hprofile evaluation⟩

/-- **SPEC §10.1/§15, `Universal.system_evaluation_rel_sound`.**  The exact
result relation of the sole public evaluator reflects independently to the
extensional correctness and resource predicates. -/
theorem system_evaluation_rel_sound {S : Setting P} {D : Decider S}
    {bytes : ByteArray} {evaluation : SystemEvaluation S bytes}
    (hrel : SystemEvaluationRel S D bytes evaluation) :
    (Correct evaluation ↔ SemanticCorrect S bytes) ∧
      (Feasible evaluation ↔ SemanticWithinResources S bytes) := by
  apply evaluateFinite_complete_reflects
  simpa [SystemEvaluationRel, evaluate] using hrel

/-- **SPEC §10.1/§15, `Universal.system_evaluation_rel_complete`.**
Extensional profile validity, correctness, and resource conformance force the
sole finite public evaluator to return a proof-carrying complete system
evaluation.  The construction uses the canonical public costed explorer on
every element of the complete raw-input enumeration. -/
theorem system_evaluation_rel_complete {S : Setting P} {D : Decider S}
    {bytes : ByteArray}
    (hprofile : ProfileValid P bytes)
    (hcorrect : SemanticCorrect S bytes)
    (hresources : SemanticWithinResources S bytes) :
    ∃ evaluation : SystemEvaluation S bytes,
      SystemEvaluationRel S D bytes evaluation := by
  obtain ⟨module, hprofileCheck⟩ :=
    (profileChecker_complete_exists_iff P bytes).mpr hprofile
  have perInputComplete : ∀ raw : Gemm.RawInvocation P,
      ∃ evaluation : InputEvaluation S module raw,
        executionChecker S module raw = .complete evaluation := by
    intro raw
    obtain ⟨checkedModule, initialization, hcheckedProfile, hinitial,
      hfinite, _, hnoOverrun⟩ :=
      semanticInput_explorerPremises hprofile hcorrect hresources raw
    have hmodule : checkedModule = module := by
      rw [hprofileCheck] at hcheckedProfile
      exact ProfileCheckResult.complete.inj hcheckedProfile.symm
    subst checkedModule
    obtain ⟨observations, coverage, htree⟩ :=
      Wasm.exploreAllCosted_complete_of_finite_noOverrun hfinite hnoOverrun
    apply execution_checker_complete_within_sublevel hinitial
    simpa [CostedMachine.exploreAllCosted] using htree
  have hall : allInputsComplete S module = true :=
    allInputsComplete_of_executionChecker_complete perInputComplete
  let perInput : ∀ raw : Gemm.RawInvocation P, InputEvaluation S module raw :=
    checkedInputOfAll hall
  have hdecode : Wasm.decode bytes = .ok module :=
    (profileChecker_complete_iff P bytes module).mp hprofileCheck |>.1
  let evaluation : SystemEvaluation S bytes :=
    assembleSystemEvaluation S bytes module hdecode perInput
  refine ⟨evaluation, ?_⟩
  change evaluate S bytes = .complete evaluation
  unfold evaluate evaluateFinite
  split
  · next fault hcheck => rw [hprofileCheck] at hcheck; contradiction
  · next checkedModule hcheck => rw [hprofileCheck] at hcheck; contradiction
  · next checkedModule hcheck => rw [hprofileCheck] at hcheck; contradiction
  · next checkedModule hcheck => rw [hprofileCheck] at hcheck; contradiction
  · next checkedModule hcheck =>
      rw [hprofileCheck] at hcheck
      have hmodule : checkedModule = module :=
        ProfileCheckResult.complete.inj hcheck.symm
      subst checkedModule
      simp only [hall, dite_true]
      rfl

end Aggregate

end WasmGemmGnaf.Universal
