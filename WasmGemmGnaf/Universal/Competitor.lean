/-
  The universal competitor universe: extensional definitions.
  Normative source: SPEC.md section 10.1 (with section 8.3 for the raw carrier).

  SCOPE — read this before citing anything here.

  This is the public amended-Core universe of SPEC section 10.1.  Every
  competitor predicate below
  quantifies over all raw invocations and all maximal executions of the selected
  public machine, and nothing is artifact-, selector-, or conclusion-dependent.
  `ProfileValid`, `SystemEvaluation`, configurations, events and observations
  all use the public representable Core carrier; `Wasm.Subset` cannot inhabit
  any of those positions.

  `Wasm/Costed.lean`, `Gemm/Reference.lean`, and `Gemm/Problem.lean` now exist.
  Parameter records keep the public evaluator independent of the release
  artifact:

    * `Universal.CostedMachine`   — costed initialization and the bounded
                                    all-branch costed explorer;
    * `Universal.Problem P`       — the problem's resource contract, workload
                                    repetitions, and reference relation;
    * `Universal.Decider`         — `Universal.evaluate` of SPEC section 10.1.

  This is the technique already used by `Cost/Proper.lean` (opaque `Profile` and
  `Problem` indices) and `Cost/Aggregate.lean` (the `decodes`, `decodeSteps`,
  `validationSteps`, `staticDataBytes` parameters).  No field of any of these
  records is a *conclusion*: none asserts correctness, feasibility, coverage,
  optimality, or finiteness of anything.  They are the data and the executable
  functions supplied at a particular public-Core setting.  The executable
  release evaluator must instantiate them with the exact public successor tree;
  the records themselves cannot assert a checker conclusion.

  Every declaration in this file is either a definition or a proved theorem.
  Nothing is assumed.
-/
import WasmGemmGnaf.Foundation.Result
import WasmGemmGnaf.Foundation.Order
import WasmGemmGnaf.Foundation.Finite
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Validate
import WasmGemmGnaf.Wasm.CoreValidation
import WasmGemmGnaf.Wasm.Evaluate
import WasmGemmGnaf.Wasm.PublicFuel
import WasmGemmGnaf.Wasm.PublicCostedExplore
import WasmGemmGnaf.Wasm.Profile
import WasmGemmGnaf.Gemm.Classify
import WasmGemmGnaf.Gemm.Problem
import WasmGemmGnaf.Gemm.Reference
import WasmGemmGnaf.Cost.Aggregate
import WasmGemmGnaf.Cost.Trace

set_option autoImplicit false

namespace WasmGemmGnaf.Universal

/-! ## Public amended-Core profile validity -/

/-- The public module has the required `memory` and `(i32,i32) -> i32` `gemm`
exports, and no export under any other name.  Kind and function type are checked
by the Core profile's own export predicate; module validation supplies the
Core-level unique-export-name invariant. -/
def HasExactGemmExports (_P : Wasm.Profile) (m : Wasm.Module) : Prop :=
  Wasm.Core.Module.satisfiesExport m.core
      { name := "memory", kind := .memory } = true ∧
  Wasm.Core.Module.satisfiesExport m.core
      { name := "gemm", kind := .function Wasm.gemmFuncType } = true ∧
  ∀ e ∈ m.core.exports,
    Wasm.Core.nameMatches "gemm" e.name = true ∨
      Wasm.Core.nameMatches "memory" e.name = true

/-- **SPEC §10.1**, public amended-Core profile validity.  The quantified module
is the image of the full amended binary grammar; no legacy subset module can
inhabit this proposition. -/
def ProfileValid (P : Wasm.Profile) (bytes : ByteArray) : Prop :=
  ∃ module : Wasm.Module,
    Wasm.decode bytes = .ok module ∧
    Wasm.validateUnder P module = true ∧
    module.core.imports = [] ∧
    HasExactGemmExports P module

/-! ## The public costed-semantics seam -/

/-- Universal evaluation uses the public initializer evidence directly. -/
abbrev InitializationObservation := Wasm.InitializationObservation

/-- Universal evaluation uses the public relational-prefix carrier directly. -/
abbrev RelationalPrefix := Wasm.RelationalPrefix

/-- The public explorer's proof-carrying overrun witness. -/
abbrev NonterminalPrefix := Wasm.NonterminalPrefix

/-- Costed observations are exactly the public profile-indexed observations. -/
abbrev CostedExecutionObservation := Wasm.CostedExecutionObservation

/-- Completed coverage is exactly the public explorer's coverage proposition. -/
abbrev CostedCoverage := Wasm.CostedCoverage

/-- The Universal checker consumes the public costed-tree result directly. -/
abbrev CostedTreeResult := Wasm.CostedTreeResult

/-- Empty token selecting the sole public costed machine.  It stores no
initializer, successor function, explorer, cost function, or conclusion. -/
structure CostedMachine (_P : Wasm.Profile) where

namespace CostedMachine

/-- Method spelling retained for the Universal evaluator.  The token is
ignored and SPEC §10.1's canonical public explorer is called directly. -/
def exploreAllCosted {P : Wasm.Profile} (_machine : CostedMachine P)
    (bound : Nat) (initial : Wasm.Config) : CostedTreeResult P bound initial :=
  Wasm.exploreAllCosted P bound initial

end CostedMachine

/-! ## The parameterized problem seam -/

/-- Problem-level data for this seam. The complete first-order GEMM problem is
retained directly; the only extra evidence states SPEC §9.2's positivity of the
workload multiplicity. No acceptance or resource callback is configurable. -/
structure Problem (P : Wasm.Profile) where
  /-- SPEC §8: the canonical first-order problem. -/
  gemm : Gemm.Problem P
  /-- SPEC §9.2: the workload multiplicity is positive. -/
  workloadRepetitionsPositive : 1 ≤ gemm.workloadRepetitions

namespace Problem

variable {P : Wasm.Profile}

/-- The problem's exact public step budget. -/
def maxSteps (problem : Problem P) : Nat := problem.gemm.maxSteps

/-- The complete public dynamic resource limit. -/
def limit (problem : Problem P) : Cost.DynamicVector :=
  problem.gemm.resources.limit

/-- The exact workload multiplicity stored in the first-order problem. -/
def workloadRepetitions (problem : Problem P) : Nat :=
  problem.gemm.workloadRepetitions

/-- SPEC §8.4's one fixed reference relation. -/
def Accepts (problem : Problem P) (raw : Gemm.RawInvocation P)
    (observation : Wasm.ExecutionObservation) : Prop :=
  Gemm.Reference.Accepts problem.gemm raw observation

end Problem

/-- **SPEC §8.3**, `Gemm.Problem.RawInvocation`.  The raw-input carrier is fixed
*before* classification and cannot be narrowed by the problem. -/
def Problem.RawInvocation {P : Wasm.Profile} (_problem : Problem P) : Type :=
  Gemm.RawInvocation P

/-- **SPEC §8.3**, `problem_raw_invocation_definitional`.  The problem's raw
carrier is the fixed carrier, definitionally: no problem instance can shrink
the input domain. -/
theorem problem_raw_invocation_definitional {P : Wasm.Profile}
    (problem : Problem P) : problem.RawInvocation = Gemm.RawInvocation P :=
  rfl

/-- **SPEC §8.3**, `Gemm.toWasmInvocation`.  The harness places exactly
`raw.body.bytes` at `raw.body.ptr` and synthesizes nothing else. -/
def toWasmInvocation {P : Wasm.Profile} (raw : Gemm.RawInvocation P) :
    Wasm.Invocation P :=
  Wasm.Invocation.gemmRaw raw.body.toWasm raw.lawful.toWasmInvocationLawful

/-- Everything the extensional definitions need, in one record: the costed
semantics, the costed machine, and the problem. -/
structure Setting (P : Wasm.Profile) where
  /-- The costed initialization and exploration entry points. -/
  machine : CostedMachine P
  /-- The exact GEMM problem. -/
  problem : Problem P

/-! ## Costed evaluation (SPEC §10.1) -/

section Evaluation

variable {P : Wasm.Profile}

/-- **SPEC §10.1**, `Universal.InputEvaluation`: the exact result of the bounded
all-successor tree on one raw invocation. -/
structure InputEvaluation (S : Setting P) (module : Wasm.Module)
    (raw : Gemm.RawInvocation P) where
  /-- The configuration the invocation starts from. -/
  initial : Wasm.Config
  /-- The costed initialization observation. -/
  initialization : InitializationObservation P
  /-- It starts at `initial`. -/
  initialConfigEq : initialization.initial = initial
  /-- It is the machine's costed initialization of this module and invocation. -/
  initialEq :
    Wasm.initialGemmInvocationCosted P module (toWasmInvocation raw) =
      .ok initialization
  /-- The canonically ordered, nonempty list of costed observations. -/
  observations :
    Foundation.NonemptyCanonicalFrontier
      (CostedExecutionObservation P initial)
  /-- The tree completed inside the problem's step budget with exactly those
  observations. -/
  treeComplete : ∃ coverage,
    S.machine.exploreAllCosted S.problem.maxSteps initial =
      .complete observations coverage
  /-- The invocation's resource vector. -/
  resourceVector : Cost.DynamicVector
  /-- It is exactly initialization composed with the worst branch. -/
  resourceExact : resourceVector =
    Cost.sequentialCompose initialization.cost
      (Cost.maxOverCosts (observations.elements.map (·.cost)))

/-- **SPEC §10.1**, `CoversEveryMaximalExecution`: no maximal execution of the
initial configuration escapes the recorded costed observations.  A divergent
execution has no finite observation, so it falsifies this predicate. -/
def InputEvaluation.CoversEveryMaximalExecution {S : Setting P}
    {module : Wasm.Module} {raw : Gemm.RawInvocation P}
    (ie : InputEvaluation S module raw) : Prop :=
  ∀ execution : Wasm.MaximalExecution ie.initial,
    ∃ costed ∈ ie.observations.elements,
      (match execution with
        | .finite o _ _ => o = costed.observation
        | .diverges _ _ _ _ => False)

variable [Foundation.Fintype (Gemm.RawInvocation P)]

/--
  **SPEC §10.1**, `Universal.SystemEvaluation`.

  The `Foundation.Fintype` instance on the raw carrier is SPEC §8.3's
  representability bound, supplied uniformly by the problem layer; it is the
  same instance `Cost.ExactAggregateCost` already requires.  It is a property of
  the *input domain*, not of any competitor, and it does not narrow the
  competitor quantifier.
-/
structure SystemEvaluation (S : Setting P) (bytes : ByteArray) where
  /-- The decoded module. -/
  module : Wasm.Module
  /-- It is exactly what `bytes` decodes to. -/
  decodeEq : Wasm.decode bytes = .ok module
  /-- One input evaluation for *every* raw invocation. -/
  perInput : ∀ raw : Gemm.RawInvocation P, InputEvaluation S module raw
  /-- Each of them covers every maximal execution. -/
  observationsComplete : ∀ raw, (perInput raw).CoversEveryMaximalExecution
  /-- The complete charged system cost. -/
  cost : Cost.CompleteSystemCost
  /-- It is the exact aggregate of SPEC §9.1. -/
  costExact :
    Cost.ExactAggregateCost P bytes module S.problem.workloadRepetitions
      (fun raw => (perInput raw).resourceVector) cost

/-- **SPEC §10.1**, `Universal.EvaluationResult`. -/
inductive EvaluationResult (S : Setting P) (bytes : ByteArray)
  /-- The tree completed on every input. -/
  | complete (evaluation : SystemEvaluation S bytes)
  /-- The bytes are not profile valid. -/
  | profileFailure (report : Foundation.FailureReport)
  /-- Costed initialization failed on some input. -/
  | initializationFailure (raw : Gemm.RawInvocation P)
      (report : Foundation.FailureReport)
  /-- Some input overran the step budget. -/
  | nonterminal (raw : Gemm.RawInvocation P) (initial : Wasm.Config)
      (overrun : NonterminalPrefix initial (S.problem.maxSteps + 1))
  /-- Some input exhausted a declared resource. -/
  | resourceExhausted (raw : Gemm.RawInvocation P)
      (report : Foundation.ResourceReport)

/-! The executable `Decider`, canonical `evaluate`, and
`SystemEvaluationRel` live in `Universal/Evaluate.lean`, after the finite
decoder/input/explorer computation they expose.  Keeping those executable
names out of this extensional layer prevents an arbitrary callback from
becoming part of the competitor universe. -/

end Evaluation

/-! ## The extensional semantic predicates (SPEC §10.1)

These are extensional predicates for the public amended-Core machine.  None
mentions an evaluation, certificate, artifact, or selector. -/

section Semantic

variable {P : Wasm.Profile}

/-- **SPEC §10.1**, `Universal.StartsCostedInvocation`. -/
def StartsCostedInvocation (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P)
    (initialization : InitializationObservation P) (initial : Wasm.Config) :
    Prop :=
  ∃ module : Wasm.Module,
    Wasm.decode bytes = .ok module ∧
    Wasm.validateUnder P module = true ∧
    Wasm.initialGemmInvocationCosted P module (toWasmInvocation raw) =
      .ok initialization ∧
    initialization.initial = initial

/--
  **SPEC §10.1**, `Wasm.IsMaximalExecutionFrom`.

  `Wasm.MaximalExecution initial` already carries the reduction and maximality
  proofs out of `initial` in both of its constructors, so the separate side
  condition is definitionally satisfied.  It is kept as a named predicate so the
  transcription of §10.1 is literal, and — decisively — so that the universal
  quantifier over executions below is *unrestricted*: it ranges over every
  inhabitant of `Wasm.MaximalExecution initial`, which is the strongest reading.
-/
def IsMaximalExecutionFrom (initial : Wasm.Config)
    (_execution : Wasm.MaximalExecution initial) : Prop :=
  True

/-- The side condition never removes an execution from the quantifier. -/
theorem isMaximalExecutionFrom_holds (initial : Wasm.Config)
    (execution : Wasm.MaximalExecution initial) :
    IsMaximalExecutionFrom initial execution :=
  trivial

/-- **SPEC §10.1**, `MaximalExecution.HasFiniteObservation`: true for a
returned, trapped or uncaught-exception finite maximal execution, and false for
`diverges`. -/
def HasFiniteObservation {initial : Wasm.Config}
    (execution : Wasm.MaximalExecution initial)
    (observation : Wasm.ExecutionObservation) : Prop :=
  match execution with
  | .finite o _ _ => o = observation
  | .diverges _ _ _ _ => False

/-- A divergent maximal execution has no finite observation. -/
theorem not_hasFiniteObservation_diverges {initial : Wasm.Config}
    (events : Nat → Wasm.Event) (configs : Nat → Wasm.Config)
    (starts : configs 0 = initial)
    (step : ∀ i, Wasm.Step (configs i) (events i) (configs (i + 1)))
    (observation : Wasm.ExecutionObservation) :
    ¬ HasFiniteObservation (Wasm.MaximalExecution.diverges events configs starts step)
      observation :=
  fun h => h

/-- A finite maximal execution has exactly its own observation. -/
theorem hasFiniteObservation_finite {initial : Wasm.Config}
    {o : Wasm.ExecutionObservation} (run : Wasm.FiniteExecution initial o)
    (maximal : Wasm.IsTerminalObservation o)
    (observation : Wasm.ExecutionObservation) :
    HasFiniteObservation (Wasm.MaximalExecution.finite o run maximal) observation ↔
      o = observation :=
  Iff.rfl

/-- **SPEC §10.1**, `MaximalExecution.CostedAs`. -/
def CostedAs {S : Setting P} {initial : Wasm.Config}
    (execution : Wasm.MaximalExecution initial)
    (costed : CostedExecutionObservation P initial) : Prop :=
  execution.CostedAs costed

/-- **SPEC §10.1**, `Universal.IsMaximalExecution`. -/
def IsMaximalExecution (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P)
    (initialization : InitializationObservation P) {initial : Wasm.Config}
    (execution : Wasm.MaximalExecution initial) : Prop :=
  StartsCostedInvocation S bytes raw initialization initial ∧
  IsMaximalExecutionFrom initial execution

/-- **SPEC §10.1**, `Universal.SemanticCorrectAt`.  Existence *and* universality:
it cannot be vacuously true for an empty run relation. -/
def SemanticCorrectAt (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P) : Prop :=
  (∃ initialization : InitializationObservation P,
    ∃ initial : Wasm.Config,
    ∃ execution : Wasm.MaximalExecution initial,
      IsMaximalExecution S bytes raw initialization execution) ∧
  ∀ (initialization : InitializationObservation P)
    (initial : Wasm.Config) (execution : Wasm.MaximalExecution initial),
    IsMaximalExecution S bytes raw initialization execution →
    ∃ observation,
      HasFiniteObservation execution observation ∧
      S.problem.Accepts raw observation

/-- **SPEC §10.1**, `Universal.SemanticCorrect`: over *every* raw invocation. -/
def SemanticCorrect (S : Setting P) (bytes : ByteArray) : Prop :=
  ∀ raw : Gemm.RawInvocation P, SemanticCorrectAt S bytes raw

/-- **SPEC §10.1**, `Universal.SemanticWithinResourcesAt`: no valid prefix
overruns the step budget, and every maximal execution is charged inside the
problem's limit. -/
def SemanticWithinResourcesAt (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P) : Prop :=
  (¬ ∃ initialization : InitializationObservation P,
    ∃ initial : Wasm.Config,
    ∃ pre : RelationalPrefix initial (S.problem.maxSteps + 1),
      StartsCostedInvocation S bytes raw initialization initial ∧ pre.Valid) ∧
  (∀ (initialization : InitializationObservation P)
    (initial : Wasm.Config) (execution : Wasm.MaximalExecution initial),
    IsMaximalExecution S bytes raw initialization execution →
    ∃ costed : CostedExecutionObservation P initial,
      CostedAs (S := S) execution costed ∧
      Cost.DynamicVector.ComponentwiseLE
        (Cost.sequentialCompose initialization.cost costed.cost)
        S.problem.limit)

/-- **SPEC §10.1**, `Universal.SemanticWithinResources`. -/
def SemanticWithinResources (S : Setting P) (bytes : ByteArray) : Prop :=
  ∀ raw : Gemm.RawInvocation P, SemanticWithinResourcesAt S bytes raw

/-- **SPEC §10.1**, `InvocationConforms`. -/
def InvocationConforms (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P) : Prop :=
  ProfileValid P bytes ∧
  SemanticCorrectAt S bytes raw ∧
  SemanticWithinResourcesAt S bytes raw

/--
  **SPEC §10.1**, `invocation_conforms_iff_extensional`.

  This is definitionally true, and that is the point: `InvocationConforms` adds
  *nothing* beyond the three extensional predicates.  It carries no certificate,
  no evaluation, no selector, and no artifact-specific side condition.  If a
  later edit smuggles an extra conjunct into `InvocationConforms`, this proof
  breaks.
-/
theorem invocation_conforms_iff_extensional (S : Setting P) (bytes : ByteArray)
    (raw : Gemm.RawInvocation P) :
    InvocationConforms S bytes raw ↔
      ProfileValid P bytes ∧
      SemanticCorrectAt S bytes raw ∧
      SemanticWithinResourcesAt S bytes raw :=
  Iff.rfl

/-- The pointwise conjunction of the three predicates is exactly conformance at
every raw invocation. -/
theorem invocation_conforms_forall (S : Setting P) (bytes : ByteArray) :
    (∀ raw : Gemm.RawInvocation P, InvocationConforms S bytes raw) ↔
      (Gemm.RawInvocation P → ProfileValid P bytes) ∧
      SemanticCorrect S bytes ∧ SemanticWithinResources S bytes := by
  constructor
  · intro h
    exact ⟨fun raw => (h raw).1, fun raw => (h raw).2.1, fun raw => (h raw).2.2⟩
  · intro h raw
    exact ⟨h.1 raw, h.2.1 raw, h.2.2 raw⟩

/-- Semantic correctness at every input is exactly `SemanticCorrect`. -/
theorem semanticCorrect_iff (S : Setting P) (bytes : ByteArray) :
    SemanticCorrect S bytes ↔ ∀ raw, SemanticCorrectAt S bytes raw :=
  Iff.rfl

/-- Resource conformance at every input is exactly `SemanticWithinResources`. -/
theorem semanticWithinResources_iff (S : Setting P) (bytes : ByteArray) :
    SemanticWithinResources S bytes ↔ ∀ raw, SemanticWithinResourcesAt S bytes raw :=
  Iff.rfl

/-- A semantically correct module really does have a maximal execution on every
input: `SemanticCorrectAt` is not vacuous. -/
theorem semanticCorrectAt_execution_exists {S : Setting P} {bytes : ByteArray}
    {raw : Gemm.RawInvocation P} (h : SemanticCorrectAt S bytes raw) :
    ∃ initialization : InitializationObservation P, ∃ initial : Wasm.Config,
      ∃ execution : Wasm.MaximalExecution initial,
        IsMaximalExecution S bytes raw initialization execution :=
  h.1

/-- Every maximal execution of a semantically correct module is accepted by the
problem's reference relation. -/
theorem semanticCorrectAt_accepts {S : Setting P} {bytes : ByteArray}
    {raw : Gemm.RawInvocation P} (h : SemanticCorrectAt S bytes raw)
    {initialization : InitializationObservation P} {initial : Wasm.Config}
    (execution : Wasm.MaximalExecution initial)
    (hmax : IsMaximalExecution S bytes raw initialization execution) :
    ∃ observation, HasFiniteObservation execution observation ∧
      S.problem.Accepts raw observation :=
  h.2 initialization initial execution hmax

/-- Semantic correctness rejects divergence: a divergent maximal execution
started by the bytes contradicts `SemanticCorrectAt`. -/
theorem semanticCorrectAt_not_diverges {S : Setting P} {bytes : ByteArray}
    {raw : Gemm.RawInvocation P} (h : SemanticCorrectAt S bytes raw)
    {initialization : InitializationObservation P} {initial : Wasm.Config}
    (events : Nat → Wasm.Event) (configs : Nat → Wasm.Config)
    (starts : configs 0 = initial)
    (step : ∀ i, Wasm.Step (configs i) (events i) (configs (i + 1)))
    (hstart : StartsCostedInvocation S bytes raw initialization initial) :
    False := by
  obtain ⟨observation, hobs, _⟩ :=
    h.2 initialization initial
      (Wasm.MaximalExecution.diverges events configs starts step) ⟨hstart, trivial⟩
  exact hobs

/-- Resource conformance forbids a valid prefix that overruns the step budget. -/
theorem semanticWithinResourcesAt_no_overrun {S : Setting P} {bytes : ByteArray}
    {raw : Gemm.RawInvocation P} (h : SemanticWithinResourcesAt S bytes raw) :
    ¬ ∃ initialization : InitializationObservation P, ∃ initial : Wasm.Config,
      ∃ pre : RelationalPrefix initial (S.problem.maxSteps + 1),
        StartsCostedInvocation S bytes raw initialization initial ∧ pre.Valid :=
  h.1

/-- Resource conformance charges every maximal execution inside the limit. -/
theorem semanticWithinResourcesAt_charge {S : Setting P} {bytes : ByteArray}
    {raw : Gemm.RawInvocation P} (h : SemanticWithinResourcesAt S bytes raw)
    {initialization : InitializationObservation P} {initial : Wasm.Config}
    (execution : Wasm.MaximalExecution initial)
    (hmax : IsMaximalExecution S bytes raw initialization execution) :
    ∃ costed : CostedExecutionObservation P initial,
      CostedAs (S := S) execution costed ∧
      Cost.DynamicVector.ComponentwiseLE
        (Cost.sequentialCompose initialization.cost costed.cost)
        S.problem.limit :=
  h.2 initialization initial execution hmax

/-- `ProfileValid` really does produce a decoded, validated, closed module. -/
theorem profileValid_module {P : Wasm.Profile} {bytes : ByteArray}
    (h : ProfileValid P bytes) :
    ∃ module : Wasm.Module,
      Wasm.decode bytes = .ok module ∧ Wasm.validateUnder P module = true ∧
      module.core.imports = [] ∧ HasExactGemmExports P module :=
  h

/-- `ProfileValid` is decode-functional: the module it names is unique. -/
theorem profileValid_module_unique {bytes : ByteArray}
    {a b : Wasm.Module} (ha : Wasm.decode bytes = .ok a)
    (hb : Wasm.decode bytes = .ok b) : a = b := by
  rw [ha] at hb
  exact (Except.ok.injEq _ _ ▸ hb).symm ▸ rfl

end Semantic

end WasmGemmGnaf.Universal
