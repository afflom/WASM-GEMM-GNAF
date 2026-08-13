/-
  Wasm/Erasure.lean --- cost instrumentation is transparent.

  Normative source: SPEC.md section 7.5:

      `Wasm/Erasure.lean` SHALL prove that removing cost labels yields exactly
      the ordinary execution:

          theorem costed_erase_iff_plain_run :
            Wasm.CostedRun P module invocation costedTrace observation ↔
              Wasm.Run module invocation (eraseCosts costedTrace) observation

      ...  Cost instrumentation SHALL not alter control, values, traps, memory,
      or observable results.

  `Wasm.CostedStep` is by construction a plain `Wasm.Step` together with the
  exact label that `Wasm.label` computes from the source configuration, so
  erasure is structural: `CostedReduces.erase` drops the labels and leaves the
  reduction sequence untouched.  The biconditional is proved in both directions.

  A remark on the exact shape of the statement.  The right-hand side of the SPEC
  display is a property of `eraseCosts costedTrace` alone, so a literal
  biconditional between it and a property of `costedTrace` can hold only if the
  costed side is invariant under changing labels inside an erasure fibre --- and
  a cost model whose labels may be changed freely is exactly the fabricated
  zero-cost trace SPEC section 7.5 forbids.  The costed side here is deliberately
  *not* invariant: `CostedStep` pins the harness installation's byte count, the
  grown page count and the rule identity to the configuration they are taken
  from.

  That is not an argument this file asks the reader to accept.  SPEC section
  7.5's literal biconditional is *refuted* here, by an explicit witness:
  `Counterexample.minimalModule` is a module that passes release validation,
  `Counterexample.forgedTrace` is a costed trace whose erasure is exactly the
  plain trace of a maximal run of that module, and
  `not_costed_erase_iff_plain_run` proves --- for every profile whatsoever ---
  that the right-hand side holds of it while the left-hand side does not.  The
  forged label differs from the one the machine computes only in a payload that
  `CostedEvent.erase` discards, which is the whole of the matter.  This is
  deviation `DEV-001` of `model/spec-deviations.json`.

  What is proved instead is the strongest true form of the display:

  * `costed_erase_iff_plain_run` --- the costed run of `costedTrace` holds
    exactly when the plain run of `eraseCosts costedTrace` holds *and*
    `costedTrace` is a labelling the machine itself produces
    (`CostedLabelling`), a condition on labels only that mentions no store, no
    terminal status and no observation;
  * `costed_run_iff_plain_run` --- with the costed trace existentially
    quantified, the side condition disappears entirely: exactly the same
    observations are reachable with and without instrumentation;
  * `costed_observation_eq_plain` --- the two runs deliver literally the same
    observation, hence the same terminal status, entry store, final ABI-visible
    store and external effects.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Costed

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Plain and costed runs -/

/-- **SPEC section 7.5.**  The plain run relation: the module and raw
invocation initialize to `initial`, and a finite execution of `initial` along
`trace` produces `observation`. -/
def Run (module : Module) (invocation : RawInvocation) (trace : List Event)
    (observation : ExecutionObservation) : Prop :=
  ∃ initial : Config,
    initialConfig module invocation = .ok initial ∧
      observation.trace = trace ∧
      FiniteExecution initial observation

/-- **SPEC section 7.5.**  The costed run relation: the same initialization,
and a costed finite execution whose recorded snapshots are the snapshots of the
configurations actually visited. -/
def CostedRun (P : Profile) (module : Module) (invocation : RawInvocation)
    (costedTrace : List CostedEvent) (observation : ExecutionObservation) : Prop :=
  ∃ (initial : Config) (configs : List ConfigResourceSnapshot),
    initialConfig module invocation = .ok initial ∧
      CostedFiniteExecution P initial costedTrace configs observation

/-- A costed trace is a *labelling of the machine* when it is the label
sequence of an actual reduction out of the initial configuration.  This is a
condition on labels alone: it mentions no observation, no store, and no
terminal status. -/
def CostedLabelling (module : Module) (invocation : RawInvocation)
    (costedTrace : List CostedEvent) : Prop :=
  ∃ (initial final : Config) (visited : List Config),
    initialConfig module invocation = .ok initial ∧
      CostedReduces initial costedTrace visited final

/-- Initialization is a function: two initial configurations of the same module
and raw invocation are equal. -/
theorem initialConfig_unique {module : Module} {invocation : RawInvocation}
    {a b : Config} (ha : initialConfig module invocation = .ok a)
    (hb : initialConfig module invocation = .ok b) : a = b := by
  rw [ha] at hb
  exact Except.ok.inj hb

/-! ## Erasure -/

/-- The costed trace of a costed run erases to exactly the observation's plain
trace. -/
theorem costedRun_erase_trace {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (h : CostedRun P module invocation costedTrace observation) :
    observation.trace = eraseCosts costedTrace := by
  obtain ⟨_, _, _, hcfe⟩ := h
  exact hcfe.trace

/-- **Erasure soundness.**  Removing the cost labels of a costed run yields the
ordinary run of the erased trace. -/
theorem costedRun_erase {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (h : CostedRun P module invocation costedTrace observation) :
    Run module invocation (eraseCosts costedTrace) observation := by
  obtain ⟨initial, configs, hinit, hcfe⟩ := h
  exact ⟨initial, hinit, hcfe.trace, hcfe.erase⟩

/-- **Erasure completeness.**  Every plain run carries a costed labelling that
erases back to it, with the same observation. -/
theorem costedRun_of_run {P : Profile} {module : Module}
    {invocation : RawInvocation} {trace : List Event}
    {observation : ExecutionObservation}
    (h : Run module invocation trace observation) :
    ∃ costedTrace : List CostedEvent,
      eraseCosts costedTrace = trace ∧
      CostedRun P module invocation costedTrace observation := by
  obtain ⟨initial, hinit, htr, final, hred, hobs⟩ := h
  rw [htr] at hred
  obtain ⟨ct, visited, hct, hcred⟩ := CostedReduces.of_reduces hred
  refine ⟨ct, hct, initial, visited.map (snapshotOf P.costTableBody.layout),
    hinit, visited, final, hcred, rfl, ?_, ?_⟩
  · rw [htr, hct]
  · exact hobs

/-! ## The decisive theorem -/

/-- **SPEC section 7.5, the decisive theorem.**  A costed run of `costedTrace`
holds exactly when the ordinary run of `eraseCosts costedTrace` holds and
`costedTrace` is a labelling the machine produces.  Cost instrumentation
therefore does not alter control, values, traps, memory, or observable results:
the whole difference between the two sides is a condition on labels. -/
theorem costed_erase_iff_plain_run {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation} :
    CostedRun P module invocation costedTrace observation ↔
      (Run module invocation (eraseCosts costedTrace) observation ∧
        CostedLabelling module invocation costedTrace) := by
  constructor
  · intro h
    refine ⟨costedRun_erase h, ?_⟩
    obtain ⟨initial, configs, hinit, visited, final, hcred, _, _, _⟩ := h
    exact ⟨initial, final, visited, hinit, hcred⟩
  · rintro ⟨⟨initial, hinit, htr, final, hred, hobs⟩,
      ⟨initial', final', visited, hinit', hcred⟩⟩
    have hi : initial' = initial := initialConfig_unique hinit' hinit
    have hcred' : CostedReduces initial costedTrace visited final' := hi ▸ hcred
    rw [htr] at hred
    have hfin : final = final' := Reduces.deterministic hred hcred'.erase
    refine ⟨initial, visited.map (snapshotOf P.costTableBody.layout), hinit,
      visited, final', hcred', rfl, htr, ?_⟩
    rw [← hfin]
    exact hobs

/-- **Cost instrumentation is transparent.**  With the costed trace
existentially quantified the side condition disappears: an observation is
reachable by a costed run exactly when it is reachable by the ordinary run of
its own trace. -/
theorem costed_run_iff_plain_run {P : Profile} {module : Module}
    {invocation : RawInvocation} {observation : ExecutionObservation} :
    (∃ costedTrace : List CostedEvent,
        CostedRun P module invocation costedTrace observation) ↔
      Run module invocation observation.trace observation := by
  constructor
  · rintro ⟨ct, h⟩
    have hrun := costedRun_erase h
    rw [← costedRun_erase_trace h] at hrun
    exact hrun
  · intro h
    obtain ⟨ct, _, hc⟩ := costedRun_of_run (P := P) h
    exact ⟨ct, hc⟩

/-- The same statement against the plain relational execution of
`Wasm/Run.lean`: instrumentation adds no observation and removes none. -/
theorem costed_run_iff_finiteExecution {P : Profile} {module : Module}
    {invocation : RawInvocation} {initial : Config}
    {observation : ExecutionObservation}
    (hinit : initialConfig module invocation = .ok initial) :
    (∃ costedTrace : List CostedEvent,
        CostedRun P module invocation costedTrace observation) ↔
      FiniteExecution initial observation := by
  rw [costed_run_iff_plain_run]
  constructor
  · rintro ⟨initial', hinit', _, hfe⟩
    have hi : initial = initial' := initialConfig_unique hinit hinit'
    rw [hi]
    exact hfe
  · intro h
    exact ⟨initial, hinit, rfl, h⟩

/-! ## SPEC section 7.5's literal biconditional is false

The display in SPEC section 7.5 reads, with its free variables universally
quantified as a Lean theorem statement does:

    CostedRun P module invocation costedTrace observation ↔
      Run module invocation (eraseCosts costedTrace) observation

The forward direction is `costedRun_erase`, proved above.  The backward
direction is refuted below.  `costedTrace` is universally quantified while the
right-hand side mentions it only through `eraseCosts costedTrace`, and
`CostedEvent.erase` is not injective: it discards the installed byte count of
`enterGemm`, the requested page count of `memoryGrowSucceed`, and it identifies
the whole of the ordinary-rule family in `Event.step`.  Any labelling in the
fibre over a genuine plain trace therefore satisfies the right-hand side, while
`CostedStep` admits exactly the one the machine computes.

The witness below is a real module of the released profile: it passes
`Wasm.validate`, it has a three-step maximal run, and the forged trace differs
from the true labelling of that run in exactly one payload. -/

/-- **Erasure is not injective.**  The installed byte count of the harness
phase transition --- the charge for the raw-byte installation --- is discarded
by erasure, so no property of an erased trace can recover it. -/
theorem erase_enterGemm_eq (n m : Nat) :
    (CostedEvent.enterGemm n).erase = (CostedEvent.enterGemm m).erase := rfl

namespace Counterexample

/-- A module of the released profile: one recursive type group holding the
pinned GEMM ABI type, one exported `gemm` returning `i32.const 0`, a zero-page
memory, and exactly the two required exports.  It is not a contrivance:
`minimalModule_validate` proves it passes the release validator. -/
def minimalModule : Module where
  types := [⟨[⟨true, [], .func gemmFuncType⟩]⟩]
  imports := []
  funcs := [⟨0, [], .cons (.i32Const 0) .nil⟩]
  tables := []
  mems := [⟨⟨.i32, ⟨0, none⟩⟩⟩]
  tags := []
  globals := []
  exports := [⟨gemmExportName, .func 0⟩, ⟨memoryExportName, .mem 0⟩]
  start := none
  elems := []
  datas := []

theorem minimalModule_exportsMemory :
    Module.exportsMemory minimalModule = true := by
  simp [Module.exportsMemory, minimalModule]

theorem minimalModule_gemmIndex : Module.gemmIndex? minimalModule = some 0 := by
  simp [Module.gemmIndex?, minimalModule]

theorem minimalModule_checkGemmExport :
    Module.checkGemmExport minimalModule = true := by
  rw [Module.checkGemmExport, minimalModule_gemmIndex]
  decide

theorem minimalModule_checkExports : Module.checkExports minimalModule = true := by
  simp [Module.checkExports, minimalModule, Module.distinctExportNames,
    Ne.symm gemmExportName_ne_memoryExportName]

/-- **The witness module passes release validation.** -/
theorem minimalModule_validate : validate minimalModule = true := by
  rw [validate, minimalModule_exportsMemory, minimalModule_checkGemmExport,
    minimalModule_checkExports]
  decide

/-- The raw invocation of the witness: no bytes at all, installed at address
zero.  The harness therefore installs exactly zero bytes. -/
def minimalRaw : RawInvocation := ⟨0, []⟩

/-- The store the witness module allocates: a zero-page memory and no global. -/
def minimalStore : Store := { memory := Memory.alloc 0 none, globals := [] }

/-- The pre-start harness configuration of the witness. -/
def minimalInitial : Config where
  store := minimalStore
  harness :=
    { gemmBody := [Instr.i32Const 0], gemmNumLocals := 0, rawPtr := 0
      rawBytes := [], args := [UInt32.ofNat 0, UInt32.ofNat 0] }
  locals := []
  stack := []
  code := []
  ctrl := []
  phase := .beforeEntry
  entry? := none
  status := .running

theorem minimal_initialConfig :
    initialConfig minimalModule minimalRaw = .ok minimalInitial := by
  simp only [initialConfig, minimalModule_validate, minimalModule_gemmIndex]
  rfl

/-- **The forged costed trace.**  Its second and third labels are the ones the
machine computes; its first claims that the harness installed one raw byte,
where the invocation carries none.  That payload is the multiplier of the
installation's `bytesWritten` charge in `eventContribution`, so forging it
forges the cost --- and the right-hand side of SPEC's display cannot tell. -/
def forgedTrace : List CostedEvent :=
  [.enterGemm 1, .i32Const, .returnGemm 0]

/-- The forged trace erases to the plain trace of the run below. -/
theorem forgedTrace_erase :
    eraseCosts forgedTrace = [Event.enterGemm, Event.step, Event.returnEvent 0] :=
  rfl

/-- The observation of that run: the exported `gemm` returns `0`, over an empty
ABI-visible store. -/
def minimalObservation : ExecutionObservation :=
  .returned (eraseCosts forgedTrace) ⟨[]⟩ 0 ⟨[]⟩ ObservableEffects.none'

/-- The run itself: install nothing, cross the harness boundary, push the
constant, return it. -/
theorem minimal_finiteExecution : FiniteExecution minimalInitial minimalObservation :=
  ⟨_,
   Reduces.cons (Step.enterGemm rfl rfl rfl rfl rfl)
     (Reduces.cons (Step.i32Const rfl rfl)
       (Reduces.single (Step.returnGemm rfl rfl rfl rfl))),
   rfl⟩

/-- **The right-hand side of SPEC's display holds of the forged trace.** -/
theorem minimal_run :
    Run minimalModule minimalRaw (eraseCosts forgedTrace) minimalObservation :=
  ⟨minimalInitial, minimal_initialConfig, rfl, minimal_finiteExecution⟩

/-- **The left-hand side does not**, under any profile: the machine labels the
harness transition with the byte count it actually installed, which is zero. -/
theorem minimal_not_costedRun (P : Profile) :
    ¬ CostedRun P minimalModule minimalRaw forgedTrace minimalObservation := by
  rintro ⟨initial, configs, hinit, visited, final, hred, -, -, -⟩
  have hi : initial = minimalInitial := initialConfig_unique hinit minimal_initialConfig
  subst hi
  cases hred with
  | cons hstep _ => exact absurd hstep.2 (by decide)

end Counterexample

/-- **SPEC section 7.5's literal biconditional is false**, and false for every
profile: instrumentation is transparent, but a plain run does not determine the
cost labels of the costed run it erases from.  This is what `DEV-001` records
and what `costed_erase_iff_plain_run` repairs with a condition on labels alone;
`costed_run_iff_plain_run` carries SPEC's intended content with no side
condition at all. -/
theorem not_costed_erase_iff_plain_run (P : Profile) :
    ¬ ∀ (module : Module) (invocation : RawInvocation)
        (costedTrace : List CostedEvent) (observation : ExecutionObservation),
        CostedRun P module invocation costedTrace observation ↔
          Run module invocation (eraseCosts costedTrace) observation := by
  intro h
  exact Counterexample.minimal_not_costedRun P
    ((h Counterexample.minimalModule Counterexample.minimalRaw
      Counterexample.forgedTrace Counterexample.minimalObservation).mpr
      Counterexample.minimal_run)

/-- The failure is one-sided: the forward direction of SPEC's display is
`costedRun_erase`, proved unconditionally.  Only the backward direction fails,
and it fails on the labels. -/
theorem costed_erase_forward {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (h : CostedRun P module invocation costedTrace observation) :
    Run module invocation (eraseCosts costedTrace) observation :=
  costedRun_erase h

/-! ## Erasure preserves the observation

The observation is the whole semantic content of a run: its terminal status,
the entry and final ABI-visible stores, and the externally visible non-memory
effects.  Erasure preserves it exactly --- not up to a projection. -/

/-- **Erasure preserves the observation.**  The plain run of an erased costed
trace delivers literally the observation the costed run delivered. -/
theorem costed_observation_eq_plain {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {costed plain : ExecutionObservation}
    (hc : CostedRun P module invocation costedTrace costed)
    (hp : Run module invocation (eraseCosts costedTrace) plain) :
    costed = plain := by
  obtain ⟨initial, configs, hinit, visited, final, hcred, _, htrc, hobsc⟩ := hc
  obtain ⟨initial', hinit', htrp, final', hredp, hobsp⟩ := hp
  have hi : initial' = initial := initialConfig_unique hinit' hinit
  rw [htrp] at hredp hobsp
  rw [htrc] at hobsc
  have hredp' : Reduces initial (eraseCosts costedTrace) final' := hi ▸ hredp
  have hfin : final = final' := Reduces.deterministic hcred.erase hredp'
  rw [hfin] at hobsc
  rw [hobsc] at hobsp
  exact Option.some.inj hobsp

/-- Consequently the deterministic semantic observation --- terminal status,
final ABI-visible store, external effects --- is preserved by erasure. -/
theorem costed_semantic_eq_plain {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {costed plain : ExecutionObservation}
    (hc : CostedRun P module invocation costedTrace costed)
    (hp : Run module invocation (eraseCosts costedTrace) plain) :
    costed.unmaskedSemantic = plain.unmaskedSemantic := by
  rw [costed_observation_eq_plain hc hp]

/-- The entry store snapshot is preserved by erasure. -/
theorem costed_entryStore_eq_plain {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {costed plain : ExecutionObservation}
    (hc : CostedRun P module invocation costedTrace costed)
    (hp : Run module invocation (eraseCosts costedTrace) plain) :
    costed.gemmEntryObservableStore? = plain.gemmEntryObservableStore? := by
  rw [costed_observation_eq_plain hc hp]

/-- The final ABI-visible store is preserved by erasure. -/
theorem costed_finalStore_eq_plain {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {costed plain : ExecutionObservation}
    (hc : CostedRun P module invocation costedTrace costed)
    (hp : Run module invocation (eraseCosts costedTrace) plain) :
    costed.finalObservableStore = plain.finalObservableStore := by
  rw [costed_observation_eq_plain hc hp]

/-- A costed observation is maximal, exactly as a plain one is. -/
theorem costedRun_maximal {P : Profile} {module : Module}
    {invocation : RawInvocation} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (_h : CostedRun P module invocation costedTrace observation) :
    IsTerminalObservation observation :=
  isTerminalObservation observation

/-! ## Cost is a function of the costed trace

SPEC section 7.5 requires the evaluator to retain the data the cost equation
needs: "a terminal store and an unannotated event list are not treated as a cost
oracle".  These are the determinism theorems that make `costExact` an equation
rather than a choice. -/

/-- **SPEC section 7.5.**  Proof-carrying evaluation evidence for one costed
maximal branch.  The cost is not a field a producer may choose: `costExact`
pins it to the fold over the retained snapshots and costed trace. -/
structure CostedExecutionObservation (P : Profile) (initial : Config) where
  /-- The plain observation this branch erases to. -/
  observation : ExecutionObservation
  /-- The costed trace. -/
  costedTrace : List CostedEvent
  /-- The recorded resource snapshots. -/
  configs : List ConfigResourceSnapshot
  /-- The costed run itself. -/
  run : CostedFiniteExecution P initial costedTrace configs observation
  /-- The observation cannot be extended. -/
  maximal : IsTerminalObservation observation
  /-- The charged cost. -/
  cost : Cost.DynamicVector
  /-- The cost equation. -/
  costExact : cost = foldTrace P.costTableBody configs costedTrace

namespace CostedExecutionObservation

variable {P : Profile} {initial : Config}

/-- **SPEC section 7.5.**  The retained cost is exactly the fold. -/
theorem cost_exact (costed : CostedExecutionObservation P initial) :
    costed.cost = foldTrace P.costTableBody costed.configs costed.costedTrace :=
  costed.costExact

/-- Erasure of the evidence: the plain finite execution it records. -/
theorem erase (costed : CostedExecutionObservation P initial) :
    FiniteExecution initial costed.observation :=
  costed.run.erase

/-- The recorded trace is the observation's trace, erased. -/
theorem trace (costed : CostedExecutionObservation P initial) :
    costed.observation.trace = eraseCosts costed.costedTrace :=
  costed.run.trace

/-- **Cost is a function of the costed trace.**  Two pieces of evidence for the
same initial configuration and the same costed trace record the same snapshots,
the same observation and therefore the same cost. -/
theorem functional_of_costedTrace
    (left right : CostedExecutionObservation P initial)
    (h : left.costedTrace = right.costedTrace) :
    left.configs = right.configs ∧
      left.observation = right.observation ∧ left.cost = right.cost := by
  obtain ⟨lv, lf, lred, lcfg, ltr, lobs⟩ := left.run
  obtain ⟨rv, rf, rred, rcfg, rtr, robs⟩ := right.run
  rw [h] at lred ltr
  obtain ⟨_, hvis, hfin⟩ := CostedReduces.unique lred rred rfl
  rw [hvis] at lcfg
  rw [hfin] at lobs
  have hcfg : left.configs = right.configs := by rw [lcfg, rcfg]
  refine ⟨hcfg, ?_, ?_⟩
  · rw [ltr] at lobs
    rw [rtr] at robs
    rw [lobs] at robs
    exact Option.some.inj robs
  · rw [left.costExact, right.costExact, hcfg, h]

/-- **A plain run cannot be paired with a cheaper costed trace.**  Evidence for
the same initial configuration whose costed traces erase to the same plain trace
is evidence for the same costed trace, the same snapshots, the same observation
and the same cost.  The rule identities, the byte counts and the peaks are all
determined by the run; none of them may be understated. -/
theorem functional_of_plainTrace
    (left right : CostedExecutionObservation P initial)
    (h : eraseCosts left.costedTrace = eraseCosts right.costedTrace) :
    left.costedTrace = right.costedTrace ∧
      left.configs = right.configs ∧
      left.observation = right.observation ∧ left.cost = right.cost := by
  obtain ⟨lv, lf, lred, lcfg, ltr, lobs⟩ := left.run
  obtain ⟨rv, rf, rred, rcfg, rtr, robs⟩ := right.run
  obtain ⟨hct, hvis, hfin⟩ := CostedReduces.unique lred rred h
  rw [hvis] at lcfg
  rw [hfin] at lobs
  have hcfg : left.configs = right.configs := by rw [lcfg, rcfg]
  refine ⟨hct, hcfg, ?_, ?_⟩
  · rw [ltr, hct] at lobs
    rw [rtr] at robs
    rw [lobs] at robs
    exact Option.some.inj robs
  · rw [left.costExact, right.costExact, hcfg, hct]

end CostedExecutionObservation

/-! ## Costed maximal executions -/

/-- Every costed finite execution erases to a maximal execution of the plain
machine. -/
def CostedFiniteExecution.maximalExecution {P : Profile} {initial : Config}
    {ct : List CostedEvent} {configs : List ConfigResourceSnapshot}
    {observation : ExecutionObservation}
    (h : CostedFiniteExecution P initial ct configs observation) :
    MaximalExecution initial :=
  .finite observation h.erase (isTerminalObservation observation)

end WasmGemmGnaf.Wasm
