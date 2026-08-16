import WasmGemmGnaf.Wasm.Core.ForcedExecution
import WasmGemmGnaf.Wasm.Core.HarnessFunctional
import WasmGemmGnaf.Wasm.Evaluate

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Harness

open WasmGemmGnaf

/-! ## Administrative charge normalization -/

/-- Instruction-sequence contexts are operational labels only; the released
charge is exactly the charge of their enclosed Core rule. -/
@[simp] theorem coreEventCost_ctxtInstrs (profile : Wasm.Profile)
    (prefixValues suffixInstrs : Nat) (event : Exec.Event) :
    Wasm.coreEventCost profile
        (.ctxtInstrs prefixValues suffixInstrs event) =
      Wasm.coreEventCost profile event := rfl

/-- Label contexts do not charge a second Core rule. -/
@[simp] theorem coreEventCost_ctxtLabel (profile : Wasm.Profile)
    (arity : Nat) (event : Exec.Event) :
    Wasm.coreEventCost profile (.ctxtLabel arity event) =
      Wasm.coreEventCost profile event := rfl

/-- Frame contexts do not charge a second Core rule. -/
@[simp] theorem coreEventCost_ctxtFrame (profile : Wasm.Profile)
    (arity : Nat) (event : Exec.Event) :
    Wasm.coreEventCost profile (.ctxtFrame arity event) =
      Wasm.coreEventCost profile event := rfl

/-- AMD-023 handler contexts are administrative labels only; as for labels
and frames, the released charge is exactly the enclosed Core rule. -/
@[simp] theorem coreEventCost_ctxtHandler (profile : Wasm.Profile)
    (arity : Nat) (event : Exec.Event) :
    Wasm.coreEventCost profile (.ctxtHandler arity event) =
      Wasm.coreEventCost profile event := rfl

/-- Releasing a completed trap from an administrative handler is one ordinary
Core rule and carries no additional dispatch or transfer coordinate. -/
@[simp] theorem coreEventCost_trapHandler (profile : Wasm.Profile)
    (arity : Nat) :
    Wasm.coreEventCost profile (.trapHandler arity) =
      Wasm.publicRuleStepCost profile := rfl

/-- Normal post-entry Harness lifting preserves the exact inner Core charge. -/
@[simp] theorem eventCost_coreAfterEntry (profile : Wasm.Profile)
    (event : Exec.Event) :
    Wasm.eventCost profile (.coreAfterEntry event) =
      Wasm.coreEventCost profile event := rfl

/-- Pre-entry Core lifting likewise preserves the exact inner Core charge. -/
@[simp] theorem eventCost_coreBeforeEntry (profile : Wasm.Profile)
    (event : Exec.Event) :
    Wasm.eventCost profile (.coreBeforeEntry event) =
      Wasm.coreEventCost profile event := rfl

/-- A successful local write contributes one ordinary Core rule and no
additional transfer or dispatch coordinate. -/
@[simp] theorem coreEventCost_localSet (profile : Wasm.Profile)
    (index : LocalIdx) :
    Wasm.coreEventCost profile (.localSet index) =
      Wasm.publicRuleStepCost profile := rfl

/-- Entering a concrete function through `call_ref` is one read rule and one
dispatch.  Its retained syntax operands do not affect the charge. -/
@[simp] theorem coreEventCost_callRefFunc (profile : Wasm.Profile)
    (operands : List Instr) :
    Wasm.coreEventCost profile (.read .callRefFunc operands) =
      { Wasm.publicRuleStepCost profile with dispatchSteps := 1 } := rfl

/-- The fixed i64-to-i32 status conversion is the sole scalar primitive in
the admitted compiler image. -/
@[simp] theorem coreEventCost_cvtopVal (profile : Wasm.Profile)
    (choice : Nat) (operands : List Instr) :
    Wasm.coreEventCost profile (.pure ⟨.cvtopVal, choice⟩ operands) =
      { Wasm.publicRuleStepCost profile with scalarOps := 1 } := rfl

/-- Exiting a value-only label costs one ordinary rule and no dispatch. -/
@[simp] theorem coreEventCost_labelVals (profile : Wasm.Profile)
    (choice : Nat) (operands : List Instr) :
    Wasm.coreEventCost profile (.pure ⟨.labelVals, choice⟩ operands) =
      Wasm.publicRuleStepCost profile := rfl

/-- Exiting a value-only activation frame contributes one dispatch. -/
@[simp] theorem coreEventCost_frameVals (profile : Wasm.Profile)
    (choice : Nat) (operands : List Instr) :
    Wasm.coreEventCost profile (.pure ⟨.frameVals, choice⟩ operands) =
      { Wasm.publicRuleStepCost profile with dispatchSteps := 1 } := rfl

/-- Exact released raw-install charge. -/
@[simp] theorem eventCost_installRaw (profile : Wasm.Profile)
    (memory : Exec.MemAddr) (offset bytes previousPages grownPages : Nat) :
    Wasm.eventCost profile
        (.installRaw memory offset bytes previousPages grownPages) =
      { Wasm.publicRuleStepCost profile with
          dispatchSteps := 1
          preparationSteps :=
            profile.costTableBody.installationPreparationUnit
          bytesWritten :=
            profile.costTableBody.installedByteWriteUnit * bytes
          memoryGrowPages := grownPages
          peakPages := previousPages + grownPages } := rfl

/-- Exact released entry-boundary charge. -/
@[simp] theorem eventCost_enterGemm (profile : Wasm.Profile)
    (function : Exec.FuncAddr) :
    Wasm.eventCost profile (.enterGemm function) =
      { Wasm.publicRuleStepCost profile with dispatchSteps := 1 } := rfl

/-- Exact released successful-return charge. -/
@[simp] theorem eventCost_returnAfterEntry (profile : Wasm.Profile) :
    Wasm.eventCost profile .returnAfterEntry =
      { Wasm.publicRuleStepCost profile with
          dispatchSteps := 1
          outputBytes := 4 } := rfl

/-! ## Compiler-path snapshot normalization -/

/-- Exact resource snapshot of an active post-entry Core configuration. -/
@[simp] theorem snapshotRaw_afterEntry
    (layout : Wasm.GcLayoutConstants) (harness : Harness)
    (entry : Exec.Store) (state : Exec.State)
    (instructions : List Exec.AdminInstr) :
    Wasm.snapshotRaw layout
        (.afterEntry harness entry (state, instructions)) =
      { liveValueSlots := state.frame.locals.length +
          (instructions.map Wasm.adminLiveSlots).sum +
          (state.store.exns.map fun exception => exception.fields.length).sum
        memoryPages := Wasm.storeMemoryPages state.store
        tableSize := Wasm.storeTableSize state.store
        liveGcBytes := Wasm.storeGcLiveBytes layout state.store } := rfl

/-- Exact resource snapshot while an instantiated module still runs its start
body, before raw bytes are installed. -/
@[simp] theorem snapshotRaw_beforeEntry
    (layout : Wasm.GcLayoutConstants) (harness : Harness)
    (state : Exec.State) (instructions : List Exec.AdminInstr) :
    Wasm.snapshotRaw layout
        (.beforeEntry harness (state, instructions)) =
      { liveValueSlots := state.frame.locals.length +
          (instructions.map Wasm.adminLiveSlots).sum +
          (state.store.exns.map fun exception => exception.fields.length).sum
        memoryPages := Wasm.storeMemoryPages state.store
        tableSize := Wasm.storeTableSize state.store
        liveGcBytes := Wasm.storeGcLiveBytes layout state.store } := rfl

/-- `readyToEnter` has no active administrative instruction list. -/
@[simp] theorem snapshotRaw_readyToEnter
    (layout : Wasm.GcLayoutConstants) (harness : Harness)
    (state : Exec.State) :
    Wasm.snapshotRaw layout (.readyToEnter harness state) =
      { liveValueSlots := state.frame.locals.length +
          (state.store.exns.map fun exception => exception.fields.length).sum
        memoryPages := Wasm.storeMemoryPages state.store
        tableSize := Wasm.storeTableSize state.store
        liveGcBytes := Wasm.storeGcLiveBytes layout state.store } := by
  simp [Wasm.snapshotRaw, Wasm.rawConfigState?, Wasm.rawConfigInstrs]

/-- A successful returned configuration likewise has no active Core list. -/
@[simp] theorem snapshotRaw_returned
    (layout : Wasm.GcLayoutConstants) (harness : Harness)
    (entry : Exec.Store) (value : Exec.Val) (state : Exec.State) :
    Wasm.snapshotRaw layout (.returned harness entry value state) =
      { liveValueSlots := state.frame.locals.length +
          (state.store.exns.map fun exception => exception.fields.length).sum
        memoryPages := Wasm.storeMemoryPages state.store
        tableSize := Wasm.storeTableSize state.store
        liveGcBytes := Wasm.storeGcLiveBytes layout state.store } := by
  simp [Wasm.snapshotRaw, Wasm.rawConfigState?, Wasm.rawConfigInstrs]

/-- The exact nested frame/label live-slot formula used at direct-compiler
function entry. -/
theorem snapshotRaw_afterEntry_frame_label
    (layout : Wasm.GcLayoutConstants) (harness : Harness)
    (entry store : Exec.Store) (outerFrame innerFrame : Exec.Frame)
    (body : List Exec.AdminInstr) :
    Wasm.snapshotRaw layout
        (.afterEntry harness entry
          (⟨store, outerFrame⟩,
            [.frame 1 innerFrame [.label 1 [] body]])) =
      { liveValueSlots :=
          outerFrame.locals.length + 1 + innerFrame.locals.length + 1 +
            (body.map Wasm.adminLiveSlots).sum +
            (store.exns.map fun exception => exception.fields.length).sum
        memoryPages := Wasm.storeMemoryPages store
        tableSize := Wasm.storeTableSize store
        liveGcBytes := Wasm.storeGcLiveBytes layout store } := by
  simp [Wasm.snapshotRaw, Wasm.rawConfigState?, Wasm.rawConfigInstrs,
    Wasm.adminLiveSlots]
  omega

/-!
# Cost-preserving target-forced execution

Administrative context rules can give one Core transition several different
event labels.  `ForcedTargets` therefore cannot compare traces.  For exact
cost reflection, however, event equality is unnecessary: it is enough that
all transitions from each forced source reach the same target and receive the
same public charge.  The carrier below records precisely that local fact.
-/

/-- A target-forced finite path whose alternative event derivations have the
same profile charge at every source.  The conclusion is not stored: every
constructor contains a genuine operational step and a local inversion proof. -/
inductive CostForcedTargets (profile : Wasm.Profile) : Config → Config → Prop where
  | terminal {config : Config} (terminal : IsTerminal config) :
      CostForcedTargets profile config config
  | cons {config next final : Config} {event : Event}
      (step : StepA config event next)
      (targetCostUnique : ∀ {otherEvent : Event} {otherNext : Config},
        StepA config otherEvent otherNext →
          otherNext = next ∧
            Wasm.eventCost profile otherEvent = Wasm.eventCost profile event)
      (tail : CostForcedTargets profile next final) :
      CostForcedTargets profile config final

/-- Locally cost-functional paths compose.  The join configuration is not
charged here; snapshots are accounted for only by the indexed carrier below. -/
theorem CostForcedTargets.trans {profile : Wasm.Profile}
    {initial middle final : Config}
    (left : CostForcedTargets profile initial middle)
    (right : CostForcedTargets profile middle final) :
    CostForcedTargets profile initial final := by
  induction left with
  | terminal _ => exact right
  | cons step targetCostUnique _ ih =>
      exact .cons step targetCostUnique (ih right)

/-- Forgetting the local cost equation leaves the ordinary target-forced
path used by trace-insensitive refinement. -/
theorem CostForcedTargets.toForcedTargets {profile : Wasm.Profile}
    {initial final : Config} (forced : CostForcedTargets profile initial final) :
    ForcedTargets initial final := by
  induction forced with
  | terminal terminal => exact .terminal terminal
  | cons step unique _ ih =>
      exact .cons step (fun other => (unique other).1) ih

/-- Along a cost-preserving target-forced path, any two independently
cost-labelled reductions to terminal configurations visit the same raw
configurations, reach the same final configuration, and have identical
cumulative event contribution.  Their event labels themselves may differ. -/
theorem CostForcedTargets.costedReduces_functional
    {profile : Wasm.Profile} {initial final : Config}
    (forced : CostForcedTargets profile initial final)
    {leftFinal rightFinal : Config}
    {leftTrace rightTrace : List Wasm.CostedEvent}
    {leftVisited rightVisited : List Config}
    (leftReduction : Wasm.CostedReduces initial leftTrace leftVisited leftFinal)
    (rightReduction : Wasm.CostedReduces initial rightTrace rightVisited rightFinal)
    (leftTerminal : IsTerminal leftFinal)
    (rightTerminal : IsTerminal rightFinal) :
    leftVisited = rightVisited ∧ leftFinal = rightFinal ∧
      Wasm.traceContribution profile.costTableBody leftTrace =
        Wasm.traceContribution profile.costTableBody rightTrace := by
  induction forced generalizing leftFinal rightFinal leftTrace rightTrace
      leftVisited rightVisited with
  | terminal sourceTerminal =>
      cases leftReduction with
      | refl =>
          cases rightReduction with
          | refl => exact ⟨rfl, rfl, rfl⟩
          | cons _ rightStep _ => exact (sourceTerminal.not_step rightStep).elim
      | cons _ leftStep _ => exact (sourceTerminal.not_step leftStep).elim
  | @cons source next final event step targetCostUnique tail ih =>
      cases leftReduction with
      | refl => exact (leftTerminal.not_step step).elim
      | @cons _ leftNext leftFinal leftRest leftVisited leftCosted leftStep
          leftTail =>
          cases rightReduction with
          | refl => exact (rightTerminal.not_step step).elim
          | @cons _ rightNext rightFinal rightRest rightVisited rightCosted
              rightStep rightTail =>
              obtain ⟨leftNextEq, leftCostEq⟩ := targetCostUnique leftStep
              obtain ⟨rightNextEq, rightCostEq⟩ := targetCostUnique rightStep
              subst leftNext
              subst rightNext
              obtain ⟨visitedEq, finalEq, contributionEq⟩ :=
                ih leftTail rightTail leftTerminal rightTerminal
              subst rightVisited
              subst rightFinal
              refine ⟨rfl, rfl, ?_⟩
              simp only [Wasm.traceContribution]
              change Wasm.eventCostBody profile.costTableBody leftCosted.event =
                Wasm.eventCostBody profile.costTableBody event at leftCostEq
              change Wasm.eventCostBody profile.costTableBody rightCosted.event =
                Wasm.eventCostBody profile.costTableBody event at rightCostEq
              rw [leftCostEq, rightCostEq, contributionEq]

/-- Consequently, two exact costed finite executions from the same forced
source retain identical resource snapshots and have the same complete
sum/maximum fold, even if redundant administrative context labels differ. -/
theorem CostForcedTargets.foldTrace_functional
    {profile : Wasm.Profile} {initial : Wasm.Config} {final : Config}
    (forced : CostForcedTargets profile initial.1 final)
    {leftTrace rightTrace : List Wasm.CostedEvent}
    {leftConfigs rightConfigs : Foundation.NonemptyCanonicalList
      Wasm.ConfigResourceSnapshot}
    {leftObservation rightObservation : Wasm.ExecutionObservation}
    (leftRun : Wasm.CostedFiniteExecution profile initial leftTrace
      leftConfigs leftObservation)
    (rightRun : Wasm.CostedFiniteExecution profile initial rightTrace
      rightConfigs rightObservation) :
    Wasm.Cost.foldTrace profile.costTableBody leftConfigs leftTrace =
      Wasm.Cost.foldTrace profile.costTableBody rightConfigs rightTrace := by
  obtain ⟨leftVisited, leftFinal, leftReduction, leftConfigsEq,
    leftObserves⟩ := leftRun
  obtain ⟨rightVisited, rightFinal, rightReduction, rightConfigsEq,
    rightObserves⟩ := rightRun
  obtain ⟨visitedEq, _, contributionEq⟩ :=
    forced.costedReduces_functional leftReduction rightReduction
      leftObserves.isTerminal rightObserves.isTerminal
  unfold Wasm.Cost.foldTrace
  rw [leftConfigsEq, rightConfigsEq, visitedEq, contributionEq]

/-! ## Directly indexed exact charge

For compiler cost reflection it is convenient to avoid first constructing a
second costed observation.  The carrier below indexes the same locally
cost-functional path by its exact event-plus-snapshot fold.  Every coordinate
is still forced by genuine steps and executable `snapshotRaw` calls.
-/

/-- Move one configuration snapshot in front of a tail trace.  Snapshot
vectors have zero cumulative coordinates, so this changes neither sums nor
the maximum of any peak coordinate. -/
theorem compose_trace_snapshot (eventCost tailCost peakCost :
    Cost.DynamicVector) (snapshot : Wasm.ConfigResourceSnapshot) :
    Cost.sequentialCompose
        (Cost.sequentialCompose eventCost tailCost)
        (Cost.ComponentwiseMax (Wasm.snapshotPeak snapshot) peakCost) =
      Cost.sequentialCompose eventCost
        (Cost.sequentialCompose (Wasm.snapshotPeak snapshot)
          (Cost.sequentialCompose tailCost peakCost)) := by
  cases eventCost
  cases tailCost
  cases peakCost
  cases snapshot
  simp [Cost.sequentialCompose, Cost.ComponentwiseMax, Wasm.snapshotPeak,
    Cost.DynamicVector.zero, Nat.add_assoc, Nat.max_comm,
    Nat.max_left_comm]

/-- A finite locally cost-functional path indexed by the exact full
event/snapshot fold of every execution it permits. -/
inductive ChargedForcedTargets (profile : Wasm.Profile) :
    Config → Cost.DynamicVector → Config → Prop where
  | terminal {config : Config} (terminal : IsTerminal config) :
      ChargedForcedTargets profile config
        (Wasm.snapshotPeak
          (Wasm.snapshotRaw profile.costTableBody.layout config)) config
  | cons {config next final : Config} {event : Event}
      {tailCost : Cost.DynamicVector}
      (step : StepA config event next)
      (targetCostUnique : ∀ {otherEvent : Event} {otherNext : Config},
        StepA config otherEvent otherNext →
          otherNext = next ∧
            Wasm.eventCost profile otherEvent = Wasm.eventCost profile event)
      (tail : ChargedForcedTargets profile next tailCost final) :
      ChargedForcedTargets profile config
        (Cost.sequentialCompose (Wasm.eventCost profile event)
          (Cost.sequentialCompose
            (Wasm.snapshotPeak
              (Wasm.snapshotRaw profile.costTableBody.layout config))
            tailCost)) final

/-- The cost index is extensional: a proved vector equality may be used to
replace it without changing the operational path. -/
theorem ChargedForcedTargets.cost_congr {profile : Wasm.Profile}
    {initial final : Config} {left right : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial left final)
    (costEq : left = right) :
    ChargedForcedTargets profile initial right final := by
  subst right
  exact forced

/-- Lift one locally target- and cost-functional Core transition through the
normal post-entry Harness phase.  Administrative Core labels may differ, but
their public charges must agree; trapping and phase-boundary alternatives are
excluded by the same concrete source/target facts used by refinement. -/
theorem afterEntry_target_cost_unique_of_core
    {profile : Wasm.Profile}
    {harness : Harness} {entry : Exec.Store}
    {source target : Exec.Config} {event : Exec.Event}
    (targetNotTrap : target.2 ≠ [.trap])
    (sourceNotReturn : ∀ (state : Exec.State) (value : Exec.Val),
      source ≠ (state, Exec.vals [value]))
    (sourceNotThrow : ∀ (state : Exec.State) (address : Exec.ExnAddr),
      source ≠ (state,
        [.addrref (.exnAddr address), .plain .throwRef]))
    (step : Exec.StepA source event target)
    (noTrap : coreTrapCause? event = none)
    (allCore : ∀ {otherEvent : Exec.Event} {otherNext : Exec.Config},
      Exec.StepA source otherEvent otherNext →
        otherNext = target ∧ coreTrapCause? otherEvent = none ∧
          Wasm.coreEventCost profile otherEvent =
            Wasm.coreEventCost profile event) :
    StepA (.afterEntry harness entry source) (.coreAfterEntry event)
        (.afterEntry harness entry target) ∧
      ∀ {otherEvent : Event} {otherNext : Config},
        StepA (.afterEntry harness entry source) otherEvent otherNext →
          otherNext = .afterEntry harness entry target ∧
            Wasm.eventCost profile otherEvent =
              Wasm.eventCost profile (.coreAfterEntry event) := by
  refine And.intro (.coreAfter step noTrap targetNotTrap) ?_
  intro otherEvent otherNext otherStep
  have targetEq := afterEntry_target_unique_of_core
    targetNotTrap sourceNotReturn sourceNotThrow
    (fun coreStep =>
      let facts := allCore coreStep
      And.intro facts.1 facts.2.1)
    otherStep
  refine And.intro targetEq ?_
  cases otherStep with
  | coreAfter coreStep otherNoTrap otherNotTrap =>
      exact (allCore coreStep).2.2
  | coreAfterTrap hStep hCause hNot =>
      have noneEq := (allCore hStep).2.1
      simp [noneEq] at hCause
  | coreAfterTrapFinal hStep hCause =>
      have noneEq := (allCore hStep).2.1
      simp [noneEq] at hCause
  | returnAfter => exact (sourceNotReturn _ _ rfl).elim
  | throwAfter => exact (sourceNotThrow _ _ rfl).elim

/-- The released entry transition is target- and cost-functional: invocation
is an executable configuration builder, and the Harness event retains only the
fixed exported address. -/
theorem enterGemm_target_cost_unique
    {profile : Wasm.Profile} {harness : Harness} {state : Exec.State}
    {target : Exec.Config}
    (invoke : Exec.InvokeA state.store harness.gemmAddr harness.args target) :
    StepA (.readyToEnter harness state) (.enterGemm harness.gemmAddr)
        (.afterEntry harness state.store target) ∧
      ∀ {otherEvent : Event} {otherNext : Config},
        StepA (.readyToEnter harness state) otherEvent otherNext →
          otherNext = .afterEntry harness state.store target ∧
            Wasm.eventCost profile otherEvent =
              Wasm.eventCost profile (.enterGemm harness.gemmAddr) := by
  refine ⟨.enterGemm invoke, ?_⟩
  intro otherEvent otherNext otherStep
  cases otherStep with
  | enterGemm otherInvoke =>
      have targetEq := Exec.InvokeA.target_functional otherInvoke invoke
      subst targetEq
      exact ⟨rfl, rfl⟩

/-- Once the empty Core body is known inert, a successful raw installation is
the sole outgoing pre-entry transition.  The exact computed result fixes its
target, payload, and public charge. -/
theorem installRaw_target_cost_unique
    {profile : Wasm.Profile} {harness : Harness} {state target : Exec.State}
    {previousPages grownPages : Nat}
    (install : installRaw? harness state =
      some (previousPages, grownPages, target))
    (noCore : ∀ {event : Exec.Event} {next : Exec.Config},
      ¬ Exec.StepA (state, []) event next) :
    StepA (.beforeEntry harness (state, []))
        (.installRaw harness.memoryAddr harness.request.rawPtr.val
          harness.request.rawLen.val previousPages grownPages)
        (.readyToEnter harness target) ∧
      ∀ {otherEvent : Event} {otherNext : Config},
        StepA (.beforeEntry harness (state, [])) otherEvent otherNext →
          otherNext = .readyToEnter harness target ∧
            Wasm.eventCost profile otherEvent = Wasm.eventCost profile
              (.installRaw harness.memoryAddr harness.request.rawPtr.val
                harness.request.rawLen.val previousPages grownPages) := by
  refine ⟨.installRaw install, ?_⟩
  intro otherEvent otherNext otherStep
  cases otherStep with
  | coreBefore coreStep hcause htarget => exact (noCore coreStep).elim
  | coreBeforeTrap coreStep hcause htarget => exact (noCore coreStep).elim
  | coreBeforeTrapFinal coreStep hcause => exact (noCore coreStep).elim
  | installRaw otherInstall =>
      have resultEq := Option.some.inj (otherInstall.symm.trans install)
      cases resultEq
      exact ⟨rfl, rfl⟩

/-- A numeric singleton result with no latent Core reduction can only take the
released return transition.  Fixing that event invokes labelled Harness
functionality for the exact target and makes its output charge canonical. -/
theorem returnAfter_num_target_cost_unique
    {profile : Wasm.Profile} {harness : Harness} {entry : Exec.Store}
    {state : Exec.State} {value : Exec.NumVal}
    (noCore : ∀ {event : Exec.Event} {next : Exec.Config},
      ¬ Exec.StepA (state, Exec.vals [.num value]) event next) :
    StepA (.afterEntry harness entry (state, Exec.vals [.num value]))
        .returnAfterEntry (.returned harness entry (.num value) state) ∧
      ∀ {otherEvent : Event} {otherNext : Config},
        StepA (.afterEntry harness entry (state, Exec.vals [.num value]))
          otherEvent otherNext →
          otherNext = .returned harness entry (.num value) state ∧
            Wasm.eventCost profile otherEvent =
              Wasm.eventCost profile .returnAfterEntry := by
  refine ⟨.returnAfter, ?_⟩
  intro otherEvent otherNext otherStep
  have eventEq : otherEvent = .returnAfterEntry := by
    generalize hsource :
      Config.afterEntry harness entry (state, Exec.vals [.num value]) =
        source at otherStep
    induction otherStep <;> simp_all [Exec.vals]
    all_goals first | exact (noCore (by assumption)).elim
  subst otherEvent
  have targetEq := StepA.target_functional otherStep
    (StepA.returnAfter (h := harness) (entry := entry) (z := state)
      (v := .num value))
  exact ⟨targetEq, rfl⟩

private theorem snapshotPeak_idempotent
    (snapshot : Wasm.ConfigResourceSnapshot) :
    Cost.sequentialCompose (Wasm.snapshotPeak snapshot)
        (Wasm.snapshotPeak snapshot) =
      Wasm.snapshotPeak snapshot := by
  cases snapshot
  simp [Cost.sequentialCompose, Wasm.snapshotPeak,
    Cost.DynamicVector.zero]

private theorem snapshotPeak_absorb_event_tail
    (snapshot : Wasm.ConfigResourceSnapshot)
    (eventCost tailCost : Cost.DynamicVector) :
    Cost.sequentialCompose (Wasm.snapshotPeak snapshot)
        (Cost.sequentialCompose eventCost
          (Cost.sequentialCompose (Wasm.snapshotPeak snapshot) tailCost)) =
      Cost.sequentialCompose eventCost
        (Cost.sequentialCompose (Wasm.snapshotPeak snapshot) tailCost) := by
  cases snapshot
  cases eventCost
  cases tailCost
  simp [Cost.sequentialCompose, Wasm.snapshotPeak,
    Cost.DynamicVector.zero]
  all_goals omega

/-- The initial snapshot of a charged path is already present in its index.
Composing that same zero-cumulative snapshot once more therefore changes
neither a cumulative coordinate nor any peak coordinate. -/
theorem ChargedForcedTargets.absorb_initial_snapshot
    {profile : Wasm.Profile} {initial final : Config}
    {cost : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial cost final) :
    Cost.sequentialCompose
        (Wasm.snapshotPeak
          (Wasm.snapshotRaw profile.costTableBody.layout initial))
        cost = cost := by
  cases forced with
  | terminal terminal =>
      exact snapshotPeak_idempotent _
  | cons step unique tail =>
      exact snapshotPeak_absorb_event_tail _ _ _

/-- Charged target-forced paths compose.  The shared join snapshot is already
the terminal snapshot of the left path and the initial snapshot of the right
path; idempotence of peak maxima makes that duplication observationally
neutral. -/
theorem ChargedForcedTargets.trans {profile : Wasm.Profile}
    {initial middle final : Config}
    {leftCost rightCost : Cost.DynamicVector}
    (left : ChargedForcedTargets profile initial leftCost middle)
    (right : ChargedForcedTargets profile middle rightCost final) :
    ChargedForcedTargets profile initial
      (Cost.sequentialCompose leftCost rightCost) final := by
  induction left with
  | terminal terminal =>
      exact right.cost_congr right.absorb_initial_snapshot.symm
  | @cons source next middle event tailCost step unique tail ih =>
      have combined := ChargedForcedTargets.cons step unique (ih right)
      apply combined.cost_congr
      simp only [Cost.sequentialCompose_assoc]

/-- Every locally cost-functional forced path constructively determines its
exact event-and-snapshot fold.  This packages the nested arithmetic index
without using choice or an evaluator. -/
theorem CostForcedTargets.exists_charged {profile : Wasm.Profile}
    {initial final : Config}
    (forced : CostForcedTargets profile initial final) :
    ∃ cost, ChargedForcedTargets profile initial cost final := by
  induction forced with
  | terminal terminal => exact ⟨_, .terminal terminal⟩
  | cons step unique _ ih =>
      obtain ⟨tailCost, tail⟩ := ih
      exact ⟨_, .cons step unique tail⟩

/-- Forget the exact index and retain the cost-functional path. -/
theorem ChargedForcedTargets.toCostForcedTargets {profile : Wasm.Profile}
    {initial final : Config} {cost : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial cost final) :
    CostForcedTargets profile initial final := by
  induction forced with
  | terminal terminal => exact .terminal terminal
  | cons step unique _ ih => exact .cons step unique ih

/-- Any independently labelled reduction along a charged forced path has the
carrier's exact full fold. -/
theorem ChargedForcedTargets.fold_of_costedReduces
    {profile : Wasm.Profile} {initial final : Config}
    {cost : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial cost final)
    {otherFinal : Config} {trace : List Wasm.CostedEvent}
    {visited : List Config}
    (reduction : Wasm.CostedReduces initial trace visited otherFinal)
    (terminal : IsTerminal otherFinal) :
    Cost.sequentialCompose
        (Wasm.traceContribution profile.costTableBody trace)
        (Wasm.peakOverConfigs
          (visited.map (Wasm.snapshotRaw profile.costTableBody.layout))) =
      cost := by
  induction forced generalizing otherFinal trace visited with
  | terminal sourceTerminal =>
      cases reduction with
      | refl =>
          simp [Wasm.traceContribution, Wasm.peakOverConfigs,
            Cost.sequentialCompose_zero_left,
            Cost.componentwiseMax_zero_right]
      | cons _ step _ => exact (sourceTerminal.not_step step).elim
  | @cons source next final event tailCost step targetCostUnique tail ih =>
      cases reduction with
      | refl => exact (terminal.not_step step).elim
      | @cons _ otherNext otherFinal rest otherVisited costed otherStep
          otherTail =>
          obtain ⟨nextEq, eventCostEq⟩ := targetCostUnique otherStep
          subst otherNext
          have tailEq := ih otherTail terminal
          simp only [Wasm.traceContribution, List.map_cons,
            Wasm.peakOverConfigs]
          change Cost.sequentialCompose
              (Cost.sequentialCompose
                (Wasm.eventCost profile costed.erase)
                (Wasm.traceContribution profile.costTableBody rest))
              (Cost.ComponentwiseMax
                (Wasm.snapshotPeak
                  (Wasm.snapshotRaw profile.costTableBody.layout source))
                (Wasm.peakOverConfigs
                  (otherVisited.map
                    (Wasm.snapshotRaw profile.costTableBody.layout)))) = _
          rw [compose_trace_snapshot, eventCostEq, tailEq]

/-- An explicitly constructed canonical cost-labelled reduction pins the
otherwise existential charge of a locally cost-functional forced path.  The
caller retains the concrete visited list, so resource peaks can be normalized
without extracting data from a proof. -/
theorem CostForcedTargets.charged_of_costedReduces
    {profile : Wasm.Profile} {initial final : Config}
    (forced : CostForcedTargets profile initial final)
    {trace : List Wasm.CostedEvent} {visited : List Config}
    (reduction : Wasm.CostedReduces initial trace visited final)
    (terminal : IsTerminal final) :
    ChargedForcedTargets profile initial
      (Cost.sequentialCompose
        (Wasm.traceContribution profile.costTableBody trace)
        (Wasm.peakOverConfigs
          (visited.map
            (Wasm.snapshotRaw profile.costTableBody.layout)))) final := by
  obtain ⟨cost, charged⟩ := forced.exists_charged
  apply charged.cost_congr
  exact (charged.fold_of_costedReduces reduction terminal).symm

/-- A concrete plain reduction along a locally cost-functional forced path
identifies the carrier's exact charge.  This lets compiler proofs calculate
one canonical labelled trace while retaining equality for every alternative
administrative labelling admitted by the relation. -/
theorem CostForcedTargets.charged_of_steps
    {profile : Wasm.Profile} {initial final : Config}
    (forced : CostForcedTargets profile initial final)
    {trace : List Event} (steps : StepsA initial trace final)
    (terminal : IsTerminal final) :
    ∃ visited : List Config,
      ChargedForcedTargets profile initial
        (Cost.sequentialCompose
          (Wasm.traceContribution profile.costTableBody
            (Wasm.labelCosts trace))
          (Wasm.peakOverConfigs
            (visited.map
              (Wasm.snapshotRaw profile.costTableBody.layout)))) final := by
  obtain ⟨visited, reduction⟩ := Wasm.CostedReduces.label steps
  exact ⟨visited, forced.charged_of_costedReduces reduction terminal⟩

/-- Public costed-execution form of `fold_of_costedReduces`. -/
theorem ChargedForcedTargets.foldTrace_eq
    {profile : Wasm.Profile} {initial : Wasm.Config} {final : Config}
    {cost : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial.1 cost final)
    {trace : List Wasm.CostedEvent}
    {configs : Foundation.NonemptyCanonicalList Wasm.ConfigResourceSnapshot}
    {observation : Wasm.ExecutionObservation}
    (run : Wasm.CostedFiniteExecution profile initial trace configs
      observation) :
    Wasm.Cost.foldTrace profile.costTableBody configs trace = cost := by
  obtain ⟨visited, otherFinal, reduction, configsEq, observes⟩ := run
  unfold Wasm.Cost.foldTrace
  rw [configsEq]
  exact forced.fold_of_costedReduces reduction observes.isTerminal

/-- The charge retained by any public costed observation along the forced
path is the carrier index itself. -/
theorem ChargedForcedTargets.observation_cost_eq
    {profile : Wasm.Profile} {initial : Wasm.Config} {final : Config}
    {cost : Cost.DynamicVector}
    (forced : ChargedForcedTargets profile initial.1 cost final)
    (observation : Wasm.CostedExecutionObservation profile initial) :
    observation.cost = cost := by
  rw [observation.costExact]
  exact forced.foldTrace_eq observation.run

end WasmGemmGnaf.Wasm.Core.Harness
