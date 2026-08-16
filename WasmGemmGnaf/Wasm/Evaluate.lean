/-
  Public amended-Core evaluation carriers and fresh-invocation initialization.

  This file is below `Universal`: every carrier is stated directly over the
  public Core harness relation.  The bounded all-branch explorer is built in a
  separate layer from the executable Harness successor enumeration.
-/
import WasmGemmGnaf.Wasm.Run
import WasmGemmGnaf.Wasm.CoreValidation
import WasmGemmGnaf.Wasm.Core.BinaryWellFormed
import WasmGemmGnaf.Wasm.Core.CostAccounting
import WasmGemmGnaf.Wasm.Core.Profile
import WasmGemmGnaf.Foundation.Result
import WasmGemmGnaf.Cost.Aggregate
import WasmGemmGnaf.Cost.Trace

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Exact public event costs -/

/-- One amended-Core rule step at the cost table's released rule-step unit. -/
def publicRuleStepCostBody (table : CostTableBody) : Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      wasmRuleSteps := table.ruleStepUnit }

/-- Profile-indexed spelling of one amended-Core rule step. -/
def publicRuleStepCost (profile : Profile) : Cost.DynamicVector :=
  publicRuleStepCostBody profile.costTableBody

/-- Scalar primitive operations completed by one pure Core rule.  A trapping
numeric rule charges the attempted rule step but no completed scalar operation,
matching the transfer convention for trapping loads and stores. -/
def pureScalarOps : Core.Exec.PureRule → Nat
  | .unopVal | .binopVal | .testop | .relop | .cvtopVal => 1
  | _ => 0

/-- Control-transfer contribution of a pure Core rule. -/
def pureDispatchSteps : Core.Exec.PureRule → Nat
  | .ifTrue | .ifFalse | .brLabelZero | .brLabelSucc | .brHandler |
      .brIfTrue | .brIfFalse | .brTableLt | .brTableGe |
      .brOnNullNull | .brOnNullAddr | .brOnNonNullNull |
      .brOnNonNullAddr | .callIndirect | .returnCallIndirect |
      .frameVals | .returnFrame | .returnLabel | .returnHandler => 1
  | _ => 0

/-- Control-transfer contribution of a store-reading Core rule. -/
def readDispatchSteps : Core.Exec.ReadRule → Nat
  | .brOnCastSucceed | .brOnCastFail | .brOnCastFailSucceed |
      .brOnCastFailFail | .call | .callRefNull | .callRefFunc | .returnCall |
      .returnCallRefLabel | .returnCallRefHandler | .returnCallRefFrameNull |
      .returnCallRefFrameAddr | .throwRefNull | .throwRefInstrs |
      .throwRefLabel | .throwRefFrame | .throwRefHandlerEmpty |
      .throwRefHandlerCatch | .throwRefHandlerCatchRef |
      .throwRefHandlerCatchAll | .throwRefHandlerCatchAllRef |
      .throwRefHandlerNext => 1
  | _ => 0

/-- The width transferred by a successful store-reading memory rule.  The
event retains the source instruction operands, so packed and vector widths are
read from the instruction that fired rather than guessed from the result. -/
def completedReadBytes : Core.Exec.ReadRule → List Core.Instr → Nat
  | .loadNumVal, [_, .load nt none _ _] => nt.size / 8
  | .loadPackVal, [_, .load _ (some op) _ _] => op.sz.toNat / 8
  | .vloadVal, [_, .vload vt none _ _] => vt.size / 8
  | .vloadPackVal, [_, .vload _ (some (.shape sz lanes _)) _ _] =>
      sz.toNat * lanes / 8
  | .vloadSplatVal, [_, .vload _ (some (.splat sz)) _ _] => sz.toNat / 8
  | .vloadZeroVal, [_, .vload _ (some (.zero sz)) _ _] => sz.toNat / 8
  | .vloadLaneVal, [_, _, .vloadLane _ sz _ _ _] => sz.toNat / 8
  | _, _ => 0

/-- The complete cost of one inner amended-Core rule event.  Context labels
charge the enclosed rule exactly once; state-writing events retain their exact
transfer/allocation operands. -/
def coreEventCostBody (table : CostTableBody) :
    Core.Exec.Event → Cost.DynamicVector
  | .ctxtInstrs _ _ inner | .ctxtLabel _ inner | .ctxtFrame _ inner |
      .ctxtHandler _ inner =>
      coreEventCostBody table inner
  | .trapHandler _ => publicRuleStepCostBody table
  | .pure event _ =>
      { publicRuleStepCostBody table with
          dispatchSteps := pureDispatchSteps event.rule
          scalarOps := pureScalarOps event.rule }
  | .read rule operands =>
      { publicRuleStepCostBody table with
          dispatchSteps := readDispatchSteps rule
          bytesRead := completedReadBytes rule operands }
  | .throw _ _ =>
      { publicRuleStepCostBody table with
          dispatchSteps := 1
          gcObjectsAllocated := 1
          gcBytesInitialized := 24 }
  | .tableGrowSucceed _ delta _ newSize =>
      { publicRuleStepCostBody table with
          tableElementsAllocated := delta
          peakStackValues := newSize }
  | .storeNumVal _ bytes | .storePackVal _ bytes |
      .vstoreVal _ bytes | .vstoreLaneVal _ bytes =>
      { publicRuleStepCostBody table with bytesWritten := bytes }
  | .memoryGrowSucceed _ delta _ newPages =>
      { publicRuleStepCostBody table with
          memoryGrowPages := delta
          peakPages := newPages }
  | .structNew _ fields =>
      { publicRuleStepCostBody table with
          gcObjectsAllocated := 1
          gcBytesInitialized :=
            8 + fields * table.layout.referenceWidth }
  | .arrayNewFixed _ fields =>
      { publicRuleStepCostBody table with
          gcObjectsAllocated := 1
          gcBytesInitialized :=
            16 + fields * table.layout.referenceWidth }
  | _ => publicRuleStepCostBody table

/-- Profile-indexed spelling of the complete Core-event charge. -/
def coreEventCost (profile : Profile) (event : Core.Exec.Event) :
    Cost.DynamicVector :=
  coreEventCostBody profile.costTableBody event

/-- The cost of one exact public Harness event. -/
def eventCostBody (table : CostTableBody) : Event → Cost.DynamicVector
  | .initialize events =>
      { Cost.DynamicVector.zero with
          instantiationSteps := events.length
          wasmRuleSteps := table.ruleStepUnit * events.length }
  | .coreBeforeEntry event | .coreAfterEntry event => coreEventCostBody table event
  | .installRaw _ _ bytes previousPages grownPages =>
      { publicRuleStepCostBody table with
          dispatchSteps := 1
          preparationSteps := table.installationPreparationUnit
          bytesWritten := table.installedByteWriteUnit * bytes
          memoryGrowPages := grownPages
          peakPages := previousPages + grownPages }
  | .enterGemm _ =>
      { publicRuleStepCostBody table with dispatchSteps := 1 }
  | .returnAfterEntry =>
      { publicRuleStepCostBody table with dispatchSteps := 1, outputBytes := 4 }
  | .throwBeforeEntry _ | .throwAfterEntry _ =>
      { publicRuleStepCostBody table with dispatchSteps := 1 }

/-- The cost of one exact public Harness event. -/
def eventCost (profile : Profile) (event : Event) : Cost.DynamicVector :=
  eventCostBody profile.costTableBody event

/-- Cost a public trace in execution order. -/
def executionTraceCost (profile : Profile) : List Event → Cost.DynamicVector
  | [] => Cost.DynamicVector.zero
  | event :: rest =>
      Cost.sequentialCompose (eventCost profile event)
        (executionTraceCost profile rest)

/-! ## Independently cost-labelled public reductions -/

/-- One public Harness event viewed as a cost label.  The numeric contribution
is computed from the profile table; no caller can supply a different cost. -/
structure CostedEvent where
  event : Event
  deriving DecidableEq, Repr, Inhabited

namespace CostedEvent

/-- Forget the computed-cost view and retain the exact authority event. -/
def erase (costed : CostedEvent) : Event := costed.event

/-- The exact profile charge of this authority event. -/
def cost (profile : Profile) (costed : CostedEvent) : Cost.DynamicVector :=
  eventCost profile costed.event

/-- Equip an authority event with its unique computed-cost view. -/
def ofEvent (event : Event) : CostedEvent := ⟨event⟩

@[simp] theorem erase_ofEvent (event : Event) :
    (ofEvent event).erase = event := rfl

end CostedEvent

/-- Erase every computed-cost view in a trace. -/
def eraseCosts (costedTrace : List CostedEvent) : List Event :=
  costedTrace.map CostedEvent.erase

/-- Canonically label every event in a plain trace. -/
def labelCosts (trace : List Event) : List CostedEvent :=
  trace.map CostedEvent.ofEvent

@[simp] theorem eraseCosts_nil : eraseCosts [] = [] := rfl

@[simp] theorem eraseCosts_cons (costed : CostedEvent)
    (rest : List CostedEvent) :
    eraseCosts (costed :: rest) = costed.erase :: eraseCosts rest := rfl

@[simp] theorem eraseCosts_labelCosts (trace : List Event) :
    eraseCosts (labelCosts trace) = trace := by
  simp [eraseCosts, labelCosts, List.map_map, Function.comp_def,
    CostedEvent.erase, CostedEvent.ofEvent]

/-- A computed-cost event has no caller-controlled payload: its erased
authority event determines the whole value. -/
theorem CostedEvent.eq_of_erase_eq {left right : CostedEvent}
    (h : left.erase = right.erase) : left = right := by
  cases left
  cases right
  simpa [CostedEvent.erase] using h

/-- Erasure is injective because `CostedEvent` contains exactly one authority
event and computes its charge rather than storing it. -/
theorem eraseCosts_injective {left right : List CostedEvent}
    (h : eraseCosts left = eraseCosts right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at h
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons rightHead rightTail =>
          have hparts := List.cons.inj h
          have hhead : head = rightHead :=
            CostedEvent.eq_of_erase_eq hparts.1
          subst rightHead
          have htail : tail = rightTail := ih hparts.2
          subst rightTail
          rfl

/-- A cost-labelled public reduction retaining every visited raw Harness
configuration.  Erasure is proved structurally below. -/
inductive CostedReduces :
    RawConfig → List CostedEvent → List RawConfig → RawConfig → Prop
  | refl (config : RawConfig) : CostedReduces config [] [config] config
  | cons {initial next final : RawConfig} {rest : List CostedEvent}
      {visited : List RawConfig} (costed : CostedEvent)
      (step : Core.Harness.StepA initial costed.erase next) :
      CostedReduces next rest visited final →
      CostedReduces initial (costed :: rest) (initial :: visited) final

namespace CostedReduces

/-- Structural erasure is the exact public Harness reduction. -/
theorem erase {initial final : RawConfig} {costedTrace : List CostedEvent}
    {visited : List RawConfig}
    (reduction : CostedReduces initial costedTrace visited final) :
    Core.Harness.StepsA initial (eraseCosts costedTrace) final := by
  induction reduction with
  | refl config => exact Core.Harness.StepsA.refl config
  | cons costed step _ ih => exact Core.Harness.StepsA.cons step ih

/-- Every plain reduction has its unique canonical computed-cost labels. -/
theorem label {initial final : RawConfig} {trace : List Event}
    (reduction : Core.Harness.StepsA initial trace final) :
    ∃ visited : List RawConfig,
      CostedReduces initial (labelCosts trace) visited final := by
  induction reduction with
  | refl raw => exact ⟨[raw], .refl raw⟩
  | @cons current next final event rest step tail ih =>
      obtain ⟨visited, labelledTail⟩ := ih
      exact ⟨current :: visited, .cons (.ofEvent event) step labelledTail⟩

/-- Reconstruct a fixed costed trace from a reduction of its erasure. -/
theorem of_erase {initial final : RawConfig} (costedTrace : List CostedEvent)
    (reduction : Core.Harness.StepsA initial (eraseCosts costedTrace) final) :
    ∃ visited : List RawConfig,
      CostedReduces initial costedTrace visited final := by
  induction costedTrace generalizing initial final with
  | nil =>
      cases reduction with
      | refl => exact ⟨[initial], .refl initial⟩
  | cons costed rest ih =>
      cases reduction with
      | cons step tail =>
          obtain ⟨visited, labelledTail⟩ := ih tail
          exact ⟨initial :: visited, .cons costed step labelledTail⟩

/-- Cost-labelled reductions are functional whenever the underlying labelled
Harness transition is functional.  Keeping the relation property explicit
here lets the typed successor layer discharge it without smuggling a global
determinism assumption into the cost carrier. -/
theorem unique_of_step_functional
    (stepFunctional : ∀ {source : RawConfig} {event : Event}
      {left right : RawConfig},
      Core.Harness.StepA source event left →
      Core.Harness.StepA source event right → left = right)
    {initial leftFinal rightFinal : RawConfig}
    {leftTrace rightTrace : List CostedEvent}
    {leftVisited rightVisited : List RawConfig}
    (leftReduction :
      CostedReduces initial leftTrace leftVisited leftFinal)
    (rightReduction :
      CostedReduces initial rightTrace rightVisited rightFinal)
    (htrace : eraseCosts leftTrace = eraseCosts rightTrace) :
    leftTrace = rightTrace ∧ leftVisited = rightVisited ∧
      leftFinal = rightFinal := by
  induction leftReduction generalizing rightTrace rightVisited rightFinal with
  | refl config =>
      cases rightReduction with
      | refl => exact ⟨rfl, rfl, rfl⟩
      | cons costed step tail => simp at htrace
  | @cons source leftNext leftFinal leftRest leftVisited costed leftStep
      leftTail ih =>
      cases rightReduction with
      | refl => simp at htrace
      | @cons _ rightNext rightFinal rightRest rightVisited rightCosted
          rightStep rightTail =>
          have hevents : costed.erase = rightCosted.erase :=
            (List.cons.inj htrace).1
          have hcosted : costed = rightCosted :=
            CostedEvent.eq_of_erase_eq hevents
          subst rightCosted
          have hnext : leftNext = rightNext :=
            stepFunctional leftStep rightStep
          subst rightNext
          obtain ⟨hrest, hvisited, hfinal⟩ :=
            ih rightTail (List.cons.inj htrace).2
          subst rightRest
          subst rightVisited
          subst rightFinal
          exact ⟨rfl, rfl, rfl⟩

end CostedReduces

/-! ## Public costed execution carriers -/

/-- Recover the active Core state from a raw Harness configuration.  The
initial request is the only phase with no allocated state. -/
def rawConfigState? : RawConfig → Option Core.Exec.State
  | .initializing _ => none
  | .beforeEntry _ core | .trappingBeforeEntry _ _ core |
      .afterEntry _ _ core | .trappingAfterEntry _ _ _ core => some core.1
  | .readyToEnter _ state | .returned _ _ _ state |
      .trappedBeforeEntry _ _ state | .trappedAfterEntry _ _ _ state |
      .thrownBeforeEntry _ _ _ state | .thrownAfterEntry _ _ _ _ state =>
      some state

/-- Recover the active administrative instruction sequence, when present. -/
def rawConfigInstrs : RawConfig → List Core.Exec.AdminInstr
  | .beforeEntry _ core | .trappingBeforeEntry _ _ core |
      .afterEntry _ _ core | .trappingAfterEntry _ _ _ core => core.2
  | _ => []

/-- Live operand/control slots represented by one administrative instruction.
The numeric payload on labels, frames and handlers is the semantic result
arity; nested bodies and frame locals remain visible to the recursive count. -/
def adminLiveSlots : Core.Exec.AdminInstr → Nat
  | .plain (.const _ _) | .plain (.vconst _ _) | .plain (.refNull _) |
      .addrref _ => 1
  | .label arity continuation body =>
      arity + (continuation.map adminLiveSlots).sum +
        (body.map adminLiveSlots).sum
  | .frame arity frame body =>
      arity + frame.locals.length + (body.map adminLiveSlots).sum
  | .handler arity _ body => arity + (body.map adminLiveSlots).sum
  | _ => 0

/-- Total ordinary-memory pages in an allocated Core store. -/
def storeMemoryPages (store : Core.Exec.Store) : Nat :=
  (store.mems.map fun memory =>
    memory.bytes.length / (64 * Core.Exec.Ki)).sum

/-- Total live table elements in an allocated Core store. -/
def storeTableSize (store : Core.Exec.Store) : Nat :=
  (store.tables.map fun table => table.refs.length).sum

/-- Canonical abstract width of one live structure instance. -/
def coreValTypeWidth (layout : GcLayoutConstants) : Core.ValType → Nat
  | .num .i32 | .num .f32 => layout.i32Width
  | .num .i64 | .num .f64 => layout.i64Width
  | .vec .v128 => layout.v128Width
  | .ref _ => layout.referenceWidth
  | .bot => 0

/-- Canonical abstract width of one public Core storage type. -/
def coreStorageWidth (layout : GcLayoutConstants) : Core.StorageType → Nat
  | .val valueType => coreValTypeWidth layout valueType
  | .pack .i8 => layout.packedI8Width
  | .pack .i16 => layout.packedI16Width

/-- Canonical abstract width of one public Core field. -/
def coreFieldWidth (layout : GcLayoutConstants) : Core.FieldType → Nat
  | .mk _ storage => coreStorageWidth layout storage

/-- Canonical alignment of one public Core field. -/
def coreFieldAlignment (layout : GcLayoutConstants) (field : Core.FieldType) :
    Nat :=
  min (coreFieldWidth layout field) layout.maxFieldAlignment

/-- Declared-order public Core field layout. -/
def coreLayoutFields (layout : GcLayoutConstants) :
    Nat → List Core.FieldType → Nat
  | offset, [] => offset
  | offset, field :: fields =>
      coreLayoutFields layout
        (alignTo (coreFieldAlignment layout field) offset +
          coreFieldWidth layout field) fields

/-- Canonical abstract width of a public Core structure shape. -/
def coreStructSize (layout : GcLayoutConstants) (fields : Core.FieldTypes) : Nat :=
  layout.roundTotal
    (coreLayoutFields layout layout.structHeaderWidth fields.toList)

/-- Canonical abstract width of a public Core array shape. -/
def coreArraySize (layout : GcLayoutConstants) (field : Core.FieldType)
    (length : Nat) : Nat :=
  layout.roundTotal
    (layout.arrayHeaderWidth + length *
      alignTo (coreFieldAlignment layout field) (coreFieldWidth layout field))

/-- Canonical abstract width of a public Core exception tag payload. -/
def coreExceptionSize (layout : GcLayoutConstants) (tagType : Core.TagType) : Nat :=
  match tagType with
  | .idx _ => 0
  | .recu _ => 0
  | .defd definedType =>
      match Core.expandDt definedType with
      | some (.func domain _) =>
          layout.roundTotal
            (domain.toList.foldl
              (fun offset valueType =>
                let width := coreValTypeWidth layout valueType
                alignTo (min width layout.maxFieldAlignment) offset + width)
              layout.exceptionHeaderWidth)
      | _ => 0

/-- Canonical abstract width of one live structure instance. -/
def structInstanceBytes (layout : GcLayoutConstants)
    (runtimeInstance : Core.Exec.StructInst) : Nat :=
  match Core.expandDt runtimeInstance.type with
  | some (.struct fields) => coreStructSize layout fields
  | _ => 0

/-- Canonical abstract width of one live array instance. -/
def arrayInstanceBytes (layout : GcLayoutConstants)
    (runtimeInstance : Core.Exec.ArrayInst) : Nat :=
  match Core.expandDt runtimeInstance.type with
  | some (.array field) =>
      coreArraySize layout field runtimeInstance.fields.length
  | _ => 0

/-- Canonical abstract width of one live exception instance. -/
def exceptionInstanceBytes (layout : GcLayoutConstants)
    (store : Core.Exec.Store) (runtimeInstance : Core.Exec.ExnInst) : Nat :=
  match store.tags[runtimeInstance.tag]? with
  | some tag => coreExceptionSize layout tag.type
  | none => 0

/-- Total live managed-heap and exception-object bytes. -/
def storeGcLiveBytes (layout : GcLayoutConstants)
    (store : Core.Exec.Store) : Nat :=
  (store.structs.map (structInstanceBytes layout)).sum +
    (store.arrays.map (arrayInstanceBytes layout)).sum +
    (store.exns.map (exceptionInstanceBytes layout store)).sum

/-- **SPEC §7.5**, the peak inputs retained for every visited public Harness
configuration. -/
structure ConfigResourceSnapshot where
  liveValueSlots : Nat
  memoryPages : Nat
  tableSize : Nat
  liveGcBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Compute the exact resource snapshot of a public raw configuration. -/
def snapshotRaw (layout : GcLayoutConstants) (config : RawConfig) :
    ConfigResourceSnapshot :=
  match rawConfigState? config with
  | none => default
  | some state =>
      { liveValueSlots := state.frame.locals.length +
          (rawConfigInstrs config |>.map adminLiveSlots).sum +
          (state.store.exns.map fun exception => exception.fields.length).sum
        memoryPages := storeMemoryPages state.store
        tableSize := storeTableSize state.store
        liveGcBytes := storeGcLiveBytes layout state.store }

/-- Snapshot a proof-carrying public configuration. -/
def snapshotOf (layout : GcLayoutConstants) (config : Config) :
    ConfigResourceSnapshot :=
  snapshotRaw layout config.1

/-- Peak-only contribution of one retained configuration. -/
def snapshotPeak (snapshot : ConfigResourceSnapshot) : Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      peakStackValues := snapshot.liveValueSlots
      peakPages := snapshot.memoryPages
      peakGcLiveBytes := snapshot.liveGcBytes }

/-- Fold event contributions in semantic order. -/
def traceContribution (table : CostTableBody) :
    List CostedEvent → Cost.DynamicVector
  | [] => Cost.DynamicVector.zero
  | event :: rest =>
      Cost.sequentialCompose (eventCostBody table event.event)
        (traceContribution table rest)

/-- Take the componentwise peak over every retained configuration. -/
def peakOverConfigs :
    List ConfigResourceSnapshot → Cost.DynamicVector
  | [] => Cost.DynamicVector.zero
  | config :: rest => Cost.ComponentwiseMax (snapshotPeak config)
      (peakOverConfigs rest)

/-- **SPEC §7.5**, the exact mixed sum/maximum fold over a costed public trace
and all visited configuration snapshots. -/
def Cost.foldTrace (table : CostTableBody)
    (configs : NonemptyCanonicalList ConfigResourceSnapshot)
    (costedTrace : List CostedEvent) : Cost.DynamicVector :=
  Cost.sequentialCompose (traceContribution table costedTrace)
    (peakOverConfigs configs.elements)

/-- The deterministic subevents of the public instantiation phase. -/
abbrev CostedInitializationEvent : Type := Core.Harness.InitializationEvent

/-- Contribution of one deterministic instantiation subevent. -/
def initializationEventCost (table : CostTableBody)
    (_event : CostedInitializationEvent) : Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      instantiationSteps := 1
      wasmRuleSteps := table.ruleStepUnit }

/-- Fold deterministic initialization events and their resource snapshots. -/
def Cost.foldInitialization (table : CostTableBody)
    (configs : NonemptyCanonicalList ConfigResourceSnapshot)
    (events : List CostedInitializationEvent) : Cost.DynamicVector :=
  Cost.sequentialCompose
    (events.foldl (fun accumulated event =>
      Cost.sequentialCompose accumulated (initializationEventCost table event))
      Cost.DynamicVector.zero)
    (peakOverConfigs configs.elements)

/-- **SPEC §7.5**, an independently cost-labelled finite public execution.
The exact visited raw states determine every retained resource snapshot. -/
def CostedFiniteExecution (profile : Profile) (initial : Config)
    (costedTrace : List CostedEvent)
    (configs : NonemptyCanonicalList ConfigResourceSnapshot)
    (observation : ExecutionObservation) : Prop :=
  ∃ (visited : List RawConfig) (final : RawConfig),
    CostedReduces initial.1 costedTrace visited final ∧
    configs.elements = visited.map (snapshotRaw profile.costTableBody.layout) ∧
    Core.Harness.Observes (eraseCosts costedTrace) final observation

namespace CostedFiniteExecution

/-- Erasing an exact costed finite execution yields the same plain public
finite execution. -/
theorem erase {profile : Profile} {initial : Config}
    {costedTrace : List CostedEvent}
    {configs : NonemptyCanonicalList ConfigResourceSnapshot}
    {observation : ExecutionObservation}
    (run : CostedFiniteExecution profile initial costedTrace configs observation) :
    FiniteExecution initial observation := by
  obtain ⟨_, final, reduction, _, observes⟩ := run
  exact Core.Harness.FiniteExecution.mk reduction.erase observes

/-- The retained costed trace erases to the trace stored in the public
observation. -/
theorem trace {profile : Profile} {initial : Config}
    {costedTrace : List CostedEvent}
    {configs : NonemptyCanonicalList ConfigResourceSnapshot}
    {observation : ExecutionObservation}
    (run : CostedFiniteExecution profile initial costedTrace configs observation) :
    observation.trace = eraseCosts costedTrace := by
  obtain ⟨_, _, _, _, observes⟩ := run
  cases observes <;> rfl

/-- Under a functional labelled Harness step, the same public observation
fixes both the costed trace and the complete visited-snapshot sequence. -/
theorem functional_of_observation
    (stepFunctional : ∀ {source : RawConfig} {event : Event}
      {left right : RawConfig},
      Core.Harness.StepA source event left →
      Core.Harness.StepA source event right → left = right)
    {profile : Profile} {initial : Config}
    {leftTrace rightTrace : List CostedEvent}
    {leftConfigs rightConfigs : NonemptyCanonicalList ConfigResourceSnapshot}
    {leftObservation rightObservation : ExecutionObservation}
    (leftRun : CostedFiniteExecution profile initial leftTrace leftConfigs
      leftObservation)
    (rightRun : CostedFiniteExecution profile initial rightTrace rightConfigs
      rightObservation)
    (hobservation : leftObservation = rightObservation) :
    leftTrace = rightTrace ∧ leftConfigs = rightConfigs := by
  subst rightObservation
  have herased : eraseCosts leftTrace = eraseCosts rightTrace := by
    rw [← leftRun.trace, ← rightRun.trace]
  have htrace : leftTrace = rightTrace := eraseCosts_injective herased
  subst rightTrace
  obtain ⟨leftVisited, leftFinal, leftReduction, leftConfigEq, _⟩ := leftRun
  obtain ⟨rightVisited, rightFinal, rightReduction, rightConfigEq, _⟩ :=
    rightRun
  obtain ⟨_, hvisited, _⟩ :=
    CostedReduces.unique_of_step_functional stepFunctional leftReduction
      rightReduction rfl
  have hconfigElements : leftConfigs.elements = rightConfigs.elements := by
    rw [leftConfigEq, rightConfigEq, hvisited]
  exact ⟨rfl, Foundation.NonemptyCanonicalList.ext hconfigElements⟩

end CostedFiniteExecution

/-- **SPEC §10.1**, the configuration and dynamic charge produced for one fresh
invocation. -/
structure InitializationObservation (profile : Profile) where
  initial : Config
  costedEvents : List CostedInitializationEvent
  configs : NonemptyCanonicalList ConfigResourceSnapshot
  cost : Cost.DynamicVector
  costExact : cost = Cost.foldInitialization profile.costTableBody configs costedEvents

/-- A public relational prefix of exactly `length` labelled steps. -/
structure RelationalPrefix (initial : Config) (length : Nat) where
  events : List Event
  final : Config
  lengthEq : events.length = length

/-- A relational prefix is valid exactly when the public relation derives it. -/
def RelationalPrefix.Valid {initial : Config} {length : Nat}
    (relPrefix : RelationalPrefix initial length) : Prop :=
  Reduces initial relPrefix.events relPrefix.final

/-- An executable exploration found a real branch beyond the permitted bound. -/
structure NonterminalPrefix (initial : Config) (length : Nat) where
  witness : RelationalPrefix initial length
  valid : witness.Valid

/-- A finite public execution paired with its exact profile charge and every
event/configuration retained by the independent costed relation. -/
structure CostedExecutionObservation (profile : Profile) (initial : Config) where
  observation : ExecutionObservation
  costedTrace : List CostedEvent
  configs : NonemptyCanonicalList ConfigResourceSnapshot
  run : CostedFiniteExecution profile initial costedTrace configs observation
  maximal : IsTerminalObservation observation
  cost : Cost.DynamicVector
  costExact : cost = Cost.foldTrace profile.costTableBody configs costedTrace

namespace CostedExecutionObservation

/-- Plain finite execution derived from the retained costed relation. -/
def execution {profile : Profile} {initial : Config}
    (costed : CostedExecutionObservation profile initial) :
    FiniteExecution initial costed.observation :=
  costed.run.erase

/-- For a functional labelled Harness relation, two costed witnesses of the
same public observation retain identical labels, snapshots, and total charge.
This is the exact peak-resource functionality needed by extensional resource
reflection. -/
theorem functional_of_observation
    (stepFunctional : ∀ {source : RawConfig} {event : Event}
      {left right : RawConfig},
      Core.Harness.StepA source event left →
      Core.Harness.StepA source event right → left = right)
    {profile : Profile} {initial : Config}
    (left right : CostedExecutionObservation profile initial)
    (hobservation : left.observation = right.observation) :
    left.costedTrace = right.costedTrace ∧ left.configs = right.configs ∧
      left.cost = right.cost := by
  obtain ⟨htrace, hconfigs⟩ :=
    left.run.functional_of_observation stepFunctional right.run hobservation
  refine ⟨htrace, hconfigs, ?_⟩
  rw [left.costExact, right.costExact, hconfigs, htrace]

end CostedExecutionObservation

/-- Proof carried by a completed bounded all-branch exploration.

The first two fields give the exact finite-branch statement.  `maximal` is the
load-bearing completion certificate: it rules out divergence and represents
every finite maximal execution in the frontier.  `noOverrun` independently
rules out a relational prefix at `bound + 1`, so the `.complete` constructor
cannot conceal a branch that merely outlived the search budget. -/
structure CostedCoverage (profile : Profile) (bound : Nat) (initial : Config)
    (observations :
      NonemptyCanonicalFrontier (CostedExecutionObservation profile initial)) : Prop where
  /-- Every emitted observation is an independently derived finite execution. -/
  elementsSound : ∀ observation ∈ observations.elements,
    FiniteExecution initial observation.observation
  /-- Every finite branch within the public bound is represented. -/
  finiteWithinBound : ∀ observation : ExecutionObservation,
    FiniteExecution initial observation → observation.trace.length ≤ bound →
    ∃ costed ∈ observations.elements, costed.observation = observation
  /-- Every unrestricted maximal execution is finite and represented; the
  divergent constructor makes this proposition definitionally false. -/
  maximal : ∀ execution : MaximalExecution initial,
    ∃ costed ∈ observations.elements,
      match execution with
      | .finite observation _ _ => observation = costed.observation
      | .diverges _ _ _ _ => False
  /-- No valid branch reaches one step beyond the advertised search bound. -/
  noOverrun : ¬ ∃ branchPrefix : RelationalPrefix initial (bound + 1),
    branchPrefix.Valid

/-- **SPEC §10.1**, result of the bounded public all-branch explorer. -/
inductive CostedTreeResult (profile : Profile) (bound : Nat) (initial : Config)
  | complete
      (observations :
        NonemptyCanonicalFrontier (CostedExecutionObservation profile initial))
      (coverage : CostedCoverage profile bound initial observations)
  | nonterminalPrefix (overrun : NonterminalPrefix initial (bound + 1))
  | initializationFailure (report : FailureReport)

/-! ## Fresh request construction -/

/-! ### Closed amended instantiation and export resolution -/

/-- If an amended-valid module has no imports, its derived module type has no
imports either.  This is the exact bridge needed to instantiate the public
closed profile with the empty external-address list. -/
theorem Core.Module_okA.moduleType_imports_eq_nil {module : Core.Module}
    {moduleType : Core.ModuleType}
    (hmodule : Core.Module_okA module moduleType)
    (himports : module.imports = []) : moduleType.imports = [] := by
  cases hmodule
  simp_all [Core.SeqLen₂, Core.Context.closModuleType,
    Core.substAllModuleType, Core.substModuleType]
  apply List.eq_nil_of_length_eq_zero
  omega

/-- Successful execution of the amended initializer for a closed module is an
exact `InstantiateA` derivation. -/
theorem Core.Exec.instantiateA?_sound_of_closed_module
    {module : Core.Module} {core : Core.Exec.Config}
    (hmodule : ∃ moduleType, Core.Module_okA module moduleType)
    (himports : module.imports = [])
    (h : Core.Exec.instantiateA? ({} : Core.Exec.Store) module [] = some core) :
    Core.Exec.InstantiateA ({} : Core.Exec.Store) module [] core := by
  obtain ⟨moduleType, moduleOk⟩ := hmodule
  have moduleTypeImports := moduleOk.moduleType_imports_eq_nil himports
  apply Core.Exec.instantiateA?_sound_of_module moduleOk
  · simp [Core.SeqLen₂, moduleTypeImports]
  · intro index address externType _ hlookup
    simp [moduleTypeImports] at hlookup
  · exact h

/-- Find the memory export with the required Core name, skipping unrelated or
same-named wrong-kind exports rather than trusting source order. -/
def findMemoryExport? (name : Core.Name) :
    List Core.Exec.ExportInst → Option Core.Exec.MemAddr
  | [] => none
  | entry :: entries =>
      if entry.name = name then
        match entry.addr with
        | .mem address => some address
        | _ => findMemoryExport? name entries
      else findMemoryExport? name entries

/-- The public resolver and the Harness initializer use the identical ordered
memory-export search. -/
theorem findMemoryExport?_eq_initialMemoryExportAddress? (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :
    findMemoryExport? name entries =
      Core.Harness.initialMemoryExportAddress? name entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases entry with
      | mk entryName address =>
          cases address <;>
            simp [findMemoryExport?,
              Core.Harness.initialMemoryExportAddress?, ih]

/-- The executable memory-export resolver returns only an actual export. -/
theorem findMemoryExport?_sound {name : Core.Name}
    {entries : List Core.Exec.ExportInst} {address : Core.Exec.MemAddr}
    (h : findMemoryExport? name entries = some address) :
    ({ name := name, addr := .mem address } : Core.Exec.ExportInst) ∈ entries := by
  induction entries with
  | nil => simp [findMemoryExport?] at h
  | cons entry entries ih =>
      cases entry with
      | mk entryName externalAddress =>
          by_cases hname : entryName = name
          · subst entryName
            cases externalAddress with
            | tag _ | global _ | table _ | func _ =>
                simp [findMemoryExport?] at h
                exact List.mem_cons_of_mem _ (ih h)
            | mem found =>
                simp [findMemoryExport?] at h
                subst found
                exact List.mem_cons_self
          · simp [findMemoryExport?, hname] at h
            exact List.mem_cons_of_mem _ (ih h)

/-- Find the function export with the required Core name. -/
def findFunctionExport? (name : Core.Name) :
    List Core.Exec.ExportInst → Option Core.Exec.FuncAddr
  | [] => none
  | entry :: entries =>
      if entry.name = name then
        match entry.addr with
        | .func address => some address
        | _ => findFunctionExport? name entries
      else findFunctionExport? name entries

/-- The public resolver and the Harness initializer use the identical ordered
function-export search. -/
theorem findFunctionExport?_eq_initialFunctionExportAddress? (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :
    findFunctionExport? name entries =
      Core.Harness.initialFunctionExportAddress? name entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases entry with
      | mk entryName address =>
          cases address <;>
            simp [findFunctionExport?,
              Core.Harness.initialFunctionExportAddress?, ih]

/-- The executable function-export resolver returns only an actual export. -/
theorem findFunctionExport?_sound {name : Core.Name}
    {entries : List Core.Exec.ExportInst} {address : Core.Exec.FuncAddr}
    (h : findFunctionExport? name entries = some address) :
    ({ name := name, addr := .func address } : Core.Exec.ExportInst) ∈ entries := by
  induction entries with
  | nil => simp [findFunctionExport?] at h
  | cons entry entries ih =>
      cases entry with
      | mk entryName externalAddress =>
          by_cases hname : entryName = name
          · subst entryName
            cases externalAddress with
            | tag _ | global _ | mem _ | table _ =>
                simp [findFunctionExport?] at h
                exact List.mem_cons_of_mem _ (ih h)
            | func found =>
                simp [findFunctionExport?] at h
                subst found
                exact List.mem_cons_self
          · simp [findFunctionExport?, hname] at h
            exact List.mem_cons_of_mem _ (ih h)

/-- Execute amended closed instantiation and retain its independently proved
relational witness.  The proof component is erased; the computed Core state is
exactly `instantiateA?`'s result. -/
abbrev ClosedInstantiationResult (module : Module) :=
  { core : Core.Exec.Config //
    Core.Exec.InstantiateA ({} : Core.Exec.Store) module.core [] core ∧
      Core.Exec.instantiateA? ({} : Core.Exec.Store) module.core [] = some core }

def instantiateClosed? (profile : Profile) (module : Module)
    (hvalid : validateUnder profile module = true) :
    Option (ClosedInstantiationResult module) :=
  match hcore : Core.Exec.instantiateA? ({} : Core.Exec.Store) module.core [] with
  | none => none
  | some core =>
      some ⟨core, ⟨
        Core.Exec.instantiateA?_sound_of_closed_module
          (validateUnder_sound hvalid).1
          (Core.Module.imports_eq_nil_of_admittedBy
            (validateUnder_sound hvalid).2) hcore,
        hcore⟩⟩

/-- Proof-carrying carrier for an executable memory-export search result. -/
abbrev ResolvedMemoryExportResult (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :=
  { address : Core.Exec.MemAddr //
    ({ name := name, addr := .mem address } : Core.Exec.ExportInst) ∈ entries }

/-- Proof-carrying result of the executable memory-export search. -/
def resolvedMemoryExport? (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :
    Option (ResolvedMemoryExportResult name entries) :=
  match h : findMemoryExport? name entries with
  | none => none
  | some address => some ⟨address, findMemoryExport?_sound h⟩

/-- Proof-carrying carrier for an executable function-export search result. -/
abbrev ResolvedFunctionExportResult (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :=
  { address : Core.Exec.FuncAddr //
    ({ name := name, addr := .func address } : Core.Exec.ExportInst) ∈ entries }

/-- Proof-carrying result of the executable function-export search. -/
def resolvedFunctionExport? (name : Core.Name)
    (entries : List Core.Exec.ExportInst) :
    Option (ResolvedFunctionExportResult name entries) :=
  match h : findFunctionExport? name entries with
  | none => none
  | some address => some ⟨address, findFunctionExport?_sound h⟩

/-- A proof-carrying memory resolution exposes the executable address selected
by the Harness initializer. -/
theorem resolvedMemoryExport?_initialAddress {name : Core.Name}
    {entries : List Core.Exec.ExportInst}
    {result : ResolvedMemoryExportResult name entries}
    (h : resolvedMemoryExport? name entries = some result) :
    Core.Harness.initialMemoryExportAddress? name entries = some result.1 := by
  unfold resolvedMemoryExport? at h
  split at h
  · simp at h
  · rename_i address haddress
    have hvalue : address = result.1 := by
      simpa using congrArg (fun option => option.map Subtype.val) h
    rw [← hvalue, ← findMemoryExport?_eq_initialMemoryExportAddress?]
    exact haddress

/-- A proof-carrying function resolution exposes the executable address
selected by the Harness initializer. -/
theorem resolvedFunctionExport?_initialAddress {name : Core.Name}
    {entries : List Core.Exec.ExportInst}
    {result : ResolvedFunctionExportResult name entries}
    (h : resolvedFunctionExport? name entries = some result) :
    Core.Harness.initialFunctionExportAddress? name entries = some result.1 := by
  unfold resolvedFunctionExport? at h
  split at h
  · simp at h
  · rename_i address haddress
    have hvalue : address = result.1 := by
      simpa using congrArg (fun option => option.map Subtype.val) h
    rw [← hvalue, ← findFunctionExport?_eq_initialFunctionExportAddress?]
    exact haddress

/-- Three successful executable selections compute the unique amended Harness
initialization target. -/
theorem initializationCandidate?_eq_some {request : Core.Harness.Request}
    {core : Core.Exec.Config} {memory : Core.Exec.MemAddr}
    {gemm : Core.Exec.FuncAddr}
    (hcore : Core.Exec.instantiateA? ({} : Core.Exec.Store) request.module [] =
      some core)
    (hmemory : Core.Harness.initialMemoryExportAddress?
      request.memoryExportName core.1.frame.mod.exports = some memory)
    (hfunction : Core.Harness.initialFunctionExportAddress?
      request.gemmExportName core.1.frame.mod.exports = some gemm) :
    Core.Harness.initializationCandidate? request =
      some (.beforeEntry
        { request := request, memoryAddr := memory, gemmAddr := gemm } core) := by
  simp [Core.Harness.initializationCandidate?, hcore, hmemory, hfunction]

/-- Embed an ABI byte in the public Core byte carrier. -/
def invocationByte (byte : UInt8) : Core.Byte :=
  ⟨byte.toNat, byte.toNat_lt⟩

/-- Turn the public profile invocation into the exact Core Harness request. -/
def requestOfInvocation {profile : Profile} (module : Module)
    (invocation : Invocation profile) : Core.Harness.Request where
  module := module.core
  memoryExportName := Core.memoryExportName
  gemmExportName := Core.gemmExportName
  rawPtr := ⟨invocation.body.ptr.toNat, by simpa using invocation.body.ptr.toNat_lt⟩
  rawLen := ⟨invocation.body.len.toNat, by simpa using invocation.body.len.toNat_lt⟩
  rawBytes := invocation.body.bytes.toList.map invocationByte
  rawLength := by
    simp only [List.length_map, Foundation.Bytes.length_toList]
    exact invocation.lawful.1.symm
  rawAddressBound := invocation.fits_address_space
  rawPageBound := by
    simpa [Core.Harness.requiredPages, pagesFor, pageSize, Core.Exec.Ki] using
      invocation.fits_pages

/-- Every public module comes from the amended binary grammar, hence its
recursive types satisfy the source-phase syntax invariant needed by the typed
harness root. -/
theorem Module.representableTypesAreSource (module : Module) :
    module.core.types.all Core.TypeDef.isSyn = true := by
  obtain ⟨bytes, hbinary⟩ := module.representable
  have hwf : Core.Module.wf module.core = true :=
    Core.Binary.BmoduleA.wf_of hbinary
  simp only [Core.Module.wf, Core.Module.isSyn, Bool.and_eq_true] at hwf
  exact hwf.2.1.1.1.1.1.1.1

/-- Canonical site for a rejected fresh public invocation. -/
def publicInitializationFaultSite : CanonicalObjectId where
  schemaVersion := 1
  domain := .generic
  typeTag := Bytes.pack []
  canonicalBodyBytes := Bytes.pack []

/-- A representable module that fails amended declarative validation cannot
enter the proof-carrying public machine. -/
def invalidModuleInitialization : FailureReport where
  site := publicInitializationFaultSite
  code := 1
  context := []

/-- A deterministic failure after validation, identified without hiding a
semantic witness in the report. -/
def publicInitializationFailure (code : Nat) : FailureReport where
  site := publicInitializationFaultSite
  code := code
  context := []

/-- The exact two snapshots retained by fresh allocation: the validated empty-
store request and the allocated pre-start configuration. -/
def initializationSnapshots (profile : Profile) (request initial : Config) :
    NonemptyCanonicalList ConfigResourceSnapshot :=
  { head := snapshotOf profile.costTableBody.layout request
    rest := [snapshotOf profile.costTableBody.layout initial] }

/-- **SPEC §7.5**, the independent plain public initializer relation.  It is
the amended Harness instantiation transition, not the executable initializer
or a theorem field stored in its output. -/
def Initializes (profile : Profile) (module : Module)
    (invocation : Invocation profile) (initial : Config) : Prop :=
  ∃ request : Config,
    request.1 = .initializing (requestOfInvocation module invocation) ∧
      Core.Harness.StepA request.1
        (.initialize (Core.Harness.initializationEvents module.core)) initial.1

/-- **SPEC §7.5**, relational allocation/static-initialization evidence.  The
event expansion and both retained snapshots are fixed by the independent
Harness transition. -/
def CostedInitialization (profile : Profile) (module : Module)
    (invocation : Invocation profile)
    (costedEvents : List CostedInitializationEvent)
    (configs : NonemptyCanonicalList ConfigResourceSnapshot)
    (initial : Config) : Prop :=
  ∃ request : Config,
    request.1 = .initializing (requestOfInvocation module invocation) ∧
      Core.Harness.StepA request.1 (.initialize costedEvents) initial.1 ∧
      costedEvents = Core.Harness.initializationEvents module.core ∧
      configs = initializationSnapshots profile request initial

/-- **SPEC §10.1**, executable fresh amended-Core allocation.  The result is
the pre-start Harness configuration: allocation and static initialization have
already occurred and are retained in `costedEvents`, while the start function,
raw installation and exported call remain ordinary explored transitions. -/
def initialGemmInvocationCosted (profile : Profile) (module : Module)
    (invocation : Invocation profile) :
    Except FailureReport (InitializationObservation profile) :=
  if hvalid : validateUnder profile module = true then
    let request := requestOfInvocation module invocation
    let validity := validateUnder_sound hvalid
    match instantiateClosed? profile module hvalid with
    | none => .error (publicInitializationFailure 2)
    | some instantiated =>
        match hmemory : resolvedMemoryExport? request.memoryExportName
            instantiated.1.1.frame.mod.exports with
        | none => .error (publicInitializationFailure 3)
        | some memoryExport =>
            match hfunction : resolvedFunctionExport? request.gemmExportName
                instantiated.1.1.frame.mod.exports with
            | none => .error (publicInitializationFailure 4)
            | some functionExport =>
                let harness : Core.Harness.Harness :=
                  { request := request
                    memoryAddr := memoryExport.1
                    gemmAddr := functionExport.1 }
                if hready : Core.Harness.GemmFunctionReady harness
                    instantiated.1.1.store then
                  if hinstallReady : Core.Harness.RawInstallReady harness
                      instantiated.1.1 then
                    let moduleImports :=
                      Core.Module.imports_eq_nil_of_admittedBy validity.2
                    let requestValid : request.Valid :=
                      And.intro module.representableTypesAreSource
                        (And.intro validity.1
                          (And.intro moduleImports
                            ⟨instantiated.1, memoryExport.1, functionExport.1,
                              instantiated.2.2,
                              resolvedMemoryExport?_initialAddress hmemory,
                              resolvedFunctionExport?_initialAddress hfunction,
                              hready, hinstallReady⟩))
                    let requestConfig :=
                      Core.Harness.TypedConfig.initializing request requestValid
                    let rawInitial : Core.Harness.Config :=
                      .beforeEntry harness instantiated.1
                    let instantiation :
                        Core.Exec.InstantiateA ({} : Core.Exec.Store) module.core []
                          instantiated.1 := instantiated.2.1
                    let resolves : Core.Harness.ResolvesExports
                        instantiated.1.1.frame.mod harness :=
                      ⟨memoryExport.2, functionExport.2⟩
                    let candidate : Core.Harness.initializationCandidate? request =
                        some rawInitial := by
                      apply initializationCandidate?_eq_some
                      · exact instantiated.2.2
                      · exact resolvedMemoryExport?_initialAddress hmemory
                      · exact resolvedFunctionExport?_initialAddress hfunction
                    let costedEvents := Core.Harness.initializationEvents module.core
                    let initializationStep : Core.Harness.StepA requestConfig.1
                        (.initialize costedEvents) rawInitial :=
                      .instantiate (.mk instantiation resolves candidate)
                    let initial := requestConfig.successor
                      (.initialize costedEvents) rawInitial initializationStep
                    let configs := initializationSnapshots profile requestConfig initial
                    .ok
                      { initial := initial
                        costedEvents := costedEvents
                        configs := configs
                        cost := Cost.foldInitialization profile.costTableBody configs
                          costedEvents
                        costExact := rfl }
                  else
                    .error (publicInitializationFailure 6)
                else
                  .error (publicInitializationFailure 5)
  else
    .error invalidModuleInitialization

/-- Successful validation, fresh instantiation, both required export lookups,
and the computed instantiated GEMM-ABI check are sufficient for the executable
initializer to return its exact proof-carrying observation.  This is a
rewriting boundary for compiler and release callers; failure remains explicit
whenever any premise is absent. -/
theorem initialGemmInvocationCosted_success_of {profile : Profile}
    {module : Module} {invocation : Invocation profile}
    (hvalid : validateUnder profile module = true)
    {instantiated : ClosedInstantiationResult module}
    (hinst : instantiateClosed? profile module hvalid = some instantiated)
    {memoryExport : ResolvedMemoryExportResult
      (requestOfInvocation module invocation).memoryExportName
      instantiated.1.1.frame.mod.exports}
    (hmem : resolvedMemoryExport?
      (requestOfInvocation module invocation).memoryExportName
      instantiated.1.1.frame.mod.exports = some memoryExport)
    {functionExport : ResolvedFunctionExportResult
      (requestOfInvocation module invocation).gemmExportName
      instantiated.1.1.frame.mod.exports}
    (hfun : resolvedFunctionExport?
      (requestOfInvocation module invocation).gemmExportName
      instantiated.1.1.frame.mod.exports = some functionExport)
    (hready : Core.Harness.GemmFunctionReady
      { request := requestOfInvocation module invocation
        memoryAddr := memoryExport.1
        gemmAddr := functionExport.1 }
      instantiated.1.1.store)
    (hinstallReady : Core.Harness.RawInstallReady
      { request := requestOfInvocation module invocation
        memoryAddr := memoryExport.1
        gemmAddr := functionExport.1 }
      instantiated.1.1) :
    ∃ initialization,
      initialGemmInvocationCosted profile module invocation =
        .ok initialization := by
  unfold initialGemmInvocationCosted
  rw [dif_pos hvalid]
  dsimp only
  rw [hinst]
  dsimp only
  split
  · simp_all
  · rename_i foundMemory hfoundMemory
    have hmemoryEq : foundMemory = memoryExport :=
      Option.some.inj (hfoundMemory.symm.trans hmem)
    subst foundMemory
    split
    · simp_all
    · rename_i foundFunction hfoundFunction
      have hfunctionEq : foundFunction = functionExport :=
        Option.some.inj (hfoundFunction.symm.trans hfun)
      subst foundFunction
      rw [dif_pos hready]
      rw [dif_pos hinstallReady]
      exact ⟨_, rfl⟩

/-- Erase the initialization charge while retaining the exact public Core
configuration.  Both initializers share one computation; the plain endpoint is
not an independently implemented compatibility model. -/
def initialGemmInvocation (profile : Profile) (module : Module)
    (invocation : Invocation profile) : Except FailureReport Config :=
  (initialGemmInvocationCosted profile module invocation).map (fun result => result.initial)

/-- A successful executable initialization retains an independently checkable
amended-Core instantiation step, its complete deterministic event expansion,
and exactly the request/pre-start resource snapshots. -/
theorem costed_initialization_sound {profile : Profile} {module : Module}
    {invocation : Invocation profile}
    {initialization : InitializationObservation profile}
    (h : initialGemmInvocationCosted profile module invocation = .ok initialization) :
    CostedInitialization profile module invocation initialization.costedEvents
      initialization.configs initialization.initial := by
  unfold initialGemmInvocationCosted at h
  split at h
  · rename_i hvalid
    try dsimp only at h
    split at h
    · simp at h
    · rename_i core hcore
      try simp only [hcore] at h
      try dsimp only at h
      split at h
      · rename_i hmemory
        try simp only [hmemory] at h
        try dsimp only at h
        simp at h
      · rename_i memoryAddress hmemory
        have hmemoryAddress := resolvedMemoryExport?_initialAddress hmemory
        try simp only [hmemory] at h
        try dsimp only at h
        split at h
        · rename_i hfunction
          try simp only [hfunction] at h
          try dsimp only at h
          simp at h
        · rename_i functionAddress hfunction
          have hfunctionAddress := resolvedFunctionExport?_initialAddress hfunction
          try simp only [hfunction] at h
          try dsimp only at h
          split at h
          · split at h
            · have hinitialization := Except.ok.inj h
              subst initialization
              refine ⟨_, rfl, ?_, rfl, rfl⟩
              have candidate : Core.Harness.initializationCandidate?
                  (requestOfInvocation module invocation) =
                  some (.beforeEntry
                    { request := requestOfInvocation module invocation
                      memoryAddr := memoryAddress.1
                      gemmAddr := functionAddress.1 } core.1) := by
                apply initializationCandidate?_eq_some
                · exact core.2.2
                · exact hmemoryAddress
                · exact hfunctionAddress
              exact Core.Harness.StepA.instantiate
                (Core.Harness.InitializesA.mk core.2.1
                  ⟨memoryAddress.2, functionAddress.2⟩ candidate)
            · simp at h
          · simp at h
  · simp at h

/-- **SPEC §7.5**, public-Core costed initialization erases to the identical
plain initialization result. -/
theorem costed_initialization_erase {profile : Profile} {module : Module}
    {invocation : Invocation profile}
    {initialization : InitializationObservation profile}
    (h : initialGemmInvocationCosted profile module invocation = .ok initialization) :
    initialGemmInvocation profile module invocation = .ok initialization.initial := by
  unfold initialGemmInvocation
  rw [h]
  rfl

/-- The recorded public initialization charge is exactly the fold of the
retained initialization events and configuration snapshots. -/
theorem initialization_cost_exact {profile : Profile}
    (initialization : InitializationObservation profile) :
    initialization.cost = Cost.foldInitialization profile.costTableBody
      initialization.configs initialization.costedEvents :=
  initialization.costExact

/-- **SPEC §7.5**, one fresh public invocation followed by one independently
labelled finite amended-Core execution.  Both relations are reconstructed from
the retained events/configurations; neither is asserted by the executable
initializer or explorer. -/
def CostedExecutionFor (profile : Profile) (module : Module)
    (invocation : Invocation profile)
    (initialization : InitializationObservation profile) {initial : Config}
    (costed : CostedExecutionObservation profile initial) : Prop :=
  initialGemmInvocationCosted profile module invocation = .ok initialization ∧
    initialization.initial = initial ∧
    CostedInitialization profile module invocation initialization.costedEvents
      initialization.configs initial ∧
    CostedFiniteExecution profile initial costed.costedTrace costed.configs
      costed.observation

namespace MaximalExecution

/-- **SPEC §10.1**, a costed observation represents exactly this maximal
execution, including its independently reconstructed costed run. -/
def CostedAs {profile : Profile} {initial : Config}
    (execution : MaximalExecution initial)
    (costed : CostedExecutionObservation profile initial) : Prop :=
  execution = .finite costed.observation costed.run.erase costed.maximal

end MaximalExecution

/-- The dynamic charge retained by a costed observation is exactly the fold of
its labelled public trace and resource snapshots. -/
theorem costed_observation_cost_exact {profile : Profile} {initial : Config}
    (costed : CostedExecutionObservation profile initial) :
    costed.cost = Cost.foldTrace profile.costTableBody costed.configs
      costed.costedTrace :=
  costed.costExact

end WasmGemmGnaf.Wasm
