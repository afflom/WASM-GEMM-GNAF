import WasmGemmGnaf.Wasm.Evaluate
import WasmGemmGnaf.Wasm.CoreBackEnd
import WasmGemmGnaf.Wasm.Core.RuntimeInstrProgress
import WasmGemmGnaf.Wasm.Core.ValidateModuleFullComplete
import WasmGemmGnaf.Wasm.Core.HarnessPhaseProgress
import WasmGemmGnaf.Wasm.Core.RuntimeActivationAlignment
import WasmGemmGnaf.Wasm.Core.RuntimeHandlerProgress
import WasmGemmGnaf.Wasm.Soundness
import WasmGemmGnaf.Wasm.PublicSuccessors

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace WasmGemmGnaf.Wasm

open Core

def handlerTrapBody : InstrSeq :=
  InstrSeq.ofList [
    .tryTable (.result (some (.num .i32))) ⟨[], by decide⟩
      (InstrSeq.ofList [.const .i32 ⟨0, by decide⟩])]

def handlerTrapCoreModule : Core.Module :=
  { Core.releaseBaselineModule with
    funcs := [{ typeidx := Core.idx0, locals := [], body := handlerTrapBody }] }

def handlerGemmDefType : Core.DefType :=
  .defd Core.gemmTypeDef.rectype 0

theorem handler_roll_types :
    Core.Validate.rollTypes [] [Core.gemmTypeDef] = [handlerGemmDefType] := by
  decide

theorem handler_gemm_deftype_ok :
    Core.Deftype_okA
      ({ Core.Context.empty with types := [handlerGemmDefType] } : Core.Context)
      handlerGemmDefType := by
  have htype := Core.Validate.checkTypeOkA_sound
    (C := Core.Context.empty) (td := Core.gemmTypeDef) (by decide)
  cases htype with
  | mk range index output rectype =>
      apply Core.Deftype_okA.mk
      · simpa [handlerGemmDefType, Core.gemmTypeDef, Core.Context.append,
          Core.rollDt, Core.rollRt] using rectype
      · decide

theorem handler_clos_types :
    Core.closDefTypes [handlerGemmDefType] = [handlerGemmDefType] := by
  decide

theorem handler_stored_deftypes :
    ({ Core.Context.empty with types := [handlerGemmDefType] } :
      Core.Context).StoredDeftypesOkA := by
  constructor
  · intro i dt hlookup
    cases i with
    | zero =>
        simp at hlookup
        subst dt
        exact handler_gemm_deftype_ok
    | succ i => simp at hlookup
  · intro i dt hlookup
    rw [handler_clos_types] at hlookup
    cases i with
    | zero =>
        simp at hlookup
        subst dt
        exact handler_gemm_deftype_ok
    | succ i => simp at hlookup

theorem handlerTrapCoreModule_okA :
    ∃ moduleType : Core.ModuleType,
      Core.Module_okA handlerTrapCoreModule moduleType := by
  apply Core.Validate.validateFullA_sound_of_stored
  · intro dts typesOk
    have hroll := Core.Validate.types_ok_roll typesOk
    change Core.Validate.rollTypes [] [Core.gemmTypeDef] = [] ++ dts at hroll
    rw [handler_roll_types] at hroll
    simp only [List.nil_append] at hroll
    subst dts
    exact handler_stored_deftypes
  · decide

def handlerRequest : Core.Harness.Request where
  module := handlerTrapCoreModule
  memoryExportName := Core.memoryExportName
  gemmExportName := Core.gemmExportName
  rawPtr := ⟨0, by decide⟩
  rawLen := ⟨0, by decide⟩
  rawBytes := []
  rawLength := rfl
  rawAddressBound := by decide
  rawPageBound := by decide

def handlerInstantiated : Core.Exec.Config :=
  (Core.Exec.instantiateA? ({} : Core.Exec.Store)
    handlerTrapCoreModule []).getD
      (⟨{ store := {}, frame := { mod := {} } }, []⟩ : Core.Exec.Config)

theorem handler_instantiate_eq :
    Core.Exec.instantiateA? ({} : Core.Exec.Store)
      handlerTrapCoreModule [] = some handlerInstantiated := by
  rfl

def handlerMemoryAddress : Core.Exec.MemAddr := 0
def handlerFunctionAddress : Core.Exec.FuncAddr := 0

def handlerHarness : Core.Harness.Harness :=
  { request := handlerRequest
    memoryAddr := handlerMemoryAddress
    gemmAddr := handlerFunctionAddress }

theorem handlerRequest_valid : handlerRequest.Valid := by
  refine ⟨by decide, handlerTrapCoreModule_okA, rfl,
    handlerInstantiated, handlerMemoryAddress, handlerFunctionAddress,
    handler_instantiate_eq, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

theorem handler_initial_instructions : handlerInstantiated.2 = [] := by
  rfl

theorem handler_find_memory :
    Core.Harness.findMemoryExportAddress? handlerRequest.memoryExportName
      handlerInstantiated.1.frame.mod.exports = some handlerMemoryAddress := by
  decide

theorem handler_find_function :
    Core.Harness.findFunctionExportAddress? handlerRequest.gemmExportName
      handlerInstantiated.1.frame.mod.exports = some handlerFunctionAddress := by
  decide

theorem handler_initialization_mem :
    ((.initialize (Core.Harness.initializationEvents handlerTrapCoreModule),
      .beforeEntry handlerHarness handlerInstantiated) ∈
        Core.Harness.initializationSuccessors handlerRequest) := by
  unfold Core.Harness.initializationSuccessors
  simp only [handlerRequest]
  simp only [handler_instantiate_eq]
  have hmemory :
      Core.Harness.findMemoryExportAddress? Core.memoryExportName
        handlerInstantiated.1.frame.mod.exports = some handlerMemoryAddress := by
    simpa [handlerRequest] using handler_find_memory
  have hfunction :
      Core.Harness.findFunctionExportAddress? Core.gemmExportName
        handlerInstantiated.1.frame.mod.exports = some handlerFunctionAddress := by
    simpa [handlerRequest] using handler_find_function
  simp only [hmemory, hfunction]
  simp [handlerHarness, handlerRequest]

theorem handler_initialization_step :
    Core.Harness.StepA (.initializing handlerRequest)
      (.initialize (Core.Harness.initializationEvents handlerTrapCoreModule))
      (.beforeEntry handlerHarness handlerInstantiated) :=
  Core.Harness.mem_initializationSuccessors_stepA handlerRequest_valid
    handler_initialization_mem

theorem handler_initial_ready :
    Core.Harness.GemmFunctionReady handlerHarness
      handlerInstantiated.1.store := by
  decide

theorem handler_install_ready :
    Core.Harness.RawInstallReady handlerHarness handlerInstantiated.1 := by
  decide

theorem handler_install_exact :
    Core.Harness.installRaw? handlerHarness handlerInstantiated.1 =
      some (1, 0, handlerInstantiated.1) := by
  rfl

theorem handler_initializes :
    Core.Harness.InitializesA handlerRequest
      (.beforeEntry handlerHarness handlerInstantiated) := by
  cases handler_initialization_step with
  | instantiate initializes => exact initializes

theorem handler_instantiateA :
    Core.Exec.InstantiateA ({} : Core.Exec.Store) handlerTrapCoreModule []
      handlerInstantiated := by
  cases handler_initializes with
  | mk hinst _ _ => exact hinst

theorem handler_resolves :
    Core.Harness.ResolvesExports handlerInstantiated.1.frame.mod
      handlerHarness := by
  cases handler_initializes with
  | mk _ resolves _ => exact resolves

def handlerInvoked : Core.Exec.Config :=
  (Core.Harness.invokeResult? handlerHarness
    handlerInstantiated.1.store).getD
      (⟨{ store := {}, frame := { mod := {} } }, []⟩ : Core.Exec.Config)

theorem handler_invoke_eq :
    Core.Harness.invokeResult? handlerHarness
      handlerInstantiated.1.store = some handlerInvoked := by
  rfl

theorem handler_invokeA :
    Core.Exec.InvokeA handlerInstantiated.1.store handlerHarness.gemmAddr
      handlerHarness.args handlerInvoked :=
  Core.Harness.invokeResult?_sound handler_invoke_eq

theorem handler_aligned_activation :
    ∃ (event : Core.Exec.Event) (target : Core.Exec.Config)
        (frame : Core.Exec.Frame) (sourceIndex : Nat)
        (sourceFunction : Core.Func) (context : Core.Context)
        (localTypes : List Core.LocalType),
      Core.Exec.StepA handlerInvoked event target ∧
      Core.Harness.coreTrapCause? event = none ∧
      target =
        (⟨handlerInstantiated.1.store, { mod := {} }⟩,
          [.frame 1 frame
            [.label 1 [] (Core.Exec.plains sourceFunction.body.toList)]]) ∧
      frame.mod = handlerInstantiated.1.frame.mod ∧
      frame.mod.types = Core.closDefTypes context.types ∧
      Core.Types_okA Core.Context.empty handlerTrapCoreModule.types
        context.types ∧
      handlerTrapCoreModule.funcs[sourceIndex]? = some sourceFunction ∧
      Core.Exec.LocalsOkA handlerInstantiated.1.store frame.locals
        ((Core.ValTypes.ofList [.num .i32, .num .i32]).toList.map
          (fun type => ⟨Core.Init.set, type⟩) ++ localTypes) ∧
      Core.Expr_okA (Core.Context.append context
        { locals :=
            (Core.ValTypes.ofList [.num .i32, .num .i32]).toList.map
                (fun type => ⟨Core.Init.set, type⟩) ++ localTypes,
          labels := [(Core.ValTypes.ofList [.num .i32]).toList],
          ret := some (Core.ValTypes.ofList [.num .i32]).toList })
        sourceFunction.body (Core.ValTypes.ofList [.num .i32]).toList := by
  exact handler_instantiateA.gemm_callRefFunc_aligned_activation
    (by decide) rfl handler_resolves handler_initial_ready handler_invokeA

def handlerTrapFunction : Core.Func :=
  { typeidx := Core.idx0, locals := [], body := handlerTrapBody }

theorem handlerTrapCoreModule_funcs :
    handlerTrapCoreModule.funcs = [handlerTrapFunction] := by
  rfl

theorem handler_source_function_eq {sourceIndex : Nat}
    {sourceFunction : Core.Func}
    (hlookup : handlerTrapCoreModule.funcs[sourceIndex]? =
      some sourceFunction) :
    sourceFunction = handlerTrapFunction := by
  rw [handlerTrapCoreModule_funcs] at hlookup
  cases sourceIndex with
  | zero => simpa using (Option.some.inj hlookup).symm
  | succ index => simp at hlookup

def handlerConstInstr : Core.Instr :=
  .const .i32 ⟨0, by decide⟩

def handlerTryInstr : Core.Instr :=
  .tryTable (.result (some (.num .i32))) ⟨[], by decide⟩
    (Core.InstrSeq.ofList [handlerConstInstr])

theorem handler_function_body :
    handlerTrapFunction.body = Core.InstrSeq.ofList [handlerTryInstr] := by
  rfl

def handlerOpaqueCore (frame : Core.Exec.Frame) : Core.Exec.Config :=
  (⟨handlerInstantiated.1.store, { mod := {} }⟩,
    [.frame 1 frame
      [.label 1 []
        [.handler 1 []
          [.label 1 [] [.plain handlerConstInstr]]]]])

theorem handler_tryTable_step (frame : Core.Exec.Frame) :
    Core.Exec.StepA
      (⟨handlerInstantiated.1.store, { mod := {} }⟩,
        [.frame 1 frame
          [.label 1 [] [.plain handlerTryInstr]]])
      (.ctxtFrame 1 (.ctxtLabel 1
        (.read .tryTable [handlerTryInstr])))
      (handlerOpaqueCore frame) := by
  letI : Core.Exec.ExecutionAuthority :=
    Core.Exec.amendedExecutionAuthority
  have hread : Core.Exec.Step_readA
      ⟨handlerInstantiated.1.store, frame⟩ .tryTable
      [.plain handlerTryInstr]
      [.handler 1 []
        [.label 1 [] [.plain handlerConstInstr]]] := by
    apply Core.Exec.Step_read.tryTable
      (vs := []) (t₁ := []) (t₂ := [.num .i32]) (m := 0) (n := 1)
    all_goals rfl
  exact .ctxtFrame (.ctxtLabel (.read hread))

def handlerOpaqueHarness (frame : Core.Exec.Frame) : Core.Harness.Config :=
  .afterEntry handlerHarness handlerInstantiated.1.store
    (handlerOpaqueCore frame)

theorem handler_opaque_core_step (frame : Core.Exec.Frame) :
    ∃ event target,
      Core.Exec.StepA (handlerOpaqueCore frame) event target ∧
      Core.Harness.coreTrapCause? event = none ∧
      target.2 ≠ [.trap] := by
  let value : Core.Exec.Val :=
    .num ⟨.i32, ⟨0, by decide⟩⟩
  have pure : Core.Exec.Step_pure Core.Exec.releasedNumerics
      [.label 1 [] [.plain handlerConstInstr]]
      (Core.Exec.vals [value]) := by
    simpa [value] using
      (Core.Exec.Step_pure.labelVals
        (Nm := Core.Exec.releasedNumerics) (n := 1) (cont := [])
        (vs := [value]))
  obtain ⟨pureEvent, member⟩ :=
    Core.Exec.step_pure_mem_pureSuccessors pure
  have hvalue :
      [.plain handlerConstInstr] = Core.Exec.vals [value] := by
    rfl
  have hpureEvent : pureEvent =
      ({ rule := .labelVals, choice := 0 } : Core.Exec.PureEvent) := by
    rw [Core.Exec.pureSuccessors_label, hvalue,
      Core.Exec.pureOfLabel_vals] at member
    simpa [Core.Exec.single] using member
  rw [hpureEvent] at member
  let innerEvent : Core.Exec.Event :=
    .pure { rule := .labelVals, choice := 0 }
      (Core.Exec.sourcePlains
        [.label 1 [] [.plain handlerConstInstr]])
  have innerStep : Core.Exec.StepA
      (⟨handlerInstantiated.1.store, frame⟩,
        [.label 1 [] [.plain handlerConstInstr]])
      innerEvent
      (⟨handlerInstantiated.1.store, frame⟩,
        Core.Exec.vals [value]) := by
    exact .pure member
  have handlerStep : Core.Exec.StepA
      (⟨handlerInstantiated.1.store, frame⟩,
        [.handler 1 []
          [.label 1 [] [.plain handlerConstInstr]]])
      (.ctxtHandler 1 innerEvent)
      (⟨handlerInstantiated.1.store, frame⟩,
        [.handler 1 [] (Core.Exec.vals [value])]) :=
    .ctxtHandler innerStep
  have labelStep : Core.Exec.StepA
      (⟨handlerInstantiated.1.store, frame⟩,
        [.label 1 []
          [.handler 1 []
            [.label 1 [] [.plain handlerConstInstr]]]])
      (.ctxtLabel 1 (.ctxtHandler 1 innerEvent))
      (⟨handlerInstantiated.1.store, frame⟩,
        [.label 1 []
          [.handler 1 [] (Core.Exec.vals [value])]]) :=
    .ctxtLabel handlerStep
  have frameStep : Core.Exec.StepA
      (handlerOpaqueCore frame)
      (.ctxtFrame 1 (.ctxtLabel 1 (.ctxtHandler 1 innerEvent)))
      (⟨handlerInstantiated.1.store, { mod := {} }⟩,
        [.frame 1 frame
          [.label 1 []
            [.handler 1 [] (Core.Exec.vals [value])]]]) := by
    simpa [handlerOpaqueCore] using
      (Core.Exec.StepA.ctxtFrame labelStep)
  refine ⟨_, _, frameStep, ?_, by simp⟩
  rfl

theorem handler_opaque_reachable :
    ∃ (frame : Core.Exec.Frame) (trace : List Core.Harness.Event),
      Core.Harness.StepsA (.initializing handlerRequest) trace
        (handlerOpaqueHarness frame) := by
  obtain ⟨activationEvent, activationTarget, frame, sourceIndex,
      sourceFunction, context, localTypes, hactivate, hactivationNoTrap,
      rfl, hframeModule, hframeTypes, htypes, hsourceFunction,
      hlocals, hbody⟩ := handler_aligned_activation
  have hsourceEq := handler_source_function_eq hsourceFunction
  subst sourceFunction
  let activation : Core.Exec.Config :=
    (⟨handlerInstantiated.1.store, { mod := {} }⟩,
      [.frame 1 frame [.label 1 [] [.plain handlerTryInstr]]])
  have hactivate' :
      Core.Exec.StepA handlerInvoked activationEvent activation := by
    simpa [activation, handler_function_body] using hactivate
  have hinstall :
      Core.Harness.StepA
        (.beforeEntry handlerHarness handlerInstantiated)
        (.installRaw handlerHarness.memoryAddr
          handlerHarness.request.rawPtr.val
          handlerHarness.request.rawLen.val 1 0)
        (.readyToEnter handlerHarness handlerInstantiated.1) := by
    simpa only [handler_initial_instructions] using
      (Core.Harness.StepA.installRaw handler_install_exact)
  have henter :
      Core.Harness.StepA
        (.readyToEnter handlerHarness handlerInstantiated.1)
        (.enterGemm handlerHarness.gemmAddr)
        (.afterEntry handlerHarness handlerInstantiated.1.store
          handlerInvoked) :=
    .enterGemm handler_invokeA
  have hactivationHarness :
      Core.Harness.StepA
        (.afterEntry handlerHarness handlerInstantiated.1.store
          handlerInvoked)
        (.coreAfterEntry activationEvent)
        (.afterEntry handlerHarness handlerInstantiated.1.store
          activation) := by
    exact .coreAfter hactivate' hactivationNoTrap (by
      simp [activation])
  have htry : Core.Exec.StepA activation
      (.ctxtFrame 1 (.ctxtLabel 1
        (.read .tryTable [handlerTryInstr])))
      (handlerOpaqueCore frame) := by
    simpa [activation] using handler_tryTable_step frame
  have htryHarness :
      Core.Harness.StepA
        (.afterEntry handlerHarness handlerInstantiated.1.store activation)
        (.coreAfterEntry
          (.ctxtFrame 1 (.ctxtLabel 1
            (.read .tryTable [handlerTryInstr]))))
        (handlerOpaqueHarness frame) := by
    exact .coreAfter htry rfl (by simp [handlerOpaqueCore])
  refine ⟨frame,
    [.initialize (Core.Harness.initializationEvents handlerTrapCoreModule),
      .installRaw handlerHarness.memoryAddr
        handlerHarness.request.rawPtr.val
        handlerHarness.request.rawLen.val 1 0,
      .enterGemm handlerHarness.gemmAddr,
      .coreAfterEntry activationEvent,
      .coreAfterEntry
        (.ctxtFrame 1 (.ctxtLabel 1
          (.read .tryTable [handlerTryInstr])))], ?_⟩
  exact .cons handler_initialization_step
    (.cons hinstall
      (.cons henter
        (.cons hactivationHarness
          (.cons htryHarness (.refl _)))))

def handlerTrapModule : Module :=
  Module.ofEncodableCore handlerTrapCoreModule (by decide)

theorem handlerTrapModule_valid : DeclarativelyValid handlerTrapModule := by
  simpa [handlerTrapModule] using handlerTrapCoreModule_okA

theorem handler_validation_progress_regression :
    ∃ (module : Module) (config : Config),
      DeclarativelyValid module ∧
      ConfigInstantiates module config ∧
      ConfigWellTyped config ∧
      ¬ IsTerminal config ∧
      (successors config).Nonempty := by
  obtain ⟨frame, trace, reaches⟩ := handler_opaque_reachable
  have wellTyped : (handlerOpaqueHarness frame).WellTyped :=
    ⟨handlerRequest, trace, handlerRequest_valid, reaches⟩
  let config : Config := ⟨handlerOpaqueHarness frame, wellTyped⟩
  have instantiates : ConfigInstantiates handlerTrapModule config := by
    exact ⟨handlerRequest, trace, rfl, handlerRequest_valid, reaches⟩
  have notTerminal : ¬ IsTerminal config := by
    unfold IsTerminal Core.Harness.IsTerminal
    change ¬ ((∃ value, Core.Harness.Halt
        (handlerOpaqueHarness frame) value) ∨
      (∃ trap, Core.Harness.Trapped
        (handlerOpaqueHarness frame) trap) ∨
      (∃ exceptionValue, Core.Harness.Thrown
        (handlerOpaqueHarness frame) exceptionValue))
    rintro (⟨_, halt⟩ | ⟨_, trapped⟩ | ⟨_, thrown⟩)
    · cases halt
    · cases trapped
    · cases thrown
  obtain ⟨coreEvent, coreTarget, coreStep, coreNoTrap, coreNotFinal⟩ :=
    handler_opaque_core_step frame
  have harnessStep : Core.Harness.StepA (handlerOpaqueHarness frame)
      (.coreAfterEntry coreEvent)
      (.afterEntry handlerHarness handlerInstantiated.1.store coreTarget) := by
    exact .coreAfter coreStep coreNoTrap coreNotFinal
  let next : Config :=
    config.successor (.coreAfterEntry coreEvent)
      (.afterEntry handlerHarness handlerInstantiated.1.store coreTarget)
      harnessStep
  have hmember :
      ((.coreAfterEntry coreEvent), next) ∈ successors config :=
    Core.Harness.stepA_mem_typedSuccessors harnessStep
  exact ⟨handlerTrapModule, config, handlerTrapModule_valid,
    instantiates, wellTyped, notTerminal, ⟨_, hmember⟩⟩

end WasmGemmGnaf.Wasm
