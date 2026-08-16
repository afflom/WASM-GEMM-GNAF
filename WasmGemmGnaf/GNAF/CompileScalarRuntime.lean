import WasmGemmGnaf.GNAF.CompileRuntime
import WasmGemmGnaf.Wasm.PublicSuccessors

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectScalar

/-- Status values retained by the observationally dead-code-eliminating
lowering, in their source order. -/
def statusAssignments : Plan → List Nat
  | .seq first second => statusAssignments first ++ statusAssignments second
  | .allocScratch _ body | .opaqueProcess _ body => statusAssignments body
  | .setStatus status => [status.code]
  | _ => []

/-- Apply an ordered list of status replacements. -/
def applyStatusAssignments : List Nat → Nat → Nat
  | [], initial => initial
  | value :: rest, _ => applyStatusAssignments rest value

theorem applyStatusAssignments_append (first second : List Nat) (initial : Nat) :
    applyStatusAssignments (first ++ second) initial =
      applyStatusAssignments second (applyStatusAssignments first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.cons_append, applyStatusAssignments]
      exact ih value

theorem apply_statusAssignments (plan : Plan) (initial : Nat) :
    applyStatusAssignments (statusAssignments plan) initial =
      plan.supportedStatus initial := by
  induction plan generalizing initial with
  | seq first second ihFirst ihSecond =>
      simp [statusAssignments, applyStatusAssignments_append, ihFirst, ihSecond,
        Plan.supportedStatus]
  | allocScratch _ body ih | opaqueProcess _ body ih =>
      simpa [statusAssignments, Plan.supportedStatus] using ih initial
  | setStatus => rfl
  | nop | classifyRaw | dispatchLayout | branch | pack | unpack | storeReg |
      loadReg | loopNest | loopReg | tiled | reduce | setReg | scalarOp |
      vectorOp | emitTable | tableLoad | buildOutput => rfl

theorem statusCode_eq_flatMap (environment : CompileEnv) (plan : Plan) :
    statusCode environment plan =
      (statusAssignments plan).flatMap (fun value =>
        [constL value, localSet environment.statusLocal]) := by
  induction plan with
  | seq first second ihFirst ihSecond =>
      simp [statusCode, statusAssignments, ihFirst, ihSecond]
  | allocScratch _ body ih | opaqueProcess _ body ih =>
      simpa [statusCode, statusAssignments] using ih
  | setStatus => rfl
  | nop | classifyRaw | dispatchLayout | branch | pack | unpack | storeReg |
      loadReg | loopNest | loopReg | tiled | reduce | setReg | scalarOp |
      vectorOp | emitTable | tableLoad | buildOutput => rfl

end DirectScalar

namespace DirectScalarRuntime

def statusValue (value : Nat) : Wasm.Core.Exec.Val :=
  .num ⟨.i64, coreU64 value⟩

def writeLocal (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val) : Wasm.Core.Exec.State :=
  { state with frame :=
      { state.frame with locals := state.frame.locals.set index (some value) } }

@[simp] theorem writeLocal_store (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val) : (writeLocal state index value).store = state.store :=
  rfl

@[simp] theorem writeLocal_locals_length (state : Wasm.Core.Exec.State)
    (index : Nat) (value : Wasm.Core.Exec.Val) :
    (writeLocal state index value).frame.locals.length = state.frame.locals.length := by
  simp [writeLocal]

theorem withLocal_eq_writeLocal (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val) (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index) :
    state.withLocal (coreU32 index) value = some (writeLocal state index value) := by
  simp [Wasm.Core.Exec.State.withLocal, Wasm.Core.Exec.setAt?, hindex, hexact,
    writeLocal]

@[simp] theorem writeLocal_local_same (state : Wasm.Core.Exec.State)
    (index : Nat) (value : Wasm.Core.Exec.Val)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index) :
    (writeLocal state index value).localOf (coreU32 index) = some (some value) := by
  simp [Wasm.Core.Exec.State.localOf, writeLocal, hexact, hindex]

def applyStatusWrites (state : Wasm.Core.Exec.State) (index : Nat) :
    List Nat → Wasm.Core.Exec.State
  | [] => state
  | value :: rest => applyStatusWrites (writeLocal state index (statusValue value))
      index rest

@[simp] theorem applyStatusWrites_store (state : Wasm.Core.Exec.State)
    (index : Nat) (assignments : List Nat) :
    (applyStatusWrites state index assignments).store = state.store := by
  induction assignments generalizing state with
  | nil => rfl
  | cons value rest ih => exact ih (writeLocal state index (statusValue value))

@[simp] theorem applyStatusWrites_locals_length (state : Wasm.Core.Exec.State)
    (index : Nat) (assignments : List Nat) :
    (applyStatusWrites state index assignments).frame.locals.length =
      state.frame.locals.length := by
  induction assignments generalizing state with
  | nil => rfl
  | cons value rest ih =>
      rw [applyStatusWrites, ih, writeLocal_locals_length]

theorem applyStatusWrites_local (state : Wasm.Core.Exec.State) (index initial : Nat)
    (assignments : List Nat) (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    (hinitial : state.localOf (coreU32 index) =
      some (some (statusValue initial))) :
    (applyStatusWrites state index assignments).localOf (coreU32 index) =
      some (some (statusValue
        (DirectScalar.applyStatusAssignments assignments initial))) := by
  induction assignments generalizing state initial with
  | nil => exact hinitial
  | cons value rest ih =>
      exact ih (writeLocal state index (statusValue value)) value
        (by simpa using hindex)
        (writeLocal_local_same state index (statusValue value) hindex hexact)

theorem statusAssignment_step (state : Wasm.Core.Exec.State) (index value : Nat)
    (suffix : List Wasm.Core.Instr) (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index) (hsuffix : suffix ≠ []) :
    ∃ event, Wasm.Core.Exec.StepA
        (state, Wasm.Core.Exec.plains
          ([constL value, localSet index] ++ suffix)) event
        (writeLocal state index (statusValue value),
          Wasm.Core.Exec.plains suffix) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  let event : Wasm.Core.Exec.Event :=
    .ctxtInstrs 0 (Wasm.Core.Exec.plains suffix).length
      (.localSet (coreU32 index))
  refine ⟨event, ?_, by simp [event, Wasm.Core.Harness.coreTrapCause?]⟩
  have hset := withLocal_eq_writeLocal state index (statusValue value)
    hindex hexact
  have hinner : Wasm.Core.Exec.StepA
      (state, [(statusValue value).toAdmin, .plain (localSet index)])
      (.localSet (coreU32 index))
      (writeLocal state index (statusValue value), []) := by
    exact .localSet hset
  have hsuffixAdmin : Wasm.Core.Exec.plains suffix ≠ [] := by
    simpa [Wasm.Core.Exec.plains] using hsuffix
  have hcontext : Wasm.Core.Exec.StepA
      (state, Wasm.Core.Exec.vals [] ++
        [(statusValue value).toAdmin, .plain (localSet index)] ++
          Wasm.Core.Exec.plains suffix)
      (.ctxtInstrs 0 (Wasm.Core.Exec.plains suffix).length
        (.localSet (coreU32 index)))
      (writeLocal state index (statusValue value),
        Wasm.Core.Exec.vals [] ++ [] ++ Wasm.Core.Exec.plains suffix) :=
    Wasm.Core.Exec.StepA.ctxtInstrs (vs := [])
      (is₁ := Wasm.Core.Exec.plains suffix) hinner (Or.inr hsuffixAdmin)
  simpa only [event, Wasm.Core.Exec.plains, statusValue, constL, localSet,
    List.map_append, List.map_cons, List.map_nil, List.nil_append,
    List.append_assoc, List.length_map] using hcontext

theorem statusAssignments_steps (state : Wasm.Core.Exec.State) (index : Nat) :
    ∀ (assignments : List Nat) (suffix : List Wasm.Core.Instr),
      index < state.frame.locals.length → (coreU32 index).val = index →
      suffix ≠ [] →
      ∃ trace, Wasm.Core.Exec.StepsA
          (state, Wasm.Core.Exec.plains
            (assignments.flatMap (fun value =>
              [constL value, localSet index]) ++ suffix)) trace
          (applyStatusWrites state index assignments,
            Wasm.Core.Exec.plains suffix) ∧
        ∀ event ∈ trace, Wasm.Core.Harness.coreTrapCause? event = none := by
  intro assignments
  induction assignments generalizing state with
  | nil =>
      intro suffix _ _ _
      exact ⟨[], .refl _, by simp⟩
  | cons value rest ih =>
      intro suffix hindex hexact hsuffix
      let remaining := rest.flatMap (fun next =>
        [constL next, localSet index]) ++ suffix
      have hremaining : remaining ≠ [] := by
        intro heq
        have : suffix = [] := by
          have := congrArg (List.drop
            (rest.flatMap (fun next => [constL next, localSet index])).length) heq
          simpa [remaining] using this
        exact hsuffix this
      obtain ⟨event, hhead, hheadSafe⟩ := statusAssignment_step state index value
        remaining hindex hexact hremaining
      obtain ⟨trace, htail, htailSafe⟩ := ih
        (writeLocal state index (statusValue value)) suffix
        (by simpa using hindex) hexact hsuffix
      refine ⟨event :: trace, .cons ?_ htail, ?_⟩
      · simpa [remaining, List.flatMap_cons, List.append_assoc] using hhead
      · intro next membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · exact hheadSafe
        · exact htailSafe next membership

/-- Lift a finite Core trace through the function's result label and frame,
and then through the post-entry Harness constructor. -/
theorem liftFunctionSteps
    {source final : Wasm.Core.Exec.Config}
    {trace : List Wasm.Core.Exec.Event}
    (steps : Wasm.Core.Exec.StepsA source trace final)
    (harness : Wasm.Core.Harness.Harness) (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (hnotrap : ∀ event ∈ trace,
      Wasm.Core.Harness.coreTrapCause? event = none) :
    Wasm.Core.Harness.StepsA
      (.afterEntry harness entry
        (⟨source.1.store, outerFrame⟩,
          [.frame 1 source.1.frame [.label 1 [] source.2]]))
      (trace.map (fun event => .coreAfterEntry
        (.ctxtFrame 1 (.ctxtLabel 1 event))))
      (.afterEntry harness entry
        (⟨final.1.store, outerFrame⟩,
          [.frame 1 final.1.frame [.label 1 [] final.2]])) := by
  induction steps with
  | refl _ => exact .refl _
  | @cons source middle final event rest head tail ih =>
      have coreHead : Wasm.Core.Exec.StepA
          (⟨source.1.store, outerFrame⟩,
            [.frame 1 source.1.frame [.label 1 [] source.2]])
          (.ctxtFrame 1 (.ctxtLabel 1 event))
          (⟨middle.1.store, outerFrame⟩,
            [.frame 1 middle.1.frame [.label 1 [] middle.2]]) :=
        .ctxtFrame (.ctxtLabel head)
      let middleHarness := Wasm.Core.Harness.Config.afterEntry harness entry
        (⟨middle.1.store, outerFrame⟩,
          [.frame 1 middle.1.frame [.label 1 [] middle.2]])
      refine @Wasm.Core.Harness.StepsA.cons _ middleHarness _ _ _ ?_ ?_
      · apply Wasm.Core.Harness.StepA.coreAfter coreHead
        · simpa [Wasm.Core.Harness.coreTrapCause?] using
            hnotrap event (by simp)
        · intro heq
          injection heq with instructionEq
          cases instructionEq
      · simpa [middleHarness] using ih (fun next hnext =>
          hnotrap next (by simp [hnext]))

/-- One released pure rule can be exposed as an exact labelled Core step. -/
theorem stepA_of_pure {state : Wasm.Core.Exec.State}
    {source target : List Wasm.Core.Exec.AdminInstr}
    (step : Wasm.Core.Exec.Step_pure Wasm.Core.Exec.releasedNumerics
      source target) :
    ∃ event, Wasm.Core.Exec.StepA (state, source) event (state, target) := by
  obtain ⟨pureEvent, membership⟩ :=
    Wasm.Core.Exec.step_pure_mem_pureSuccessors step
  exact ⟨.pure pureEvent (Wasm.Core.Exec.sourcePlains source), .pure membership⟩

/-- The exact two-step status epilogue: read the `i64` status local and wrap it
to the public `i32` result. -/
theorem statusEpilogue_steps (state : Wasm.Core.Exec.State) (index value : Nat)
    (hlocal : state.localOf (coreU32 index) =
      some (some (statusValue value))) (hvalue : value < 2 ^ 32) :
    ∃ trace, Wasm.Core.Exec.StepsA
        (state, Wasm.Core.Exec.plains [localGet index, wrapI64]) trace
        (state, [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin]) ∧
      ∀ event ∈ trace, Wasm.Core.Harness.coreTrapCause? event = none := by
  letI : Wasm.Core.Exec.ExecutionAuthority :=
    Wasm.Core.Exec.amendedExecutionAuthority
  have readInner : Wasm.Core.Exec.StepA
      (state, [.plain (localGet index)])
      (.read .localGet [localGet index])
      (state, [(statusValue value).toAdmin]) := by
    apply Wasm.Core.Exec.StepA.read
    exact Wasm.Core.Exec.Step_read.localGet hlocal
  have readStep : Wasm.Core.Exec.StepA
      (state, Wasm.Core.Exec.plains [localGet index, wrapI64])
      (.ctxtInstrs 0 1 (.read .localGet [localGet index]))
      (state, [(statusValue value).toAdmin, .plain wrapI64]) := by
    have contextual := Wasm.Core.Exec.StepA.ctxtInstrs (vs := [])
      (is₁ := [.plain wrapI64]) readInner (Or.inr (by simp))
    simpa [Wasm.Core.Exec.plains, List.append_assoc] using contextual
  have hcvtop :
      Wasm.Core.Exec.releasedNumerics.cvtop__ .i64 .i32 (.ii .wrap)
        (coreU64 value) = [coreU32 value] := by
    change [Wasm.Core.Exec.ConcreteNumerics.wrap 64 32 (coreU64 value)] =
      [coreU32 value]
    congr 2
    apply Subtype.ext
    simp [Wasm.Core.Exec.ConcreteNumerics.wrap,
      Wasm.Core.Exec.Numerics.ofNatWrap, coreU32, coreU64,
      Nat.mod_eq_of_lt hvalue,
      Nat.mod_eq_of_lt (Nat.lt_trans hvalue (by decide : 2 ^ 32 < 2 ^ 64))]
  have hwrap : coreU32 value ∈
      Wasm.Core.Exec.releasedNumerics.cvtop__ .i64 .i32 (.ii .wrap)
        (coreU64 value) := by
    rw [hcvtop]
    exact List.mem_singleton.mpr rfl
  have pureWrap : Wasm.Core.Exec.Step_pure
      Wasm.Core.Exec.releasedNumerics
      [(statusValue value).toAdmin, .plain wrapI64]
      [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin] := by
    exact .cvtopVal hwrap
  let wrapPureEvent : Wasm.Core.Exec.PureEvent := ⟨.cvtopVal, 0⟩
  let wrapEvent : Wasm.Core.Exec.Event :=
    .pure wrapPureEvent (Wasm.Core.Exec.sourcePlains
      [(statusValue value).toAdmin, .plain wrapI64])
  have wrapMembership : (wrapPureEvent,
      [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin]) ∈
      Wasm.Core.Exec.pureSuccessors Wasm.Core.Exec.releasedNumerics
        [(statusValue value).toAdmin, .plain wrapI64] := by
    rw [show [(statusValue value).toAdmin, .plain wrapI64] =
      Wasm.Core.Exec.vals [statusValue value] ++ [.plain wrapI64] by rfl]
    rw [Wasm.Core.Exec.pureSuccessors_ofInstr
      [statusValue value] wrapI64 (by rfl)]
    simp [Wasm.Core.Exec.pureOfInstr, Wasm.Core.Exec.Val.toAdmin,
      statusValue, wrapI64, hcvtop, Wasm.Core.Exec.choices,
      Wasm.Core.Exec.withIndex, wrapPureEvent]
  have wrapStep : Wasm.Core.Exec.StepA
      (state, [(statusValue value).toAdmin, .plain wrapI64]) wrapEvent
      (state, [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin]) := by
    exact .pure wrapMembership
  refine ⟨[.ctxtInstrs 0 1 (.read .localGet [localGet index]), wrapEvent],
    .cons readStep (.cons wrapStep (.refl _)), ?_⟩
  intro event membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · rfl
  · rfl

theorem execSteps_append {initial middle final : Wasm.Core.Exec.Config}
    {first second : List Wasm.Core.Exec.Event}
    (left : Wasm.Core.Exec.StepsA initial first middle)
    (right : Wasm.Core.Exec.StepsA middle second final) :
    Wasm.Core.Exec.StepsA initial (first ++ second) final := by
  induction left with
  | refl _ => simpa using right
  | cons head tail ih => exact .cons head (ih right)

/-- The complete currently admitted emitted body returns exactly the source
status transformer and preserves the entire Core store. -/
theorem emittedBody_steps {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (state : Wasm.Core.Exec.State)
    (hindex : (envOf checked.inputSig checked.plan).statusLocal <
      state.frame.locals.length)
    (hexact : (coreU32 (envOf checked.inputSig checked.plan).statusLocal).val =
      (envOf checked.inputSig checked.plan).statusLocal)
    (hzero : state.localOf
      (coreU32 (envOf checked.inputSig checked.plan).statusLocal) =
        some (some (statusValue 0))) :
    ∃ (finalState : Wasm.Core.Exec.State)
        (trace : List Wasm.Core.Exec.Event),
      Wasm.Core.Exec.StepsA
        (state, Wasm.Core.Exec.plains
          (bodyCode (envOf checked.inputSig checked.plan)
            checked.inputSig.scratch checked.plan)) trace
        (finalState,
          [(Wasm.Core.Exec.Val.num
            ⟨.i32, coreU32 checked.returnedStatus⟩).toAdmin]) ∧
      finalState.store = state.store ∧
      ∀ event ∈ trace, Wasm.Core.Harness.coreTrapCause? event = none := by
  let environment := envOf checked.inputSig checked.plan
  let assignments := DirectScalar.statusAssignments checked.plan
  let suffix := [localGet environment.statusLocal, wrapI64]
  obtain ⟨statusTrace, statusSteps, statusSafe⟩ :=
    statusAssignments_steps state environment.statusLocal assignments suffix
      (by simpa [environment] using hindex)
      (by simpa [environment] using hexact) (by simp [suffix])
  let afterStatus := applyStatusWrites state environment.statusLocal assignments
  have hstatusLocal : afterStatus.localOf (coreU32 environment.statusLocal) =
      some (some (statusValue checked.returnedStatus)) := by
    have hlocal := applyStatusWrites_local state environment.statusLocal 0
      assignments (by simpa [environment] using hindex)
      (by simpa [environment] using hexact)
      (by simpa [environment] using hzero)
    simpa [afterStatus, assignments, CheckedPlan.returnedStatus,
      DirectScalar.apply_statusAssignments] using hlocal
  obtain ⟨epilogueTrace, epilogueSteps, epilogueSafe⟩ :=
    statusEpilogue_steps afterStatus environment.statusLocal
      checked.returnedStatus hstatusLocal checked.returnedStatus_lt_two_pow_32
  refine ⟨afterStatus, statusTrace ++ epilogueTrace, ?_, ?_, ?_⟩
  · have combined := execSteps_append statusSteps epilogueSteps
    have bodyEq := DirectScalar.bodyCode_eq_statusCode checked
    rw [DirectScalar.statusCode_eq_flatMap] at bodyEq
    simpa [environment, assignments, suffix, bodyEq] using combined
  · exact applyStatusWrites_store state environment.statusLocal assignments
  · intro event membership
    rw [List.mem_append] at membership
    exact membership.elim (statusSafe event) (epilogueSafe event)

theorem statusLocal_lt_two_pow_32 {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    (envOf checked.inputSig checked.plan).statusLocal < 2 ^ 32 := by
  have represented := of_decide_eq_true checked.coreRepresentable
  have himmediate := represented.1
  simp [envOf, CompileEnv.statusLocal] at ⊢
  have hdepth : 3 + checked.inputSig.regs + checked.plan.depth < 2 ^ 32 := by
    omega
  omega

theorem emittedFunctionState_status_zero {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (store : Wasm.Core.Exec.Store) (harness : Wasm.Core.Harness.Harness)
    (moduleInstance : Wasm.Core.Exec.ModuleInst) :
    let environment := envOf checked.inputSig checked.plan
    let frame : Wasm.Core.Exec.Frame :=
      { locals := harness.args.map some ++
          (List.replicate environment.declaredLocals
            ({ valtype := .num .i64 } : Wasm.Core.Local)).map
              (fun declaration => Wasm.Core.Exec.default_ declaration.valtype)
        mod := moduleInstance }
    let state : Wasm.Core.Exec.State := ⟨store, frame⟩
    environment.statusLocal < state.frame.locals.length ∧
      state.localOf (coreU32 environment.statusLocal) =
        some (some (statusValue 0)) := by
  intro environment frame state
  have hexact := coreU32_exact environment.statusLocal
    (by simpa [environment] using statusLocal_lt_two_pow_32 checked)
  constructor
  · simp [state, frame, environment, Wasm.Core.Harness.Harness.args,
      CompileEnv.statusLocal, CompileEnv.declaredLocals]
    omega
  · simp only [state, Wasm.Core.Exec.State.localOf, frame]
    rw [hexact]
    rw [List.getElem?_append_right]
    · simp [environment, Wasm.Core.Harness.Harness.args,
        CompileEnv.statusLocal, CompileEnv.declaredLocals, statusValue,
        Wasm.Core.Exec.default_, coreU64, List.getElem?_replicate]
      constructor
      · omega
      · rfl
    · simp [environment, Wasm.Core.Harness.Harness.args,
        CompileEnv.statusLocal]

/-- The administrative result label closes in one exact pure Core step. -/
theorem labelVals_step (state : Wasm.Core.Exec.State) (n : Nat)
    (continuation : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.StepA
      (state, [.label n continuation (Wasm.Core.Exec.vals values)])
      (.pure ⟨.labelVals, 0⟩
        (Wasm.Core.Exec.sourcePlains
          [.label n continuation (Wasm.Core.Exec.vals values)]))
      (state, Wasm.Core.Exec.vals values) := by
  apply Wasm.Core.Exec.StepA.pure
  rw [Wasm.Core.Exec.pureSuccessors_label,
    Wasm.Core.Exec.pureOfLabel_vals]
  simp [Wasm.Core.Exec.single]

/-- The administrative function frame closes once its exact result arity is
present. -/
theorem frameVals_step (state : Wasm.Core.Exec.State) (n : Nat)
    (frame : Wasm.Core.Exec.Frame) (values : List Wasm.Core.Exec.Val)
    (hlength : values.length = n) :
    Wasm.Core.Exec.StepA
      (state, [.frame n frame (Wasm.Core.Exec.vals values)])
      (.pure ⟨.frameVals, 0⟩
        (Wasm.Core.Exec.sourcePlains
          [.frame n frame (Wasm.Core.Exec.vals values)]))
      (state, Wasm.Core.Exec.vals values) := by
  apply Wasm.Core.Exec.StepA.pure
  rw [Wasm.Core.Exec.pureSuccessors_frame,
    Wasm.Core.Exec.pureOfFrame_vals, if_pos hlength]
  simp [Wasm.Core.Exec.single]

/-- Execute the complete admitted body and discharge its administrative
result label/frame and the Harness return boundary. -/
theorem emittedFunction_steps {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (state : Wasm.Core.Exec.State)
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store) (outerFrame : Wasm.Core.Exec.Frame)
    (hindex : (envOf checked.inputSig checked.plan).statusLocal <
      state.frame.locals.length)
    (hexact : (coreU32
      (envOf checked.inputSig checked.plan).statusLocal).val =
        (envOf checked.inputSig checked.plan).statusLocal)
    (hzero : state.localOf
      (coreU32 (envOf checked.inputSig checked.plan).statusLocal) =
        some (some (statusValue 0))) :
    ∃ trace : List Wasm.Core.Harness.Event,
      Wasm.Core.Harness.StepsA
        (.afterEntry harness entry
          (⟨state.store, outerFrame⟩,
            [.frame 1 state.frame [.label 1 []
              (Wasm.Core.Exec.plains
                (bodyCode (envOf checked.inputSig checked.plan)
                  checked.inputSig.scratch checked.plan))]]))
        trace
        (.returned harness entry
          (.num ⟨.i32, coreU32 checked.returnedStatus⟩)
          ⟨state.store, outerFrame⟩) := by
  let value : Wasm.Core.Exec.Val :=
    .num ⟨.i32, coreU32 checked.returnedStatus⟩
  obtain ⟨finalState, bodyTrace, bodySteps, hstore, bodySafe⟩ :=
    emittedBody_steps checked state hindex hexact hzero
  have lifted := liftFunctionSteps bodySteps harness entry outerFrame bodySafe
  let labelPureEvent : Wasm.Core.Exec.PureEvent := ⟨.labelVals, 0⟩
  let labelEvent : Wasm.Core.Exec.Event :=
    .pure labelPureEvent
      (Wasm.Core.Exec.sourcePlains
        [.label 1 [] (Wasm.Core.Exec.vals [value])])
  have labelInner : Wasm.Core.Exec.StepA
      (finalState, [.label 1 [] (Wasm.Core.Exec.vals [value])])
      labelEvent (finalState, Wasm.Core.Exec.vals [value]) := by
    simpa [labelEvent, labelPureEvent, value] using
      labelVals_step finalState 1 [] [value]
  have labelCore : Wasm.Core.Exec.StepA
      (⟨finalState.store, outerFrame⟩,
        [.frame 1 finalState.frame
          [.label 1 [] (Wasm.Core.Exec.vals [value])]])
      (.ctxtFrame 1 labelEvent)
      (⟨finalState.store, outerFrame⟩,
        [.frame 1 finalState.frame (Wasm.Core.Exec.vals [value])]) :=
    .ctxtFrame labelInner
  have labelHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩,
          [.frame 1 finalState.frame
            [.label 1 [] (Wasm.Core.Exec.vals [value])]]))
      (.coreAfterEntry (.ctxtFrame 1 labelEvent))
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩,
          [.frame 1 finalState.frame (Wasm.Core.Exec.vals [value])])) := by
    apply Wasm.Core.Harness.StepA.coreAfter labelCore
    · rfl
    · simp
  let framePureEvent : Wasm.Core.Exec.PureEvent := ⟨.frameVals, 0⟩
  let frameEvent : Wasm.Core.Exec.Event :=
    .pure framePureEvent
      (Wasm.Core.Exec.sourcePlains
        [.frame 1 finalState.frame (Wasm.Core.Exec.vals [value])])
  have frameCore : Wasm.Core.Exec.StepA
      (⟨finalState.store, outerFrame⟩,
        [.frame 1 finalState.frame (Wasm.Core.Exec.vals [value])])
      frameEvent
      (⟨finalState.store, outerFrame⟩, Wasm.Core.Exec.vals [value]) := by
    simpa [frameEvent, framePureEvent] using
      frameVals_step ⟨finalState.store, outerFrame⟩ 1 finalState.frame
        [value] (by simp)
  have frameHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩,
          [.frame 1 finalState.frame (Wasm.Core.Exec.vals [value])]))
      (.coreAfterEntry frameEvent)
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩, Wasm.Core.Exec.vals [value])) := by
    apply Wasm.Core.Harness.StepA.coreAfter frameCore
    · rfl
    · simp [value, Wasm.Core.Exec.Val.toAdmin]
  have returned : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩, Wasm.Core.Exec.vals [value]))
      .returnAfterEntry
      (.returned harness entry value ⟨finalState.store, outerFrame⟩) :=
    .returnAfter
  have suffix : Wasm.Core.Harness.StepsA
      (.afterEntry harness entry
        (⟨finalState.store, outerFrame⟩,
          [.frame 1 finalState.frame
            [.label 1 [] (Wasm.Core.Exec.vals [value])]]))
      [(.coreAfterEntry (.ctxtFrame 1 labelEvent)),
       (.coreAfterEntry frameEvent), .returnAfterEntry]
      (.returned harness entry value ⟨finalState.store, outerFrame⟩) :=
    .cons labelHarness (.cons frameHarness (.cons returned (.refl _)))
  refine ⟨bodyTrace.map (fun event => .coreAfterEntry
      (.ctxtFrame 1 (.ctxtLabel 1 event))) ++
      [(.coreAfterEntry (.ctxtFrame 1 labelEvent)),
       (.coreAfterEntry frameEvent), .returnAfterEntry], ?_⟩
  have combined := Wasm.Core.Harness.StepsA.append lifted suffix
  simpa [value, hstore] using combined

/-- The direct compiler has a concrete finite public execution for every
successful canonical initialization.  This construction is independent of
the refinement theorem's quantification over an arbitrary relational run. -/
theorem compile_canonical_finiteExecution {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    ∃ (trace : List Wasm.Event) (observation : Wasm.ExecutionObservation),
      Wasm.ExecutionObservation.trace observation = trace ∧
        Wasm.FiniteExecution initial observation ∧
        Accepts checked raw observation := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  let harness : Wasm.Core.Harness.Harness :=
    { request := request, memoryAddr := 0, gemmAddr := 0 }
  let emittedFunction : Wasm.Core.Func :=
    { typeidx := coreU32 0
      locals := List.replicate environment.declaredLocals
        { valtype := .num .i64 }
      body := Wasm.Core.InstrSeq.ofList
        (bodyCode environment checked.inputSig.scratch checked.plan) }
  obtain ⟨ready, after, bodyState, installedState, function, entry,
      callEvent, installStep, enterStep, callStep, bodyShape,
      entryObserved, entryMatches⟩ :=
    compile_public_steps_into_emitted_body checked raw hplain
  let innerFrame : Wasm.Core.Exec.Frame :=
    { locals := harness.args.map some ++
        emittedFunction.locals.map
          (fun declaration => Wasm.Core.Exec.default_ declaration.valtype)
      mod := function.mod }
  let innerState : Wasm.Core.Exec.State :=
    ⟨installedState.store, innerFrame⟩
  let outerFrame : Wasm.Core.Exec.Frame := { mod := {} }
  have initializedStatus := emittedFunctionState_status_zero checked
    installedState.store harness function.mod
  have statusIndex : environment.statusLocal < innerState.frame.locals.length := by
    simpa [environment, innerState, innerFrame, emittedFunction] using
      initializedStatus.1
  have statusZero : innerState.localOf (coreU32 environment.statusLocal) =
      some (some (statusValue 0)) := by
    simpa [environment, innerState, innerFrame, emittedFunction] using
      initializedStatus.2
  have statusExact : (coreU32 environment.statusLocal).val =
      environment.statusLocal :=
    coreU32_exact environment.statusLocal
      (by simpa [environment] using statusLocal_lt_two_pow_32 checked)
  obtain ⟨bodyExitTrace, bodyExit⟩ :=
    emittedFunction_steps checked innerState harness installedState.store
      outerFrame (by simpa [environment] using statusIndex)
      (by simpa [environment] using statusExact)
      (by simpa [environment] using statusZero)
  let returnedState : Wasm.Core.Exec.State :=
    ⟨installedState.store, outerFrame⟩
  let returnedValue : Wasm.Value :=
    .num ⟨.i32, coreU32 checked.returnedStatus⟩
  have bodyExitFromPublic : Wasm.Core.Harness.StepsA bodyState.1 bodyExitTrace
      (.returned harness installedState.store returnedValue returnedState) := by
    rw [bodyShape]
    simpa [innerState, innerFrame, outerFrame, emittedFunction,
      returnedValue, returnedState] using bodyExit
  let installEvent : Wasm.Event :=
    .installRaw 0 request.rawPtr.val request.rawLen.val environment.pages
      (Wasm.Core.Harness.rawTargetPages request - environment.pages)
  let enterEvent : Wasm.Event := .enterGemm 0
  let callHarnessEvent : Wasm.Event := .coreAfterEntry callEvent
  have completeSteps : Wasm.Core.Harness.StepsA initial.1
      (installEvent :: enterEvent :: callHarnessEvent :: bodyExitTrace)
      (.returned harness installedState.store returnedValue returnedState) :=
    .cons installStep (.cons enterStep (.cons callStep bodyExitFromPublic))
  let fullTrace : List Wasm.Event :=
    installEvent :: enterEvent :: callHarnessEvent :: bodyExitTrace
  let observation : Wasm.ExecutionObservation :=
    .returned fullTrace entry returnedValue entry Wasm.ObservableEffects.none
  have finalObserved :
      Wasm.Core.Harness.observeStore harness returnedState.store = some entry := by
    simpa [returnedState, outerFrame] using entryObserved
  have observes : Wasm.Core.Harness.Observes fullTrace
      (.returned harness installedState.store returnedValue returnedState)
      observation := by
    exact .returned entryObserved finalObserved
  refine ⟨fullTrace, observation, rfl,
    Wasm.Core.Harness.FiniteExecution.mk completeSteps observes, ?_⟩
  simp only [Accepts, observation]
  refine ⟨entryMatches, ?_, ?_, True.intro⟩
  · rw [evaluatedStatus_eq_returnedStatus]
    simp [returnedI32?, returnedValue, coreU32,
      Nat.mod_eq_of_lt checked.returnedStatus_lt_two_pow_32]
  · exact MemoryMatches.congrMachine
      (evaluatedMemory_eq_initial checked raw).symm entryMatches

end DirectScalarRuntime

end WasmGemmGnaf.GNAF
