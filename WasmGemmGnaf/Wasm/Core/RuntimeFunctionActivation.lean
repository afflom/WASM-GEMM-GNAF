import WasmGemmGnaf.Wasm.Core.EventExecution
import WasmGemmGnaf.Wasm.Core.RuntimeLocalsTyping

set_option autoImplicit false

/-!
# Typed activation of a defined Core function

The relation below is the first administrative layer of the runtime typing
invariant.  It records the ordinary amended source typing of a function body
and the pointwise typing of the concrete local vector installed by
`Step_read/call_ref-func`.  It deliberately records no transition,
nonemptiness, progress, or termination conclusion.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Static/runtime typing evidence carried by a freshly-created defined
function frame.  The body is still the exact source expression, embedded under
the result label prescribed by the Core reduction rule. -/
inductive FunctionActivationOkA (store : Store) (frame : Frame) :
    Nat → List AdminInstr → Prop where
  | mk {context : Context} {function : Func} {domain codomain : ValTypes}
      {localTypes : List LocalType} :
      LocalsOkA store frame.locals
        (domain.toList.map (fun type => ⟨Init.set, type⟩) ++ localTypes) →
      Expr_okA (Context.append context
        { locals := domain.toList.map (fun type => ⟨Init.set, type⟩) ++
            localTypes,
          labels := [codomain.toList],
          ret := some codomain.toList }) function.body codomain.toList →
      FunctionActivationOkA store frame codomain.length
        [.label codomain.length [] (plains function.body.toList)]

/-- A successful `call_ref` of a defined, source-typed function takes the
exact Core step to a runtime activation carrying the genuine local/body typing
invariant.  Allocation provenance is intentionally an explicit premise here;
the downstream instantiation bridge supplies `functionInstance.code` and the
source-body premises from the validated module. -/
theorem callRefFunc_step_to_typed_activation
    {state : State} {arguments : List Val} {address : FuncAddr}
    {typeUse : TypeUse} {functionInstance : FuncInst} {function : Func}
    {context : Context} {domain codomain : ValTypes}
    {localTypes : List LocalType}
    (hlookup : state.funcinst[address]? = some functionInstance)
    (hexpand : Expand functionInstance.type (.func domain codomain))
    (hcode : functionInstance.code = .func function)
    (harguments : ValuesOkA state.store arguments domain.toList)
    (hlocalsLength : SeqLen₂ function.locals localTypes)
    (hlocals : SeqAll₂ (Local_okA context) function.locals localTypes)
    (hbody : Expr_okA (Context.append context
      { locals := domain.toList.map (fun type => ⟨Init.set, type⟩) ++
          localTypes,
        labels := [codomain.toList],
        ret := some codomain.toList }) function.body codomain.toList) :
    ∃ frame,
      StepA
        (state, vals arguments ++
          [.addrref (.funcAddr address), .plain (.callRef typeUse)])
        (.read .callRefFunc
          (sourcePlains (vals arguments ++
            [.addrref (.funcAddr address), .plain (.callRef typeUse)])))
        (state, [.frame codomain.length frame
          [.label codomain.length [] (plains function.body.toList)]]) ∧
      FunctionActivationOkA state.store frame codomain.length
        [.label codomain.length [] (plains function.body.toList)] := by
  let frame : Frame :=
    { locals := arguments.map some ++
        function.locals.map (fun localDecl => default_ localDecl.valtype)
      mod := functionInstance.mod }
  have hargumentsLength : arguments.length = domain.length := by
    simpa [SeqLen₂] using (ValuesOkA.iff_seq.mp harguments).1
  have hread : Step_readA state .callRefFunc
      (vals arguments ++
        [.addrref (.funcAddr address), .plain (.callRef typeUse)])
      [.frame codomain.length frame
        [.label codomain.length [] (plains function.body.toList)]] := by
    letI : ExecutionAuthority := amendedExecutionAuthority
    apply Step_read.callRefFunc hlookup hexpand rfl rfl hargumentsLength hcode
    rfl
  refine ⟨frame, StepA.read hread, ?_⟩
  exact .mk (function_frame_locals_typed harguments hlocalsLength hlocals) hbody

/-- A typed activation whose source body is empty takes the ordinary
`label-vals` contextual step.  The source typing judgment forces the result
arity to be zero; no progress fact is stored in `FunctionActivationOkA`. -/
theorem FunctionActivationOkA.step_of_body_empty
    {outer : State} {frame : Frame} {resultArity : Nat}
    {body : List AdminInstr}
    (htyped : FunctionActivationOkA outer.store frame resultArity body)
    (hbody : body = [.label resultArity [] []]) :
    ∃ event next, StepA (outer, [.frame resultArity frame body]) event next := by
  cases htyped with
  | @mk context function domain codomain localTypes hlocals hsourceTyping =>
      have hplain : plains function.body.toList = [] := by
        simpa using hbody
      have hsourceEmpty : function.body.toList = [] := by
        simpa [plains] using hplain
      cases hsourceTyping with
      | mk hinstructions =>
          have hlength := Instrs_okA.nil_length hinstructions hsourceEmpty
          have hcodomain : codomain.length = 0 := by
            simpa using hlength.symm
          have hpure : Step_pure releasedNumerics [.label 0 [] []] [] :=
            Step_pure.labelVals (Nm := releasedNumerics)
              (n := 0) (cont := []) (vs := [])
          obtain ⟨pureEvent, hpureMem⟩ := step_pure_mem_pureSuccessors hpure
          have hinner : StepA (⟨outer.store, frame⟩, [.label 0 [] []])
              (.pure pureEvent (sourcePlains [.label 0 [] []]))
              (⟨outer.store, frame⟩, []) :=
            .pure hpureMem
          let event : Event :=
            .ctxtFrame 0 (.pure pureEvent (sourcePlains [.label 0 [] []]))
          let next : Config := (outer, [.frame 0 frame []])
          refine ⟨event, next, ?_⟩
          have houter : StepA
              (outer, [.frame 0 frame [.label 0 [] []]]) event next :=
            .ctxtFrame hinner
          simpa [hcodomain, hplain] using houter

end WasmGemmGnaf.Wasm.Core.Exec
