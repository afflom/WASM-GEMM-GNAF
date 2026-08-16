import WasmGemmGnaf.Wasm.Core.RuntimeInstrProgress

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Source control/reference progress leaves

These lemmas cover source instructions whose redex is obtained from the
active module-instance address vectors.  The lookup premises are deliberately
explicit: the active runtime typing/alignment invariant must derive them from
validated allocation and store preservation.  None of the premises or
definitions below contains a transition or progress conclusion.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Runtime representations that can inhabit the external-reference family.
The property states only the canonical shape used by the two pure reduction
rules; it contains no transition. -/
inductive ExternReferenceShape : Ref → Prop where
  | null {heapType : HeapType} :
      ExternReferenceShape (.null heapType)
  | addr {reference : AddrRef} :
      ExternReferenceShape (.addr (.extern reference))

/-- The two genuine runtime shapes of a `call_ref` operand.  A function
address additionally carries only the store lookup, function expansion,
defined-code equation, and argument-count equality consumed by the authority
rule. -/
inductive CallRefReadyA (state : State) : List Val → Ref → Prop where
  | null {arguments : List Val} {heapType : HeapType} :
      CallRefReadyA state arguments (.null heapType)
  | func {arguments : List Val} {address : FuncAddr} {function : FuncInst}
      {sourceFunction : Func} {domain codomain : ValTypes} :
      state.store.funcs[address]? = some function →
      Expand function.type (.func domain codomain) →
      function.code = .func sourceFunction →
      domain.length = arguments.length →
      CallRefReadyA state arguments (.addr (.funcAddr address))

/-- Runtime tag alignment sufficient to execute a source `throw`.  This is a
lookup/expansion certificate, not an execution result. -/
inductive ThrowReadyA (state : State) (index : TagIdx) :
    List Val → Prop where
  | mk {fields : List Val} {tagInstance : TagInst} {definedType : DefType}
      {domain : ValTypes} {tagAddress : TagAddr} :
      state.tagOf index = some tagInstance →
      asDefType tagInstance.type = some definedType →
      Expand definedType (.func domain .nil) →
      domain.length = fields.length →
      state.frame.mod.tags[index.val]? = some tagAddress →
      ThrowReadyA state index fields

/-- A source `call` whose function index resolves in both the active module
instance and store takes the authority's exact call-expansion read step. -/
theorem Instr_okA.call_source_progress
    {context : Context} {state : State} {index : FuncIdx}
    {instructionType : InstrType} {values : List Val}
    {address : FuncAddr} {function : FuncInst}
    (typed : Instr_okA context (.call index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (haddress : state.frame.mod.funcs[index.val]? = some address)
    (hfunction : state.store.funcs[address]? = some function) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.call index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  have hread : Step_readA state .call [.plain (.call index)]
      [.addrref (.funcAddr address),
        .plain (.callRef (.defd function.type))] :=
    .call haddress hfunction
  have inner : StepA (state, [.plain (.call index)])
      (.read .call (sourcePlains [.plain (.call index)]))
      (state,
        [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))]) :=
    .read hread
  simpa [List.append_assoc] using inner.exists_of_prepend_values values

/-- A source tail call first resolves to the exact runtime function address
and closed type.  Its later frame escape remains an administrative step. -/
theorem Instr_okA.returnCall_source_progress
    {context : Context} {state : State} {index : FuncIdx}
    {instructionType : InstrType} {values : List Val}
    {address : FuncAddr} {function : FuncInst}
    (typed : Instr_okA context (.returnCall index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (haddress : state.frame.mod.funcs[index.val]? = some address)
    (hfunction : state.store.funcs[address]? = some function) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.returnCall index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  have hread : Step_readA state .returnCall [.plain (.returnCall index)]
      [.addrref (.funcAddr address),
        .plain (.returnCallRef (.defd function.type))] :=
    .returnCall haddress hfunction
  have inner : StepA (state, [.plain (.returnCall index)])
      (.read .returnCall (sourcePlains [.plain (.returnCall index)]))
      (state,
        [.addrref (.funcAddr address),
          .plain (.returnCallRef (.defd function.type))]) :=
    .read hread
  simpa [List.append_assoc] using inner.exists_of_prepend_values values

/-- A source `call_ref` either traps on null or activates the looked-up
defined function.  The readiness witness contains precisely the runtime
facts appearing in those two authority rules. -/
theorem Instr_okA.callRef_source_progress
    {context : Context} {state : State} {typeUse : TypeUse}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.callRef typeUse) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (ready : ∃ arguments reference,
      values = arguments ++ [.ref reference] ∧
      CallRefReadyA state arguments reference) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.callRef typeUse)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  obtain ⟨arguments, reference, hvalues, readiness⟩ := ready
  subst values
  cases readiness with
  | @null heapType =>
      have hread : Step_readA state .callRefNull
          [Ref.toAdmin (.null heapType), .plain (.callRef typeUse)]
          [.trap] := .callRefNull
      have inner : StepA
          (state,
            [Ref.toAdmin (.null heapType), .plain (.callRef typeUse)])
          (.read .callRefNull _)
          (state, [.trap]) := .read hread
      simpa [vals, List.append_assoc] using
        inner.exists_of_prepend_values arguments
  | @func address function sourceFunction domain codomain
      hlookup hexpand hcode hlength =>
      let frame : Frame :=
        { locals := arguments.map some ++
            sourceFunction.locals.map
              (fun localDecl => default_ localDecl.valtype)
          mod := function.mod }
      have hread : Step_readA state .callRefFunc
          (vals arguments ++
            [.addrref (.funcAddr address), .plain (.callRef typeUse)])
          [.frame codomain.length frame
            [.label codomain.length []
              (plains sourceFunction.body.toList)]] := by
        apply Step_read.callRefFunc hlookup hexpand hlength rfl rfl hcode
        rfl
      exact ⟨.read .callRefFunc _,
        (state,
          [.frame codomain.length frame
            [.label codomain.length []
              (plains sourceFunction.body.toList)]]),
        by simpa [vals, List.append_assoc] using StepA.read hread⟩

/-- A typed source `throw` allocates the genuine exception instance from the
tag-aligned operand suffix.  Any stack-polymorphic prefix is retained by the
ordinary instruction context and is removed by subsequent throw propagation. -/
theorem Instr_okA.throw_source_progress
    {context : Context} {state : State} {index : TagIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.throw index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (ready : ∃ leadingValues fields,
      values = leadingValues ++ fields ∧ ThrowReadyA state index fields) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.throw index)]) event target := by
  obtain ⟨leadingValues, fields, hvalues, readiness⟩ := ready
  subst values
  cases readiness with
  | @mk tagInstance definedType domain tagAddress htag hasType hexpand
      hlength haddress =>
      let address : ExnAddr := state.store.exns.length
      let exception : ExnInst :=
        { tag := tagAddress, fields := fields }
      have inner : StepA
          (state, vals fields ++ [.plain (.throw index)])
          (.throw index fields.length)
          (state.addExnInst [exception],
            [.addrref (.exnAddr address), .plain .throwRef]) := by
        apply StepA.throw htag hasType hexpand hlength rfl
        · rfl
        · exact haddress
        · rfl
      cases leadingValues with
      | nil =>
          exact ⟨.throw index fields.length,
            (state.addExnInst [exception],
              [.addrref (.exnAddr address), .plain .throwRef]),
            by simpa [vals] using inner⟩
      | cons value values =>
          let event : Event :=
            .ctxtInstrs (value :: values).length 0 (.throw index fields.length)
          exact ⟨event,
            (state.addExnInst [exception],
              vals (value :: values) ++
                [.addrref (.exnAddr address), .plain .throwRef]),
            by
              simpa [event, vals, List.append_assoc] using
                (@StepA.ctxtInstrs state (state.addExnInst [exception])
                  (value :: values)
                  (vals fields ++ [.plain (.throw index)])
                  [.addrref (.exnAddr address), .plain .throwRef]
                  [] (.throw index fields.length) inner
                  (Or.inl (by simp)))⟩

/-- A validated `ref.func` resolves through the active module-instance
function vector and takes the exact read rule. -/
theorem Instr_okA.refFunc_source_progress
    {context : Context} {state : State} {index : FuncIdx}
    {instructionType : InstrType} {values : List Val}
    {address : FuncAddr}
    (typed : Instr_okA context (.refFunc index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (haddress : state.frame.mod.funcs[index.val]? = some address) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.refFunc index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | ref_func =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have hread : Step_readA state .refFunc [.plain (.refFunc index)]
          [.addrref (.funcAddr address)] := .refFunc haddress
      exact ⟨.read .refFunc _, (state, [.addrref (.funcAddr address)]),
        .read hread⟩

/-- `any.convert_extern` is total on both runtime representations admitted by
source reference typing. -/
theorem Instr_okA.anyConvertExtern_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .anyConvertExtern instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (shape : ∃ reference, values = [.ref reference] ∧
      ExternReferenceShape reference) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .anyConvertExtern]) event target := by
  cases typed with
  | any_convert_extern =>
      obtain ⟨reference, hvalues, referenceShape⟩ := shape
      subst values
      cases referenceShape with
      | @null heapType =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null heapType), .plain .anyConvertExtern]
              [Ref.toAdmin (.null (.abs .any))] := .anyConvertExternNull
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [Ref.toAdmin (.null (.abs .any))]),
            by simpa [vals] using StepA.pure member⟩
      | @addr address =>
          have pure : Step_pure releasedNumerics
              [.addrref (.extern address), .plain .anyConvertExtern]
              [.addrref address] := .anyConvertExternAddr
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.addrref address]),
            by simpa [vals] using StepA.pure member⟩

end WasmGemmGnaf.Wasm.Core.Exec
