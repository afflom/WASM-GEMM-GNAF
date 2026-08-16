import WasmGemmGnaf.Wasm.Core.EventExecution
import WasmGemmGnaf.Wasm.Core.RuntimeSourceValues

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Progress for the context-free parametric Core instructions

This is the first ordinary instruction family of the runtime progress proof.
The syntactic classifier below contains only instructions whose redex does not
consult the store or module frame.  Its progress theorem consumes the real
amended `Instr_okA` derivation and runtime `Val_okA` operands.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- The context-free parametric instructions handled in this first family. -/
inductive SimplePureInstr : Instr → Prop where
  | nop : SimplePureInstr .nop
  | unreachable : SimplePureInstr .unreachable
  | drop : SimplePureInstr .drop
  | select (types : Option (List ValType)) : SimplePureInstr (.select types)

/-- An exact Core step remains available when a nonempty runtime-value prefix
surrounds its redex through the ordinary `ctxt-instrs` evaluation context. -/
theorem StepA.exists_of_prepend_values {state : State}
    {source target : List AdminInstr} {event : Event}
    (step : StepA (state, source) event (state, target))
    (values : List Val) :
    ∃ liftedEvent liftedTarget,
      StepA (state, vals values ++ source) liftedEvent liftedTarget := by
  cases values with
  | nil =>
      exact ⟨event, (state, target), by simpa using step⟩
  | cons value values =>
      refine ⟨.ctxtInstrs (value :: values).length 0 event,
        (state, vals (value :: values) ++ target), ?_⟩
      simpa using (@StepA.ctxtInstrs state state (value :: values) source
        target [] event step (Or.inl (by simp)))

/-- Every well-typed runtime instance of a context-free parametric instruction
is an actual amended-Core redex. -/
theorem Instr_okA.simplePure_progress
    {context : Context} {state : State} {instruction : Instr}
    {instructionType : InstrType} {values : List Val}
    (simple : SimplePureInstr instruction)
    (typed : Instr_okA context instruction instructionType)
    (valuesTyped : ValuesOkA state.store values instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain instruction]) event target := by
  cases simple with
  | nop =>
      cases typed with
      | nop =>
          have hvalues : values = [] :=
            ValuesOkA.nil_types_iff.mp valuesTyped
          subst values
          have pure : Step_pure releasedNumerics [.plain .nop] [] := .nop
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent (sourcePlains [.plain .nop]),
            (state, []), .pure member⟩
  | unreachable =>
      cases typed with
      | unreachable =>
          have pure : Step_pure releasedNumerics [.plain .unreachable]
              [.trap] := .unreachable
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact (StepA.pure member).exists_of_prepend_values values
  | drop =>
      cases typed with
      | drop _ =>
          obtain ⟨value, hvalues, _⟩ :=
            ValuesOkA.singleton_iff.mp valuesTyped
          subst values
          have pure : Step_pure releasedNumerics
              [value.toAdmin, .plain .drop] [] := .drop
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent
              (sourcePlains [value.toAdmin, .plain .drop]),
            (state, []), by simpa [vals] using StepA.pure member⟩
  | select types =>
      cases typed with
      | @select_expl _ selectedType _ =>
          obtain ⟨first, second, condition, hvalues, _, _, conditionTyped⟩ :=
            ValuesOkA.triple_iff.mp valuesTyped
          obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
          subst condition
          subst values
          by_cases hzero : literal.val = 0
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin,
                  (.num ⟨.i32, literal⟩ : Val).toAdmin,
                  .plain (.select (some [selectedType]))] [second.toAdmin] :=
              .selectFalse hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [second.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin,
                  (.num ⟨.i32, literal⟩ : Val).toAdmin,
                  .plain (.select (some [selectedType]))] [first.toAdmin] :=
              .selectTrue hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [first.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
      | select_impl _ _ _ =>
          obtain ⟨first, second, condition, hvalues, _, _, conditionTyped⟩ :=
            ValuesOkA.triple_iff.mp valuesTyped
          obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
          subst condition
          subst values
          by_cases hzero : literal.val = 0
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin,
                  (.num ⟨.i32, literal⟩ : Val).toAdmin,
                  .plain (.select none)] [second.toAdmin] :=
              .selectFalse hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [second.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin,
                  (.num ⟨.i32, literal⟩ : Val).toAdmin,
                  .plain (.select none)] [first.toAdmin] :=
              .selectTrue hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [first.toAdmin]),
              by simpa [vals] using StepA.pure member⟩

/-- Numeric instructions whose typed operands form an immediate pure redex.
Numeric constants are deliberately absent: a constant is already a runtime
value and belongs to the value/terminal arm of the later sequence theorem. -/
inductive NumericRedexInstr : Instr → Prop where
  | unop (numberType : NumType) (operator : Unop) :
      NumericRedexInstr (.unop numberType operator)
  | binop (numberType : NumType) (operator : Binop) :
      NumericRedexInstr (.binop numberType operator)
  | cvtop (targetType sourceType : NumType) (operator : Cvtop) :
      NumericRedexInstr (.cvtop targetType sourceType operator)

/-- Every well-typed numeric redex has either a numeric-result or trap rule,
exactly according to the released numeric provider's finite result list. -/
theorem Instr_okA.numericRedex_progress
    {context : Context} {state : State} {instruction : Instr}
    {instructionType : InstrType} {values : List Val}
    (numeric : NumericRedexInstr instruction)
    (typed : Instr_okA context instruction instructionType)
    (valuesTyped : ValuesOkA state.store values instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain instruction]) event target := by
  cases numeric with
  | unop numberType operator =>
      cases typed with
      | unop _ =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            ValuesOkA.singleton_iff.mp valuesTyped
          obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
          subst value
          subst values
          cases hresult : releasedNumerics.unop_ numberType operator literal with
          | nil =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const numberType literal),
                    .plain (.unop numberType operator)] [.trap] :=
                .unopTrap hresult
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [.trap]),
                by simpa [vals] using StepA.pure member⟩
          | cons result results =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const numberType literal),
                    .plain (.unop numberType operator)]
                  [.plain (.const numberType result)] :=
                .unopVal (by simp [hresult])
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _,
                (state, [.plain (.const numberType result)]),
                by simpa [vals] using StepA.pure member⟩
  | binop numberType operator =>
      cases typed with
      | binop _ =>
          obtain ⟨first, second, hvalues, firstTyped, secondTyped⟩ :=
            ValuesOkA.pair_iff.mp valuesTyped
          obtain ⟨firstLiteral, hfirst⟩ := firstTyped.num_canonical
          obtain ⟨secondLiteral, hsecond⟩ := secondTyped.num_canonical
          subst first
          subst second
          subst values
          cases hresult : releasedNumerics.binop_ numberType operator
              firstLiteral secondLiteral with
          | nil =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const numberType firstLiteral),
                    .plain (.const numberType secondLiteral),
                    .plain (.binop numberType operator)] [.trap] :=
                .binopTrap hresult
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [.trap]),
                by simpa [vals] using StepA.pure member⟩
          | cons result results =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const numberType firstLiteral),
                    .plain (.const numberType secondLiteral),
                    .plain (.binop numberType operator)]
                  [.plain (.const numberType result)] :=
                .binopVal (by simp [hresult])
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _,
                (state, [.plain (.const numberType result)]),
                by simpa [vals] using StepA.pure member⟩
  | cvtop targetType sourceType operator =>
      cases typed with
      | cvtop _ =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            ValuesOkA.singleton_iff.mp valuesTyped
          obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
          subst value
          subst values
          cases hresult : releasedNumerics.cvtop__ sourceType targetType
              operator literal with
          | nil =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const sourceType literal),
                    .plain (.cvtop targetType sourceType operator)] [.trap] :=
                .cvtopTrap hresult
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [.trap]),
                by simpa [vals] using StepA.pure member⟩
          | cons result results =>
              have pure : Step_pure releasedNumerics
                  [.plain (.const sourceType literal),
                    .plain (.cvtop targetType sourceType operator)]
                  [.plain (.const targetType result)] :=
                .cvtopVal (by simp [hresult])
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _,
                (state, [.plain (.const targetType result)]),
                by simpa [vals] using StepA.pure member⟩

/-- Source-indexed runtime typing supplies the same numeric canonical operands;
static source subtyping cannot change a numeric type. -/
theorem Instr_okA.numericRedex_source_progress
    {context : Context} {state : State} {instruction : Instr}
    {instructionType : InstrType} {values : List Val}
    (numeric : NumericRedexInstr instruction)
    (typed : Instr_okA context instruction instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain instruction]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases numeric with
  | unop numberType operator =>
      cases typed with
      | unop operatorValid =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp valuesTyped
          obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
          subst value
          subst values
          apply Instr_okA.numericRedex_progress
            (context := context) (numeric := .unop numberType operator)
            (typed := Instr_okA.unop (C := context) operatorValid)
          exact .cons (.num .mk) .nil
  | binop numberType operator =>
      cases typed with
      | binop operatorValid =>
          obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
            valuesTyped.split (leftTypes := [.num numberType])
              (rightTypes := [.num numberType])
          obtain ⟨leftValue, hleftValues, leftValueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp leftTyped
          obtain ⟨rightValue, hrightValues, rightValueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp rightTyped
          obtain ⟨leftLiteral, hleftValue⟩ :=
            leftValueTyped.num_canonical
          obtain ⟨rightLiteral, hrightValue⟩ :=
            rightValueTyped.num_canonical
          subst leftValue
          subst rightValue
          subst leftValues
          subst rightValues
          subst values
          apply Instr_okA.numericRedex_progress
            (context := context) (numeric := .binop numberType operator)
            (typed := Instr_okA.binop (C := context) operatorValid)
          exact .cons (.num .mk) (.cons (.num .mk) .nil)
  | cvtop targetType sourceType operator =>
      cases typed with
      | cvtop operatorValid =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp valuesTyped
          obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
          subst value
          subst values
          apply Instr_okA.numericRedex_progress
            (context := context)
            (numeric := .cvtop targetType sourceType operator)
            (typed := Instr_okA.cvtop (C := context) operatorValid)
          exact .cons (.num .mk) .nil

end WasmGemmGnaf.Wasm.Core.Exec
