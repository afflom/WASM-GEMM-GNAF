import WasmGemmGnaf.Wasm.Core.RuntimePureProgress
import WasmGemmGnaf.Wasm.Core.RuntimeTypeClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Progress for ordinary source instructions

This file extends the first context-free runtime families with the remaining
scalar predicates.  The hypotheses are the actual amended source typing and
source-indexed runtime value typing judgments.  No transition or progress
claim is stored in a runtime configuration.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- A source-typed reference value is represented by an actual runtime
reference.  Source subtyping may narrow the reference type but cannot change
the value family. -/
theorem SourceValOkA.ref_canonical {store : Store} {context : Context}
    {value : Val} {referenceType : RefType}
    (typed : SourceValOkA store context value (.ref referenceType)) :
    ∃ reference : Ref, value = .ref reference := by
  obtain ⟨actualType, runtimeTyped, subtype⟩ := typed
  cases subtype with
  | ref referenceSubtype =>
      obtain ⟨reference, hvalue, _⟩ :=
        (by
          simpa [Context.closValType, substAllValType, substValType] using
            runtimeTyped.ref_canonical)
      exact ⟨reference, hvalue⟩
  | bot =>
      exact False.elim (Val_okA.not_bot (by
        simpa [Context.closValType, substAllValType, substValType] using
          runtimeTyped))

/-- A source-typed vector value is the corresponding canonical runtime vector
literal; vector subtyping cannot change its vector family. -/
theorem SourceValOkA.vec_canonical {store : Store} {context : Context}
    {value : Val} {vectorType : VecType}
    (typed : SourceValOkA store context value (.vec vectorType)) :
    ∃ literal : VecLit vectorType.toVnn,
      value = .vec ⟨vectorType, literal⟩ := by
  obtain ⟨actualType, runtimeTyped, subtype⟩ := typed
  cases subtype with
  | vec vectorSubtype =>
      cases vectorSubtype
      simpa [Context.closValType, substAllValType, substValType] using
        runtimeTyped.vec_canonical
  | bot =>
      exact False.elim (Val_okA.not_bot (by
        simpa [Context.closValType, substAllValType, substValType] using
          runtimeTyped))

/-- The parametric context-free family remains a redex under source-indexed
runtime typing, including reference-typed `drop` and `select` operands. -/
theorem Instr_okA.simplePure_source_progress
    {context : Context} {state : State} {instruction : Instr}
    {instructionType : InstrType} {values : List Val}
    (simple : SimplePureInstr instruction)
    (typed : Instr_okA context instruction instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain instruction]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases simple with
  | nop =>
      cases typed with
      | nop =>
          have hvalues : values = [] := valuesTyped.nil_values
          subst values
          have pure : Step_pure releasedNumerics [.plain .nop] [] := .nop
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, []), .pure member⟩
  | unreachable =>
      cases typed with
      | unreachable =>
          have pure : Step_pure releasedNumerics [.plain .unreachable]
              [.trap] := .unreachable
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          have inner : StepA (state, [.plain .unreachable])
              (.pure pureEvent _) (state, [.trap]) := .pure member
          simpa [vals, List.append_assoc] using
            inner.exists_of_prepend_values values
  | drop =>
      cases typed with
      | drop typeValid =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp valuesTyped
          subst values
          have pure : Step_pure releasedNumerics
              [value.toAdmin, .plain .drop] [] := .drop
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, []),
            by simpa [vals] using StepA.pure member⟩
  | select types =>
      cases typed with
      | @select_expl _ selectedType selectedValid =>
          obtain ⟨selected, conditions, hvalues, selectedTyped,
              conditionTyped⟩ :=
            valuesTyped.split
              (leftTypes := [selectedType, selectedType])
              (rightTypes := [ValType.i32])
          obtain ⟨firstValues, secondValues, hselected, firstTyped,
              secondTyped⟩ :=
            selectedTyped.split (leftTypes := [selectedType])
              (rightTypes := [selectedType])
          obtain ⟨first, hfirst, firstTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp firstTyped
          obtain ⟨second, hsecond, secondTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp secondTyped
          obtain ⟨condition, hconditions, conditionTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp conditionTyped
          obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
          subst condition
          subst firstValues
          subst secondValues
          subst selected
          subst conditions
          subst values
          by_cases hzero : literal.val = 0
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin, constI32 literal,
                  .plain (.select (some [selectedType]))]
                [second.toAdmin] := .selectFalse hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [second.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin, constI32 literal,
                  .plain (.select (some [selectedType]))]
                [first.toAdmin] := .selectTrue hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [first.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
      | @select_impl _ selectedType targetType selectedValid selectedSubtype
          targetShape =>
          obtain ⟨selected, conditions, hvalues, selectedTyped,
              conditionTyped⟩ :=
            valuesTyped.split
              (leftTypes := [selectedType, selectedType])
              (rightTypes := [ValType.i32])
          obtain ⟨firstValues, secondValues, hselected, firstTyped,
              secondTyped⟩ :=
            selectedTyped.split (leftTypes := [selectedType])
              (rightTypes := [selectedType])
          obtain ⟨first, hfirst, firstTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp firstTyped
          obtain ⟨second, hsecond, secondTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp secondTyped
          obtain ⟨condition, hconditions, conditionTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp conditionTyped
          obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
          subst condition
          subst firstValues
          subst secondValues
          subst selected
          subst conditions
          subst values
          by_cases hzero : literal.val = 0
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin, constI32 literal,
                  .plain (.select none)] [second.toAdmin] :=
              .selectFalse hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [second.toAdmin]),
              by simpa [vals] using StepA.pure member⟩
          · have pure : Step_pure releasedNumerics
                [first.toAdmin, second.toAdmin, constI32 literal,
                  .plain (.select none)] [first.toAdmin] :=
              .selectTrue hzero
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            exact ⟨.pure pureEvent _, (state, [first.toAdmin]),
              by simpa [vals] using StepA.pure member⟩

/-- Scalar predicates whose result is the canonical `i32` Boolean value. -/
inductive ScalarPredicateInstr : Instr → Prop where
  | testop (numberType : NumType) (operator : Testop) :
      ScalarPredicateInstr (.testop numberType operator)
  | relop (numberType : NumType) (operator : Relop) :
      ScalarPredicateInstr (.relop numberType operator)

/-- A well-typed scalar predicate applied to source-typed runtime operands is
an immediate amended-Core pure redex. -/
theorem Instr_okA.scalarPredicate_source_progress
    {context : Context} {state : State} {instruction : Instr}
    {instructionType : InstrType} {values : List Val}
    (predicate : ScalarPredicateInstr instruction)
    (typed : Instr_okA context instruction instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain instruction]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases predicate with
  | testop numberType operator =>
      cases typed with
      | testop operatorValid =>
          obtain ⟨value, hvalues, valueTyped⟩ :=
            SourceValuesOkA.singleton_iff.mp valuesTyped
          obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
          subst value
          subst values
          have hresult : ∃ result,
              Numerics.testop_ numberType operator literal = some result := by
            cases numberType <;> cases operator <;>
              simp_all [Testop.wf, NumType.toInn?, Numerics.testop_]
          obtain ⟨result, hresult⟩ := hresult
          have pure : Step_pure releasedNumerics
              [.plain (.const numberType literal),
                .plain (.testop numberType operator)]
              [constI32 result] := .testop hresult
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [constI32 result]),
            by simpa [vals] using StepA.pure member⟩
  | relop numberType operator =>
      cases typed with
      | relop operatorValid =>
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
          have hresult : ∃ result,
              releasedNumerics.relop_ numberType operator
                leftLiteral rightLiteral = some result := by
            cases numberType <;> cases operator <;>
              simp_all [Relop.wf, NumType.toInn?, NumType.toFnn?,
                Numerics.relop_]
          obtain ⟨result, hresult⟩ := hresult
          have pure : Step_pure releasedNumerics
              [.plain (.const numberType leftLiteral),
                .plain (.const numberType rightLiteral),
                .plain (.relop numberType operator)]
              [constI32 result] := .relop hresult
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [constI32 result]),
            by simpa [vals] using StepA.pure member⟩

/-- Whole-vector unary bit operations are single-result pure reductions. -/
theorem Instr_okA.vvunop_source_progress
    {context : Context} {state : State} {operator : VVUnop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vvunop .v128 operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vvunop .v128 operator)])
        event target := by
  cases typed with
  | vvunop =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      let result : V128Lit := releasedNumerics.inot_ 128 literal
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 literal),
            .plain (.vvunop .v128 operator)]
          [.plain (.vconst .v128 result)] := .vvunop (by
            cases operator
            simp [Numerics.vvunop_, result])
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Whole-vector binary bit operations are single-result pure reductions. -/
theorem Instr_okA.vvbinop_source_progress
    {context : Context} {state : State} {operator : VVBinop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vvbinop .v128 operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vvbinop .v128 operator)])
        event target := by
  cases typed with
  | vvbinop =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      let result : V128Lit := match operator with
        | .and => releasedNumerics.iand_ 128 leftLiteral rightLiteral
        | .andnot => releasedNumerics.iandnot_ 128 leftLiteral rightLiteral
        | .or => releasedNumerics.ior_ 128 leftLiteral rightLiteral
        | .xor => releasedNumerics.ixor_ 128 leftLiteral rightLiteral
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 leftLiteral),
            .plain (.vconst .v128 rightLiteral),
            .plain (.vvbinop .v128 operator)]
          [.plain (.vconst .v128 result)] := .vvbinop (by
            cases operator <;> simp [Numerics.vvbinop_, result])
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Whole-vector ternary bit selection is a single-result pure reduction. -/
theorem Instr_okA.vvternop_source_progress
    {context : Context} {state : State} {operator : VVTernop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vvternop .v128 operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vvternop .v128 operator)])
        event target := by
  cases typed with
  | vvternop =>
      obtain ⟨firstValues, tailValues, hvalues, firstTyped, tailTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128, .vec .v128])
      obtain ⟨secondValues, thirdValues, htail, secondTyped, thirdTyped⟩ :=
        tailTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨first, hfirstValues, firstTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp firstTyped
      obtain ⟨second, hsecondValues, secondTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp secondTyped
      obtain ⟨third, hthirdValues, thirdTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp thirdTyped
      obtain ⟨firstLiteral, hfirst⟩ := firstTyped.vec_canonical
      obtain ⟨secondLiteral, hsecond⟩ := secondTyped.vec_canonical
      obtain ⟨thirdLiteral, hthird⟩ := thirdTyped.vec_canonical
      subst first
      subst second
      subst third
      subst firstValues
      subst secondValues
      subst thirdValues
      subst tailValues
      subst values
      let result : V128Lit := releasedNumerics.ibitselect_ 128
        firstLiteral secondLiteral thirdLiteral
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 firstLiteral),
            .plain (.vconst .v128 secondLiteral),
            .plain (.vconst .v128 thirdLiteral),
            .plain (.vvternop .v128 operator)]
          [.plain (.vconst .v128 result)] := .vvternop (by
            cases operator
            simp [Numerics.vvternop_, result])
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Whole-vector `any_true` always computes its canonical `i32` result. -/
theorem Instr_okA.vvtestop_source_progress
    {context : Context} {state : State} {operator : VVTestop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vvtestop .v128 operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vvtestop .v128 operator)])
        event target := by
  cases typed with
  | vvtestop =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      cases operator
      let zero : IN 128 := ⟨0, by decide⟩
      let result : U32 := Numerics.ine_ 128 literal zero
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 literal),
            .plain (.vvtestop .v128 .anyTrue)]
          [constI32 result] := .vvtestop rfl rfl
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _, (state, [constI32 result]),
        by simpa [vals] using StepA.pure member⟩

/-- Lane splatting is a total pure reduction for every well-typed shape. -/
theorem Instr_okA.vsplat_source_progress
    {context : Context} {state : State} {shape : Shape}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vsplat shape) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vsplat shape)]) event target := by
  cases typed with
  | vsplat =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
      subst value
      subst values
      let result : V128Lit := releasedNumerics.inv_lanes_ shape
        (List.replicate shape.dim.toNat
          (releasedNumerics.lpacknum_ shape.lane literal))
      have pure : Step_pure releasedNumerics
          [.plain (.const shape.lane.unpack literal),
            .plain (.vsplat shape)]
          [.plain (.vconst .v128 result)] := .vsplat rfl
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- The released concrete lane projection returns exactly the shape's stated
number of lanes. -/
@[simp] theorem releasedNumerics_lanes_length (shape : Shape)
    (literal : V128Lit) :
    (releasedNumerics.lanes_ shape literal).length = shape.dim.toNat := by
  simp [releasedNumerics, ConcreteNumerics.released,
    ConcreteNumerics.lanes]

/-- A validated lane extraction has an in-range lane in the released concrete
vector representation.  Its signedness side condition selects exactly the
numeric-lane or packed-lane reduction rule. -/
theorem Instr_okA.vextractLane_source_progress
    {context : Context} {state : State} {shape : Shape}
    {signedness : Option Sx} {index : LaneIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vextractLane shape signedness index)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state,
        vals values ++ [.plain (.vextractLane shape signedness index)])
        event target := by
  cases typed with
  | vextract_lane shapeWf signednessShape indexBound =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      cases shape with
      | mk lane dimension =>
          cases lane with
          | num numberType =>
              have hsignedness : signedness = none := by
                cases signedness <;> simp_all [Shape.laneIsNum]
              subst signedness
              let laneValue :=
                (releasedNumerics.lanes_
                  ({ lane := .num numberType, dim := dimension } : Shape)
                  literal)[index.val]'(by
                    rw [releasedNumerics_lanes_length]
                    exact indexBound)
              have hlane :
                  (releasedNumerics.lanes_
                    ({ lane := .num numberType, dim := dimension } : Shape)
                    literal)[index.val]? = some laneValue :=
                List.getElem?_eq_getElem _
              have pure : Step_pure releasedNumerics
                  [.plain (.vconst .v128 literal),
                    .plain (.vextractLane
                      { lane := .num numberType, dim := dimension } none index)]
                  [.plain (.const numberType laneValue)] :=
                .vextractLaneNum hlane
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _,
                (state, [.plain (.const numberType laneValue)]),
                by simpa [vals] using StepA.pure member⟩
          | pack packType =>
              cases signedness with
              | none => simp [Shape.laneIsNum] at signednessShape
              | some sx =>
                  let laneValue :=
                    (releasedNumerics.lanes_
                      ({ lane := .pack packType, dim := dimension } : Shape)
                      literal)[index.val]'(by
                        rw [releasedNumerics_lanes_length]
                        exact indexBound)
                  have hlane :
                      (releasedNumerics.lanes_
                        ({ lane := .pack packType, dim := dimension } : Shape)
                        literal)[index.val]? = some laneValue :=
                    List.getElem?_eq_getElem _
                  let result : U32 := releasedNumerics.extend__
                    packType.size 32 sx laneValue
                  have pure : Step_pure releasedNumerics
                      [.plain (.vconst .v128 literal),
                        .plain (.vextractLane
                          { lane := .pack packType, dim := dimension }
                          (some sx) index)]
                      [constI32 result] :=
                    .vextractLanePack hlane rfl
                  obtain ⟨pureEvent, member⟩ :=
                    step_pure_mem_pureSuccessors pure
                  exact ⟨.pure pureEvent _, (state, [constI32 result]),
                    by simpa [vals] using StepA.pure member⟩

/-- A validated lane replacement updates an in-range lane of the released
concrete vector representation and rebuilds the result vector. -/
theorem Instr_okA.vreplaceLane_source_progress
    {context : Context} {state : State} {shape : Shape} {index : LaneIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vreplaceLane shape index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vreplaceLane shape index)])
        event target := by
  cases typed with
  | vreplace_lane shapeWf indexBound =>
      obtain ⟨vectorValues, laneValues, hvalues, vectorTyped, laneTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.num shape.unpack])
      obtain ⟨vector, hvectorValues, vectorTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp vectorTyped
      obtain ⟨lane, hlaneValues, laneTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp laneTyped
      obtain ⟨vectorLiteral, hvector⟩ := vectorTyped.vec_canonical
      obtain ⟨laneLiteral, hlane⟩ := laneTyped.num_canonical
      subst vector
      subst lane
      subst vectorValues
      subst laneValues
      subst values
      let laneList := releasedNumerics.lanes_ shape vectorLiteral
      let replacement := releasedNumerics.lpacknum_ shape.lane laneLiteral
      let updated := laneList.set index.val replacement
      have hlaneBound : index.val < laneList.length := by
        rw [show laneList.length = shape.dim.toNat by
          simpa [laneList] using
            releasedNumerics_lanes_length shape vectorLiteral]
        exact indexBound
      have hset : setAt? laneList index.val replacement = some updated := by
        simp [setAt?, updated, hlaneBound]
      let result := releasedNumerics.inv_lanes_ shape updated
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 vectorLiteral),
            .plain (.const shape.unpack laneLiteral),
            .plain (.vreplaceLane shape index)]
          [.plain (.vconst .v128 result)] :=
        .vreplaceLane hset rfl
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Lane-wise unary operations always expose either the released numeric
result or the specified trap branch. -/
theorem Instr_okA.vunop_source_progress
    {context : Context} {state : State} {shape : Shape} {operator : VUnop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vunop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vunop shape operator)])
        event target := by
  cases typed with
  | vunop _ _ =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      cases hresult : releasedNumerics.vunop_ shape operator literal with
      | nil =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 literal),
                .plain (.vunop shape operator)] [.trap] :=
            .vunopTrap hresult
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.trap]),
            by simpa [vals] using StepA.pure member⟩
      | cons result results =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 literal),
                .plain (.vunop shape operator)]
              [.plain (.vconst .v128 result)] :=
            .vunopVal (by simp [hresult])
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [.plain (.vconst .v128 result)]),
            by simpa [vals] using StepA.pure member⟩

/-- Lane-wise binary operations likewise have an explicit value-or-trap
reduction for every pair of canonical vector operands. -/
theorem Instr_okA.vbinop_source_progress
    {context : Context} {state : State} {shape : Shape} {operator : VBinop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vbinop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vbinop shape operator)])
        event target := by
  cases typed with
  | vbinop _ _ =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      cases hresult : releasedNumerics.vbinop_ shape operator
          leftLiteral rightLiteral with
      | nil =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 leftLiteral),
                .plain (.vconst .v128 rightLiteral),
                .plain (.vbinop shape operator)] [.trap] :=
            .vbinopTrap hresult
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.trap]),
            by simpa [vals] using StepA.pure member⟩
      | cons result results =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 leftLiteral),
                .plain (.vconst .v128 rightLiteral),
                .plain (.vbinop shape operator)]
              [.plain (.vconst .v128 result)] :=
            .vbinopVal (by simp [hresult])
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [.plain (.vconst .v128 result)]),
            by simpa [vals] using StepA.pure member⟩

/-- Lane-wise ternary operations have the same released value-or-trap
dichotomy on their three canonical vector operands. -/
theorem Instr_okA.vternop_source_progress
    {context : Context} {state : State} {shape : Shape} {operator : VTernop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vternop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vternop shape operator)])
        event target := by
  cases typed with
  | vternop _ _ =>
      obtain ⟨firstValues, tailValues, hvalues, firstTyped, tailTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128, .vec .v128])
      obtain ⟨secondValues, thirdValues, htail, secondTyped, thirdTyped⟩ :=
        tailTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨first, hfirstValues, firstTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp firstTyped
      obtain ⟨second, hsecondValues, secondTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp secondTyped
      obtain ⟨third, hthirdValues, thirdTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp thirdTyped
      obtain ⟨firstLiteral, hfirst⟩ := firstTyped.vec_canonical
      obtain ⟨secondLiteral, hsecond⟩ := secondTyped.vec_canonical
      obtain ⟨thirdLiteral, hthird⟩ := thirdTyped.vec_canonical
      subst first
      subst second
      subst third
      subst firstValues
      subst secondValues
      subst thirdValues
      subst tailValues
      subst values
      cases hresult : releasedNumerics.vternop_ shape operator
          firstLiteral secondLiteral thirdLiteral with
      | nil =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 firstLiteral),
                .plain (.vconst .v128 secondLiteral),
                .plain (.vconst .v128 thirdLiteral),
                .plain (.vternop shape operator)] [.trap] :=
            .vternopTrap hresult
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.trap]),
            by simpa [vals] using StepA.pure member⟩
      | cons result results =>
          have pure : Step_pure releasedNumerics
              [.plain (.vconst .v128 firstLiteral),
                .plain (.vconst .v128 secondLiteral),
                .plain (.vconst .v128 thirdLiteral),
                .plain (.vternop shape operator)]
              [.plain (.vconst .v128 result)] :=
            .vternopVal (by simp [hresult])
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [.plain (.vconst .v128 result)]),
            by simpa [vals] using StepA.pure member⟩

/-- A product of concrete Boolean encodings is still a concrete `u32`.
This is the only carrier bound needed by lane-wise `all_true`. -/
theorem prodNat_map_bool_lt_u32 {alpha : Type} (predicate : alpha → Bool)
    (items : List alpha) :
    prodNat
        (items.map (fun item => (Numerics.bool_ (predicate item)).val)) <
      2 ^ 32 := by
  induction items with
  | nil => simp [prodNat]
  | cons item items ih =>
      rw [List.map_cons, prodNat]
      cases hp : predicate item with
      | false =>
          change (Numerics.bool_ false).val * _ < _
          simp [Numerics.bool_]
      | true =>
          change (Numerics.bool_ true).val * _ < _
          simpa [Numerics.bool_] using ih

/-- The released lane-wise test is defined on every statically admitted
integer shape. -/
theorem released_vtestop_total (shape : Shape) (operator : VTestop)
    (literal : V128Lit) (operatorWf : VTestop.wf shape operator = true) :
    ∃ result, releasedNumerics.vtestop_ shape operator literal = some result := by
  cases operator with
  | int operation =>
      cases operation
      cases hitems : releasedNumerics.intLanes shape literal with
      | none =>
          cases shape with
          | mk lane dimension =>
              cases lane with
              | num numberType =>
                  cases numberType <;>
                    simp_all [VTestop.wf, LaneType.toJnn?,
                      Numerics.intLanes, lanesJ?, releasedNumerics,
                      ConcreteNumerics.released]
              | pack packType =>
                  cases packType <;>
                    simp_all [Numerics.intLanes, lanesJ?, releasedNumerics,
                      ConcreteNumerics.released]
      | some items =>
          have hbound : prodNat
              (items.map (fun item =>
                (Numerics.inez_ shape.lane.size item).val)) < 2 ^ 32 := by
            simpa [Numerics.inez_] using
              prodNat_map_bool_lt_u32 (fun item => item.val != 0) items
          let result : U32 := ⟨prodNat
            (items.map (fun item =>
              (Numerics.inez_ shape.lane.size item).val)), hbound⟩
          refine ⟨result, ?_⟩
          simp [Numerics.vtestop_, Numerics.ivtestop_, hitems,
            inOfNat?, result, hbound]

/-- Lane-wise `all_true` therefore takes its exact pure result step. -/
theorem Instr_okA.vtestop_source_progress
    {context : Context} {state : State} {shape : Shape} {operator : VTestop}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vtestop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vtestop shape operator)])
        event target := by
  cases typed with
  | vtestop shapeWf operatorWf =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      obtain ⟨result, hresult⟩ :=
        released_vtestop_total shape operator literal operatorWf
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 literal), .plain (.vtestop shape operator)]
          [constI32 result] := .vtestop hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _, (state, [constI32 result]),
        by simpa [vals] using StepA.pure member⟩

/-- Reading integer lanes is total at every integer shape admitted by the
syntax-level subtype. -/
theorem released_intLanes_total (shape : Shape) (literal : V128Lit)
    (integerShape : shape.isIShape = true) :
    ∃ lanes, releasedNumerics.intLanes shape literal = some lanes := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType <;>
            simp_all [Shape.isIShape, LaneType.toJnn?, Numerics.intLanes,
              lanesJ?, releasedNumerics, ConcreteNumerics.released]
      | pack packType =>
          cases packType <;>
            simp_all [Shape.isIShape, LaneType.toJnn?, Numerics.intLanes,
              lanesJ?, releasedNumerics, ConcreteNumerics.released]

/-- Rebuilding a vector from integer lanes is total at the same admitted
integer shapes. -/
theorem released_intVec_total (shape : Shape)
    (lanes : List (IN shape.lane.size))
    (integerShape : shape.isIShape = true) :
    ∃ literal, releasedNumerics.intVec shape lanes = some literal := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType <;>
            simp_all [Shape.isIShape, LaneType.toJnn?, Numerics.intVec,
              ofLanesJ?, releasedNumerics, ConcreteNumerics.released]
      | pack packType =>
          cases packType <;>
            simp_all [Shape.isIShape, LaneType.toJnn?, Numerics.intVec,
              ofLanesJ?, releasedNumerics, ConcreteNumerics.released]

/-- A successful integer-lane view retains the dimension stated by its
shape. -/
theorem released_intLanes_length {shape : Shape} {literal : V128Lit}
    {lanes : List (IN shape.lane.size)}
    (h : releasedNumerics.intLanes shape literal = some lanes) :
    lanes.length = shape.dim.toNat := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType <;>
            simp [Numerics.intLanes, lanesJ?, releasedNumerics,
              ConcreteNumerics.released, ConcreteNumerics.lanes] at h <;>
            subst lanes <;> cases dimension <;> rfl
      | pack packType =>
          cases packType <;>
            simp [Numerics.intLanes, lanesJ?, releasedNumerics,
              ConcreteNumerics.released, ConcreteNumerics.lanes] at h <;>
            subst lanes <;> cases dimension <;> rfl

/-- Released integer-lane shifts are total. -/
theorem released_vshiftop_total (shape : IShape) (operator : VShiftop)
    (literal : V128Lit) (amount : U32) :
    ∃ result,
      releasedNumerics.vshiftop_ shape operator literal amount = some result := by
  obtain ⟨lanes, hlanes⟩ :=
    released_intLanes_total shape.val literal shape.property
  cases operator with
  | shl =>
      obtain ⟨result, hresult⟩ := released_intVec_total shape.val
        (lanes.map (fun lane =>
          releasedNumerics.ishl_ shape.val.lane.size lane amount))
        shape.property
      refine ⟨result, ?_⟩
      simp [Numerics.vshiftop_, Numerics.ivshiftop_, hlanes]
      simpa [releasedNumerics, ConcreteNumerics.released] using hresult
  | shr signedness =>
      obtain ⟨result, hresult⟩ := released_intVec_total shape.val
        (lanes.map (fun lane =>
          releasedNumerics.ishr_ shape.val.lane.size signedness lane amount))
        shape.property
      refine ⟨result, ?_⟩
      simp [Numerics.vshiftop_, Numerics.ivshiftopsx_, hlanes]
      simpa [releasedNumerics, ConcreteNumerics.released] using hresult

/-- A source-typed vector shift therefore takes its exact pure result step. -/
theorem Instr_okA.vshiftop_source_progress
    {context : Context} {state : State} {shape : IShape}
    {operator : VShiftop} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vshiftop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vshiftop shape operator)])
        event target := by
  cases typed with
  | vshiftop shapeWf =>
      obtain ⟨vectorValues, amountValues, hvalues, vectorTyped, amountTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [ValType.i32])
      obtain ⟨vector, hvectorValues, vectorTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp vectorTyped
      obtain ⟨amount, hamountValues, amountTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp amountTyped
      obtain ⟨vectorLiteral, hvector⟩ := vectorTyped.vec_canonical
      obtain ⟨amountLiteral, hamount⟩ := amountTyped.num_canonical
      subst vector
      subst amount
      subst vectorValues
      subst amountValues
      subst values
      obtain ⟨result, hresult⟩ :=
        released_vshiftop_total shape operator vectorLiteral amountLiteral
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 vectorLiteral), constI32 amountLiteral,
            .plain (.vshiftop shape operator)]
          [.plain (.vconst .v128 result)] := .vshiftop hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- The signed lane comparison consumed by `v128.bitmask` always encodes an
actual bit. -/
theorem bitOfU32_ilt_signed_total (width : Nat) (left right : IN width) :
    ∃ bit, bitOfU32? (Numerics.ilt_ width .s left right) = some bit := by
  by_cases less : Numerics.signed_ width left < Numerics.signed_ width right
  · refine ⟨Bit.b1, ?_⟩
    simp [Numerics.ilt_, less, Numerics.bool_, bitOfU32?]
  · refine ⟨Bit.b0, ?_⟩
    simp [Numerics.ilt_, less, Numerics.bool_, bitOfU32?]

/-- Mapping those signed comparisons over a concrete lane list cannot fail. -/
theorem mapM_bitOfU32_ilt_signed_total (width : Nat) (zero : IN width)
    (items : List (IN width)) :
    ∃ bits,
      items.mapM (fun item =>
        bitOfU32? (Numerics.ilt_ width .s item zero)) = some bits := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons item items ih =>
      obtain ⟨bit, hbit⟩ := bitOfU32_ilt_signed_total width item zero
      obtain ⟨bits, hbits⟩ := ih
      exact ⟨bit :: bits, by simp [hbit, hbits]⟩

/-- The released integer-lane bitmask operation is total. -/
theorem released_vbitmaskop_total (shape : IShape) (literal : V128Lit) :
    ∃ result, releasedNumerics.vbitmaskop_ shape literal = some result := by
  obtain ⟨lanes, hlanes⟩ :=
    released_intLanes_total shape.val literal shape.property
  let zero := inZero shape.val.lane.size
  obtain ⟨bits, hbits⟩ := mapM_bitOfU32_ilt_signed_total
    shape.val.lane.size zero lanes
  let result : U32 := releasedNumerics.irev_ 32
    (releasedNumerics.inv_ibits_ 32
      (bits ++ List.replicate (32 - shape.val.dim.toNat) Bit.b0))
  refine ⟨result, ?_⟩
  simp [Numerics.vbitmaskop_, Numerics.ivbitmaskop_, hlanes,
    zero, hbits, result]

/-- A source-typed vector bitmask therefore takes its exact pure result step. -/
theorem Instr_okA.vbitmask_source_progress
    {context : Context} {state : State} {shape : IShape}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vbitmask shape) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vbitmask shape)]) event target := by
  cases typed with
  | vbitmask shapeWf =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.vec_canonical
      subst value
      subst values
      obtain ⟨result, hresult⟩ := released_vbitmaskop_total shape literal
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 literal), .plain (.vbitmask shape)]
          [constI32 result] := .vbitmask hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _, (state, [constI32 result]),
        by simpa [vals] using StepA.pure member⟩

/-- Released relaxed swizzle is total whenever its source lane list is
nonempty.  That nonemptiness comes from the validated vector shape below. -/
theorem released_irelaxed_swizzle_lane_total (width : Nat)
    (items : List (IN width)) (index : IN width) (nonempty : items ≠ []) :
    ∃ result,
      releasedNumerics.irelaxed_swizzle_lane_ width items index = some result := by
  unfold Numerics.irelaxed_swizzle_lane_
  cases hdirect : items[index.val]? with
  | some result => exact ⟨result, by simp⟩
  | none =>
      by_cases negative : Numerics.signed_ width index < 0
      · exact ⟨inZero width, by simp [negative]⟩
      · have hlength : 0 < items.length := by
          cases items with
          | nil => contradiction
          | cons item items => simp
        have hbound : index.val % items.length < items.length :=
          Nat.mod_lt _ hlength
        let selected := items[index.val % items.length]'hbound
        let result := relaxed2 releasedNumerics.nd
          releasedNumerics.r_swizzle (inZero width) selected
        refine ⟨result, ?_⟩
        simp [negative, List.getElem?_eq_getElem hbound, result,
          selected]

/-- Every byte shape is also an integer shape. -/
theorem BShape.integerShape (shape : BShape) : shape.val.isIShape = true := by
  rcases shape with ⟨⟨lane, dimension⟩, byteShape⟩
  cases lane with
  | num numberType =>
      cases numberType <;> cases byteShape
  | pack packType =>
      cases packType with
      | i8 => rfl
      | i16 => cases byteShape

/-- Mapping the released relaxed-swizzle primitive over selectors is total
when the source lane list is nonempty. -/
theorem mapM_released_irelaxed_swizzle_total (width : Nat)
    (source : List (IN width)) (nonempty : source ≠ [])
    (indices : List (IN width)) :
    ∃ results,
      indices.mapM (fun index =>
        releasedNumerics.irelaxed_swizzle_lane_ width source index) =
        some results := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index indices ih =>
      obtain ⟨result, hresult⟩ :=
        released_irelaxed_swizzle_lane_total width source index nonempty
      obtain ⟨results, hresults⟩ := ih
      exact ⟨result :: results, by simp [hresult, hresults]⟩

/-- Mapping an everywhere-successful option function has the ordinary list
map as its result. -/
theorem mapM_some {alpha beta : Type} (function : alpha → beta)
    (items : List alpha) :
    items.mapM (fun item => some (function item)) = some (items.map function) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

/-- Both specified byte-lane swizzles are total in the released provider. -/
theorem released_vswizzlop_total (shape : BShape) (operator : VSwizzlop)
    (left right : V128Lit) :
    ∃ result,
      releasedNumerics.vswizzlop_ shape operator left right = some result := by
  have integerShape := BShape.integerShape shape
  obtain ⟨leftLanes, hleft⟩ :=
    released_intLanes_total shape.val left integerShape
  obtain ⟨rightLanes, hright⟩ :=
    released_intLanes_total shape.val right integerShape
  have hleftLength := released_intLanes_length hleft
  have hleftNonempty : leftLanes ≠ [] := by
    intro hempty
    rw [hempty] at hleftLength
    have hdimension : 0 < shape.val.dim.toNat := by
      cases shape.val.dim <;> decide
    simp at hleftLength
    omega
  cases operator with
  | swizzle =>
      let results := rightLanes.map (fun index =>
        Numerics.iswizzle_lane_ shape.val.lane.size leftLanes index)
      obtain ⟨result, hresult⟩ :=
        released_intVec_total shape.val results integerShape
      have hmap : rightLanes.mapM (fun index =>
          some (Numerics.iswizzle_lane_ shape.val.lane.size leftLanes index)) =
          some results := by
        simpa [results] using mapM_some
          (fun index =>
            Numerics.iswizzle_lane_ shape.val.lane.size leftLanes index)
          rightLanes
      refine ⟨result, ?_⟩
      simp [Numerics.vswizzlop_, Numerics.ivswizzlop_, hleft, hright,
        hmap]
      exact hresult
  | relaxedSwizzle =>
      obtain ⟨results, hresults⟩ :=
        mapM_released_irelaxed_swizzle_total shape.val.lane.size
          leftLanes hleftNonempty rightLanes
      obtain ⟨result, hresult⟩ :=
        released_intVec_total shape.val results integerShape
      refine ⟨result, ?_⟩
      simp [Numerics.vswizzlop_, Numerics.ivswizzlop_, hleft, hright,
        hresults]
      exact hresult

/-- A source-typed swizzle therefore takes its exact pure result step. -/
theorem Instr_okA.vswizzlop_source_progress
    {context : Context} {state : State} {shape : BShape}
    {operator : VSwizzlop} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vswizzlop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vswizzlop shape operator)])
        event target := by
  cases typed with
  | vswizzlop shapeWf =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      obtain ⟨result, hresult⟩ :=
        released_vswizzlop_total shape operator leftLiteral rightLiteral
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 leftLiteral),
            .plain (.vconst .v128 rightLiteral),
            .plain (.vswizzlop shape operator)]
          [.plain (.vconst .v128 result)] := .vswizzlop hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Mapping in-range lane indices to list lookup is total. -/
theorem mapM_getElem_total {alpha : Type} (items : List alpha)
    (indices : List LaneIdx)
    (bounds : SeqAll (fun index : LaneIdx => index.val < items.length)
      indices) :
    ∃ results,
      indices.mapM (fun index => items[index.val]?) = some results := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index indices ih =>
      have hindex : index.val < items.length := bounds index (by simp)
      have hrest : SeqAll (fun index : LaneIdx => index.val < items.length)
          indices := by
        intro rest hmem
        exact bounds rest (by simp [hmem])
      obtain ⟨results, hresults⟩ := ih hrest
      let result := items[index.val]'hindex
      exact ⟨result :: results, by
        simp [List.getElem?_eq_getElem hindex, hresults, result]⟩

/-- Validated shuffle bounds make every lookup into the concatenated concrete
lane lists succeed. -/
theorem released_vshufflop_total (shape : BShape) (indices : List LaneIdx)
    (left right : V128Lit)
    (bounds : SeqAll
      (fun index : LaneIdx => index.val < 2 * shape.val.dim.toNat) indices) :
    ∃ result,
      releasedNumerics.vshufflop_ shape indices left right = some result := by
  have integerShape := BShape.integerShape shape
  obtain ⟨leftLanes, hleft⟩ :=
    released_intLanes_total shape.val left integerShape
  obtain ⟨rightLanes, hright⟩ :=
    released_intLanes_total shape.val right integerShape
  have hleftLength := released_intLanes_length hleft
  have hrightLength := released_intLanes_length hright
  have hbounds : SeqAll
      (fun index : LaneIdx =>
        index.val < (leftLanes ++ rightLanes).length) indices := by
    intro index hmem
    have hindex := bounds index hmem
    simp [hleftLength, hrightLength]
    omega
  obtain ⟨results, hresults⟩ :=
    mapM_getElem_total (leftLanes ++ rightLanes) indices hbounds
  have hresults' : indices.unattach.mapM
      (fun index => (leftLanes ++ rightLanes)[index]?) = some results := by
    simpa using hresults
  obtain ⟨result, hresult⟩ :=
    released_intVec_total shape.val results integerShape
  refine ⟨result, ?_⟩
  simp [Numerics.vshufflop_, Numerics.ivshufflop_, hleft, hright,
    hresults']
  exact hresult

/-- A source-typed shuffle therefore takes its exact pure result step. -/
theorem Instr_okA.vshuffle_source_progress
    {context : Context} {state : State} {shape : BShape}
    {indices : List LaneIdx} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vshuffle shape indices) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vshuffle shape indices)])
        event target := by
  cases typed with
  | vshuffle shapeWf indicesLength bounds =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      obtain ⟨result, hresult⟩ := released_vshufflop_total
        shape indices leftLiteral rightLiteral bounds
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 leftLiteral),
            .plain (.vconst .v128 rightLiteral),
            .plain (.vshuffle shape indices)]
          [.plain (.vconst .v128 result)] := .vshuffle hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Substitution preserves the number of source value types. -/
theorem substValTypes_length (types : ValTypes) :
    ∀ (variables : List TypeVar) (uses : List TypeUse),
      (substValTypes types variables uses).length = types.length
  | variables, uses => by
      cases types with
      | nil => rfl
      | cons type types =>
          simp [substValTypes, ValTypes.length,
            substValTypes_length types variables uses]

/-- Closing a source value-type sequence preserves its runtime arity. -/
theorem Context.closValTypes_toList_length (context : Context) :
    ∀ types : ValTypes,
      (context.closValTypes types).toList.length = types.toList.length
  | .nil => rfl
  | .cons type types => by
      simp [Context.closValTypes, ValTypes.length_toList,
        substValTypes_length]

/-- A valid source block type computes at runtime, with the same domain and
codomain arities as its amended typing derivation. -/
theorem Blocktype_okA.runtime_total
    {moduleTypes : List TypeDef} {context : Context} {state : State}
    {blockType : BlockType} {instructionType : InstrType}
    (typed : Blocktype_okA context blockType instructionType)
    (hsyntax : moduleTypes.all TypeDef.isSyn = true)
    (typesValid : Types_okA Context.empty moduleTypes context.types)
    (frameTypes : state.frame.mod.types = closDefTypes context.types) :
    ∃ runtimeDomain runtimeCodomain,
      blocktype_ state blockType = some (runtimeDomain, runtimeCodomain) ∧
      runtimeDomain.length = instructionType.dom.length ∧
      runtimeCodomain.length = instructionType.cod.length := by
  cases typed with
  | valtype typeValid =>
      exact ⟨[], _, rfl, rfl, rfl⟩
  | @typeidx index definedType domain codomain hlookup hexpand =>
      have hclosedLookup := closDefTypes_get_full
        (typesValid.storedFreeBefore hsyntax) typesValid.outputLength_le hlookup
      have htypeOf : state.typeOf index =
          some (context.closDefType definedType) := by
        simp [State.typeOf, frameTypes, Context.closDefType,
          Context.closTypes]
        exact hclosedLookup
      have hclosedExpand := hexpand.close_func (context := context)
      cases hclosedExpand with
      | mk hclosedExpand =>
          refine ⟨(context.closValTypes domain).toList,
            (context.closValTypes codomain).toList, ?_, ?_, ?_⟩
          · simp [blocktype_, htypeOf, hclosedExpand]
          · exact Context.closValTypes_toList_length context domain
          · exact Context.closValTypes_toList_length context codomain

/-- Source value typing fixes the value-stack arity. -/
theorem SourceValuesOkA.length {store : Store} {context : Context}
    {values : List Val} {types : List ValType}
    (typed : SourceValuesOkA store context values types) :
    values.length = types.length := by
  obtain ⟨actualTypes, runtimeTyped, subtype⟩ := typed
  have hruntime := (ValuesOkA.iff_seq.mp runtimeTyped).1
  cases subtype with
  | mk hlength hsubtype =>
      calc
        values.length =
            (context.closResultType actualTypes).length := hruntime
        _ = actualTypes.length := by simp [Context.closResultType]
        _ = types.length := by simpa [SeqLen₂] using hlength

/-- A typed `block` with a source-typed operand prefix takes the structural
read step to its result-arity label. -/
theorem Instr_okA.block_source_progress
    {moduleTypes : List TypeDef} {context : Context} {state : State}
    {blockType : BlockType} {body : InstrSeq}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.block blockType body) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hsyntax : moduleTypes.all TypeDef.isSyn = true)
    (typesValid : Types_okA Context.empty moduleTypes context.types)
    (frameTypes : state.frame.mod.types = closDefTypes context.types) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.block blockType body)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @block _ _ _ sourceDomain sourceCodomain locals blockTyped bodyTyped =>
      obtain ⟨runtimeDomain, runtimeCodomain, hblockType,
          hdomainLength, hcodomainLength⟩ :=
        Blocktype_okA.runtime_total blockTyped hsyntax typesValid frameTypes
      have hvaluesLength := valuesTyped.length
      have hread : Step_readA state .block
          (vals values ++ [.plain (.block blockType body)])
          [.label runtimeCodomain.length []
            (vals values ++ plains body.toList)] := by
        apply Step_read.block hblockType rfl rfl
        exact hvaluesLength.trans hdomainLength.symm
      exact ⟨.read .block _,
        (state, [.label runtimeCodomain.length []
          (vals values ++ plains body.toList)]), .read hread⟩

/-- A typed `loop` with a source-typed operand prefix takes the structural
read step to its argument-arity label and reinstalls the loop continuation. -/
theorem Instr_okA.loop_source_progress
    {moduleTypes : List TypeDef} {context : Context} {state : State}
    {blockType : BlockType} {body : InstrSeq}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.loop blockType body) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hsyntax : moduleTypes.all TypeDef.isSyn = true)
    (typesValid : Types_okA Context.empty moduleTypes context.types)
    (frameTypes : state.frame.mod.types = closDefTypes context.types) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.loop blockType body)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @loop _ _ _ sourceDomain sourceCodomain locals blockTyped bodyTyped =>
      obtain ⟨runtimeDomain, runtimeCodomain, hblockType,
          hdomainLength, hcodomainLength⟩ :=
        Blocktype_okA.runtime_total blockTyped hsyntax typesValid frameTypes
      have hvaluesLength := valuesTyped.length
      have hread : Step_readA state .loop
          (vals values ++ [.plain (.loop blockType body)])
          [.label runtimeDomain.length [.plain (.loop blockType body)]
            (vals values ++ plains body.toList)] := by
        apply Step_read.loop hblockType rfl rfl
        exact hvaluesLength.trans hdomainLength.symm
      exact ⟨.read .loop _,
        (state, [.label runtimeDomain.length [.plain (.loop blockType body)]
          (vals values ++ plains body.toList)]), .read hread⟩

/-- A typed `try_table` with a source-typed operand prefix takes the structural
read step to its result-arity handler and enclosed label. -/
theorem Instr_okA.tryTable_source_progress
    {moduleTypes : List TypeDef} {context : Context} {state : State}
    {blockType : BlockType} {catches : List_ Catch} {body : InstrSeq}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.tryTable blockType catches body)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hsyntax : moduleTypes.all TypeDef.isSyn = true)
    (typesValid : Types_okA Context.empty moduleTypes context.types)
    (frameTypes : state.frame.mod.types = closDefTypes context.types) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tryTable blockType catches body)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @try_table _ _ _ _ sourceDomain sourceCodomain locals blockTyped bodyTyped
      catchesTyped =>
      obtain ⟨runtimeDomain, runtimeCodomain, hblockType,
          hdomainLength, hcodomainLength⟩ :=
        Blocktype_okA.runtime_total blockTyped hsyntax typesValid frameTypes
      have hvaluesLength := valuesTyped.length
      have hread : Step_readA state .tryTable
          (vals values ++ [.plain (.tryTable blockType catches body)])
          [.handler runtimeCodomain.length catches.val
            [.label runtimeCodomain.length []
              (vals values ++ plains body.toList)]] := by
        apply Step_read.tryTable hblockType rfl rfl
        exact hvaluesLength.trans hdomainLength.symm
      exact ⟨.read .tryTable _,
        (state, [.handler runtimeCodomain.length catches.val
          [.label runtimeCodomain.length []
            (vals values ++ plains body.toList)]]), .read hread⟩

/-- A typed `if` first consumes its canonical `i32` condition and selects the
corresponding source block.  Any block arguments remain as the surrounding
value prefix of the evaluation context. -/
theorem Instr_okA.if_source_progress
    {context : Context} {state : State} {blockType : BlockType}
    {thenBody elseBody : InstrSeq} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context (.ifElse blockType thenBody elseBody)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA
        (state, vals values ++
          [.plain (.ifElse blockType thenBody elseBody)])
        event target := by
  cases typed with
  | @if_ _ _ _ _ argumentTypes _ _ _ _ _ =>
      obtain ⟨arguments, conditions, hvalues, _, conditionTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [ValType.i32])
      obtain ⟨condition, hconditions, conditionTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp conditionTyped
      obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
      subst condition
      subst conditions
      subst values
      by_cases hzero : literal.val = 0
      · have pure : Step_pure releasedNumerics
            [constI32 literal,
              .plain (.ifElse blockType thenBody elseBody)]
            [.plain (.block blockType elseBody)] := .ifFalse hzero
        obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
        have inner : StepA
            (state, [constI32 literal,
              .plain (.ifElse blockType thenBody elseBody)])
            (.pure pureEvent _) (state, [.plain (.block blockType elseBody)]) :=
          .pure member
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments
      · have pure : Step_pure releasedNumerics
            [constI32 literal,
              .plain (.ifElse blockType thenBody elseBody)]
            [.plain (.block blockType thenBody)] := .ifTrue hzero
        obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
        have inner : StepA
            (state, [constI32 literal,
              .plain (.ifElse blockType thenBody elseBody)])
            (.pure pureEvent _) (state, [.plain (.block blockType thenBody)]) :=
          .pure member
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments

/-- `ref.i31` is an immediate pure redex on its canonical `i32` operand. -/
theorem Instr_okA.refI31_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .refI31 instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .refI31]) event target := by
  cases typed with
  | ref_i31 =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.num_canonical
      subst value
      subst values
      let wrapped : U31 := releasedNumerics.wrap__ 32 31 literal
      have pure : Step_pure releasedNumerics
          [constI32 literal, .plain .refI31]
          [.addrref (.i31 wrapped)] := .refI31 rfl
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _, (state, [.addrref (.i31 wrapped)]),
        by simpa [vals] using StepA.pure member⟩

/-- `ref.is_null` is total on every source-typed runtime reference. -/
theorem Instr_okA.refIsNull_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .refIsNull instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .refIsNull]) event target := by
  cases typed with
  | ref_is_null _ =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst values
      cases reference with
      | null heapType =>
          let one : U32 := ⟨1, by decide⟩
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null heapType), .plain .refIsNull]
              [constI32 one] := .refIsNullTrue rfl
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [constI32 one]),
            by simpa [vals] using StepA.pure member⟩
      | addr address =>
          let zero : U32 := ⟨0, by decide⟩
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.addr address), .plain .refIsNull]
              [constI32 zero] := .refIsNullFalse (by
                intro heapType hbad
                cases hbad) rfl
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [constI32 zero]),
            by simpa [vals] using StepA.pure member⟩

/-- `ref.as_non_null` either preserves an address reference or traps on null. -/
theorem Instr_okA.refAsNonNull_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .refAsNonNull instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .refAsNonNull]) event target := by
  cases typed with
  | ref_as_non_null _ =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst values
      cases reference with
      | null heapType =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null heapType), .plain .refAsNonNull]
              [.trap] := .refAsNonNullNull
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.trap]),
            by simpa [vals] using StepA.pure member⟩
      | addr address =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.addr address), .plain .refAsNonNull]
              [Ref.toAdmin (.addr address)] := .refAsNonNullAddr (by
                intro heapType hbad
                cases hbad)
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [Ref.toAdmin (.addr address)]),
            by simpa [vals] using StepA.pure member⟩

/-- `ref.eq` is total on the two canonical runtime references supplied by its
source typing derivation. -/
theorem Instr_okA.refEq_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .refEq instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .refEq]) event target := by
  cases typed with
  | ref_eq =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.ref RefType.eqref])
          (rightTypes := [.ref RefType.eqref])
      obtain ⟨leftValue, hleftValues, leftValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨rightValue, hrightValues, rightValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftReference, hleftValue⟩ := leftValueTyped.ref_canonical
      obtain ⟨rightReference, hrightValue⟩ := rightValueTyped.ref_canonical
      subst leftValue
      subst rightValue
      subst leftValues
      subst rightValues
      subst values
      let one : U32 := ⟨1, by decide⟩
      let zero : U32 := ⟨0, by decide⟩
      cases leftReference with
      | null leftHeap =>
          cases rightReference with
          | null rightHeap =>
              have pure : Step_pure releasedNumerics
                  [Ref.toAdmin (.null leftHeap), Ref.toAdmin (.null rightHeap),
                    .plain .refEq]
                  [constI32 one] := .refEqNull rfl
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [constI32 one]),
                by simpa [vals] using StepA.pure member⟩
          | addr rightAddress =>
              have pure : Step_pure releasedNumerics
                  [Ref.toAdmin (.null leftHeap), Ref.toAdmin (.addr rightAddress),
                    .plain .refEq]
                  [constI32 zero] := .refEqFalse (by
                    intro firstHeap secondHeap bothNull
                    cases bothNull.2) (by intro hbad; cases hbad) rfl
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [constI32 zero]),
                by simpa [vals] using StepA.pure member⟩
      | addr leftAddress =>
          cases rightReference with
          | null rightHeap =>
              have pure : Step_pure releasedNumerics
                  [Ref.toAdmin (.addr leftAddress), Ref.toAdmin (.null rightHeap),
                    .plain .refEq]
                  [constI32 zero] := .refEqFalse (by
                    intro firstHeap secondHeap bothNull
                    cases bothNull.1) (by intro hbad; cases hbad) rfl
              obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
              exact ⟨.pure pureEvent _, (state, [constI32 zero]),
                by simpa [vals] using StepA.pure member⟩
          | addr rightAddress =>
              by_cases heq : leftAddress = rightAddress
              · subst rightAddress
                have pure : Step_pure releasedNumerics
                    [Ref.toAdmin (.addr leftAddress),
                      Ref.toAdmin (.addr leftAddress), .plain .refEq]
                    [constI32 one] := .refEqTrue (by
                      intro firstHeap secondHeap bothNull
                      cases bothNull.1) rfl rfl
                obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
                exact ⟨.pure pureEvent _, (state, [constI32 one]),
                  by simpa [vals] using StepA.pure member⟩
              · have hrefNe : Ref.addr leftAddress ≠ Ref.addr rightAddress := by
                  intro hbad
                  injection hbad with hbad
                  exact heq hbad
                have pure : Step_pure releasedNumerics
                    [Ref.toAdmin (.addr leftAddress),
                      Ref.toAdmin (.addr rightAddress), .plain .refEq]
                    [constI32 zero] := .refEqFalse (by
                      intro firstHeap secondHeap bothNull
                      cases bothNull.1) hrefNe rfl
                obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
                exact ⟨.pure pureEvent _, (state, [constI32 zero]),
                  by simpa [vals] using StepA.pure member⟩

/-- `ref.test` always selects its positive or negative runtime matching rule.
The test itself is total; executable matcher completeness is needed only to
enumerate that relational choice, not to exhibit it. -/
theorem Instr_okA.refTest_source_progress
    {context : Context} {state : State} {referenceType : RefType}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.refTest referenceType) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.refTest referenceType)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @ref_test _ targetType sourceType targetValid sourceValid subtype =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst values
      by_cases hmatch : ∃ actualType,
          Ref_okA state.store reference actualType ∧
            Reftype_subA Context.empty actualType
              (instRefType state.frame.mod referenceType)
      · obtain ⟨actualType, referenceTyped, actualSubtype⟩ := hmatch
        have hread : Step_readA state .refTestTrue
            [reference.toAdmin, .plain (.refTest referenceType)]
            [constI32 ⟨1, by decide⟩] :=
          .refTestTrue referenceTyped actualSubtype rfl
        exact ⟨.read .refTestTrue _,
          (state, [constI32 ⟨1, by decide⟩]), .read hread⟩
      · have hread : Step_readA state .refTestFalse
            [reference.toAdmin, .plain (.refTest referenceType)]
            [constI32 ⟨0, by decide⟩] :=
          .refTestFalse hmatch rfl
        exact ⟨.read .refTestFalse _,
          (state, [constI32 ⟨0, by decide⟩]), .read hread⟩

/-- `ref.cast` likewise either preserves its matching reference or traps under
the ordinary negative runtime rule. -/
theorem Instr_okA.refCast_source_progress
    {context : Context} {state : State} {referenceType : RefType}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.refCast referenceType) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.refCast referenceType)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @ref_cast _ targetType sourceType targetValid sourceValid subtype =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst values
      by_cases hmatch : ∃ actualType,
          Ref_okA state.store reference actualType ∧
            Reftype_subA Context.empty actualType
              (instRefType state.frame.mod referenceType)
      · obtain ⟨actualType, referenceTyped, actualSubtype⟩ := hmatch
        have hread : Step_readA state .refCastSucceed
            [reference.toAdmin, .plain (.refCast referenceType)]
            [reference.toAdmin] :=
          .refCastSucceed referenceTyped actualSubtype
        exact ⟨.read .refCastSucceed _,
          (state, [reference.toAdmin]), .read hread⟩
      · have hread : Step_readA state .refCastFail
            [reference.toAdmin, .plain (.refCast referenceType)] [.trap] :=
          .refCastFail hmatch
        exact ⟨.read .refCastFail _, (state, [.trap]), .read hread⟩

/-- `br_on_cast` decides the runtime match on its canonical reference operand;
the preceding branch arguments remain in the instruction context. -/
theorem Instr_okA.brOnCast_source_progress
    {context : Context} {state : State} {label : LabelIdx}
    {sourceType targetType : RefType} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context (.brOnCast label sourceType targetType)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state,
        vals values ++ [.plain (.brOnCast label sourceType targetType)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @br_on_cast _ _ _ _ _ argumentTypes hlabel sourceValid targetValid
      targetSource targetLabel =>
      obtain ⟨arguments, references, hvalues, argumentsTyped,
          referenceTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [.ref sourceType])
      obtain ⟨value, hreferences, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst references
      subst values
      by_cases hmatch : ∃ actualType,
          Ref_okA state.store reference actualType ∧
            Reftype_subA Context.empty actualType
              (instRefType state.frame.mod targetType)
      · obtain ⟨actualType, referenceRuntimeTyped, actualSubtype⟩ := hmatch
        have hread : Step_readA state .brOnCastSucceed
            [reference.toAdmin,
              .plain (.brOnCast label sourceType targetType)]
            [reference.toAdmin, .plain (.br label)] :=
          .brOnCastSucceed referenceRuntimeTyped actualSubtype
        have inner : StepA
            (state, [reference.toAdmin,
              .plain (.brOnCast label sourceType targetType)])
            (.read .brOnCastSucceed _)
            (state, [reference.toAdmin, .plain (.br label)]) := .read hread
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments
      · have hread : Step_readA state .brOnCastFail
            [reference.toAdmin,
              .plain (.brOnCast label sourceType targetType)]
            [reference.toAdmin] := .brOnCastFail hmatch
        have inner : StepA
            (state, [reference.toAdmin,
              .plain (.brOnCast label sourceType targetType)])
            (.read .brOnCastFail _) (state, [reference.toAdmin]) := .read hread
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments

/-- `br_on_cast_fail` uses the complementary branch direction of the same
runtime reference match. -/
theorem Instr_okA.brOnCastFail_source_progress
    {context : Context} {state : State} {label : LabelIdx}
    {sourceType targetType : RefType} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context (.brOnCastFail label sourceType targetType)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state,
        vals values ++ [.plain (.brOnCastFail label sourceType targetType)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @br_on_cast_fail _ _ _ _ _ argumentTypes hlabel sourceValid targetValid
      targetSource differenceLabel =>
      obtain ⟨arguments, references, hvalues, argumentsTyped,
          referenceTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [.ref sourceType])
      obtain ⟨value, hreferences, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst references
      subst values
      by_cases hmatch : ∃ actualType,
          Ref_okA state.store reference actualType ∧
            Reftype_subA Context.empty actualType
              (instRefType state.frame.mod targetType)
      · obtain ⟨actualType, referenceRuntimeTyped, actualSubtype⟩ := hmatch
        have hread : Step_readA state .brOnCastFailSucceed
            [reference.toAdmin,
              .plain (.brOnCastFail label sourceType targetType)]
            [reference.toAdmin] :=
          .brOnCastFailSucceed referenceRuntimeTyped actualSubtype
        have inner : StepA
            (state, [reference.toAdmin,
              .plain (.brOnCastFail label sourceType targetType)])
            (.read .brOnCastFailSucceed _)
            (state, [reference.toAdmin]) := .read hread
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments
      · have hread : Step_readA state .brOnCastFailFail
            [reference.toAdmin,
              .plain (.brOnCastFail label sourceType targetType)]
            [reference.toAdmin, .plain (.br label)] :=
          .brOnCastFailFail hmatch
        have inner : StepA
            (state, [reference.toAdmin,
              .plain (.brOnCastFail label sourceType targetType)])
            (.read .brOnCastFailFail _)
            (state, [reference.toAdmin, .plain (.br label)]) := .read hread
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments

/-- Conditional branch dispatch is an immediate pure redex; the branch
arguments remain in the surrounding value context. -/
theorem Instr_okA.brIf_source_progress
    {context : Context} {state : State} {label : LabelIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.brIf label) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.brIf label)]) event target := by
  cases typed with
  | @br_if _ _ argumentTypes _ =>
      obtain ⟨arguments, conditions, hvalues, _, conditionTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [ValType.i32])
      obtain ⟨condition, hconditions, conditionTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp conditionTyped
      obtain ⟨literal, hcondition⟩ := conditionTyped.num_canonical
      subst condition
      subst conditions
      subst values
      by_cases hzero : literal.val = 0
      · have pure : Step_pure releasedNumerics
            [constI32 literal, .plain (.brIf label)] [] := .brIfFalse hzero
        obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
        have inner : StepA
            (state, [constI32 literal, .plain (.brIf label)])
            (.pure pureEvent _) (state, []) := .pure member
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments
      · have pure : Step_pure releasedNumerics
            [constI32 literal, .plain (.brIf label)] [.plain (.br label)] :=
          .brIfTrue hzero
        obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
        have inner : StepA
            (state, [constI32 literal, .plain (.brIf label)])
            (.pure pureEvent _) (state, [.plain (.br label)]) := .pure member
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments

/-- Branch-table index selection is total for the canonical `i32` selector. -/
theorem Instr_okA.brTable_source_progress
    {context : Context} {state : State} {labels : List LabelIdx}
    {defaultLabel : LabelIdx} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context (.brTable labels defaultLabel) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state,
        vals values ++ [.plain (.brTable labels defaultLabel)]) event target := by
  cases typed with
  | @br_table _ _ _ sharedTypes polymorphicTypes _ _ _ _ _ _ =>
      obtain ⟨arguments, selectors, hvalues, _, selectorTyped⟩ :=
        valuesTyped.split
          (leftTypes := polymorphicTypes ++ sharedTypes)
          (rightTypes := [ValType.i32])
      obtain ⟨selector, hselectors, selectorTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp selectorTyped
      obtain ⟨literal, hselector⟩ := selectorTyped.num_canonical
      subst selector
      subst selectors
      subst values
      by_cases hin : literal.val < labels.length
      · cases hselected : labels[literal.val]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at hselected
            omega
        | some selected =>
            have pure : Step_pure releasedNumerics
                [constI32 literal, .plain (.brTable labels defaultLabel)]
                [.plain (.br selected)] := .brTableLt hselected
            obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
            have inner : StepA
                (state, [constI32 literal,
                  .plain (.brTable labels defaultLabel)])
                (.pure pureEvent _) (state, [.plain (.br selected)]) :=
              .pure member
            simpa [vals, List.append_assoc] using
              inner.exists_of_prepend_values arguments
      · have hge : literal.val ≥ labels.length := Nat.le_of_not_gt hin
        have pure : Step_pure releasedNumerics
            [constI32 literal, .plain (.brTable labels defaultLabel)]
            [.plain (.br defaultLabel)] := .brTableGe hge
        obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
        have inner : StepA
            (state, [constI32 literal,
              .plain (.brTable labels defaultLabel)])
            (.pure pureEvent _) (state, [.plain (.br defaultLabel)]) := .pure member
        simpa [vals, List.append_assoc] using
          inner.exists_of_prepend_values arguments

/-- Null-branch dispatch is total on its source-typed runtime reference. -/
theorem Instr_okA.brOnNull_source_progress
    {context : Context} {state : State} {label : LabelIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.brOnNull label) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.brOnNull label)]) event target := by
  cases typed with
  | @br_on_null _ _ argumentTypes heapType _ _ =>
      obtain ⟨arguments, references, hvalues, _, referenceTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [.ref (.ref (some .null) heapType)])
      obtain ⟨value, hreferences, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst references
      subst values
      cases reference with
      | null runtimeHeap =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null runtimeHeap), .plain (.brOnNull label)]
              [.plain (.br label)] := .brOnNullNull
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          have inner : StepA
              (state, [Ref.toAdmin (.null runtimeHeap),
                .plain (.brOnNull label)])
              (.pure pureEvent _) (state, [.plain (.br label)]) := .pure member
          simpa [vals, List.append_assoc] using
            inner.exists_of_prepend_values arguments
      | addr address =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.addr address), .plain (.brOnNull label)]
              [Ref.toAdmin (.addr address)] := .brOnNullAddr (by
                intro runtimeHeap hbad
                cases hbad)
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          have inner : StepA
              (state, [Ref.toAdmin (.addr address),
                .plain (.brOnNull label)])
              (.pure pureEvent _) (state, [Ref.toAdmin (.addr address)]) :=
            .pure member
          simpa [vals, List.append_assoc] using
            inner.exists_of_prepend_values arguments

/-- Non-null-branch dispatch is total on its source-typed runtime reference. -/
theorem Instr_okA.brOnNonNull_source_progress
    {context : Context} {state : State} {label : LabelIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.brOnNonNull label) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.brOnNonNull label)]) event target := by
  cases typed with
  | @br_on_non_null _ _ argumentTypes nullability heapType _ =>
      obtain ⟨arguments, references, hvalues, _, referenceTyped⟩ :=
        valuesTyped.split (leftTypes := argumentTypes)
          (rightTypes := [.ref (.ref (some .null) heapType)])
      obtain ⟨value, hreferences, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst references
      subst values
      cases reference with
      | null runtimeHeap =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null runtimeHeap), .plain (.brOnNonNull label)]
              [] := .brOnNonNullNull
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          have inner : StepA
              (state, [Ref.toAdmin (.null runtimeHeap),
                .plain (.brOnNonNull label)])
              (.pure pureEvent _) (state, []) := .pure member
          simpa [vals, List.append_assoc] using
            inner.exists_of_prepend_values arguments
      | addr address =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.addr address), .plain (.brOnNonNull label)]
              [Ref.toAdmin (.addr address), .plain (.br label)] :=
            .brOnNonNullAddr (by
              intro runtimeHeap hbad
              cases hbad)
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          have inner : StepA
              (state, [Ref.toAdmin (.addr address),
                .plain (.brOnNonNull label)])
              (.pure pureEvent _)
              (state, [Ref.toAdmin (.addr address), .plain (.br label)]) :=
            .pure member
          simpa [vals, List.append_assoc] using
            inner.exists_of_prepend_values arguments

/-- Indirect calls first expand to the explicit table lookup, cast, and
typed-reference call sequence, independently of the current store. -/
theorem Instr_okA.callIndirect_source_progress
    {context : Context} {state : State} {table : TableIdx}
    {typeUse : TypeUse} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.callIndirect table typeUse) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.callIndirect table typeUse)])
        event target := by
  have pure : Step_pure releasedNumerics
      [.plain (.callIndirect table typeUse)]
      [.plain (.tableGet table),
        .plain (.refCast (.ref (some .null) (.use typeUse))),
        .plain (.callRef typeUse)] := .callIndirect
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  have inner : StepA (state, [.plain (.callIndirect table typeUse)])
      (.pure pureEvent _) (state,
        [.plain (.tableGet table),
          .plain (.refCast (.ref (some .null) (.use typeUse))),
          .plain (.callRef typeUse)]) := .pure member
  simpa [vals, List.append_assoc] using
    inner.exists_of_prepend_values values

/-- Indirect tail calls have the corresponding context-free expansion. -/
theorem Instr_okA.returnCallIndirect_source_progress
    {context : Context} {state : State} {table : TableIdx}
    {typeUse : TypeUse} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.returnCallIndirect table typeUse)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA
        (state, vals values ++
          [.plain (.returnCallIndirect table typeUse)]) event target := by
  have pure : Step_pure releasedNumerics
      [.plain (.returnCallIndirect table typeUse)]
      [.plain (.tableGet table),
        .plain (.refCast (.ref (some .null) (.use typeUse))),
        .plain (.returnCallRef typeUse)] := .returnCallIndirect
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  have inner : StepA
      (state, [.plain (.returnCallIndirect table typeUse)])
      (.pure pureEvent _) (state,
        [.plain (.tableGet table),
          .plain (.refCast (.ref (some .null) (.use typeUse))),
          .plain (.returnCallRef typeUse)]) := .pure member
  simpa [vals, List.append_assoc] using
    inner.exists_of_prepend_values values

/-- Pointwise local typing exposes the runtime slot at every statically
resolved local index. -/
theorem LocalsOkA.lookup {store : Store} {slots : List (Option Val)}
    {types : List LocalType} (typed : LocalsOkA store slots types)
    {index : Nat} {type : LocalType} (hlookup : types[index]? = some type) :
    ∃ slot, slots[index]? = some slot ∧ LocalSlotOkA store slot type := by
  induction typed generalizing index with
  | nil => simp at hlookup
  | @cons slot headType slots types headTyped tailTyped ih =>
      cases index with
      | zero =>
          simp at hlookup
          subst type
          exact ⟨slot, by simp, headTyped⟩
      | succ index =>
          exact ih (by simpa using hlookup)

/-- An initialized source local resolves to its genuinely stored runtime value
and takes the specified read step. -/
theorem Instr_okA.localGet_source_progress
    {context : Context} {state : State} {index : LocalIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.localGet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (localsTyped : LocalsOkA state.store state.frame.locals context.locals) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.localGet index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @local_get _ _ type hlocal =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      obtain ⟨slot, hslot, slotTyped⟩ := localsTyped.lookup hlocal
      cases slotTyped with
      | @set value slotType valueTyped =>
          have hread : Step_readA state .localGet [.plain (.localGet index)]
              [value.toAdmin] := by
            apply Step_read.localGet
            simpa [State.localOf] using hslot
          exact ⟨.read .localGet _, (state, [value.toAdmin]), .read hread⟩

/-- A source-typed `local.set` targets an in-range runtime slot and therefore
computes its exact updated state. -/
theorem Instr_okA.localSet_source_progress
    {context : Context} {state : State} {index : LocalIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.localSet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (localsTyped : LocalsOkA state.store state.frame.locals context.locals) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.localSet index)]) event target := by
  cases typed with
  | @local_set _ _ initialization type hlocal =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      subst values
      obtain ⟨slot, hslot, slotTyped⟩ := localsTyped.lookup hlocal
      have hindex : index.val < state.frame.locals.length :=
        (List.getElem?_eq_some_iff.mp hslot).1
      let updatedLocals := state.frame.locals.set index.val (some value)
      let targetState : State :=
        { state with frame := { state.frame with locals := updatedLocals } }
      have hset : setAt? state.frame.locals index.val (some value) =
          some updatedLocals := by
        simp [setAt?, hindex, updatedLocals]
      have hupdate : state.withLocal index value = some targetState := by
        simp [State.withLocal, hset, targetState]
      have step : StepA
          (state, [value.toAdmin, .plain (.localSet index)])
          (.localSet index) (targetState, []) := .localSet hupdate
      exact ⟨.localSet index, (targetState, []), by simpa [vals] using step⟩

/-- `local.tee` duplicates its typed runtime operand and exposes the ordinary
state-writing `local.set` instruction. -/
theorem Instr_okA.localTee_source_progress
    {context : Context} {state : State} {index : LocalIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.localTee index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.localTee index)]) event target := by
  cases typed with
  | local_tee =>
      obtain ⟨value, hvalues, _⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      subst values
      have pure : Step_pure releasedNumerics
          [value.toAdmin, .plain (.localTee index)]
          [value.toAdmin, value.toAdmin, .plain (.localSet index)] :=
        .localTee
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [value.toAdmin, value.toAdmin, .plain (.localSet index)]),
        by simpa [vals] using StepA.pure member⟩

/-- `array.new` expands a typed element and canonical `i32` length to the
fixed-arity allocation form prescribed by the Core relation. -/
theorem Instr_okA.arrayNew_source_progress
    {context : Context} {state : State} {index : TypeIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.arrayNew index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.arrayNew index)]) event target := by
  cases typed with
  | @array_new _ _ _ fieldType _ _ =>
      obtain ⟨elements, lengths, hvalues, elementTyped, lengthTyped⟩ :=
        valuesTyped.split
          (leftTypes := [StorageType.unpack fieldType.storage])
          (rightTypes := [ValType.i32])
      obtain ⟨element, helements, _⟩ :=
        SourceValuesOkA.singleton_iff.mp elementTyped
      obtain ⟨length, hlengths, lengthTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp lengthTyped
      obtain ⟨literal, hlength⟩ := lengthTyped.num_canonical
      subst length
      subst elements
      subst lengths
      subst values
      have pure : Step_pure releasedNumerics
          [element.toAdmin, constI32 literal, .plain (.arrayNew index)]
          (vals (List.replicate literal.val element) ++
            [.plain (.arrayNewFixed index literal)]) := .arrayNew
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, vals (List.replicate literal.val element) ++
          [.plain (.arrayNewFixed index literal)]),
        by simpa [vals] using StepA.pure member⟩

/-- `extern.convert_any` is total on null and address runtime references. -/
theorem Instr_okA.externConvertAny_source_progress
    {context : Context} {state : State} {instructionType : InstrType}
    {values : List Val}
    (typed : Instr_okA context .externConvertAny instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain .externConvertAny]) event target := by
  cases typed with
  | extern_convert_any =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨reference, hvalue⟩ := valueTyped.ref_canonical
      subst value
      subst values
      cases reference with
      | null heapType =>
          have pure : Step_pure releasedNumerics
              [Ref.toAdmin (.null heapType), .plain .externConvertAny]
              [Ref.toAdmin (.null (.abs .extern))] := .externConvertAnyNull
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _,
            (state, [Ref.toAdmin (.null (.abs .extern))]),
            by simpa [vals] using StepA.pure member⟩
      | addr address =>
          have pure : Step_pure releasedNumerics
              [.addrref address, .plain .externConvertAny]
              [.addrref (.extern address)] := .externConvertAnyAddr
          obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
          exact ⟨.pure pureEvent _, (state, [.addrref (.extern address)]),
            by simpa [vals] using StepA.pure member⟩

/-! ## Lane-wise vector comparisons -/

/-- Reading floating lanes is total at every shape admitted by the floating
operator syntax. -/
theorem released_floatLanes_total (shape : Shape) (literal : V128Lit)
    (floatShape : shape.lane.toFnn?.isSome = true) :
    ∃ lanes, releasedNumerics.floatLanes shape literal = some lanes := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType with
          | i32 => simp_all [LaneType.toFnn?]
          | i64 => simp_all [LaneType.toFnn?]
          | f32 =>
              simp_all [LaneType.toFnn?, Numerics.floatLanes, lanesF?,
                releasedNumerics, ConcreteNumerics.released]
          | f64 =>
              simp_all [LaneType.toFnn?, Numerics.floatLanes, lanesF?,
                releasedNumerics, ConcreteNumerics.released]
      | pack packType =>
          cases packType <;>
            simp_all [LaneType.toFnn?]

/-- A successful floating-lane view retains the dimension stated by its
shape. -/
theorem released_floatLanes_length {shape : Shape} {literal : V128Lit}
    {lanes : List (FN shape.lane.size)}
    (h : releasedNumerics.floatLanes shape literal = some lanes) :
    lanes.length = shape.dim.toNat := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType <;>
            simp [Numerics.floatLanes, lanesF?] at h <;>
            subst lanes <;> cases dimension <;> rfl
      | pack packType =>
          cases packType <;>
            simp [Numerics.floatLanes, lanesF?] at h

/-- Every member produced by a binary lockstep map satisfies a pointwise
property satisfied by the mapped function. -/
theorem zipWith_all {alpha beta gamma : Type}
    (function : alpha → beta → gamma) (property : gamma → Prop)
    (hall : ∀ left right, property (function left right)) :
    ∀ (left : List alpha) (right : List beta) (result : gamma),
      result ∈ List.zipWith function left right → property result
  | [], right, result, member => by simp at member
  | left :: lefts, [], result, member => by simp at member
  | left :: lefts, right :: rights, result, member => by
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact hall left right
      · exact zipWith_all function property hall lefts rights result member

/-- A list of comparison results known to encode bits can all be extended to
the target lane width. -/
theorem mapM_bitExtend_total (width : Nat) (items : List U32)
    (bounded : ∀ item ∈ items, item.val < 2) :
    ∃ results,
      items.mapM (fun item =>
        (inOfNat? 1 item.val).map
          (releasedNumerics.extend__ 1 width .s)) = some results := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons item items ih =>
      have hitem : item.val < 2 := bounded item (by simp)
      have htail : ∀ rest ∈ items, rest.val < 2 := by
        intro rest hmem
        exact bounded rest (by simp [hmem])
      obtain ⟨results, hresults⟩ := ih htail
      let bit : IN 1 := ⟨item.val, by simpa using hitem⟩
      refine ⟨releasedNumerics.extend__ 1 width .s bit :: results, ?_⟩
      simp only [List.mapM_cons]
      rw [show (inOfNat? 1 item.val).map
        (releasedNumerics.extend__ 1 width .s) =
          some (releasedNumerics.extend__ 1 width .s bit) by
        simp [inOfNat?, hitem, bit]]
      rw [hresults]
      rfl

/-- The source numeric boolean always inhabits the two-element bit range. -/
theorem Numerics.bool_bound (value : Bool) :
    (Numerics.bool_ value).val < 2 := by
  cases value <;> simp [Numerics.bool_]

/-- Every scalar integer comparison produces a bit-valued `u32`. -/
theorem released_integerComparison_bound (width : Nat)
    (operator : VRelopJ) (left right : IN width) :
    (match operator with
      | .eq => Numerics.ieq_ width left right
      | .ne => Numerics.ine_ width left right
      | .lt sign => Numerics.ilt_ width sign left right
      | .gt sign => Numerics.igt_ width sign left right
      | .le sign => Numerics.ile_ width sign left right
      | .ge sign => Numerics.ige_ width sign left right).val < 2 := by
  cases operator with
  | eq => exact Numerics.bool_bound _
  | ne => exact Numerics.bool_bound _
  | lt sign => cases sign <;> exact Numerics.bool_bound _
  | gt sign => cases sign <;> exact Numerics.bool_bound _
  | le sign => cases sign <;> exact Numerics.bool_bound _
  | ge sign => cases sign <;> exact Numerics.bool_bound _

/-- The concrete floating comparison dispatcher also always returns a
bit-valued `u32`. -/
theorem ConcreteNumerics.floatPredicate_bound
    (predicate : Ordering → Bool) (width : Nat) (left right : FN width) :
    (ConcreteNumerics.floatPredicate predicate width left right).val < 2 := by
  simp only [ConcreteNumerics.floatPredicate]
  split
  · exact Numerics.bool_bound _
  · split
    · exact Numerics.bool_bound _
    · split <;> exact Numerics.bool_bound _

/-- Every released scalar floating comparison produces a bit-valued `u32`. -/
theorem released_floatComparison_bound (width : Nat)
    (operator : VRelopF) (left right : FN width) :
    (match operator with
      | .eq => releasedNumerics.feq_ width left right
      | .ne => releasedNumerics.fne_ width left right
      | .lt => releasedNumerics.flt_ width left right
      | .gt => releasedNumerics.fgt_ width left right
      | .le => releasedNumerics.fle_ width left right
      | .ge => releasedNumerics.fge_ width left right).val < 2 := by
  cases operator with
  | eq => exact ConcreteNumerics.floatPredicate_bound _ _ _ _
  | ne =>
      simp only [releasedNumerics, ConcreteNumerics.released,
        ConcreteNumerics.fne]
      split
      · simp [Numerics.bool_]
      · exact ConcreteNumerics.floatPredicate_bound _ _ _ _
  | lt => exact ConcreteNumerics.floatPredicate_bound _ _ _ _
  | gt => exact ConcreteNumerics.floatPredicate_bound _ _ _ _
  | le => exact ConcreteNumerics.floatPredicate_bound _ _ _ _
  | ge => exact ConcreteNumerics.floatPredicate_bound _ _ _ _

/-- Every admitted floating shape has the integer result shape used by the
source vector-comparison equations. -/
theorem Shape.floatIntShape (shape : Shape)
    (floatShape : shape.lane.toFnn?.isSome = true) :
    ∃ integerShape,
      intShapeOf shape = some integerShape ∧
      integerShape.isIShape = true := by
  cases shape with
  | mk lane dimension =>
      cases lane with
      | num numberType =>
          cases numberType <;>
            simp_all [LaneType.toFnn?, intShapeOf, Shape.isIShape,
              LaneType.toJnn?]
      | pack packType =>
          cases packType <;> simp_all [LaneType.toFnn?]

/-- Integer lockstep vector comparison is total when its scalar comparison is
bit-valued. -/
theorem released_ivrelop_total (shape : Shape)
    (function : (width : Nat) → IN width → IN width → U32)
    (left right : V128Lit) (integerShape : shape.isIShape = true)
    (bounded : ∀ left right,
      (function shape.lane.size left right).val < 2) :
    ∃ result,
      releasedNumerics.ivrelop_ shape function left right = some result := by
  obtain ⟨lefts, hlefts⟩ :=
    released_intLanes_total shape left integerShape
  obtain ⟨rights, hrights⟩ :=
    released_intLanes_total shape right integerShape
  have lengths : lefts.length = rights.length := by
    rw [released_intLanes_length hlefts,
      released_intLanes_length hrights]
  let compared := List.zipWith (function shape.lane.size) lefts rights
  have hcompared :
      zipWith? (function shape.lane.size) lefts rights = some compared := by
    simp [zipWith?, lengths, compared]
  have comparedBound : ∀ item ∈ compared, item.val < 2 := by
    exact zipWith_all (function shape.lane.size)
      (fun item => item.val < 2) bounded lefts rights
  obtain ⟨extended, hextended⟩ :=
    mapM_bitExtend_total shape.lane.size compared comparedBound
  have hextended' : compared.unattach.mapM (fun item =>
      (inOfNat? 1 item).map
        (releasedNumerics.extend__ 1 shape.lane.size .s)) =
      some extended := by
    simpa using hextended
  obtain ⟨result, hresult⟩ :=
    released_intVec_total shape extended integerShape
  refine ⟨result, ?_⟩
  simp [Numerics.ivrelop_, hlefts, hrights, hcompared, hextended',
    hresult]

/-- Signed integer lockstep vector comparison has the same totality
property. -/
theorem released_ivrelopsx_total (shape : Shape)
    (function : (width : Nat) → Sx → IN width → IN width → U32)
    (sign : Sx) (left right : V128Lit)
    (integerShape : shape.isIShape = true)
    (bounded : ∀ left right,
      (function shape.lane.size sign left right).val < 2) :
    ∃ result,
      releasedNumerics.ivrelopsx_ shape function sign left right =
        some result := by
  simpa [Numerics.ivrelopsx_, Numerics.ivrelop_] using
    released_ivrelop_total shape (fun width => function width sign)
      left right integerShape bounded

/-- Floating lockstep vector comparison is total when its scalar comparison
is bit-valued. -/
theorem released_fvrelop_total (shape : Shape)
    (function : (width : Nat) → FN width → FN width → U32)
    (left right : V128Lit)
    (floatShape : shape.lane.toFnn?.isSome = true)
    (bounded : ∀ left right,
      (function shape.lane.size left right).val < 2) :
    ∃ result,
      releasedNumerics.fvrelop_ shape function left right = some result := by
  obtain ⟨integerShape, hintegerShape, integerShapeWf⟩ :=
    Shape.floatIntShape shape floatShape
  obtain ⟨lefts, hlefts⟩ :=
    released_floatLanes_total shape left floatShape
  obtain ⟨rights, hrights⟩ :=
    released_floatLanes_total shape right floatShape
  have lengths : lefts.length = rights.length := by
    rw [released_floatLanes_length hlefts,
      released_floatLanes_length hrights]
  let compared := List.zipWith (function shape.lane.size) lefts rights
  have hcompared :
      zipWith? (function shape.lane.size) lefts rights = some compared := by
    simp [zipWith?, lengths, compared]
  have comparedBound : ∀ item ∈ compared, item.val < 2 := by
    exact zipWith_all (function shape.lane.size)
      (fun item => item.val < 2) bounded lefts rights
  obtain ⟨extended, hextended⟩ :=
    mapM_bitExtend_total integerShape.lane.size compared comparedBound
  have hextended' : compared.unattach.mapM (fun item =>
      (inOfNat? 1 item).map
        (releasedNumerics.extend__ 1 integerShape.lane.size .s)) =
      some extended := by
    simpa using hextended
  obtain ⟨result, hresult⟩ :=
    released_intVec_total integerShape extended integerShapeWf
  refine ⟨result, ?_⟩
  simp [Numerics.fvrelop_, hintegerShape, hlefts, hrights, hcompared,
    hextended', hresult]

/-- Every statically admitted released lane-wise vector comparison has a
concrete result. -/
theorem released_vrelop_total (shape : Shape) (operator : VRelop)
    (left right : V128Lit) (operatorWf : VRelop.wf shape operator = true) :
    ∃ result,
      releasedNumerics.vrelop_ shape operator left right = some result := by
  cases operator with
  | int operation =>
      have integerShape : shape.isIShape = true := by
        simp only [VRelop.wf, Bool.and_eq_true] at operatorWf
        exact operatorWf.1
      cases operation with
      | eq =>
          exact released_ivrelop_total shape Numerics.ieq_ left right
            integerShape (fun left right =>
              released_integerComparison_bound _ .eq left right)
      | ne =>
          exact released_ivrelop_total shape Numerics.ine_ left right
            integerShape (fun left right =>
              released_integerComparison_bound _ .ne left right)
      | lt sign =>
          exact released_ivrelopsx_total shape Numerics.ilt_ sign
            left right integerShape
            (fun left right =>
              released_integerComparison_bound _ (.lt sign) left right)
      | gt sign =>
          exact released_ivrelopsx_total shape Numerics.igt_ sign
            left right integerShape
            (fun left right =>
              released_integerComparison_bound _ (.gt sign) left right)
      | le sign =>
          exact released_ivrelopsx_total shape Numerics.ile_ sign
            left right integerShape
            (fun left right =>
              released_integerComparison_bound _ (.le sign) left right)
      | ge sign =>
          exact released_ivrelopsx_total shape Numerics.ige_ sign
            left right integerShape
            (fun left right =>
              released_integerComparison_bound _ (.ge sign) left right)
  | float operation =>
      have floatShape : shape.lane.toFnn?.isSome = true := by
        simpa [VRelop.wf] using operatorWf
      cases operation with
      | eq =>
          exact released_fvrelop_total shape releasedNumerics.feq_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .eq
              left right)
      | ne =>
          exact released_fvrelop_total shape releasedNumerics.fne_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .ne
              left right)
      | lt =>
          exact released_fvrelop_total shape releasedNumerics.flt_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .lt
              left right)
      | gt =>
          exact released_fvrelop_total shape releasedNumerics.fgt_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .gt
              left right)
      | le =>
          exact released_fvrelop_total shape releasedNumerics.fle_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .le
              left right)
      | ge =>
          exact released_fvrelop_total shape releasedNumerics.fge_
            left right floatShape
            (fun left right => released_floatComparison_bound _ .ge
              left right)

/-- A source-typed lane-wise vector comparison takes its exact pure result
step. -/
theorem Instr_okA.vrelop_source_progress
    {context : Context} {state : State} {shape : Shape}
    {operator : VRelop} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vrelop shape operator) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.vrelop shape operator)])
        event target := by
  cases typed with
  | vrelop shapeWf operatorWf =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      obtain ⟨result, hresult⟩ := released_vrelop_total
        shape operator leftLiteral rightLiteral operatorWf
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 leftLiteral),
            .plain (.vconst .v128 rightLiteral),
            .plain (.vrelop shape operator)]
          [.plain (.vconst .v128 result)] := .vrelop hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

/-- Lane narrowing is total on both canonical integer-vector operands. -/
theorem released_vnarrow_total (source target : IShape) (sign : Sx)
    (left right : V128Lit) :
    ∃ result,
      releasedNumerics.vnarrowop__ source target sign left right =
        some result := by
  obtain ⟨lefts, hlefts⟩ :=
    released_intLanes_total source.val left source.property
  obtain ⟨rights, hrights⟩ :=
    released_intLanes_total source.val right source.property
  let narrow := releasedNumerics.narrow__ source.val.lane.size
    target.val.lane.size sign
  obtain ⟨result, hresult⟩ := released_intVec_total target.val
    (lefts.map narrow ++ rights.map narrow) target.property
  refine ⟨result, ?_⟩
  simp [Numerics.vnarrowop__, hlefts, hrights]
  exact hresult

/-- A source-typed vector narrowing instruction takes its exact pure result
step. -/
theorem Instr_okA.vnarrow_source_progress
    {context : Context} {state : State} {source target : IShape}
    {sign : Sx} {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.vnarrow target source sign) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event next,
      StepA (state, vals values ++ [.plain (.vnarrow target source sign)])
        event next := by
  cases typed with
  | vnarrow targetWf sourceWf laneSize laneBound =>
      obtain ⟨leftValues, rightValues, hvalues, leftTyped, rightTyped⟩ :=
        valuesTyped.split (leftTypes := [.vec .v128])
          (rightTypes := [.vec .v128])
      obtain ⟨left, hleftValues, leftTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp leftTyped
      obtain ⟨right, hrightValues, rightTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp rightTyped
      obtain ⟨leftLiteral, hleft⟩ := leftTyped.vec_canonical
      obtain ⟨rightLiteral, hright⟩ := rightTyped.vec_canonical
      subst left
      subst right
      subst leftValues
      subst rightValues
      subst values
      obtain ⟨result, hresult⟩ := released_vnarrow_total source target
        sign leftLiteral rightLiteral
      have pure : Step_pure releasedNumerics
          [.plain (.vconst .v128 leftLiteral),
            .plain (.vconst .v128 rightLiteral),
            .plain (.vnarrow target source sign)]
          [.plain (.vconst .v128 result)] := .vnarrow hresult
      obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
      exact ⟨.pure pureEvent _,
        (state, [.plain (.vconst .v128 result)]),
        by simpa [vals] using StepA.pure member⟩

end WasmGemmGnaf.Wasm.Core.Exec
