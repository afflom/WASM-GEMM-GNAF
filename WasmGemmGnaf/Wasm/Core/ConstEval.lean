/-
  Executable evaluation of validated Core constant expressions.

  Core instantiation states global, table, and element initialization through
  the relational `Eval_expr` judgment.  The syntax admitted by `Expr_const` is
  finite and loop free, however: literals, immutable-global reads, reference
  construction/conversion, the three integer ring operations, and the GC
  constructors.  This file evaluates exactly that syntax without selecting a
  path from the general reduction relation.

  The function is deliberately `Option`-valued.  A malformed stack, missing
  runtime address/type, failed packed-field conversion, or instruction outside
  `Expr_const` is rejected rather than completed with a junk value.
-/
import WasmGemmGnaf.Wasm.Core.EventExecution
import WasmGemmGnaf.Wasm.Core.Validation.Instructions

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Remove the final stack value, retaining the prefix below it. -/
def popOne : List Val → Option (List Val × Val)
  | values =>
      match values.reverse with
      | [] => none
      | final :: reversedRetained => some (reversedRetained.reverse, final)

/-- Remove the final two stack values in source order. -/
def popTwo (values : List Val) : Option (List Val × Val × Val) := do
  match popOne values with
  | none => none
  | some (prefixAndFirst, second) =>
      match popOne prefixAndFirst with
      | none => none
      | some (retained, first) => some (retained, first, second)

/-- Split off exactly `count` final stack values. -/
def popMany (count : Nat) (values : List Val) : Option (List Val × List Val) :=
  if _h : count ≤ values.length then
    some (values.take (values.length - count), values.drop (values.length - count))
  else none

theorem popOne_eq_some {values retained : List Val} {final : Val}
    (h : popOne values = some (retained, final)) :
    values = retained ++ [final] := by
  unfold popOne at h
  cases hreverse : values.reverse with
  | nil => simp [hreverse] at h
  | cons actualFinal reversedRetained =>
      simp only [hreverse, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hreversed := congrArg List.reverse hreverse
      simpa using hreversed

theorem popTwo_eq_some {values retained : List Val} {first second : Val}
    (h : popTwo values = some (retained, first, second)) :
    values = retained ++ [first, second] := by
  unfold popTwo at h
  cases hlast : popOne values with
  | none => simp [hlast] at h
  | some lastPair =>
      rcases lastPair with ⟨prefixAndFirst, actualSecond⟩
      cases hfirst : popOne prefixAndFirst with
      | none => simp [hlast, hfirst] at h
      | some firstPair =>
          rcases firstPair with ⟨actualRetained, actualFirst⟩
          simp only [hlast, hfirst, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [popOne_eq_some hlast, popOne_eq_some hfirst]
          simp

theorem popMany_eq_some {count : Nat} {values retained removed : List Val}
    (h : popMany count values = some (retained, removed)) :
    values = retained ++ removed ∧ removed.length = count := by
  unfold popMany at h
  split at h
  next hle =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · exact (List.take_append_drop (values.length - count) values).symm
    · simp
      omega
  next hnot => simp at h

/-- Successful option-valued traversal preserves list length. -/
theorem mapM_eq_some_length {alpha beta : Type} (f : alpha → Option beta)
    {source : List alpha} {target : List beta}
    (h : source.mapM f = some target) : target.length = source.length := by
  induction source generalizing target with
  | nil =>
      simp at h
      subst target
      rfl
  | cons head tail ih =>
      cases hhead : f head with
      | none => simp [hhead] at h
      | some value =>
          cases htail : tail.mapM f with
          | none => simp [hhead, htail] at h
          | some rest =>
              simp [hhead, htail] at h
              subst target
              simp [ih htail]

/-- Traversing a replicated input with one successful deterministic conversion
replicates the converted output. -/
theorem mapM_replicate_eq {alpha beta : Type} (f : alpha → Option beta)
    {source : alpha} {target : beta} (h : f source = some target) :
    ∀ count, (List.replicate count source).mapM f =
      some (List.replicate count target)
  | 0 => rfl
  | count + 1 => by simp [List.replicate_succ, h, mapM_replicate_eq f h count]

/-- Runtime state and operand stack after one constant instruction. -/
structure ConstInstrOutput where
  state : State
  values : List Val

/-- Append a produced value to the retained stack prefix. -/
def appendValue (state : State) (retained : List Val) (value : Val) :
    ConstInstrOutput :=
  { state := state, values := retained ++ [value] }

/-- The one-result case of a source numeric result set.  Integer add, subtract,
and multiply have exactly this shape under `releasedNumerics`; retaining the
check keeps the evaluator total on every syntactic `Binop`. -/
def exactlyOne {alpha : Type} : List alpha → Option alpha
  | [value] => some value
  | _ => none

/-- Execute one instruction of the Core `Expr_const` grammar.

The operand stack is in source order: the most recently produced value is its
last element, matching `vals values ++ [.plain instruction]` in the relational
rules. -/
def evalConstInstr (state : State) (values : List Val) : Instr →
    Option ConstInstrOutput
  | .const nt literal =>
      some (appendValue state values (.num ⟨nt, literal⟩))
  | .vconst vt literal =>
      some (appendValue state values (.vec ⟨vt, literal⟩))
  | .refNull (.use (.idx index)) => do
      let deftype ← state.typeOf index
      pure (appendValue state values (.ref (.null (.use (.defd deftype)))))
  | .refNull heapType =>
      some (appendValue state values (.ref (.null heapType)))
  | .globalGet index => do
      let global ← state.globalOf index
      pure (appendValue state values global.value)
  | .refFunc index => do
      let address ← state.moduleinst.funcs[index.val]?
      pure (appendValue state values (.ref (.addr (.funcAddr address))))
  | .refI31 => do
      let (retained, value) ← popOne values
      match value with
      | .num ⟨.i32, literal⟩ =>
          pure (appendValue state retained
            (.ref (.addr (.i31 (releasedNumerics.wrap__ 32 31 literal)))))
      | _ => none
  | .externConvertAny => do
      let (retained, value) ← popOne values
      match value with
      | .ref (.null _) =>
          pure (appendValue state retained (.ref (.null (.abs .extern))))
      | .ref (.addr address) =>
          pure (appendValue state retained (.ref (.addr (.extern address))))
      | _ => none
  | .anyConvertExtern => do
      let (retained, value) ← popOne values
      match value with
      | .ref (.null _) =>
          pure (appendValue state retained (.ref (.null (.abs .any))))
      | .ref (.addr (.extern address)) =>
          pure (appendValue state retained (.ref (.addr address)))
      | _ => none
  | .binop nt op => do
      let (retained, first, second) ← popTwo values
      match first, second with
      | .num ⟨firstType, firstLiteral⟩, .num ⟨secondType, secondLiteral⟩ =>
          if hFirst : firstType = nt then
            if hSecond : secondType = nt then
              let firstLiteral' : Num_ nt := hFirst ▸ firstLiteral
              let secondLiteral' : Num_ nt := hSecond ▸ secondLiteral
              do
                let result ← exactlyOne
                  (releasedNumerics.binop_ nt op firstLiteral' secondLiteral')
                pure (appendValue state retained (.num ⟨nt, result⟩))
            else none
          else none
      | _, _ => none
  | .structNew typeIndex => do
      let deftype ← state.typeOf typeIndex
      let .struct fields ← expandDt deftype | none
      let (retained, fieldValues) ← popMany fields.toList.length values
      let packed ← (fields.toList.zip fieldValues).mapM
        (fun pair => releasedNumerics.packfield_ (fieldStorage pair.1) pair.2)
      let address := state.structinst.length
      let allocated : StructInst := { type := deftype, fields := packed }
      pure (appendValue (state.addStructInst [allocated]) retained
        (.ref (.addr (.structAddr address))))
  | .structNewDefault typeIndex => do
      let deftype ← state.typeOf typeIndex
      let .struct fields ← expandDt deftype | none
      let defaults ← fields.toList.mapM
        (fun field => default_ (fieldStorage field).unpack)
      let packed ← (fields.toList.zip defaults).mapM
        (fun pair => releasedNumerics.packfield_ (fieldStorage pair.1) pair.2)
      let address := state.structinst.length
      let allocated : StructInst := { type := deftype, fields := packed }
      pure (appendValue (state.addStructInst [allocated]) values
        (.ref (.addr (.structAddr address))))
  | .arrayNew typeIndex => do
      let (retained, elementValue, countValue) ← popTwo values
      let .num ⟨.i32, count⟩ := countValue | none
      let deftype ← state.typeOf typeIndex
      let .array field ← expandDt deftype | none
      let packedValue ← releasedNumerics.packfield_ (fieldStorage field) elementValue
      let address := state.arrayinst.length
      let allocated : ArrayInst :=
        { type := deftype, fields := List.replicate count.val packedValue }
      pure (appendValue (state.addArrayInst [allocated]) retained
        (.ref (.addr (.arrayAddr address))))
  | .arrayNewDefault typeIndex => do
      let (retained, countValue) ← popOne values
      let .num ⟨.i32, count⟩ := countValue | none
      let deftype ← state.typeOf typeIndex
      let .array field ← expandDt deftype | none
      let defaultValue ← default_ (fieldStorage field).unpack
      let packedValue ← releasedNumerics.packfield_ (fieldStorage field) defaultValue
      let address := state.arrayinst.length
      let allocated : ArrayInst :=
        { type := deftype, fields := List.replicate count.val packedValue }
      pure (appendValue (state.addArrayInst [allocated]) retained
        (.ref (.addr (.arrayAddr address))))
  | .arrayNewFixed typeIndex count => do
      let (retained, elementValues) ← popMany count.val values
      let deftype ← state.typeOf typeIndex
      let .array field ← expandDt deftype | none
      let packed ← elementValues.mapM
        (releasedNumerics.packfield_ (fieldStorage field))
      let address := state.arrayinst.length
      let allocated : ArrayInst := { type := deftype, fields := packed }
      pure (appendValue (state.addArrayInst [allocated]) retained
        (.ref (.addr (.arrayAddr address))))
  | _ => none

/-- Execute a sequence of constant instructions from a supplied operand stack. -/
def evalConstInstrs : State → List Val → List Instr →
    Option (State × List Val)
  | state, values, [] => some (state, values)
  | state, values, instruction :: rest => do
      let output ← evalConstInstr state values instruction
      evalConstInstrs output.state output.values rest

/-- Execute one Core constant expression from an empty operand stack. -/
def evalConstExpr (state : State) (expression : Expr) :
    Option (State × List Val) :=
  evalConstInstrs state [] expression.toList

/-! ## Relational soundness helpers -/

local instance constEvalExecutionAuthority : ExecutionAuthority :=
  amendedExecutionAuthority

/-- Lift one Core transition below an already evaluated value prefix. -/
theorem StepEraseA.withValuePrefix {state nextState : State}
    {source target : List AdminInstr} (retained : List Val)
    (step : StepEraseA state source nextState target) :
    StepEraseA state (vals retained ++ source) nextState
      (vals retained ++ target) := by
  cases retained with
  | nil => simpa using step
  | cons value rest =>
      simpa using
        (@Step.ctxtInstrs amendedExecutionAuthority releasedNumerics
          state nextState (value :: rest) source target [] step
          (Or.inl (by simp)))

/-- A single reduction viewed as a reflexive-transitive reduction. -/
theorem StepsEraseA.single {state nextState : State}
    {source target : List AdminInstr}
    (step : StepEraseA state source nextState target) :
    StepsEraseA state source nextState target :=
  .trans step (.refl)

/-- Concatenate two Core reduction sequences. -/
theorem StepsEraseA.append {a b c : State} {source middle target : List AdminInstr}
    (left : StepsEraseA a source b middle)
    (right : StepsEraseA b middle c target) :
    StepsEraseA a source c target := by
  induction left with
  | refl => exact right
  | trans first _ ih => exact .trans first (ih right)

/-- A literal numeric instruction is already the administrative encoding of
the value it produces, so evaluating it needs no transition. -/
theorem evalConstInstr_const_sound (state : State) (values : List Val)
    (nt : NumType) (literal : Num_ nt) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.const nt literal) = some output) :
    StepsEraseA state (vals values ++ [.plain (.const nt literal)])
      output.state (vals output.values) := by
  simp only [evalConstInstr, Option.some.injEq] at h
  subst output
  simpa [appendValue, vals_append] using
    (@Steps.refl amendedExecutionAuthority releasedNumerics
      (z := state) (is := vals (values ++ [Val.num ⟨nt, literal⟩])))

/-- Vector literals likewise are values without a transition. -/
theorem evalConstInstr_vconst_sound (state : State) (values : List Val)
    (vt : VecType) (literal : VecLit vt.toVnn) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.vconst vt literal) = some output) :
    StepsEraseA state (vals values ++ [.plain (.vconst vt literal)])
      output.state (vals output.values) := by
  simp only [evalConstInstr, Option.some.injEq] at h
  subst output
  simpa [appendValue, vals_append] using
    (@Steps.refl amendedExecutionAuthority releasedNumerics
      (z := state) (is := vals (values ++ [Val.vec ⟨vt, literal⟩])))

/-- Abstract and closed `ref.null` literals are values without a transition. -/
theorem evalConstInstr_refNull_closed_sound (state : State) (values : List Val)
    (heapType : HeapType) (hclosed : ∀ index, heapType ≠ .use (.idx index))
    (output : ConstInstrOutput)
    (h : evalConstInstr state values (.refNull heapType) = some output) :
    StepsEraseA state (vals values ++ [.plain (.refNull heapType)])
      output.state (vals output.values) := by
  cases heapType with
  | abs abstract =>
      simp only [evalConstInstr, Option.some.injEq] at h
      subst output
      simpa [appendValue, vals_append] using
        (@Steps.refl amendedExecutionAuthority releasedNumerics
          (z := state)
          (is := vals (values ++ [Val.ref (.null (.abs abstract))])))
  | use typeUse =>
      cases typeUse with
      | idx index => exact absurd rfl (hclosed index)
      | defd deftype =>
          simp only [evalConstInstr, Option.some.injEq] at h
          subst output
          simpa [appendValue, vals_append] using
            (@Steps.refl amendedExecutionAuthority releasedNumerics
              (z := state)
              (is := vals (values ++ [Val.ref (.null (.use (.defd deftype)))])))
      | recu recIndex =>
          simp only [evalConstInstr, Option.some.injEq] at h
          subst output
          simpa [appendValue, vals_append] using
            (@Steps.refl amendedExecutionAuthority releasedNumerics
              (z := state)
              (is := vals
                (values ++ [Val.ref (.null (.use (.recu recIndex)))])))

/-- Indexed `ref.null` performs exactly the authority-prescribed type lookup. -/
theorem evalConstInstr_refNull_idx_sound (state : State) (values : List Val)
    (index : TypeIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.refNull (.use (.idx index))) = some output) :
    StepsEraseA state (vals values ++ [.plain (.refNull (.use (.idx index)))])
      output.state (vals output.values) := by
  simp only [evalConstInstr] at h
  cases htype : state.typeOf index with
  | none => simp [htype] at h
  | some deftype =>
      simp [htype] at h
      subst output
      have one : StepEraseA state [.plain (.refNull (.use (.idx index)))] state
          [Ref.toAdmin (.null (.use (.defd deftype)))] :=
        .read (.refNullIdx htype)
      simpa [appendValue, vals_append] using
        StepsEraseA.single (one.withValuePrefix values)

/-- Immutable-global reads use the exact runtime global selected by the frame. -/
theorem evalConstInstr_globalGet_sound (state : State) (values : List Val)
    (index : GlobalIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.globalGet index) = some output) :
    StepsEraseA state (vals values ++ [.plain (.globalGet index)])
      output.state (vals output.values) := by
  simp only [evalConstInstr] at h
  cases hglobal : state.globalOf index with
  | none => simp [hglobal] at h
  | some global =>
      simp [hglobal] at h
      subst output
      have one : StepEraseA state [.plain (.globalGet index)] state
          [global.value.toAdmin] := .read (.globalGet hglobal)
      simpa [appendValue, vals_append] using
        StepsEraseA.single (one.withValuePrefix values)

/-- `ref.func` resolves through the active module instance. -/
theorem evalConstInstr_refFunc_sound (state : State) (values : List Val)
    (index : FuncIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.refFunc index) = some output) :
    StepsEraseA state (vals values ++ [.plain (.refFunc index)])
      output.state (vals output.values) := by
  simp only [evalConstInstr] at h
  cases hfunc : state.moduleinst.funcs[index.val]? with
  | none => simp [hfunc] at h
  | some address =>
      simp [hfunc] at h
      subst output
      have one : StepEraseA state [.plain (.refFunc index)] state
          [.addrref (.funcAddr address)] := .read (.refFunc hfunc)
      simpa [appendValue, vals_append] using
        StepsEraseA.single (one.withValuePrefix values)

theorem exactlyOne_eq_some {alpha : Type} {values : List alpha} {value : alpha}
    (h : exactlyOne values = some value) : values = [value] := by
  cases values with
  | nil => simp [exactlyOne] at h
  | cons first rest =>
      cases rest with
      | nil =>
          simp [exactlyOne] at h
          subst value
          rfl
      | cons second rest => simp [exactlyOne] at h

/-- `ref.i31` consumes the final i32 value and preserves the stack below it. -/
theorem evalConstInstr_refI31_sound (state : State) (values : List Val)
    (output : ConstInstrOutput)
    (h : evalConstInstr state values .refI31 = some output) :
    StepsEraseA state (vals values ++ [.plain .refI31])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popOne values with
  | none => simp [hpop] at h
  | some pair =>
      rcases pair with ⟨retained, value⟩
      cases value with
      | num numeric =>
          rcases numeric with ⟨nt, literal⟩
          cases nt with
          | i32 =>
              simp [hpop] at h
              subst output
              rw [popOne_eq_some hpop]
              have one : StepEraseA state
                  [constI32 literal, .plain .refI31] state
                  [.addrref (.i31 (releasedNumerics.wrap__ 32 31 literal))] :=
                .pure (.refI31 rfl)
              simpa [appendValue, vals_append] using
                StepsEraseA.single (one.withValuePrefix retained)
          | i64 => simp [hpop] at h
          | f32 => simp [hpop] at h
          | f64 => simp [hpop] at h
      | vec vector => simp [hpop] at h
      | ref reference => simp [hpop] at h

/-- `extern.convert_any` is the corresponding deterministic pure rule. -/
theorem evalConstInstr_externConvertAny_sound (state : State) (values : List Val)
    (output : ConstInstrOutput)
    (h : evalConstInstr state values .externConvertAny = some output) :
    StepsEraseA state (vals values ++ [.plain .externConvertAny])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popOne values with
  | none => simp [hpop] at h
  | some pair =>
      rcases pair with ⟨retained, value⟩
      cases value with
      | num numeric => simp [hpop] at h
      | vec vector => simp [hpop] at h
      | ref reference =>
          cases reference with
          | null heapType =>
              simp [hpop] at h
              subst output
              rw [popOne_eq_some hpop]
              have one : StepEraseA state
                  [Ref.toAdmin (.null heapType), .plain .externConvertAny] state
                  [Ref.toAdmin (.null (.abs .extern))] :=
                .pure .externConvertAnyNull
              simpa [appendValue, vals_append] using
                StepsEraseA.single (one.withValuePrefix retained)
          | addr address =>
              simp [hpop] at h
              subst output
              rw [popOne_eq_some hpop]
              have one : StepEraseA state
                  [.addrref address, .plain .externConvertAny] state
                  [.addrref (.extern address)] :=
                .pure .externConvertAnyAddr
              simpa [appendValue, vals_append] using
                StepsEraseA.single (one.withValuePrefix retained)

/-- `any.convert_extern` succeeds exactly on the two forms stated by Core. -/
theorem evalConstInstr_anyConvertExtern_sound (state : State) (values : List Val)
    (output : ConstInstrOutput)
    (h : evalConstInstr state values .anyConvertExtern = some output) :
    StepsEraseA state (vals values ++ [.plain .anyConvertExtern])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popOne values with
  | none => simp [hpop] at h
  | some pair =>
      rcases pair with ⟨retained, value⟩
      cases value with
      | num numeric => simp [hpop] at h
      | vec vector => simp [hpop] at h
      | ref reference =>
          cases reference with
          | null heapType =>
              simp [hpop] at h
              subst output
              rw [popOne_eq_some hpop]
              have one : StepEraseA state
                  [Ref.toAdmin (.null heapType), .plain .anyConvertExtern] state
                  [Ref.toAdmin (.null (.abs .any))] :=
                .pure .anyConvertExternNull
              simpa [appendValue, vals_append] using
                StepsEraseA.single (one.withValuePrefix retained)
          | addr address =>
              cases address with
              | extern underlying =>
                  simp [hpop] at h
                  subst output
                  rw [popOne_eq_some hpop]
                  have one : StepEraseA state
                      [.addrref (.extern underlying), .plain .anyConvertExtern]
                      state [.addrref underlying] :=
                    .pure .anyConvertExternAddr
                  simpa [appendValue, vals_append] using
                    StepsEraseA.single (one.withValuePrefix retained)
              | i31 value => simp [hpop] at h
              | structAddr address => simp [hpop] at h
              | arrayAddr address => simp [hpop] at h
              | funcAddr address => simp [hpop] at h
              | exnAddr address => simp [hpop] at h
              | hostAddr address => simp [hpop] at h

/-- A successfully evaluated numeric binary operation is one of the results
permitted by the pinned numeric relation. -/
theorem evalConstInstr_binop_sound (state : State) (values : List Val)
    (nt : NumType) (op : Binop) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.binop nt op) = some output) :
    StepsEraseA state (vals values ++ [.plain (.binop nt op)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popTwo values with
  | none => simp [hpop] at h
  | some triple =>
      rcases triple with ⟨retained, first, second⟩
      cases first with
      | vec vector => simp [hpop] at h
      | ref reference => simp [hpop] at h
      | num firstNumeric =>
          rcases firstNumeric with ⟨firstType, firstLiteral⟩
          cases second with
          | vec vector => simp [hpop] at h
          | ref reference => simp [hpop] at h
          | num secondNumeric =>
              rcases secondNumeric with ⟨secondType, secondLiteral⟩
              by_cases hfirst : firstType = nt
              · subst firstType
                by_cases hsecond : secondType = nt
                · subst secondType
                  cases hone : exactlyOne
                      (releasedNumerics.binop_ nt op firstLiteral secondLiteral) with
                  | none => simp [hpop, hone] at h
                  | some result =>
                      simp [hpop, hone] at h
                      subst output
                      rw [popTwo_eq_some hpop]
                      have hresults := exactlyOne_eq_some hone
                      have hmember : result ∈
                          releasedNumerics.binop_ nt op firstLiteral secondLiteral := by
                        rw [hresults]
                        simp
                      have one : StepEraseA state
                          [.plain (.const nt firstLiteral),
                            .plain (.const nt secondLiteral),
                            .plain (.binop nt op)] state
                          [.plain (.const nt result)] :=
                        .pure (.binopVal hmember)
                      simpa [appendValue, vals_append] using
                        StepsEraseA.single (one.withValuePrefix retained)
                · simp [hpop, hsecond] at h
              · simp [hpop, hfirst] at h

/-- `struct.new` performs the exact field packing and heap allocation described
by the Core state-writing rule. -/
theorem evalConstInstr_structNew_sound (state : State) (values : List Val)
    (typeIndex : TypeIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.structNew typeIndex) = some output) :
    StepsEraseA state (vals values ++ [.plain (.structNew typeIndex)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases htype : state.typeOf typeIndex with
  | none => simp [htype] at h
  | some deftype =>
      cases hexpand : expandDt deftype with
      | none => simp [htype, hexpand] at h
      | some composite =>
          cases composite with
          | func domain codomain => simp [htype, hexpand] at h
          | array field => simp [htype, hexpand] at h
          | struct fields =>
              cases hpop : popMany fields.toList.length values with
              | none => simp [htype, hexpand, hpop] at h
              | some splitValues =>
                  rcases splitValues with ⟨retained, fieldValues⟩
                  cases hpack : (fields.toList.zip fieldValues).mapM
                      (fun pair => releasedNumerics.packfield_
                        (fieldStorage pair.1) pair.2) with
                  | none => simp [htype, hexpand, hpop, hpack] at h
                  | some packed =>
                      simp [htype, hexpand, hpop, hpack] at h
                      subst output
                      have hsplit := popMany_eq_some hpop
                      rw [hsplit.1]
                      have one : StepEraseA state
                          (vals fieldValues ++ [.plain (.structNew typeIndex)])
                          (state.addStructInst
                            [{ type := deftype, fields := packed }])
                          [.addrref (.structAddr state.structinst.length)] :=
                        .structNew htype (.mk hexpand) hsplit.2.symm rfl rfl
                          hpack rfl
                      simpa [appendValue, vals_append] using
                        StepsEraseA.single (one.withValuePrefix retained)

/-- `struct.new_default` first materializes the validated field defaults and
then uses the ordinary structure allocation rule. -/
theorem evalConstInstr_structNewDefault_sound (state : State)
    (values : List Val) (typeIndex : TypeIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.structNewDefault typeIndex) = some output) :
    StepsEraseA state (vals values ++ [.plain (.structNewDefault typeIndex)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases htype : state.typeOf typeIndex with
  | none => simp [htype] at h
  | some deftype =>
      cases hexpand : expandDt deftype with
      | none => simp [htype, hexpand] at h
      | some composite =>
          cases composite with
          | func domain codomain => simp [htype, hexpand] at h
          | array field => simp [htype, hexpand] at h
          | struct fields =>
              cases hdefaults : fields.toList.mapM
                  (fun field => default_ (fieldStorage field).unpack) with
              | none => simp [htype, hexpand, hdefaults] at h
              | some defaults =>
                  cases hpack : (fields.toList.zip defaults).mapM
                      (fun pair => releasedNumerics.packfield_
                        (fieldStorage pair.1) pair.2) with
                  | none => simp [htype, hexpand, hdefaults, hpack] at h
                  | some packed =>
                      simp [htype, hexpand, hdefaults, hpack] at h
                      subst output
                      have materialize : StepEraseA state
                          [.plain (.structNewDefault typeIndex)] state
                          (vals defaults ++ [.plain (.structNew typeIndex)]) :=
                        .read (.structNewDefault htype (.mk hexpand) hdefaults)
                      have hlength : defaults.length = fields.toList.length := by
                        exact mapM_eq_some_length _ hdefaults
                      have allocate : StepEraseA state
                          (vals defaults ++ [.plain (.structNew typeIndex)])
                          (state.addStructInst
                            [{ type := deftype, fields := packed }])
                          [.addrref (.structAddr state.structinst.length)] :=
                        .structNew htype (.mk hexpand) hlength.symm rfl rfl
                          hpack rfl
                      exact StepsEraseA.append
                        (StepsEraseA.single (materialize.withValuePrefix values))
                        (by
                          simpa [appendValue, vals_append] using
                            StepsEraseA.single (allocate.withValuePrefix values))

/-- `array.new` expands the element to the requested length, then allocates
through `array.new_fixed`. -/
theorem evalConstInstr_arrayNew_sound (state : State) (values : List Val)
    (typeIndex : TypeIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.arrayNew typeIndex) = some output) :
    StepsEraseA state (vals values ++ [.plain (.arrayNew typeIndex)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popTwo values with
  | none => simp [hpop] at h
  | some triple =>
      rcases triple with ⟨retained, elementValue, countValue⟩
      cases countValue with
      | vec vector => simp [hpop] at h
      | ref reference => simp [hpop] at h
      | num numeric =>
          rcases numeric with ⟨countType, count⟩
          cases countType with
          | i64 => simp [hpop] at h
          | f32 => simp [hpop] at h
          | f64 => simp [hpop] at h
          | i32 =>
              cases htype : state.typeOf typeIndex with
              | none => simp [hpop, htype] at h
              | some deftype =>
                  cases hexpand : expandDt deftype with
                  | none => simp [hpop, htype, hexpand] at h
                  | some composite =>
                      cases composite with
                      | func domain codomain => simp [hpop, htype, hexpand] at h
                      | struct fields => simp [hpop, htype, hexpand] at h
                      | array field =>
                          cases hpack : releasedNumerics.packfield_
                              (fieldStorage field) elementValue with
                          | none => simp [hpop, htype, hexpand, hpack] at h
                          | some packedValue =>
                              simp [hpop, htype, hexpand, hpack] at h
                              subst output
                              rw [popTwo_eq_some hpop]
                              have expandElements : StepEraseA state
                                  [elementValue.toAdmin, constI32 count,
                                    .plain (.arrayNew typeIndex)] state
                                  (vals (List.replicate count.val elementValue) ++
                                    [.plain (.arrayNewFixed typeIndex count)]) :=
                                .pure .arrayNew
                              have hpacked :
                                  (List.replicate count.val elementValue).mapM
                                      (releasedNumerics.packfield_
                                        (fieldStorage field)) =
                                    some (List.replicate count.val packedValue) :=
                                mapM_replicate_eq _ hpack count.val
                              have allocate : StepEraseA state
                                  (vals (List.replicate count.val elementValue) ++
                                    [.plain (.arrayNewFixed typeIndex count)])
                                  (state.addArrayInst
                                    [{ type := deftype,
                                       fields := List.replicate count.val packedValue }])
                                  [.addrref (.arrayAddr state.arrayinst.length)] :=
                                .arrayNewFixed htype (.mk hexpand) (by simp) rfl
                                  hpacked rfl
                              have expandedRun : StepsEraseA state
                                  (vals (retained ++ [elementValue,
                                    .num ⟨.i32, count⟩]) ++
                                    [.plain (.arrayNew typeIndex)]) state
                                  (vals (retained ++
                                      List.replicate count.val elementValue) ++
                                    [.plain (.arrayNewFixed typeIndex count)]) := by
                                simpa [vals_append, List.append_assoc] using
                                  StepsEraseA.single
                                    (expandElements.withValuePrefix retained)
                              have allocatedRun : StepsEraseA state
                                  (vals (retained ++
                                      List.replicate count.val elementValue) ++
                                    [.plain (.arrayNewFixed typeIndex count)])
                                  (state.addArrayInst
                                    [{ type := deftype,
                                       fields := List.replicate count.val packedValue }])
                                  (vals (retained ++
                                    [.ref (.addr
                                      (.arrayAddr state.arrayinst.length))])) := by
                                simpa [vals_append, List.append_assoc] using
                                  StepsEraseA.single
                                    (allocate.withValuePrefix retained)
                              simpa [appendValue] using
                                StepsEraseA.append expandedRun allocatedRun

/-- `array.new_fixed` consumes exactly its declared element count and performs
the corresponding packed allocation. -/
theorem evalConstInstr_arrayNewFixed_sound (state : State)
    (values : List Val) (typeIndex : TypeIdx) (count : U32)
    (output : ConstInstrOutput)
    (h : evalConstInstr state values (.arrayNewFixed typeIndex count) =
      some output) :
    StepsEraseA state
      (vals values ++ [.plain (.arrayNewFixed typeIndex count)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popMany count.val values with
  | none => simp [hpop] at h
  | some splitValues =>
      rcases splitValues with ⟨retained, elementValues⟩
      cases htype : state.typeOf typeIndex with
      | none => simp [hpop, htype] at h
      | some deftype =>
          cases hexpand : expandDt deftype with
          | none => simp [hpop, htype, hexpand] at h
          | some composite =>
              cases composite with
              | func domain codomain => simp [hpop, htype, hexpand] at h
              | struct fields => simp [hpop, htype, hexpand] at h
              | array field =>
                  cases hpack : elementValues.mapM
                      (releasedNumerics.packfield_ (fieldStorage field)) with
                  | none => simp [hpop, htype, hexpand, hpack] at h
                  | some packed =>
                      simp [hpop, htype, hexpand, hpack] at h
                      subst output
                      have hsplit := popMany_eq_some hpop
                      rw [hsplit.1]
                      have allocate : StepEraseA state
                          (vals elementValues ++
                            [.plain (.arrayNewFixed typeIndex count)])
                          (state.addArrayInst
                            [{ type := deftype, fields := packed }])
                          [.addrref (.arrayAddr state.arrayinst.length)] :=
                        .arrayNewFixed htype (.mk hexpand) hsplit.2 rfl hpack rfl
                      simpa [appendValue, vals_append] using
                        StepsEraseA.single (allocate.withValuePrefix retained)

/-- `array.new_default` reads the field default, replicates it, and then uses
the fixed-length allocation rule. -/
theorem evalConstInstr_arrayNewDefault_sound (state : State)
    (values : List Val) (typeIndex : TypeIdx) (output : ConstInstrOutput)
    (h : evalConstInstr state values (.arrayNewDefault typeIndex) = some output) :
    StepsEraseA state
      (vals values ++ [.plain (.arrayNewDefault typeIndex)])
      output.state (vals output.values) := by
  unfold evalConstInstr at h
  cases hpop : popOne values with
  | none => simp [hpop] at h
  | some pair =>
      rcases pair with ⟨retained, countValue⟩
      cases countValue with
      | vec vector => simp [hpop] at h
      | ref reference => simp [hpop] at h
      | num numeric =>
          rcases numeric with ⟨countType, count⟩
          cases countType with
          | i64 => simp [hpop] at h
          | f32 => simp [hpop] at h
          | f64 => simp [hpop] at h
          | i32 =>
              cases htype : state.typeOf typeIndex with
              | none => simp [hpop, htype] at h
              | some deftype =>
                  cases hexpand : expandDt deftype with
                  | none => simp [hpop, htype, hexpand] at h
                  | some composite =>
                      cases composite with
                      | func domain codomain => simp [hpop, htype, hexpand] at h
                      | struct fields => simp [hpop, htype, hexpand] at h
                      | array field =>
                          cases hdefault : default_ (fieldStorage field).unpack with
                          | none => simp [hpop, htype, hexpand, hdefault] at h
                          | some defaultValue =>
                              cases hpack : releasedNumerics.packfield_
                                  (fieldStorage field) defaultValue with
                              | none =>
                                  simp [hpop, htype, hexpand, hdefault, hpack] at h
                              | some packedValue =>
                                  simp [hpop, htype, hexpand, hdefault, hpack] at h
                                  subst output
                                  rw [popOne_eq_some hpop]
                                  have materialize : StepEraseA state
                                      [constI32 count,
                                        .plain (.arrayNewDefault typeIndex)] state
                                      (vals (List.replicate count.val defaultValue) ++
                                        [.plain
                                          (.arrayNewFixed typeIndex count)]) :=
                                    .read (.arrayNewDefault htype (.mk hexpand)
                                      hdefault)
                                  have hpacked :
                                      (List.replicate count.val defaultValue).mapM
                                          (releasedNumerics.packfield_
                                            (fieldStorage field)) =
                                        some (List.replicate count.val packedValue) :=
                                    mapM_replicate_eq _ hpack count.val
                                  have allocate : StepEraseA state
                                      (vals (List.replicate count.val defaultValue) ++
                                        [.plain
                                          (.arrayNewFixed typeIndex count)])
                                      (state.addArrayInst
                                        [{ type := deftype,
                                           fields := List.replicate count.val
                                             packedValue }])
                                      [.addrref
                                        (.arrayAddr state.arrayinst.length)] :=
                                    .arrayNewFixed htype (.mk hexpand) (by simp)
                                      rfl hpacked rfl
                                  have materializedRun : StepsEraseA state
                                      (vals (retained ++
                                          [.num ⟨.i32, count⟩]) ++
                                        [.plain
                                          (.arrayNewDefault typeIndex)]) state
                                      (vals (retained ++ List.replicate
                                          count.val defaultValue) ++
                                        [.plain
                                          (.arrayNewFixed typeIndex count)]) := by
                                    simpa [vals_append, List.append_assoc] using
                                      StepsEraseA.single
                                        (materialize.withValuePrefix retained)
                                  have allocatedRun : StepsEraseA state
                                      (vals (retained ++ List.replicate
                                          count.val defaultValue) ++
                                        [.plain
                                          (.arrayNewFixed typeIndex count)])
                                      (state.addArrayInst
                                        [{ type := deftype,
                                           fields := List.replicate count.val
                                             packedValue }])
                                      (vals (retained ++
                                        [.ref (.addr (.arrayAddr
                                          state.arrayinst.length))])) := by
                                    simpa [vals_append, List.append_assoc] using
                                      StepsEraseA.single
                                        (allocate.withValuePrefix retained)
                                  simpa [appendValue] using
                                    StepsEraseA.append materializedRun allocatedRun

/-! ## Constant-grammar and sequence soundness -/

/-- Every successful executable case admitted by `Instr_const` realizes a Core
reduction sequence. -/
theorem evalConstInstr_sound_of_const {context : Context} {instruction : Instr}
    (hconst : Instr_const context instruction) (state : State)
    (values : List Val) (output : ConstInstrOutput)
    (h : evalConstInstr state values instruction = some output) :
    StepsEraseA state (vals values ++ [.plain instruction])
      output.state (vals output.values) := by
  cases hconst with
  | const _ => exact evalConstInstr_const_sound state values _ _ output h
  | vconst => exact evalConstInstr_vconst_sound state values _ _ output h
  | ref_null =>
      rename_i heapType
      cases heapType with
      | abs abstract =>
          exact evalConstInstr_refNull_closed_sound state values _
            (by simp) output h
      | use typeUse =>
          cases typeUse with
          | idx index =>
              exact evalConstInstr_refNull_idx_sound state values index output h
          | defd deftype =>
              exact evalConstInstr_refNull_closed_sound state values _
                (by simp) output h
          | recu index =>
              exact evalConstInstr_refNull_closed_sound state values _
                (by simp) output h
  | ref_i31 => exact evalConstInstr_refI31_sound state values output h
  | ref_func => exact evalConstInstr_refFunc_sound state values _ output h
  | struct_new => exact evalConstInstr_structNew_sound state values _ output h
  | struct_new_default =>
      exact evalConstInstr_structNewDefault_sound state values _ output h
  | array_new => exact evalConstInstr_arrayNew_sound state values _ output h
  | array_new_default =>
      exact evalConstInstr_arrayNewDefault_sound state values _ output h
  | array_new_fixed =>
      exact evalConstInstr_arrayNewFixed_sound state values _ _ output h
  | any_convert_extern =>
      exact evalConstInstr_anyConvertExtern_sound state values output h
  | extern_convert_any =>
      exact evalConstInstr_externConvertAny_sound state values output h
  | global_get => exact evalConstInstr_globalGet_sound state values _ output h
  | binop _ => exact evalConstInstr_binop_sound state values _ _ output h

/-- Keep a fixed instruction suffix around every transition in a reduction
sequence.  A nonempty suffix is exactly the side condition of Core's instruction
context rule; the empty case is definitional. -/
theorem StepsEraseA.withSuffix {state nextState : State}
    {source target : List AdminInstr}
    (run : StepsEraseA state source nextState target)
    (suffix : List AdminInstr) :
    StepsEraseA state (source ++ suffix) nextState (target ++ suffix) := by
  cases suffix with
  | nil => simpa using run
  | cons first rest =>
      induction run with
      | refl => exact .refl
      | trans step _ ih =>
          exact .trans
            (@Step.ctxtInstrs amendedExecutionAuthority releasedNumerics
              _ _ [] _ _ (first :: rest) step (Or.inr (by simp)))
            ih

/-- Successful execution of a list of constant instructions agrees with the
reflexive-transitive Core semantics. -/
theorem evalConstInstrs_sound_of_const {context : Context}
    (instructions : List Instr)
    (hconst : SeqAll (Instr_const context) instructions)
    (state : State) (values : List Val) (finalState : State)
    (finalValues : List Val)
    (h : evalConstInstrs state values instructions =
      some (finalState, finalValues)) :
    StepsEraseA state (vals values ++ plains instructions)
      finalState (vals finalValues) := by
  induction instructions generalizing state values with
  | nil =>
      simp [evalConstInstrs] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [plains] using
        (@Steps.refl amendedExecutionAuthority releasedNumerics
          (z := state) (is := vals values))
  | cons instruction rest ih =>
      have hinstruction : Instr_const context instruction :=
        hconst instruction (by simp)
      have hrest : SeqAll (Instr_const context) rest := by
        intro next hmember
        exact hconst next (by simp [hmember])
      simp only [evalConstInstrs] at h
      cases hone : evalConstInstr state values instruction with
      | none => simp [hone] at h
      | some output =>
          simp only [hone] at h
          have firstRun := evalConstInstr_sound_of_const hinstruction state
            values output hone
          have firstWithRest := firstRun.withSuffix (plains rest)
          have remainingRun := ih hrest output.state output.values h
          simpa [plains, List.append_assoc] using
            StepsEraseA.append firstWithRest remainingRun

/-- The expression wrapper of the executable evaluator is sound for every Core
constant expression. -/
theorem evalConstExpr_sound {context : Context} {state finalState : State}
    {expression : Expr} {values : List Val}
    (hconst : Expr_const context expression)
    (h : evalConstExpr state expression = some (finalState, values)) :
    Eval_exprEraseA state expression finalState values := by
  cases hconst with
  | mk hall =>
      apply Eval_expr.mk
      simpa [evalConstExpr, exprAdmin] using
        evalConstInstrs_sound_of_const expression.toList hall state []
          finalState values h

end WasmGemmGnaf.Wasm.Core.Exec
