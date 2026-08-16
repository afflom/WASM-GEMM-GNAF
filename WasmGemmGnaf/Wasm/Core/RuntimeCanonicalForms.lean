import WasmGemmGnaf.Wasm.Core.RuntimeLocalsTyping

set_option autoImplicit false

/-!
# Canonical forms for amended Core runtime values

These are the ordinary canonical-form lemmas needed by runtime progress.  They
invert only the amended `Val_okA` and pointwise `ValuesOkA` judgments; no
transition, successor, progress, or termination proposition occurs in their
statements.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- A runtime value of numeric type is the corresponding numeric literal. -/
theorem Val_okA.num_canonical {store : Store} {value : Val}
    {numberType : NumType} (typed : Val_okA store value (.num numberType)) :
    ∃ literal : Num_ numberType, value = .num ⟨numberType, literal⟩ := by
  cases typed with
  | num numeric =>
      cases numeric
      exact ⟨_, rfl⟩

/-- A runtime value of vector type is the corresponding vector literal. -/
theorem Val_okA.vec_canonical {store : Store} {value : Val}
    {vectorType : VecType} (typed : Val_okA store value (.vec vectorType)) :
    ∃ literal : VecLit vectorType.toVnn,
      value = .vec ⟨vectorType, literal⟩ := by
  cases typed with
  | vec vector =>
      cases vector
      exact ⟨_, rfl⟩

/-- A runtime value of reference type is an actual runtime reference. -/
theorem Val_okA.ref_canonical {store : Store} {value : Val}
    {referenceType : RefType}
    (typed : Val_okA store value (.ref referenceType)) :
    ∃ reference : Ref,
      value = .ref reference ∧ Ref_okA store reference referenceType := by
  cases typed with
  | ref reference => exact ⟨_, rfl, reference⟩

/-- The amended bottom value type has no runtime inhabitant. -/
theorem Val_okA.not_bot {store : Store} {value : Val} :
    ¬ Val_okA store value .bot := by
  intro typed
  cases typed

/-- Inversion of one pointwise-typed runtime value. -/
theorem ValuesOkA.cons_iff {store : Store} {value : Val}
    {valueType : ValType} {values : List Val} {valueTypes : List ValType} :
    ValuesOkA store (value :: values) (valueType :: valueTypes) ↔
      Val_okA store value valueType ∧
        ValuesOkA store values valueTypes := by
  constructor
  · intro typed
    cases typed
    exact ⟨by assumption, by assumption⟩
  · rintro ⟨head, tail⟩
    exact .cons head tail

/-- Pointwise typing fixes the empty runtime value sequence. -/
theorem ValuesOkA.nil_types_iff {store : Store} {values : List Val} :
    ValuesOkA store values [] ↔ values = [] := by
  constructor
  · intro typed
    cases typed
    rfl
  · rintro rfl
    exact .nil

/-- Pointwise typing of a singleton exposes the unique runtime value. -/
theorem ValuesOkA.singleton_iff {store : Store} {values : List Val}
    {valueType : ValType} :
    ValuesOkA store values [valueType] ↔
      ∃ value, values = [value] ∧ Val_okA store value valueType := by
  constructor
  · intro typed
    cases typed with
    | cons head tail =>
        have empty : _ = [] := ValuesOkA.nil_types_iff.mp tail
        subst empty
        exact ⟨_, rfl, head⟩
  · rintro ⟨value, rfl, typed⟩
    exact .cons typed .nil

/-- Pointwise typing of two operands exposes both runtime values in order. -/
theorem ValuesOkA.pair_iff {store : Store} {values : List Val}
    {firstType secondType : ValType} :
    ValuesOkA store values [firstType, secondType] ↔
      ∃ first second, values = [first, second] ∧
        Val_okA store first firstType ∧ Val_okA store second secondType := by
  constructor
  · intro typed
    cases typed with
    | cons firstTyped tail =>
        cases tail with
        | cons secondTyped empty =>
            have hempty : _ = [] := ValuesOkA.nil_types_iff.mp empty
            subst hempty
            exact ⟨_, _, rfl, firstTyped, secondTyped⟩
  · rintro ⟨first, second, rfl, firstTyped, secondTyped⟩
    exact .cons firstTyped (.cons secondTyped .nil)

/-- Pointwise typing of three operands exposes all runtime values in order. -/
theorem ValuesOkA.triple_iff {store : Store} {values : List Val}
    {firstType secondType thirdType : ValType} :
    ValuesOkA store values [firstType, secondType, thirdType] ↔
      ∃ first second third, values = [first, second, third] ∧
        Val_okA store first firstType ∧ Val_okA store second secondType ∧
          Val_okA store third thirdType := by
  constructor
  · intro typed
    cases typed with
    | cons firstTyped tail =>
        cases tail with
        | cons secondTyped tail =>
            cases tail with
            | cons thirdTyped empty =>
                have hempty : _ = [] := ValuesOkA.nil_types_iff.mp empty
                subst hempty
                exact ⟨_, _, _, rfl, firstTyped, secondTyped, thirdTyped⟩
  · rintro ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩
    exact .cons firstTyped (.cons secondTyped (.cons thirdTyped .nil))

/-- A pointwise-typed runtime stack splits at the same boundary as its source
type list. -/
theorem ValuesOkA.split {store : Store} {values : List Val}
    {leftTypes rightTypes : List ValType}
    (typed : ValuesOkA store values (leftTypes ++ rightTypes)) :
    ∃ leftValues rightValues,
      values = leftValues ++ rightValues ∧
        ValuesOkA store leftValues leftTypes ∧
          ValuesOkA store rightValues rightTypes := by
  induction leftTypes generalizing values with
  | nil => exact ⟨[], values, rfl, .nil, by simpa using typed⟩
  | cons leftType leftTypes ih =>
      cases values with
      | nil => cases typed
      | cons value values =>
          have headAndTail := ValuesOkA.cons_iff.mp (by simpa using typed)
          obtain ⟨leftValues, rightValues, hvalues, hleft, hright⟩ :=
            ih headAndTail.2
          exact ⟨value :: leftValues, rightValues, by simp [hvalues],
            .cons headAndTail.1 hleft, hright⟩

/-- Appending a newly produced runtime value extends a typed value prefix by
its corresponding result type. -/
theorem ValuesOkA.snoc {store : Store} {values : List Val}
    {types : List ValType} {value : Val} {type : ValType}
    (typed : ValuesOkA store values types)
    (head : Val_okA store value type) :
    ValuesOkA store (values ++ [value]) (types ++ [type]) :=
  typed.append (.cons head .nil)

end WasmGemmGnaf.Wasm.Core.Exec
