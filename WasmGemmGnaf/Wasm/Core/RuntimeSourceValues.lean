import WasmGemmGnaf.Wasm.Core.RuntimeCanonicalForms
import WasmGemmGnaf.Wasm.Core.SubtypeSound
import WasmGemmGnaf.Wasm.Core.SubtypeTransport

set_option autoImplicit false

/-!
# Runtime values at source validation types

Function-body validation uses rolled/indexed source types while runtime values
carry closed allocated types.  `SourceValuesOkA` relates the two in the
ordinary way: an actual source type is closed for `Val_okA`, then admitted at
the expected source type by amended subtyping.  This is a static logical
relation; it contains no execution or progress proposition.
-/

namespace WasmGemmGnaf.Wasm.Core

/-- Pointwise closure of a source result type. -/
def Context.closResultType (context : Context) (types : List ValType) :
    List ValType := types.map context.closValType

@[simp] theorem Context.closResultType_nil (context : Context) :
    context.closResultType [] = [] := rfl

@[simp] theorem Context.closResultType_cons (context : Context)
    (type : ValType) (types : List ValType) :
    context.closResultType (type :: types) =
      context.closValType type :: context.closResultType types := rfl

/-- A valid amended value type is a subtype of itself. -/
theorem Valtype_okA.sub_refl {context : Context} {type : ValType}
    (valid : Valtype_okA context type) : Valtype_subA context type type := by
  cases valid with
  | num numeric => cases numeric; exact .num .mk
  | vec vector => cases vector; exact .vec .mk
  | @ref _ referenceType reference =>
      cases referenceType with
      | ref nullability heapType =>
          cases nullability with
          | none => exact .ref (.nonnull .refl)
          | some nullability => exact .ref (.null .refl)
  | bot => exact .bot

/-- A valid amended result type is pointwise a subtype of itself. -/
theorem Resulttype_okA.sub_refl {context : Context} {types : List ValType}
    (valid : Resulttype_okA context types) :
    Resulttype_subA context types types := by
  cases valid with
  | mk hall =>
      exact .mk rfl (fun index left right hleft hright => by
        have heq : left = right := Option.some.inj (hleft.symm.trans hright)
        subst right
        exact (hall left (List.mem_of_getElem? hleft)).sub_refl)

/-- Amended result subtyping restricts to equal prefixes. -/
theorem Resulttype_subA.take {context : Context}
    {source target : List ValType}
    (subtype : Resulttype_subA context source target) (count : Nat) :
    Resulttype_subA context (source.take count) (target.take count) := by
  cases subtype with
  | mk length pointwise =>
      apply Resulttype_subA.mk
      · simp [SeqLen₂, length]
      · intro index left right hleft hright
        rw [List.getElem?_take] at hleft hright
        split at hleft <;> simp_all
        exact pointwise index left right hleft hright

/-- Amended result subtyping restricts to equal suffixes. -/
theorem Resulttype_subA.drop {context : Context}
    {source target : List ValType}
    (subtype : Resulttype_subA context source target) (count : Nat) :
    Resulttype_subA context (source.drop count) (target.drop count) := by
  cases subtype with
  | mk length pointwise =>
      apply Resulttype_subA.mk
      · simp [SeqLen₂, length]
      · intro index left right hleft hright
        rw [List.getElem?_drop] at hleft hright
        exact pointwise (count + index) left right hleft hright

/-- Amended result subtyping is closed under list concatenation. -/
theorem Resulttype_subA.append {context : Context}
    {leftSource leftTarget rightSource rightTarget : List ValType}
    (left : Resulttype_subA context leftSource leftTarget)
    (right : Resulttype_subA context rightSource rightTarget) :
    Resulttype_subA context (leftSource ++ rightSource)
      (leftTarget ++ rightTarget) := by
  cases left with
  | mk leftLength leftPointwise =>
      cases right with
      | mk rightLength rightPointwise =>
          apply Resulttype_subA.mk
          · simp [SeqLen₂, leftLength, rightLength]
          · intro index sourceType targetType hsource htarget
            by_cases hindex : index < leftSource.length
            · have htargetIndex : index < leftTarget.length := by
                simpa [SeqLen₂, leftLength] using hindex
              rw [List.getElem?_append_left hindex] at hsource
              rw [List.getElem?_append_left htargetIndex] at htarget
              exact leftPointwise index sourceType targetType hsource htarget
            · have hsourceIndex : leftSource.length ≤ index := Nat.le_of_not_gt hindex
              have htargetIndex : leftTarget.length ≤ index := by
                simpa [SeqLen₂, leftLength] using hsourceIndex
              rw [List.getElem?_append_right hsourceIndex] at hsource
              rw [List.getElem?_append_right htargetIndex] at htarget
              have hoffset : index - leftSource.length =
                  index - leftTarget.length := by simp [SeqLen₂, leftLength]
              rw [← hoffset] at htarget
              exact rightPointwise (index - leftSource.length)
                sourceType targetType hsource htarget

namespace Exec

/-- One runtime value at a rolled source type. -/
def SourceValOkA (store : Store) (context : Context)
    (value : Val) (expectedType : ValType) : Prop :=
  ∃ actualType,
    Val_okA store value (context.closValType actualType) ∧
      Valtype_subA context actualType expectedType

/-- Runtime values typed at a rolled source result type.  `actualTypes` retain
the possibly narrower source types whose closures are the exact runtime
`Val_okA` types. -/
def SourceValuesOkA (store : Store) (context : Context)
    (values : List Val) (expectedTypes : List ValType) : Prop :=
  ∃ actualTypes,
    ValuesOkA store values (context.closResultType actualTypes) ∧
      Resulttype_subA context actualTypes expectedTypes

/-- A source-typed numeric value has the ordinary numeric canonical form. -/
theorem SourceValOkA.num_canonical {store : Store} {context : Context}
    {value : Val} {numberType : NumType}
    (typed : SourceValOkA store context value (.num numberType)) :
    ∃ literal : Num_ numberType,
      value = .num ⟨numberType, literal⟩ := by
  obtain ⟨actualType, runtimeTyped, subtype⟩ := typed
  cases subtype with
  | num numericSubtype =>
      cases numericSubtype
      exact (by
        simpa [Context.closValType, substAllValType, substValType] using
          runtimeTyped.num_canonical)
  | bot =>
      exact False.elim (Val_okA.not_bot (by
        simpa [Context.closValType, substAllValType, substValType] using
          runtimeTyped))

/-- A singleton source runtime stack is exactly one source-typed value. -/
theorem SourceValuesOkA.singleton_iff {store : Store} {context : Context}
    {values : List Val} {expectedType : ValType} :
    SourceValuesOkA store context values [expectedType] ↔
      ∃ value, values = [value] ∧
        SourceValOkA store context value expectedType := by
  constructor
  · rintro ⟨actualTypes, runtimeTyped, actualSubtype⟩
    cases actualTypes with
    | nil => cases actualSubtype with | mk length _ => simp [SeqLen₂] at length
    | cons actualType actualTypes =>
        cases actualTypes with
        | nil =>
            obtain ⟨value, hvalues, valueTyped⟩ :=
              ValuesOkA.singleton_iff.mp runtimeTyped
            subst values
            cases actualSubtype with
            | mk _ pointwise =>
                exact ⟨value, rfl, actualType, valueTyped,
                  pointwise 0 actualType expectedType (by simp) (by simp)⟩
        | cons next rest =>
            cases actualSubtype with
            | mk length _ => simp [SeqLen₂] at length
  · rintro ⟨value, rfl, actualType, valueTyped, subtype⟩
    refine ⟨[actualType], by simpa [Context.closResultType] using
      (ValuesOkA.cons valueTyped ValuesOkA.nil), ?_⟩
    exact .mk rfl (fun index left right hleft hright => by
      cases index with
      | zero =>
          simp at hleft hright
          simpa [hleft, hright] using subtype
      | succ index => simp at hleft)

/-- Exact closed runtime typing embeds into source runtime typing. -/
theorem SourceValuesOkA.of_exact {store : Store} {context : Context}
    {values : List Val} {types : List ValType}
    (valid : Resulttype_okA context types)
    (typed : ValuesOkA store values (context.closResultType types)) :
    SourceValuesOkA store context values types :=
  ⟨types, typed, valid.sub_refl⟩

/-- Source result subtyping composes with runtime source typing. -/
theorem SourceValuesOkA.sub {store : Store} {context : Context}
    {values : List Val} {sourceTypes targetTypes : List ValType}
    (typed : SourceValuesOkA store context values sourceTypes)
    (sourceValid : Resulttype_okA context sourceTypes)
    (subtype : Resulttype_subA context sourceTypes targetTypes) :
    SourceValuesOkA store context values targetTypes := by
  obtain ⟨actualTypes, runtimeTyped, actualSubtype⟩ := typed
  exact ⟨actualTypes, runtimeTyped,
    Resulttype_subA.trans sourceValid actualSubtype subtype⟩

/-- Source runtime typing transports across context changes that preserve the
type and recursive-type environments. -/
theorem SourceValuesOkA.transport {store : Store} {source target : Context}
    (typesEq : source.types = target.types)
    (recsEq : source.recs = target.recs)
    {values : List Val} {types : List ValType}
    (typed : SourceValuesOkA store source values types) :
    SourceValuesOkA store target values types := by
  obtain ⟨actualTypes, runtimeTyped, actualSubtype⟩ := typed
  have hclosure : source.closResultType actualTypes =
      target.closResultType actualTypes := by
    simp [Context.closResultType, Context.closValType,
      Context.closTypes, typesEq]
  exact ⟨actualTypes, by simpa [hclosure] using runtimeTyped,
    Resulttype_subA.transport typesEq recsEq actualSubtype⟩

/-- Empty source runtime stacks have no hidden values. -/
theorem SourceValuesOkA.nil_values {store : Store} {context : Context}
    {values : List Val} (typed : SourceValuesOkA store context values []) :
    values = [] := by
  obtain ⟨actualTypes, runtimeTyped, actualSubtype⟩ := typed
  cases actualSubtype with
  | mk length _ =>
      have hempty : actualTypes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [SeqLen₂] using length)
      subst actualTypes
      exact ValuesOkA.nil_types_iff.mp runtimeTyped

/-- Source runtime stacks split at an expected source-type boundary. -/
theorem SourceValuesOkA.split {store : Store} {context : Context}
    {values : List Val} {leftTypes rightTypes : List ValType}
    (typed : SourceValuesOkA store context values
      (leftTypes ++ rightTypes)) :
    ∃ leftValues rightValues,
      values = leftValues ++ rightValues ∧
        SourceValuesOkA store context leftValues leftTypes ∧
          SourceValuesOkA store context rightValues rightTypes := by
  obtain ⟨actualTypes, runtimeTyped, actualSubtype⟩ := typed
  let count := leftTypes.length
  have htargetLength : actualTypes.length =
      (leftTypes ++ rightTypes).length := by
    cases actualSubtype with
    | mk length _ => simpa [SeqLen₂] using length
  have hleftTarget : (leftTypes ++ rightTypes).take count = leftTypes := by
    simp [count]
  have hrightTarget : (leftTypes ++ rightTypes).drop count = rightTypes := by
    simp [count]
  have hclosed : context.closResultType actualTypes =
      context.closResultType (actualTypes.take count) ++
        context.closResultType (actualTypes.drop count) := by
    simp only [Context.closResultType, List.map_take, List.map_drop]
    exact (List.take_append_drop count
      (actualTypes.map context.closValType)).symm
  rw [hclosed] at runtimeTyped
  obtain ⟨leftValues, rightValues, hvalues, hleftRuntime,
      hrightRuntime⟩ := runtimeTyped.split
  refine ⟨leftValues, rightValues, hvalues,
    ⟨actualTypes.take count, hleftRuntime, ?_⟩,
    ⟨actualTypes.drop count, hrightRuntime, ?_⟩⟩
  · simpa [hleftTarget] using actualSubtype.take count
  · simpa [hrightTarget] using actualSubtype.drop count

/-- Concatenation of independently source-typed runtime value sequences. -/
theorem SourceValuesOkA.append {store : Store} {context : Context}
    {leftValues rightValues : List Val} {leftTypes rightTypes : List ValType}
    (left : SourceValuesOkA store context leftValues leftTypes)
    (right : SourceValuesOkA store context rightValues rightTypes) :
    SourceValuesOkA store context (leftValues ++ rightValues)
      (leftTypes ++ rightTypes) := by
  obtain ⟨leftActual, leftRuntime, leftSubtype⟩ := left
  obtain ⟨rightActual, rightRuntime, rightSubtype⟩ := right
  refine ⟨leftActual ++ rightActual, ?_, leftSubtype.append rightSubtype⟩
  simpa [Context.closResultType] using leftRuntime.append rightRuntime

end Exec
end WasmGemmGnaf.Wasm.Core
