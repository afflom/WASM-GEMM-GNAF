import WasmGemmGnaf.Wasm.Core.ModuleFunctionTyping
import WasmGemmGnaf.Wasm.Core.Runtime

set_option autoImplicit false

/-!
# Runtime typing for function arguments and locals

This file supplies the value/local fragment of the runtime logical relation
needed by public Core progress.  It relates actual runtime values to the
ordinary amended `Val_okA` judgment and actual optional local slots to the
`SET`/`UNSET` local types produced by `Func_okA`.  No transition, progress, or
termination proposition occurs in the definitions.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Pointwise runtime typing of a value stack. -/
inductive ValuesOkA (store : Store) : List Val → List ValType → Prop where
  | nil : ValuesOkA store [] []
  | cons {value : Val} {type : ValType} {values : List Val}
      {types : List ValType} :
      Val_okA store value type →
      ValuesOkA store values types →
      ValuesOkA store (value :: values) (type :: types)

/-- The inductive runtime relation is exactly the indexed SpecTec sequence
premises used by invocation and validation. -/
theorem ValuesOkA.iff_seq {store : Store} {values : List Val}
    {types : List ValType} :
    ValuesOkA store values types ↔
      SeqLen₂ values types ∧
        SeqAll₂ (fun value type => Val_okA store value type) values types := by
  constructor
  · intro h
    induction h with
    | nil =>
        exact ⟨rfl, fun index value type hvalue _ => by
          simp at hvalue⟩
    | cons hhead htail ih =>
        refine ⟨by simp [SeqLen₂, ih.1], ?_⟩
        intro index value type hvalue htype
        cases index with
        | zero =>
            simp at hvalue htype
            subst value
            subst type
            exact hhead
        | succ index =>
            exact ih.2 index value type (by simpa using hvalue)
              (by simpa using htype)
  · rintro ⟨hlength, hall⟩
    induction values generalizing types with
    | nil =>
        have : types = [] := List.eq_nil_of_length_eq_zero (by
          simpa [SeqLen₂] using hlength.symm)
        subst types
        exact .nil
    | cons value values ih =>
        cases types with
        | nil => simp [SeqLen₂] at hlength
        | cons type types =>
            apply ValuesOkA.cons
            · exact hall 0 value type (by simp) (by simp)
            · apply ih
              · simpa [SeqLen₂] using Nat.succ.inj hlength
              · intro index tailValue tailType hvalue htype
                exact hall (index + 1) tailValue tailType
                  (by simpa [Nat.add_comm] using hvalue)
                  (by simpa [Nat.add_comm] using htype)

/-- Concatenating two independently typed value sequences preserves their
pointwise runtime types. -/
theorem ValuesOkA.append {store : Store} {leftValues rightValues : List Val}
    {leftTypes rightTypes : List ValType}
    (left : ValuesOkA store leftValues leftTypes)
    (right : ValuesOkA store rightValues rightTypes) :
    ValuesOkA store (leftValues ++ rightValues) (leftTypes ++ rightTypes) := by
  induction left with
  | nil => exact right
  | cons hhead _ ih => exact .cons hhead ih

/-- A runtime local slot is either initialized with a value of its declared
type, or absent at an ordinary `UNSET` local type. -/
inductive LocalSlotOkA (store : Store) : Option Val → LocalType → Prop where
  | set {value : Val} {type : ValType} :
      Val_okA store value type →
      LocalSlotOkA store (some value) ⟨Init.set, type⟩
  | unset {type : ValType} :
      LocalSlotOkA store none ⟨Init.unset, type⟩

/-- Pointwise runtime typing of a frame's optional local slots. -/
inductive LocalsOkA (store : Store) :
    List (Option Val) → List LocalType → Prop where
  | nil : LocalsOkA store [] []
  | cons {slot : Option Val} {type : LocalType}
      {slots : List (Option Val)} {types : List LocalType} :
      LocalSlotOkA store slot type →
      LocalsOkA store slots types →
      LocalsOkA store (slot :: slots) (type :: types)

/-- Every validation-defaultable type computes a runtime default value of
that same amended runtime type. -/
theorem default_value_typed {store : Store} {type : ValType}
    (hdefault : WasmGemmGnaf.Wasm.Core.Defaultable type) :
    ∃ value, default_ type = some value ∧ Val_okA store value type := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases hdefault with
  | mk hhas =>
      cases type with
      | num numberType =>
          cases numberType <;>
            first
              | exact ⟨_, rfl, .num .mk⟩
              | simp [ValType.hasDefault] at hhas
      | vec vectorType =>
          cases vectorType
          exact ⟨_, rfl, .vec .mk⟩
      | ref referenceType =>
          cases referenceType with
          | ref nullability heapType =>
              cases nullability with
              | none => simp [ValType.hasDefault] at hhas
              | some nullability =>
                  cases nullability
                  refine ⟨.ref (.null heapType), rfl, .ref ?_⟩
                  exact .null Heaptype_subA.refl
      | bot => simp [ValType.hasDefault] at hhas

/-- A validation-nondefaultable type computes the absent runtime local slot. -/
theorem default_eq_none_of_nondefaultable {type : ValType}
    (hdefault : WasmGemmGnaf.Wasm.Core.Nondefaultable type) :
    default_ type = none := by
  cases hdefault with
  | mk hnone =>
      cases type with
      | num numberType => simp [ValType.noDefault] at hnone
      | vec vectorType => simp [ValType.noDefault] at hnone
      | ref referenceType =>
          cases referenceType with
          | ref nullability heapType =>
              cases nullability <;> simp_all [ValType.noDefault, default_]
      | bot => simp [ValType.noDefault] at hnone

/-- The optional runtime slot computed for one validated local has exactly its
declarative `SET`/`UNSET` local type. -/
theorem local_default_typed {store : Store} {context : Context}
    {localDecl : Local} {type : LocalType}
    (hlocal : Local_okA context localDecl type) :
    LocalSlotOkA store (default_ localDecl.valtype) type := by
  cases hlocal with
  | set _ hdefault =>
      obtain ⟨value, hvalue, htyped⟩ := default_value_typed hdefault
      rw [hvalue]
      exact .set htyped
  | unset _ hdefault =>
      rw [default_eq_none_of_nondefaultable hdefault]
      exact .unset

/-- Mapping the executable default computation over a validated local list
produces a pointwise well-typed runtime local suffix. -/
theorem local_defaults_typed {store : Store} {context : Context}
    {locals : List Local} {types : List LocalType}
    (hlength : SeqLen₂ locals types)
    (htyped : SeqAll₂ (Local_okA context) locals types) :
    LocalsOkA store
      (locals.map (fun localDecl => default_ localDecl.valtype)) types := by
  induction locals generalizing types with
  | nil =>
      have : types = [] := List.eq_nil_of_length_eq_zero (by
        simpa [SeqLen₂] using hlength.symm)
      subst types
      exact .nil
  | cons localDecl locals ih =>
      cases types with
      | nil => simp [SeqLen₂] at hlength
      | cons type types =>
          apply LocalsOkA.cons
          · exact local_default_typed
              (htyped 0 localDecl type (by simp) (by simp))
          · apply ih
            · simpa [SeqLen₂] using Nat.succ.inj hlength
            · intro index tailLocal tailType hlocal htype
              exact htyped (index + 1) tailLocal tailType
                (by simpa [Nat.add_comm] using hlocal)
                (by simpa [Nat.add_comm] using htype)

/-- Runtime function arguments become initialized local slots. -/
theorem ValuesOkA.toLocals {store : Store} {values : List Val}
    {types : List ValType} (h : ValuesOkA store values types) :
    LocalsOkA store (values.map some)
      (types.map (fun type => ⟨Init.set, type⟩)) := by
  induction h with
  | nil => exact .nil
  | cons hhead _ ih => exact .cons (.set hhead) ih

/-- Concatenation for the runtime frame-local logical relation. -/
theorem LocalsOkA.append {store : Store}
    {leftSlots rightSlots : List (Option Val)}
    {leftTypes rightTypes : List LocalType}
    (left : LocalsOkA store leftSlots leftTypes)
    (right : LocalsOkA store rightSlots rightTypes) :
    LocalsOkA store (leftSlots ++ rightSlots) (leftTypes ++ rightTypes) := by
  induction left with
  | nil => exact right
  | cons hhead _ ih => exact .cons hhead ih

/-- The exact local vector installed by `Step_read/call_ref-func` is typed by
the function's amended validation context: initialized argument slots followed
by the computed defaults (or `none`) for declared locals. -/
theorem function_frame_locals_typed {store : Store} {context : Context}
    {arguments : List Val} {domain : ValTypes} {locals : List Local}
    {localTypes : List LocalType}
    (harguments : ValuesOkA store arguments domain.toList)
    (hlength : SeqLen₂ locals localTypes)
    (hlocals : SeqAll₂ (Local_okA context) locals localTypes) :
    LocalsOkA store
      (arguments.map some ++
        locals.map (fun localDecl => default_ localDecl.valtype))
      (domain.toList.map (fun type => ⟨Init.set, type⟩) ++ localTypes) :=
  harguments.toLocals.append (local_defaults_typed hlength hlocals)

end WasmGemmGnaf.Wasm.Core.Exec
