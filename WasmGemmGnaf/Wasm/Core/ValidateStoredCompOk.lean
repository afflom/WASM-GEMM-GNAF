import WasmGemmGnaf.Wasm.Core.ValidateRolledSources

set_option autoImplicit false

/-!
# Validity of composite types from stored-type provenance

This file isolates the nonrecursive structural half of the full validator
context invariant.  Once every stored closed defined type is known valid,
`CompType.SourceA` supplies exactly the lookup provenance needed to rebuild all
composite-type validity derivations.
-/

namespace WasmGemmGnaf.Wasm.Core

namespace Context

/-- Every raw or computed-closure defined type admitted by `SourceA` is
semantically valid in that same context. -/
def StoredDeftypesOkA (C : Context) : Prop :=
  (∀ {i : Nat} {dt : DefType},
      C.types[i]? = some dt → Deftype_okA C dt) ∧
    (∀ {i : Nat} {dt : DefType},
      (closDefTypes C.types)[i]? = some dt → Deftype_okA C dt)

end Context

theorem HeapType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {ht : HeapType}
    (hsource : ht.SourceA C) : Heaptype_okA C ht := by
  cases ht with
  | abs _ => exact .abs
  | use tu =>
      apply Heaptype_okA.typeuse
      rcases hsource with hraw | hclosed
      · obtain ⟨rank, hnode⟩ := hraw
        cases hnode with
        | idx hlookup => exact .typeidx hlookup
        | defd hlookup => exact .deftype (hstored.1 hlookup)
      · obtain ⟨i, dt, htu, hlookup, hrecs⟩ := hclosed
        subst tu
        exact .deftype (hstored.2 hlookup)

theorem RefType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {rt : RefType}
    (hsource : rt.SourceA C) : Reftype_okA C rt := by
  cases rt with
  | ref _ ht => exact .mk (HeapType.SourceA.ok_of_stored hstored hsource)

theorem ValType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {t : ValType}
    (hsource : t.SourceA C) : Valtype_okA C t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref rt => exact .ref (RefType.SourceA.ok_of_stored hstored hsource)
  | bot => exact .bot

theorem StorageType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {zt : StorageType}
    (hsource : zt.SourceA C) : Storagetype_okA C zt := by
  cases zt with
  | val t => exact .val (ValType.SourceA.ok_of_stored hstored hsource)
  | pack _ => exact .pack .mk

theorem FieldType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {ft : FieldType}
    (hsource : ft.SourceA C) : Fieldtype_okA C ft := by
  cases ft with
  | mk _ zt => exact .mk (StorageType.SourceA.ok_of_stored hstored hsource)

theorem CompType.SourceA.ok_of_stored {C : Context}
    (hstored : C.StoredDeftypesOkA) {ct : CompType}
    (hsource : ct.SourceA C) : Comptype_okA C ct := by
  cases ct with
  | struct fts =>
      apply Comptype_okA.struct
      intro ft hft
      exact FieldType.SourceA.ok_of_stored hstored (hsource ft hft)
  | array ft =>
      exact .array (FieldType.SourceA.ok_of_stored hstored hsource)
  | func dom cod =>
      apply Comptype_okA.func
      · apply Resulttype_okA.mk
        intro t ht
        exact ValType.SourceA.ok_of_stored hstored (hsource.1 t ht)
      · apply Resulttype_okA.mk
        intro t ht
        exact ValType.SourceA.ok_of_stored hstored (hsource.2 t ht)

/-- Stored expansion validity follows from the already-proved rolled source
provenance and the one recursive closed-type invariant. -/
theorem Types_okA.storedCompOkA_of_storedDeftypes {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA C tds dts)
    (hstored : ({ C with types := C.types ++ dts } : Context).StoredDeftypesOkA)
    {i : Nat} {dt : DefType} {ct : CompType}
    (hlookup : dts[i]? = some dt) (hexpand : Expand dt ct) :
    Comptype_okA { C with types := C.types ++ dts } ct := by
  cases hexpand with
  | mk hexpand =>
      cases hunroll : unrollDt dt with
      | none => simp [expandDt, hunroll] at hexpand
      | some st =>
          cases st with
          | sub fin sups expanded =>
              simp [expandDt, hunroll] at hexpand
              subst expanded
              exact (hvalid.storedCompSourceA hsyn i dt hlookup hunroll).ok_of_stored
                hstored

end WasmGemmGnaf.Wasm.Core
