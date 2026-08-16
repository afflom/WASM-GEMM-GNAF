/-
  Source provenance for the staged contexts of amended-Core module validation.

  This file replaces the legacy fragment premise on closed import projections
  with the actual `/syn` invariant checked by `Module.wf`.  It establishes
  provenance only; no subtype conclusion is stored or assumed.
-/
import WasmGemmGnaf.Wasm.Core.ValidateStoredCompOk
import WasmGemmGnaf.Wasm.Core.ValidateContextSources

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

namespace SourceTypeCompleteA

private theorem closTypes_length {C : Context}
    (h : SourceTypeCompleteA C) : C.closTypes.length = C.types.length := by
  simp only [Context.closTypes, List.length_map]
  simpa [closDefTypes] using closDefTypesAux_length [] C.types

/-- Closing a syntactic, valid heap type replaces its source index by the
corresponding literal member of the checked type-section closure. -/
theorem closHeapSource {C : Context} (h : SourceTypeCompleteA C)
    {ht : HeapType} (hsyn : ht.isSyn = true) (hok : Heaptype_okA C ht) :
    (substHeapType ht (idxVars C.closTypes.length) C.closTypes).SourceA C := by
  cases hok with
  | abs => trivial
  | typeuse htu =>
      cases htu with
      | @typeidx _ x dt hlookup =>
          have hx : x.val < C.types.length :=
            (List.getElem?_eq_some_iff.mp hlookup).1
          have hclosedLength :
              (closDefTypes C.types).length = C.types.length := by
            simpa [closDefTypes] using closDefTypesAux_length [] C.types
          have hxClosed : x.val < (closDefTypes C.types).length := by
            simpa [hclosedLength] using hx
          let closed := (closDefTypes C.types)[x.val]
          have hclosed : (closDefTypes C.types)[x.val]? = some closed :=
            List.getElem?_eq_getElem hxClosed
          have hclosLookup : C.closTypes[x.val]? = some (.defd closed) := by
            simp [Context.closTypes, List.getElem?_map, hclosed]
          have hbound : C.closTypes.length ≤ 2 ^ 32 := by
            rw [closTypes_length h, h.types]
            exact h.typesOk.outputLength_le
          have hsubst := substTypeVar_idxVars_get hbound hclosLookup
          simp only [substHeapType, substTypeUse, hsubst]
          exact Or.inr ⟨x.val, closed, rfl, hclosed, h.recs⟩
      | rec_ _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | deftype _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

/-- Reference-type form of `closHeapSource`. -/
theorem closRefSource {C : Context} (h : SourceTypeCompleteA C)
    {rt : RefType} (hsyn : rt.isSyn = true) (hok : Reftype_okA C rt) :
    (substAllRefType rt C.closTypes).SourceA C := by
  cases rt with
  | ref nul ht =>
      cases hok with
      | mk hht =>
          exact h.closHeapSource
            (by simpa [RefType.isSyn] using hsyn) hht

/-- Value-type form of `closHeapSource`; this is the provenance needed by
closed imported globals. -/
theorem closValSource {C : Context} (h : SourceTypeCompleteA C)
    {t : ValType} (hsyn : t.isSyn = true) (hok : Valtype_okA C t) :
    (C.closValType t).SourceA C := by
  cases t with
  | num nt => trivial
  | vec vt => trivial
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      cases hok with
      | ref hrt =>
          exact h.closRefSource
            (by simpa [ValType.isSyn] using hsyn) hrt

/-- Closing preserves source provenance even for semantic defined-type leaves.
Raw ranked leaves are sent to the corresponding member of `closDefTypes`, and
already-closed leaves are fixed by validated closure idempotence. -/
theorem closHeapSourceA {C : Context} (h : SourceTypeCompleteA C)
    {ht : HeapType} (hsource : ht.SourceA C) :
    (substHeapType ht (idxVars C.closTypes.length) C.closTypes).SourceA C := by
  cases ht with
  | abs a => trivial
  | use tu =>
      rcases hsource with hraw | hclosed
      · obtain ⟨rank, hnode⟩ := hraw
        cases hnode with
        | @idx x dt hlookup =>
            exact h.closHeapSource rfl (.typeuse (.typeidx hlookup))
        | @defd i dt hlookup =>
            have hlookupDts : h.dts[i]? = some dt := by
              simpa [h.types] using hlookup
            have hclosedLookup := closDefTypes_get_full
              (h.typesOk.storedFreeBefore h.syn)
              h.typesOk.outputLength_le hlookupDts
            have hclosedLookupC :
                (closDefTypes C.types)[i]? = some (C.closDefType dt) := by
              simpa [h.types, Context.closDefType, Context.closTypes] using
                hclosedLookup
            change (HeapType.use (TypeUse.defd (C.closDefType dt))).SourceA C
            exact Or.inr ⟨i, C.closDefType dt, rfl, hclosedLookupC, h.recs⟩
      · obtain ⟨i, dt, htu, hlookup, hrecs⟩ := hclosed
        subst tu
        have hmemC : dt ∈ closDefTypes C.types :=
          List.mem_of_getElem? hlookup
        have hmemDts : dt ∈ closDefTypes h.dts := by
          simpa [h.types] using hmemC
        have hfixed : C.closDefType dt = dt :=
          h.typesOk.closDefType_closed_member h.syn hmemDts
        have hfixed' :
            substDefType dt (idxVars C.closTypes.length) C.closTypes = dt := by
          simpa [Context.closDefType, substAllDefType] using hfixed
        simp only [substHeapType, substTypeUse, hfixed']
        exact Or.inr ⟨i, dt, rfl, hlookup, hrecs⟩

theorem closRefSourceA {C : Context} (h : SourceTypeCompleteA C)
    {rt : RefType} (hsource : rt.SourceA C) :
    (substAllRefType rt C.closTypes).SourceA C := by
  cases rt with
  | ref nul ht => exact h.closHeapSourceA hsource

theorem closValSourceA {C : Context} (h : SourceTypeCompleteA C)
    {t : ValType} (hsource : t.SourceA C) :
    (substAllValType t C.closTypes).SourceA C := by
  cases t with
  | num nt | vec nt | bot => trivial
  | ref rt => exact h.closRefSourceA hsource

private theorem closStorageSourceA {C : Context}
    (h : SourceTypeCompleteA C) {zt : StorageType} (hsource : zt.SourceA C) :
    (substStorageType zt (idxVars C.closTypes.length)
      C.closTypes).SourceA C := by
  cases zt with
  | pack pt => trivial
  | val t => exact h.closValSourceA hsource

private theorem closFieldSourceA {C : Context}
    (h : SourceTypeCompleteA C) {ft : FieldType} (hsource : ft.SourceA C) :
    (substFieldType ft (idxVars C.closTypes.length)
      C.closTypes).SourceA C := by
  cases ft with
  | mk m zt =>
      simpa [FieldType.SourceA, substFieldType] using
        (closStorageSourceA h hsource)

private theorem closFieldTypesSourceA {C : Context}
    (h : SourceTypeCompleteA C) : ∀ (fts : FieldTypes),
      (∀ ft ∈ FieldTypes.toList fts, ft.SourceA C) →
      ∀ ft ∈ FieldTypes.toList
        (substFieldTypes fts (idxVars C.closTypes.length) C.closTypes),
        ft.SourceA C := by
  intro fts
  cases fts with
  | nil => simp [FieldTypes.toList, substFieldTypes]
  | cons ft rest =>
      intro hsource out hout
      simp only [substFieldTypes, FieldTypes.toList, List.mem_cons] at hout
      rcases hout with rfl | hout
      · exact closFieldSourceA h
          (hsource ft (by simp [FieldTypes.toList]))
      · exact closFieldTypesSourceA h rest
          (fun candidate hc => hsource candidate (by
            simp [FieldTypes.toList, hc])) out hout

private theorem closValTypesSourceA {C : Context}
    (h : SourceTypeCompleteA C) : ∀ (ts : ValTypes),
      (∀ t ∈ ValTypes.toList ts, t.SourceA C) →
      ∀ t ∈ ValTypes.toList
        (substValTypes ts (idxVars C.closTypes.length) C.closTypes),
        t.SourceA C := by
  intro ts
  cases ts with
  | nil => simp [ValTypes.toList, substValTypes]
  | cons t rest =>
      intro hsource out hout
      simp only [substValTypes, ValTypes.toList, List.mem_cons] at hout
      rcases hout with rfl | hout
      · exact h.closValSourceA
          (hsource t (by simp [ValTypes.toList]))
      · exact closValTypesSourceA h rest
          (fun candidate hc => hsource candidate (by
            simp [ValTypes.toList, hc])) out hout

/-- Structural closing of a source-provenant composite preserves provenance.
This is the bridge needed by closed imported function and tag expansions. -/
theorem closCompSourceA {C : Context} (h : SourceTypeCompleteA C)
    {ct : CompType} (hsource : ct.SourceA C) :
    (substCompType ct (idxVars C.closTypes.length) C.closTypes).SourceA C := by
  cases ct with
  | struct fts => exact closFieldTypesSourceA h fts hsource
  | array ft => exact closFieldSourceA h hsource
  | func dom cod =>
      exact ⟨closValTypesSourceA h dom hsource.1,
        closValTypesSourceA h cod hsource.2⟩

end SourceTypeCompleteA

/-! ## Closing commutes with recursive unrolling

The import projection closes a stored defined type before later validation
expands it.  The source context exposes the same type by expanding first.  The
following structural equalities connect those two orders. -/

private theorem commuteCloseUnrollTypeUse (closed : List DefType)
    (qt : RecType) (n : Nat) (tu : TypeUse) :
    substTypeUse (closeUse closed tu) (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      closeUse closed
        (substTypeUse tu (recvTVars n) (unrollTUses qt n)) := by
  exact (commute_close_unroll_typeuse closed qt n tu).symm

private theorem commuteCloseUnrollHeapType (closed : List DefType)
    (qt : RecType) (n : Nat) (ht : HeapType) :
    substHeapType
        (substHeapType ht (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substHeapType
        (substHeapType ht (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases ht with
  | abs a => rfl
  | use tu =>
      simpa [substHeapType, closeUse] using
        commuteCloseUnrollTypeUse closed qt n tu

private theorem commuteCloseUnrollRefType (closed : List DefType)
    (qt : RecType) (n : Nat) (rt : RefType) :
    substRefType
        (substRefType rt (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substRefType
        (substRefType rt (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases rt with
  | ref nul ht =>
      simpa [substRefType] using
        commuteCloseUnrollHeapType closed qt n ht

private theorem commuteCloseUnrollValType (closed : List DefType)
    (qt : RecType) (n : Nat) (t : ValType) :
    substValType
        (substValType t (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substValType
        (substValType t (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases t with
  | num nt | vec nt | bot => rfl
  | ref rt =>
      simpa [substValType] using
        commuteCloseUnrollRefType closed qt n rt

private theorem commuteCloseUnrollStorageType (closed : List DefType)
    (qt : RecType) (n : Nat) (zt : StorageType) :
    substStorageType
        (substStorageType zt (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substStorageType
        (substStorageType zt (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases zt with
  | pack pt => rfl
  | val t =>
      simpa [substStorageType] using
        commuteCloseUnrollValType closed qt n t

private theorem commuteCloseUnrollFieldType (closed : List DefType)
    (qt : RecType) (n : Nat) (ft : FieldType) :
    substFieldType
        (substFieldType ft (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substFieldType
        (substFieldType ft (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases ft with
  | mk m zt =>
      simpa [substFieldType] using
        commuteCloseUnrollStorageType closed qt n zt

private theorem commuteCloseUnrollFieldTypes (closed : List DefType)
    (qt : RecType) (n : Nat) : ∀ (fts : FieldTypes),
    substFieldTypes
        (substFieldTypes fts (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substFieldTypes
        (substFieldTypes fts (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  intro fts
  cases fts with
  | nil => rfl
  | cons ft rest =>
      simp only [substFieldTypes]
      rw [commuteCloseUnrollFieldType closed qt n ft,
        commuteCloseUnrollFieldTypes closed qt n rest]

private theorem commuteCloseUnrollValTypes (closed : List DefType)
    (qt : RecType) (n : Nat) : ∀ (ts : ValTypes),
    substValTypes
        (substValTypes ts (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substValTypes
        (substValTypes ts (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t rest =>
      simp only [substValTypes]
      rw [commuteCloseUnrollValType closed qt n t,
        commuteCloseUnrollValTypes closed qt n rest]

private theorem commuteCloseUnrollCompType (closed : List DefType)
    (qt : RecType) (n : Nat) (ct : CompType) :
    substCompType
        (substCompType ct (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substCompType
        (substCompType ct (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases ct with
  | struct fts =>
      simpa [substCompType] using
        commuteCloseUnrollFieldTypes closed qt n fts
  | array ft =>
      simpa [substCompType] using
        commuteCloseUnrollFieldType closed qt n ft
  | func dom cod =>
      simp only [substCompType]
      rw [commuteCloseUnrollValTypes closed qt n dom,
        commuteCloseUnrollValTypes closed qt n cod]

private theorem commuteCloseUnrollTypeUses (closed : List DefType)
    (qt : RecType) (n : Nat) : ∀ (tus : TypeUses),
    substTypeUses
        (substTypeUses tus (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substTypeUses
        (substTypeUses tus (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  intro tus
  cases tus with
  | nil => rfl
  | cons tu rest =>
      simp only [substTypeUses]
      rw [show substTypeUse
            (substTypeUse tu (idxVars closed.length)
              (closed.map TypeUse.defd))
            (recvTVars n)
            (unrollTUses
              (substRecType qt (idxVars closed.length)
                (closed.map TypeUse.defd)) n) =
          substTypeUse
            (substTypeUse tu (recvTVars n) (unrollTUses qt n))
            (idxVars closed.length) (closed.map TypeUse.defd) by
          simpa [closeUse] using
            commuteCloseUnrollTypeUse closed qt n tu,
        commuteCloseUnrollTypeUses closed qt n rest]

private theorem commuteCloseUnrollSubType (closed : List DefType)
    (qt : RecType) (n : Nat) (st : SubType) :
    substSubType
        (substSubType st (idxVars closed.length)
          (closed.map TypeUse.defd))
        (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      substSubType
        (substSubType st (recvTVars n) (unrollTUses qt n))
        (idxVars closed.length) (closed.map TypeUse.defd) := by
  cases st with
  | sub fin sups ct =>
      simp only [substSubType]
      rw [commuteCloseUnrollTypeUses closed qt n sups,
        commuteCloseUnrollCompType closed qt n ct]

/-- Closing a defined type and then unrolling it is the same as unrolling the
source entry and closing the resulting subtype. -/
theorem unrollDt_close (closed : List DefType) (dt : DefType) :
    unrollDt (substAllDefType dt (closed.map TypeUse.defd)) =
      (unrollDt dt).map (fun st =>
        substSubType st (idxVars closed.length)
          (closed.map TypeUse.defd)) := by
  cases dt with
  | defd qt i =>
      cases qt with
      | recr sts =>
          simp only [substAllDefType, substDefType, List.length_map,
            substRecType]
          have hminus :
              minusRecs (idxVars closed.length) (closed.map TypeUse.defd) =
                (idxVars closed.length, closed.map TypeUse.defd) := by
            simpa using minus_idxVars (closed.map TypeUse.defd)
          rw [hminus]
          rw [unrollDt_recr_eq, unrollDt_recr_eq]
          rw [SubTypes.getElem?_substSubTypes]
          cases hget : (SubTypes.toList sts)[i]? with
          | none => simp [hget]
          | some st =>
              simp only [hget, Option.map_some,
                SubTypes.length_substSubTypes]
              have hcomm := commuteCloseUnrollSubType closed (.recr sts)
                (SubTypes.length sts) st
              simp only [substRecType] at hcomm
              rw [hminus] at hcomm
              exact congrArg some hcomm

/-- The corresponding expansion equation. -/
theorem expandDt_close (closed : List DefType) (dt : DefType) :
    expandDt (substAllDefType dt (closed.map TypeUse.defd)) =
      (expandDt dt).map (fun ct =>
        substCompType ct (idxVars closed.length)
          (closed.map TypeUse.defd)) := by
  rw [expandDt, unrollDt_close]
  cases h : unrollDt dt with
  | none => simp [h, expandDt]
  | some st =>
      cases st with
      | sub fin sups ct => simp [h, expandDt, substSubType]

namespace SourceTypeCompleteA

/-- Every expansion of an exact member of the validated closed type vector has
source provenance.  This is the missing imported function/tag context fact:
the closed expansion is forced by `expandDt_close` to be the closure of the
corresponding raw stored expansion. -/
theorem closedCompSource {C : Context} (h : SourceTypeCompleteA C)
    {i : Nat} {closed : DefType} {ct : CompType}
    (hlookup : (closDefTypes C.types)[i]? = some closed)
    (hexpand : Expand closed ct) : ct.SourceA C := by
  have hclosedLength : (closDefTypes C.types).length = C.types.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] C.types
  have hi : i < C.types.length := by
    have hiClosed := (List.getElem?_eq_some_iff.mp hlookup).1
    simpa [hclosedLength] using hiClosed
  let raw := C.types[i]
  have hrawLookup : C.types[i]? = some raw :=
    List.getElem?_eq_getElem hi
  have hcausal : StoredFreeBefore C.types := by
    intro j dt hj
    exact h.typesOk.storedFreeBefore h.syn j dt (by
      simpa [h.types] using hj)
  have hbound : C.types.length ≤ 2 ^ 32 := by
    simpa [h.types] using h.typesOk.outputLength_le
  have hexpected := closDefTypes_get_full hcausal hbound hrawLookup
  have hexpected' :
      (closDefTypes C.types)[i]? = some (C.closDefType raw) := by
    simpa [Context.closDefType, Context.closTypes] using hexpected
  have hclosedEq : closed = C.closDefType raw :=
    Option.some.inj (hlookup.symm.trans hexpected')
  subst closed
  cases hexpand with
  | mk hexpand =>
      have hcommute :
          expandDt (C.closDefType raw) =
            (expandDt raw).map (fun expanded =>
              substCompType expanded (idxVars C.closTypes.length)
                C.closTypes) := by
        simpa [Context.closDefType, Context.closTypes] using
          expandDt_close (closDefTypes C.types) raw
      rw [hcommute] at hexpand
      cases hrawExpand : expandDt raw with
      | none => simp [hrawExpand] at hexpand
      | some rawCt =>
          rw [hrawExpand] at hexpand
          simp only [Option.map_some, Option.some.injEq] at hexpand
          subst ct
          have hiBound : i < 2 ^ 32 := by omega
          let x : TypeIdx := TypeIdx.ofNat i
          have hxval : x.val = i := TypeIdx.ofNat_val_of_lt i hiBound
          have hrawLookupX : C.types[x.val]? = some raw := by
            simpa [hxval] using hrawLookup
          exact h.closCompSourceA
            (h.compSource hrawLookupX (.mk hrawExpand))

/-- Expansion provenance from the existing heap-leaf provenance package.  A
semantic defined type is either a raw stored node or an exact closed member;
the two cases are discharged by `compSource` and `closedCompSource`. -/
theorem compSourceOfDefd {C : Context} (h : SourceTypeCompleteA C)
    {dt : DefType} {ct : CompType}
    (hsource : (HeapType.use (.defd dt)).SourceA C)
    (hexpand : Expand dt ct) : ct.SourceA C := by
  rcases hsource with hraw | hclosed
  · obtain ⟨rank, hnode⟩ := hraw
    cases hnode with
    | @defd i _ hlookup =>
        have hi : i < C.types.length :=
          (List.getElem?_eq_some_iff.mp hlookup).1
        have hbound : C.types.length ≤ 2 ^ 32 := by
          simpa [h.types] using h.typesOk.outputLength_le
        have hiBound : i < 2 ^ 32 := by omega
        let x : TypeIdx := TypeIdx.ofNat i
        have hxval : x.val = i := TypeIdx.ofNat_val_of_lt i hiBound
        have hx : C.types[x.val]? = some dt := by
          simpa [hxval] using hlookup
        exact h.compSource hx hexpand
  · obtain ⟨i, closed, heq, hlookup, hrecs⟩ := hclosed
    injection heq with heq
    subst closed
    exact h.closedCompSource hlookup hexpand

end SourceTypeCompleteA

/-- Closing a syntactic valid tag type yields a source-provenant closed
defined-type leaf. -/
theorem Tagtype_okA.closHeapSource {C : Context}
    (htypes : SourceTypeCompleteA C) {jt : TagType}
    (hsyn : jt.isSyn = true) (h : Tagtype_okA C jt) :
    (HeapType.use (C.closTagType jt)).SourceA C := by
  cases h with
  | mk htu _ =>
      simpa [Context.closTagType, substAllTagType] using
        htypes.closHeapSource (ht := HeapType.use jt)
          (by simpa [HeapType.isSyn] using hsyn) (.typeuse htu)

/-- Global projection of a closed syntactic external type carries source
provenance. -/
theorem Externtype_okA.closGlobalSource {C : Context}
    (htypes : SourceTypeCompleteA C) {xt : ExternType}
    (hsyn : xt.isSyn = true) (h : Externtype_okA C xt) :
    ∀ {gt : GlobalType}, C.closExternType xt = .global gt →
      gt.valtype.SourceA C := by
  intro gt heq
  cases h with
  | tag htag => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | mem hmem => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | table htable => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | func htu hexpand => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | global hglobal =>
      rename_i raw
      cases hglobal with
      | mk hval =>
          have hvalSyn : raw.valtype.isSyn = true := by
            simpa [ExternType.isSyn, GlobalType.isSyn] using hsyn
          have hsource := htypes.closValSource hvalSyn hval
          simp only [Context.closExternType, substAllExternType,
            substExternType] at heq
          injection heq with heq
          subst gt
          exact hsource

/-- Table projection of a closed syntactic external type carries source
provenance. -/
theorem Externtype_okA.closTableSource {C : Context}
    (htypes : SourceTypeCompleteA C) {xt : ExternType}
    (hsyn : xt.isSyn = true) (h : Externtype_okA C xt) :
    ∀ {tt : TableType}, C.closExternType xt = .table tt →
      tt.elem.SourceA C := by
  intro tt heq
  cases h with
  | tag htag => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | global hglobal => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | mem hmem => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | func htu hexpand => simp [Context.closExternType, substAllExternType,
      substExternType] at heq
  | table htable =>
      rename_i raw
      cases htable with
      | mk hlim href =>
          have hrefSyn : raw.elem.isSyn = true := by
            simpa [ExternType.isSyn, TableType.isSyn] using hsyn
          have hsource := htypes.closRefSource hrefSyn href
          simp only [Context.closExternType, substAllExternType,
            substExternType] at heq
          injection heq with heq
          subst tt
          exact hsource

/-- Right-side membership inversion for the length-plus-pointwise sequence
encoding used by the declarative module rules. -/
theorem seqAll₂_right_mem {A B : Type} {R : A → B → Prop}
    {as : List A} {bs : List B} (hlen : SeqLen₂ as bs)
    (hall : SeqAll₂ R as bs) {b : B} (hb : b ∈ bs) :
    ∃ a ∈ as, R a b := by
  obtain ⟨i, hib⟩ := List.getElem?_of_mem hb
  have hiB : i < bs.length := (List.getElem?_eq_some_iff.mp hib).1
  have hiA : i < as.length := by simpa [SeqLen₂, hlen] using hiB
  let a := as[i]
  have hia : as[i]? = some a := List.getElem?_eq_getElem hiA
  exact ⟨a, List.mem_of_getElem? hia, hall i a b hia hib⟩

/-- Imported external-type validity stripped of its deterministically closed
result value. -/
theorem Import_okA.extern_ok {C : Context} {i : Import} {xt : ExternType}
    (h : Import_okA C i xt) : Externtype_okA C i.externtype := by
  cases h with
  | mk h => exact h

theorem imports_extern_ok {C : Context} {is : List Import}
    {xts : List ExternType} (hlen : SeqLen₂ is xts)
    (hall : SeqAll₂ (Import_okA C) is xts) :
    SeqAll (fun i : Import => Externtype_okA C i.externtype) is := by
  intro i hi
  obtain ⟨k, hik⟩ := List.getElem?_of_mem hi
  have hkI : k < is.length := (List.getElem?_eq_some_iff.mp hik).1
  have hkX : k < xts.length := by simpa [SeqLen₂, hlen] using hkI
  let xt := xts[k]
  have hkxt : xts[k]? = some xt := List.getElem?_eq_getElem hkX
  exact Validate.Import_okA.extern_ok (hall k i xt hik hkxt)

/-- A defined function result type is a raw stored entry selected by that
function's source type index. -/
theorem funcs_type_lookup_source {C : Context} {fs : List Func}
    {dts : List DefType} (hlen : SeqLen₂ fs dts)
    (hall : SeqAll₂ (Func_okA C) fs dts) {dt : DefType}
    (hdt : dt ∈ dts) :
    ∃ x : TypeIdx, C.types[x.val]? = some dt := by
  obtain ⟨f, hf, hok⟩ := seqAll₂_right_mem hlen hall hdt
  cases hok with
  | mk hlookup _ _ _ _ => exact ⟨f.typeidx, hlookup⟩

/-- Raw function results inherit both heap-leaf and expansion provenance from
the checked type section. -/
theorem funcs_source {C : Context} (htypes : SourceTypeCompleteA C)
    {fs : List Func} {dts : List DefType} (hlen : SeqLen₂ fs dts)
    (hall : SeqAll₂ (Func_okA C) fs dts) {dt : DefType}
    (hdt : dt ∈ dts) :
    (HeapType.use (.defd dt)).SourceA C ∧
      ∀ {ct : CompType}, Expand dt ct → ct.SourceA C := by
  obtain ⟨x, hx⟩ := funcs_type_lookup_source hlen hall hdt
  exact ⟨htypes.defdSource hx, fun hexpand => htypes.compSource hx hexpand⟩

/-- Output tag types of a syntactic declarative tag list carry the closed
heap-leaf provenance created by `closTagType`. -/
theorem tags_source {C : Context} (htypes : SourceTypeCompleteA C)
    {ts : List Tag} {jts : List TagType} (hsyn : ts.all Tag.isSyn = true)
    (hlen : SeqLen₂ ts jts) (hall : SeqAll₂ (Tag_okA C) ts jts) :
    ∀ jt ∈ jts, (HeapType.use jt).SourceA C := by
  intro jt hjt
  obtain ⟨t, ht, hok⟩ := seqAll₂_right_mem hlen hall hjt
  cases hok with
  | mk htag =>
      have htSyn := List.all_eq_true.mp hsyn t ht
      exact Validate.Tagtype_okA.closHeapSource htypes
        (by simpa [Tag.isSyn] using htSyn) htag

/-- A source-provenant tag type exposes source-provenant parameters whenever
its declarative expansion is a function with empty result. -/
theorem SourceTypeCompleteA.tagDomSource {C : Context}
    (htypes : SourceTypeCompleteA C) {jt : TagType} {dt : DefType}
    {dom : ValTypes} (hsource : (HeapType.use jt).SourceA C)
    (hasDef : asDefType jt = some dt)
    (hexpand : Expand dt (.func dom .nil)) :
    ResultSourceA C (ValTypes.toList dom) := by
  cases jt with
  | idx x => simp [asDefType] at hasDef
  | recu i => simp [asDefType] at hasDef
  | defd actual =>
      simp only [asDefType, Option.some.injEq] at hasDef
      subst actual
      exact (htypes.compSourceOfDefd hsource hexpand).1

/-- Output global types of a syntactic declarative global list carry source
provenance. -/
theorem globals_source {C : Context} {gs : List Global}
    {gts : List GlobalType} (hsyn : gs.all Global.isSyn = true)
    (hlen : SeqLen₂ gs gts) (hall : SeqAll₂ (Global_okA C) gs gts) :
    ∀ gt ∈ gts, gt.valtype.SourceA C := by
  intro gt hgt
  obtain ⟨g, hg, hok⟩ := seqAll₂_right_mem hlen hall hgt
  cases hok with
  | mk hglobal _ =>
      cases hglobal with
      | mk hval =>
          apply hval.sourceA_of_syn
          have hgSyn := List.all_eq_true.mp hsyn g hg
          rw [Global.isSyn, Bool.and_eq_true] at hgSyn
          simpa [GlobalType.isSyn] using hgSyn.1

/-- The staged `Globals_okA` fold changes only the `GLOBALS` component, so
source provenance transports back to the stage's initial type environment. -/
theorem Globals_okA.source {C : Context} {gs : List Global}
    {gts : List GlobalType} (htypes : SourceTypeCompleteA C)
    (hsyn : gs.all Global.isSyn = true) (h : Globals_okA C gs gts) :
    ∀ gt ∈ gts, gt.valtype.SourceA C := by
  induction h with
  | empty =>
      intro gt hgt
      simp at hgt
  | @cons C g gs gt gts hhead htail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      intro candidate hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · cases hhead with
        | mk hglobal _ =>
            cases hglobal with
            | mk hval =>
                apply hval.sourceA_of_syn
                rw [Global.isSyn, Bool.and_eq_true] at hsyn
                simpa [GlobalType.isSyn] using hsyn.1.1
      · have hsame : SameTypeEnv C
            (Context.append C { globals := [gt] }) := by
          simp [SameTypeEnv, Context.append]
        have htypesTail := htypes.transport hsame
        exact (ih htypesTail hsyn.2 candidate hc).of_types_eq
          hsame.1.symm hsame.2.symm

/-- Output table types of a syntactic declarative table list carry source
provenance. -/
theorem tables_source {C : Context} {ts : List Table}
    {tts : List TableType} (hsyn : ts.all Table.isSyn = true)
    (hlen : SeqLen₂ ts tts) (hall : SeqAll₂ (Table_okA C) ts tts) :
    ∀ tt ∈ tts, tt.elem.SourceA C := by
  intro tt htt
  obtain ⟨t, ht, hok⟩ := seqAll₂_right_mem hlen hall htt
  cases hok with
  | mk htable _ =>
      cases htable with
      | mk _ href =>
          apply href.sourceA_of_syn
          have htSyn := List.all_eq_true.mp hsyn t ht
          rw [Table.isSyn, Bool.and_eq_true] at htSyn
          simpa [TableType.isSyn] using htSyn.1

/-- Output element types of a syntactic declarative element list carry source
provenance. -/
theorem elems_source {C : Context} {es : List Elem}
    {rts : List ElemType} (hsyn : es.all Elem.isSyn = true)
    (hlen : SeqLen₂ es rts) (hall : SeqAll₂ (Elem_okA C) es rts) :
    ∀ rt ∈ rts, rt.SourceA C := by
  intro rt hrt
  obtain ⟨e, he, hok⟩ := seqAll₂_right_mem hlen hall hrt
  cases hok with
  | mk href _ _ =>
      apply href.sourceA_of_syn
      have heSyn := List.all_eq_true.mp hsyn e he
      rw [Elem.isSyn, Bool.and_eq_true] at heSyn
      have hhead := heSyn.1
      rw [Bool.and_eq_true] at hhead
      exact hhead.1

/-- The external-type list in `Module_okA` is definitionally determined by
its import list; this fact does not require the legacy fragment. -/
theorem imports_types_eq_of_isSyn {C : Context} :
    ∀ (is : List Import) (xts : List ExternType),
      is.length = xts.length → SeqAll₂ (Import_okA C) is xts →
      xts = is.map (fun i => C.closExternType i.externtype) := by
  intro is
  induction is with
  | nil =>
      intro xts hlen hall
      cases xts with
      | nil => rfl
      | cons xt xts => simp at hlen
  | cons i is ih =>
      intro xts hlen hall
      cases xts with
      | nil => simp at hlen
      | cons xt xts =>
          have hhead := hall 0 i xt rfl rfl
          have htail : SeqAll₂ (Import_okA C) is xts := by
            intro j a b ha hb
            exact hall (j + 1) a b (by simpa using ha) (by simpa using hb)
          have hrest := ih xts (by simpa using hlen) htail
          have hxt : xt = C.closExternType i.externtype := by
            cases hhead with
            | mk _ => rfl
          rw [List.map_cons, ← hrest, hxt]

/-- Every imported tag projected from a syntactic, valid import list carries a
source-provenant closed function heap leaf. -/
theorem tags_closExternType_source {C : Context}
    (htypes : SourceTypeCompleteA C) : ∀ (is : List Import),
      is.all Import.isSyn = true →
      SeqAll (fun i : Import => Externtype_okA C i.externtype) is →
      ∀ jt ∈ ExternType.tags
        (is.map (fun i => C.closExternType i.externtype)),
        (HeapType.use jt).SourceA C := by
  intro is
  induction is with
  | nil =>
      intro hsyn hall jt hjt
      simp [ExternType.tags] at hjt
  | cons i is ih =>
      intro hsyn hall jt hjt
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      have hiOk : Externtype_okA C i.externtype := hall i (by simp)
      have htail :
          SeqAll (fun j : Import => Externtype_okA C j.externtype) is := by
        intro j hj
        exact hall j (by simp [hj])
      cases hxt : i.externtype with
      | tag raw =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tags,
            List.mem_cons] at hjt
          rw [hxt] at hiOk
          rcases hjt with rfl | hjt
          · cases hiOk with
            | tag htag =>
                have hrawSyn : raw.isSyn = true := by
                  simpa [Import.isSyn, hxt, ExternType.isSyn] using hsyn.1
                exact Validate.Tagtype_okA.closHeapSource
                  htypes hrawSyn htag
          · exact ih hsyn.2 htail jt hjt
      | global gt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tags] at hjt
          exact ih hsyn.2 htail jt hjt
      | mem mt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tags] at hjt
          exact ih hsyn.2 htail jt hjt
      | table tt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tags] at hjt
          exact ih hsyn.2 htail jt hjt
      | func tu =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tags] at hjt
          exact ih hsyn.2 htail jt hjt

/-- Every imported global projected from a syntactic, valid import list has a
source-provenant value type. -/
theorem globals_closExternType_source {C : Context}
    (htypes : SourceTypeCompleteA C) : ∀ (is : List Import),
      is.all Import.isSyn = true →
      SeqAll (fun i : Import => Externtype_okA C i.externtype) is →
      ∀ gt ∈ ExternType.globals
        (is.map (fun i => C.closExternType i.externtype)),
        gt.valtype.SourceA C := by
  intro is
  induction is with
  | nil =>
      intro hsyn hall gt hgt
      simp [ExternType.globals] at hgt
  | cons i is ih =>
      intro hsyn hall gt hgt
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      have hiOk : Externtype_okA C i.externtype := hall i (by simp)
      have htail :
          SeqAll (fun j : Import => Externtype_okA C j.externtype) is := by
        intro j hj
        exact hall j (by simp [hj])
      cases hxt : i.externtype with
      | tag jt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.globals] at hgt
          exact ih hsyn.2 htail gt hgt
      | global raw =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.globals,
            List.mem_cons] at hgt
          rcases hgt with rfl | hgt
          · exact Validate.Externtype_okA.closGlobalSource
              htypes hsyn.1 hiOk (by
                simp [hxt, Context.closExternType, substAllExternType,
                  substExternType])
          · exact ih hsyn.2 htail gt hgt
      | mem mt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.globals] at hgt
          exact ih hsyn.2 htail gt hgt
      | table tt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.globals] at hgt
          exact ih hsyn.2 htail gt hgt
      | func tu =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.globals] at hgt
          exact ih hsyn.2 htail gt hgt

/-- Every imported table projected from a syntactic, valid import list has a
source-provenant element reference type. -/
theorem tables_closExternType_source {C : Context}
    (htypes : SourceTypeCompleteA C) : ∀ (is : List Import),
      is.all Import.isSyn = true →
      SeqAll (fun i : Import => Externtype_okA C i.externtype) is →
      ∀ tt ∈ ExternType.tables
        (is.map (fun i => C.closExternType i.externtype)),
        tt.elem.SourceA C := by
  intro is
  induction is with
  | nil =>
      intro hsyn hall tt htt
      simp [ExternType.tables] at htt
  | cons i is ih =>
      intro hsyn hall tt htt
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      have hiOk : Externtype_okA C i.externtype := hall i (by simp)
      have htail :
          SeqAll (fun j : Import => Externtype_okA C j.externtype) is := by
        intro j hj
        exact hall j (by simp [hj])
      cases hxt : i.externtype with
      | tag jt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tables] at htt
          exact ih hsyn.2 htail tt htt
      | global gt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tables] at htt
          exact ih hsyn.2 htail tt htt
      | mem mt =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tables] at htt
          exact ih hsyn.2 htail tt htt
      | table raw =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tables,
            List.mem_cons] at htt
          rcases htt with rfl | htt
          · exact Validate.Externtype_okA.closTableSource
              htypes hsyn.1 hiOk (by
                simp [hxt, Context.closExternType, substAllExternType,
                  substExternType])
          · exact ih hsyn.2 htail tt htt
      | func tu =>
          simp only [List.map_cons, hxt, Context.closExternType,
            substAllExternType, substExternType, ExternType.tables] at htt
          exact ih hsyn.2 htail tt htt

/-- Every defined type returned by `$funcsxt` from syntactic closed imports is
an entry of the context's computed closed type section.  The legacy
fragment-completeness proof used `Import.frag` here, but only its `/syn`
consequence was relevant. -/
theorem funcsXt_closExternType_mem_of_isSyn (C : Context) :
    ∀ (is : List Import) (dts : List DefType),
      is.all Import.isSyn = true →
      funcsXt (is.map (fun i => C.closExternType i.externtype)) = some dts →
      ∀ dt ∈ dts, TypeUse.defd dt ∈ C.closTypes := by
  intro is
  induction is with
  | nil =>
      intro dts _ hfx dt hdt
      have hdts : dts = [] := by
        have h' : (some [] : Option (List DefType)) = some dts := hfx
        injection h' with h'
        exact h'.symm
      subst dts
      simp at hdt
  | cons i is ih =>
      intro dts hsyn hfx dt hdt
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      have hiSyn : i.externtype.isSyn = true := hsyn.1
      rw [List.map_cons] at hfx
      cases hxt : i.externtype with
      | tag jt =>
          rw [hxt] at hfx
          exact ih dts hsyn.2 hfx dt hdt
      | global gt =>
          rw [hxt] at hfx
          exact ih dts hsyn.2 hfx dt hdt
      | mem mt =>
          rw [hxt] at hfx
          exact ih dts hsyn.2 hfx dt hdt
      | table tt =>
          rw [hxt] at hfx
          exact ih dts hsyn.2 hfx dt hdt
      | func tu =>
          rw [hxt] at hiSyn
          cases tu with
          | recu _ =>
              exact absurd hiSyn (by simp [ExternType.isSyn, TypeUse.isSyn])
          | defd _ =>
              exact absurd hiSyn (by simp [ExternType.isSyn, TypeUse.isSyn])
          | idx x =>
              rw [hxt] at hfx
              have hcl :
                  C.closExternType (ExternType.func (.idx x)) =
                    ExternType.func
                      (substTypeVar (.idx x) (idxVars C.closTypes.length)
                        C.closTypes) := rfl
              rw [hcl, funcsXt] at hfx
              cases hasd :
                  asDefType
                    (substTypeVar (.idx x) (idxVars C.closTypes.length)
                      C.closTypes) with
              | none =>
                  rw [hasd] at hfx
                  exact absurd hfx (by cases funcsXt _ <;> simp)
              | some dt₀ =>
                  cases hrest :
                      funcsXt
                        (is.map (fun i => C.closExternType i.externtype)) with
                  | none =>
                      rw [hasd, hrest] at hfx
                      exact absurd hfx (by simp)
                  | some rest =>
                      rw [hasd, hrest] at hfx
                      have hdtsEq : dt₀ :: rest = dts := by
                        have h' :
                            (some (dt₀ :: rest) : Option (List DefType)) =
                              some dts := hfx
                        injection h' with h'
                      subst dts
                      have htu :
                          substTypeVar (.idx x)
                              (idxVars C.closTypes.length) C.closTypes =
                            .defd dt₀ := by
                        cases hs :
                            substTypeVar (.idx x)
                              (idxVars C.closTypes.length) C.closTypes with
                        | idx y =>
                            rw [hs] at hasd
                            exact absurd hasd (by simp [asDefType])
                        | recu n =>
                            rw [hs] at hasd
                            exact absurd hasd (by simp [asDefType])
                        | defd d =>
                            rw [hs] at hasd
                            simp only [asDefType, Option.some.injEq] at hasd
                            rw [hasd]
                      rcases List.mem_cons.mp hdt with rfl | hrestMem
                      · rcases substTypeVar_mem_or (.idx x)
                            (idxVars C.closTypes.length) C.closTypes with
                          hmem | heq
                        · rwa [htu] at hmem
                        · rw [htu] at heq
                          exact absurd heq (by simp [TypeVar.toTypeUse])
                      · exact ih rest hsyn.2 hrest dt hrestMem

/-- A function projection obtained from syntactic closed imports carries the
literal closed-source provenance used by the source-restricted subtype
decision theorem. -/
theorem HeapType.sourceA_of_funcsXt_closExternType
    {C : Context} (hrecs : C.recs = []) {is : List Import}
    (hsyn : is.all Import.isSyn = true) {dts : List DefType}
    (hfuncs : funcsXt
      (is.map (fun i => C.closExternType i.externtype)) = some dts)
    {dt : DefType} (hdt : dt ∈ dts) :
    (HeapType.use (.defd dt)).SourceA C := by
  have hmem : TypeUse.defd dt ∈ C.closTypes :=
    funcsXt_closExternType_mem_of_isSyn C is dts hsyn hfuncs dt hdt
  obtain ⟨closed, hclosed, heq⟩ := List.mem_map.mp hmem
  injection heq with heq
  subst closed
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hclosed
  exact Or.inr ⟨i, dt, rfl, hi, hrecs⟩

/-- Every expansion of a function type projected from syntactic imports has
source-provenant parameter/result leaves. -/
theorem SourceTypeCompleteA.funcsXtCompSource
    {C : Context} (htypes : SourceTypeCompleteA C) {is : List Import}
    (hsyn : is.all Import.isSyn = true) {dts : List DefType}
    (hfuncs : funcsXt
      (is.map (fun i => C.closExternType i.externtype)) = some dts)
    {dt : DefType} (hdt : dt ∈ dts) {ct : CompType}
    (hexpand : Expand dt ct) : ct.SourceA C := by
  exact htypes.compSourceOfDefd
    (HeapType.sourceA_of_funcsXt_closExternType htypes.recs hsyn hfuncs hdt)
    hexpand

/-- The first staged context existentially exposed by every syntactic amended
module derivation carries the exact checked-type and heap-source packages used
by source-restricted instruction completeness. -/
theorem Module_okA.stageSource {m : Module} {mt : ModuleType}
    (hsyn : m.isSyn = true) (hmod : Module_okA m mt) :
    ∃ (C C' : Context), ∃ (_ : SourceTypeCompleteA C),
      ∃ (_ : SourceTypeCompleteA C'), C.SourceA ∧ C'.SourceA := by
  cases hmod with
  | @mk C C' dts' xtsI xtsE jts gts mts tts dts oks rts nms
      jtsI gtsI mtsI ttsI dtsI xs htypes himpLen himp htagLen htags
      hglobals hmemLen hmems htableLen htables hfuncLen hfuncs hdataLen
      hdatas helemLen helems hstart hexportLen hexports hdisjoint hC hC'
      hxs hjtsI hgtsI hmtsI httsI hdtsI =>
      simp only [Module.isSyn, Bool.and_eq_true] at hsyn
      rcases hsyn with
        ⟨⟨⟨⟨⟨⟨⟨htypesSyn, himportsSyn⟩, htagsSyn⟩,
          hglobalsSyn⟩, htablesSyn⟩, hfuncsSyn⟩, hdatasSyn⟩,
          helemsSyn⟩
      let B : Context := { Context.empty with types := dts' }
      have htypesB : SourceTypeCompleteA B := {
        tds := m.types
        dts := dts'
        syn := htypesSyn
        typesOk := htypes
        types := rfl
        recs := rfl
      }
      have hC'types : C'.types = dts' := by
        rw [hC']
      have hC'recs : C'.recs = [] := by
        rw [hC']
      have hCtypes : C.types = dts' := by
        rw [hC, hC']
        simp [Context.append]
      have hCrecs : C.recs = [] := by
        rw [hC, hC']
        simp [Context.append]
      have htypesC' : SourceTypeCompleteA C' := {
        tds := m.types
        dts := dts'
        syn := htypesSyn
        typesOk := htypes
        types := hC'types
        recs := hC'recs
      }
      have htypesC : SourceTypeCompleteA C := {
        tds := m.types
        dts := dts'
        syn := htypesSyn
        typesOk := htypes
        types := hCtypes
        recs := hCrecs
      }
      have hBC' : SameTypeEnv B C' := by
        constructor
        · simpa [B] using hC'types.symm
        · change [] = C'.recs
          exact hC'recs.symm
      have hCC' : SameTypeEnv C C' :=
        ⟨hCtypes.trans hC'types.symm, hCrecs.trans hC'recs.symm⟩
      have hBC : SameTypeEnv B C :=
        ⟨by simpa [B] using hCtypes.symm,
          by change [] = C.recs; exact hCrecs.symm⟩
      have hC'C : SameTypeEnv C' C := hCC'.symm
      have himpOk :
          SeqAll (fun i : Import => Externtype_okA B i.externtype)
            m.imports :=
        imports_extern_ok himpLen himp
      have hxtsEq :
          xtsI = m.imports.map
            (fun i => B.closExternType i.externtype) :=
        imports_types_eq_of_isSyn m.imports xtsI himpLen himp
      have hdtsIClosed : funcsXt
          (m.imports.map (fun i => B.closExternType i.externtype)) =
            some dtsI := by
        rw [← hxtsEq]
        exact hdtsI
      have himpGlobalsB :
          ∀ gt ∈ gtsI, gt.valtype.SourceA B := by
        rw [hgtsI, hxtsEq]
        exact globals_closExternType_source htypesB m.imports
          himportsSyn himpOk
      have himpTagsB :
          ∀ jt ∈ jtsI, (HeapType.use jt).SourceA B := by
        rw [hjtsI, hxtsEq]
        exact tags_closExternType_source htypesB m.imports
          himportsSyn himpOk
      have himpTablesB :
          ∀ tt ∈ ttsI, tt.elem.SourceA B := by
        rw [httsI, hxtsEq]
        exact tables_closExternType_source htypesB m.imports
          himportsSyn himpOk
      have hdefTagsC' :
          ∀ jt ∈ jts, (HeapType.use jt).SourceA C' :=
        tags_source htypesC' htagsSyn htagLen htags
      have hdefGlobalsC' :
          ∀ gt ∈ gts, gt.valtype.SourceA C' :=
        Globals_okA.source htypesC' hglobalsSyn hglobals
      have hdefTablesC' :
          ∀ tt ∈ tts, tt.elem.SourceA C' :=
        tables_source htablesSyn htableLen htables
      have hElemsC : ∀ rt ∈ rts, rt.SourceA C :=
        elems_source helemsSyn helemLen helems
      have hC'Funcs : C'.funcs = dtsI ++ dts := by
        rw [hC']
      have hC'Globals : C'.globals = gtsI := by
        rw [hC']
      have hC'Source : C'.SourceA := by
        constructor
        · intro x dt ct hx he
          exact htypesC'.compSource hx he
        · intro x dt ct hx he
          have hmem : dt ∈ dtsI ++ dts := by
            rw [hC'Funcs] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact (htypesB.funcsXtCompSource himportsSyn hdtsIClosed
                himp he).of_types_eq hBC'.1 hBC'.2
          · exact CompType.SourceA.of_types_eq hCC'.1 hCC'.2
              ((funcs_source htypesC hfuncLen hfuncs hdef).2 he)
        · intro x dt hx
          have hmem : dt ∈ dtsI ++ dts := by
            rw [hC'Funcs] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact (HeapType.sourceA_of_funcsXt_closExternType
                htypesB.recs himportsSyn hdtsIClosed himp).of_types_eq
              hBC'.1 hBC'.2
          · exact HeapType.SourceA.of_types_eq hCC'.1 hCC'.2
              (funcs_source htypesC hfuncLen hfuncs hdef).1
        · intro x jt dt dom hx hj he
          rw [hC'] at hx
          simp at hx
        · intro x gt hx
          have hmem : gt ∈ gtsI := by
            rw [hC'Globals] at hx
            exact List.mem_of_getElem? hx
          exact (himpGlobalsB gt hmem).of_types_eq hBC'.1 hBC'.2
        · intro x tt hx
          rw [hC'] at hx
          simp at hx
        · intro x rt hx
          rw [hC'] at hx
          simp at hx
        · intro x lt hx
          rw [hC'] at hx
          simp at hx
        · intro x ts hx
          rw [hC'] at hx
          simp at hx
        · intro ts hx
          rw [hC'] at hx
          simp at hx
      have hCFuncs : C.funcs = dtsI ++ dts := by
        rw [hC, hC']
        simp [Context.append]
      have hCTags : C.tags = jtsI ++ jts := by
        rw [hC, hC']
        simp [Context.append]
      have hCGlobals : C.globals = gtsI ++ gts := by
        rw [hC, hC']
        simp [Context.append]
      have hCTables : C.tables = ttsI ++ tts := by
        rw [hC, hC']
        simp [Context.append]
      have hCElems : C.elems = rts := by
        rw [hC, hC']
        simp [Context.append]
      have hCSource : C.SourceA := by
        constructor
        · intro x dt ct hx he
          exact htypesC.compSource hx he
        · intro x dt ct hx he
          have hmem : dt ∈ dtsI ++ dts := by
            rw [hCFuncs] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact CompType.SourceA.of_types_eq hBC.1 hBC.2
              (htypesB.funcsXtCompSource himportsSyn hdtsIClosed himp he)
          · exact (funcs_source htypesC hfuncLen hfuncs hdef).2 he
        · intro x dt hx
          have hmem : dt ∈ dtsI ++ dts := by
            rw [hCFuncs] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact HeapType.SourceA.of_types_eq hBC.1 hBC.2
              (HeapType.sourceA_of_funcsXt_closExternType
                htypesB.recs himportsSyn hdtsIClosed himp)
          · exact (funcs_source htypesC hfuncLen hfuncs hdef).1
        · intro x jt dt dom hx hj he
          have hmem : jt ∈ jtsI ++ jts := by
            rw [hCTags] at hx
            exact List.mem_of_getElem? hx
          have hsource : (HeapType.use jt).SourceA C := by
            rcases List.mem_append.mp hmem with himp | hdef
            · exact HeapType.SourceA.of_types_eq hBC.1 hBC.2
                (himpTagsB jt himp)
            · exact HeapType.SourceA.of_types_eq hC'C.1 hC'C.2
                (hdefTagsC' jt hdef)
          exact htypesC.tagDomSource hsource hj he
        · intro x gt hx
          have hmem : gt ∈ gtsI ++ gts := by
            rw [hCGlobals] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact ValType.SourceA.of_types_eq hBC.1 hBC.2
              (himpGlobalsB gt himp)
          · exact ValType.SourceA.of_types_eq hC'C.1 hC'C.2
              (hdefGlobalsC' gt hdef)
        · intro x tt hx
          have hmem : tt ∈ ttsI ++ tts := by
            rw [hCTables] at hx
            exact List.mem_of_getElem? hx
          rcases List.mem_append.mp hmem with himp | hdef
          · exact RefType.SourceA.of_types_eq hBC.1 hBC.2
              (himpTablesB tt himp)
          · exact RefType.SourceA.of_types_eq hC'C.1 hC'C.2
              (hdefTablesC' tt hdef)
        · intro x rt hx
          have hmem : rt ∈ rts := by
            rw [hCElems] at hx
            exact List.mem_of_getElem? hx
          exact hElemsC rt hmem
        · intro x lt hx
          rw [hC, hC'] at hx
          simp [Context.append] at hx
        · intro x ts hx
          rw [hC, hC'] at hx
          simp [Context.append] at hx
        · intro ts hx
          rw [hC, hC'] at hx
          simp [Context.append] at hx
      exact ⟨C, C', htypesC, htypesC', hCSource, hC'Source⟩

end Validate
end WasmGemmGnaf.Wasm.Core
