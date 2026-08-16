import WasmGemmGnaf.Wasm.Core.TypeGraphOrigin

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

def FreeTypesBounded (C : Context) (f : Free) : Prop :=
  ∀ x ∈ f.types, x.val < C.types.length

theorem freeTypeUses_mem : ∀ {tus : TypeUses} {x : TypeIdx},
    x ∈ (freeTypeUses tus).types →
      ∃ tu ∈ TypeUses.toList tus, x ∈ (freeTypeUse tu).types
  | .nil, _, h => by simp [freeTypeUses, Free.empty] at h
  | .cons tu tus, x, h => by
      simp only [freeTypeUses, Free.append] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨tu, by simp [TypeUses.toList], h⟩
      · obtain ⟨u, hu, hx⟩ := freeTypeUses_mem h
        exact ⟨u, by simp [TypeUses.toList, hu], hx⟩

theorem freeFieldTypes_mem : ∀ {fts : FieldTypes} {x : TypeIdx},
    x ∈ (freeFieldTypes fts).types →
      ∃ ft ∈ FieldTypes.toList fts, x ∈ (freeFieldType ft).types
  | .nil, _, h => by simp [freeFieldTypes, Free.empty] at h
  | .cons ft fts, x, h => by
      simp only [freeFieldTypes, Free.append] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨ft, by simp [FieldTypes.toList], h⟩
      · obtain ⟨u, hu, hx⟩ := freeFieldTypes_mem h
        exact ⟨u, by simp [FieldTypes.toList, hu], hx⟩

theorem freeValTypes_mem : ∀ {vts : ValTypes} {x : TypeIdx},
    x ∈ (freeValTypes vts).types →
      ∃ t ∈ ValTypes.toList vts, x ∈ (freeValType t).types
  | .nil, _, h => by simp [freeValTypes, Free.empty] at h
  | .cons t vts, x, h => by
      simp only [freeValTypes, Free.append] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨t, by simp [ValTypes.toList], h⟩
      · obtain ⟨u, hu, hx⟩ := freeValTypes_mem h
        exact ⟨u, by simp [ValTypes.toList, hu], hx⟩

theorem freeSubTypes_mem : ∀ {sts : SubTypes} {x : TypeIdx},
    x ∈ (freeSubTypes sts).types →
      ∃ st ∈ SubTypes.toList sts, x ∈ (freeSubType st).types
  | .nil, _, h => by simp [freeSubTypes, Free.empty] at h
  | .cons st sts, x, h => by
      simp only [freeSubTypes, Free.append] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨st, by simp [SubTypes.toList], h⟩
      · obtain ⟨u, hu, hx⟩ := freeSubTypes_mem h
        exact ⟨u, by simp [SubTypes.toList, hu], hx⟩

mutual
def wtTypeUse : TypeUse → Nat
  | .idx _ | .recu _ => 1
  | .defd dt => 1 + wtDefType dt
def wtDefType : DefType → Nat
  | .defd qt _ => 1 + wtRecType qt
def wtRecType : RecType → Nat
  | .recr sts => 1 + wtSubTypes sts
def wtSubTypes : SubTypes → Nat
  | .nil => 0
  | .cons st sts => wtSubType st + wtSubTypes sts
def wtSubType : SubType → Nat
  | .sub _ tus ct => 1 + wtTypeUses tus + wtCompType ct
def wtTypeUses : TypeUses → Nat
  | .nil => 0
  | .cons tu tus => wtTypeUse tu + wtTypeUses tus
def wtCompType : CompType → Nat
  | .struct fts => 1 + wtFieldTypes fts
  | .array ft => 1 + wtFieldType ft
  | .func dom cod => 1 + wtValTypes dom + wtValTypes cod
def wtFieldTypes : FieldTypes → Nat
  | .nil => 0
  | .cons ft fts => wtFieldType ft + wtFieldTypes fts
def wtFieldType : FieldType → Nat
  | .mk _ z => 1 + wtStorageType z
def wtStorageType : StorageType → Nat
  | .pack _ => 1
  | .val t => 1 + wtValType t
def wtValTypes : ValTypes → Nat
  | .nil => 0
  | .cons t ts => wtValType t + wtValTypes ts
def wtValType : ValType → Nat
  | .num _ | .vec _ | .bot => 1
  | .ref rt => 1 + wtRefType rt
def wtRefType : RefType → Nat
  | .ref _ ht => 1 + wtHeapType ht
def wtHeapType : HeapType → Nat
  | .abs _ => 1
  | .use tu => 1 + wtTypeUse tu
end

def wtValList : List ValType → Nat
  | [] => 0
  | t :: ts => wtValType t + wtValList ts

@[simp] theorem wtValList_toList : ∀ ts : ValTypes,
    wtValList (ValTypes.toList ts) = wtValTypes ts
  | .nil => rfl
  | .cons t ts => by
      change wtValType t + wtValList (ValTypes.toList ts) =
        wtValType t + wtValTypes ts
      rw [wtValList_toList ts]

theorem wtTypeUse_le_of_mem : ∀ {tu : TypeUse} {tus : TypeUses},
    tu ∈ TypeUses.toList tus → wtTypeUse tu ≤ wtTypeUses tus
  | _, .nil, h => by simp [TypeUses.toList] at h
  | tu, .cons head tail, h => by
      simp only [TypeUses.toList, List.mem_cons] at h
      rcases h with rfl | h
      · simp [wtTypeUses]
      · have := wtTypeUse_le_of_mem h
        simp [wtTypeUses]
        omega

theorem wtFieldType_le_of_mem : ∀ {ft : FieldType} {fts : FieldTypes},
    ft ∈ FieldTypes.toList fts → wtFieldType ft ≤ wtFieldTypes fts
  | _, .nil, h => by simp [FieldTypes.toList] at h
  | ft, .cons head tail, h => by
      simp only [FieldTypes.toList, List.mem_cons] at h
      rcases h with rfl | h
      · simp [wtFieldTypes]
      · have := wtFieldType_le_of_mem h
        simp [wtFieldTypes]
        omega

theorem wtValType_le_of_mem : ∀ {t : ValType} {ts : List ValType},
    t ∈ ts → wtValType t ≤ wtValList ts
  | _, [], h => by simp at h
  | t, head :: tail, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp [wtValList]
      · have := wtValType_le_of_mem h
        simp [wtValList]
        omega

theorem wtSubType_pos (st : SubType) : 0 < wtSubType st := by
  cases st
  simp [wtSubType]
  omega

mutual

theorem Typeuse_okA.freeTypesBounded {C : Context} {tu : TypeUse}
    (h : Typeuse_okA C tu) : FreeTypesBounded C (freeTypeUse tu) := by
  cases h with
  | typeidx hlookup =>
      intro x hx
      simp only [freeTypeUse, Free.ofTypeIdx, List.mem_singleton] at hx
      subst x
      exact (List.getElem?_eq_some_iff.mp hlookup).1
  | rec_ _ =>
      intro x hx
      simp [freeTypeUse, Free.empty] at hx
  | deftype hdt => simpa [freeTypeUse] using hdt.freeTypesBounded
termination_by 2 * wtTypeUse tu
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUse] at *
  all_goals omega

theorem Heaptype_okA.freeTypesBounded {C : Context} {ht : HeapType}
    (h : Heaptype_okA C ht) : FreeTypesBounded C (freeHeapType ht) := by
  cases h with
  | abs => simp [FreeTypesBounded, freeHeapType, Free.empty]
  | typeuse htu => simpa [freeHeapType] using htu.freeTypesBounded
termination_by 2 * wtHeapType ht
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtHeapType] at *
  all_goals omega

theorem Reftype_okA.freeTypesBounded {C : Context} {rt : RefType}
    (h : Reftype_okA C rt) : FreeTypesBounded C (freeRefType rt) := by
  cases h with
  | mk hht => simpa [freeRefType] using hht.freeTypesBounded
termination_by 2 * wtRefType rt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRefType] at *
  all_goals omega

theorem Valtype_okA.freeTypesBounded {C : Context} {t : ValType}
    (h : Valtype_okA C t) : FreeTypesBounded C (freeValType t) := by
  cases h with
  | num => simp [FreeTypesBounded, freeValType, Free.empty]
  | vec => simp [FreeTypesBounded, freeValType, Free.empty]
  | bot => simp [FreeTypesBounded, freeValType, Free.empty]
  | ref hrt => simpa [freeValType] using hrt.freeTypesBounded
termination_by 2 * wtValType t
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValType] at *
  all_goals omega

theorem Resulttype_okA.freeTypesBounded {C : Context} {ts : List ValType}
    (h : Resulttype_okA C ts) :
    ∀ t ∈ ts, FreeTypesBounded C (freeValType t) := by
  cases h with
  | mk hall =>
      intro t ht
      have _hw := wtValType_le_of_mem ht
      exact (hall t ht).freeTypesBounded
termination_by 2 * wtValList ts + 1
decreasing_by
  all_goals subst_vars
  all_goals omega

theorem Storagetype_okA.freeTypesBounded {C : Context} {z : StorageType}
    (h : Storagetype_okA C z) : FreeTypesBounded C (freeStorageType z) := by
  cases h with
  | val hv => simpa [freeStorageType] using hv.freeTypesBounded
  | pack => simp [FreeTypesBounded, freeStorageType, Free.empty]
termination_by 2 * wtStorageType z
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtStorageType] at *
  all_goals omega

theorem Fieldtype_okA.freeTypesBounded {C : Context} {ft : FieldType}
    (h : Fieldtype_okA C ft) : FreeTypesBounded C (freeFieldType ft) := by
  cases h with
  | mk hz => simpa [freeFieldType] using hz.freeTypesBounded
termination_by 2 * wtFieldType ft
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldType] at *
  all_goals omega

theorem Comptype_okA.freeTypesBounded {C : Context} {ct : CompType}
    (h : Comptype_okA C ct) : FreeTypesBounded C (freeCompType ct) := by
  cases h with
  | struct hall =>
      intro x hx
      obtain ⟨ft, hft, hxf⟩ := freeFieldTypes_mem hx
      have _hw := wtFieldType_le_of_mem hft
      exact (hall ft hft).freeTypesBounded x hxf
  | array hft => simpa [freeCompType] using hft.freeTypesBounded
  | func hdom hcod =>
      intro x hx
      simp only [freeCompType, Free.append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨t, ht, hxt⟩ := freeValTypes_mem hx
        exact (hdom.freeTypesBounded t ht) x hxt
      · obtain ⟨t, ht, hxt⟩ := freeValTypes_mem hx
        exact (hcod.freeTypesBounded t ht) x hxt
termination_by 2 * wtCompType ct
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtCompType, wtValList_toList] at *
  all_goals omega

theorem Subtype_okA.freeTypesBounded {C : Context} {st : SubType}
    {x₀ : TypeIdx} (h : Subtype_okA C st x₀) :
    FreeTypesBounded C (freeSubType st) := by
  cases h with
  | @mk C fin xs ct x₀ cts hlen hlen₂ hall hct hsub =>
      intro z hz
      simp only [freeSubType, Free.append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · obtain ⟨tu, htu, hztu⟩ := freeTypeUses_mem hz
        simp only [TypeUses.toList_ofList, List.mem_map] at htu
        obtain ⟨y, hy, rfl⟩ := htu
        simp only [freeTypeUse, Free.ofTypeIdx, List.mem_singleton] at hztu
        subst z
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
        have hjlt : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
        have hjctlt : j < cts.length := by
          simpa [SeqLen₂] using (hlen₂ ▸ hjlt)
        have hp := hall j y cts[j] hj (List.getElem?_eq_getElem hjctlt)
        obtain ⟨_, dt, _, _, hlookup, _⟩ := hp
        exact (List.getElem?_eq_some_iff.mp hlookup).1
      · exact hct.freeTypesBounded z hz
termination_by 2 * wtSubType st
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubType] at *
  all_goals omega

theorem Subtype_ok2A.freeTypesBounded {C : Context} {st : SubType}
    {x : TypeIdx} {i : Nat} (h : Subtype_ok2A C st x i) :
    FreeTypesBounded C (freeSubType st) := by
  cases h with
  | @mk C fin sups ct x i cts hlen hlen₂ hall hvalid hct hsub =>
      intro y hy
      simp only [freeSubType, Free.append] at hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨tu, htu, hytu⟩ := freeTypeUses_mem hy
        have _hw := wtTypeUse_le_of_mem htu
        exact (hvalid tu htu).freeTypesBounded y hytu
      · exact hct.freeTypesBounded y hy
termination_by 2 * wtSubType st
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubType] at *
  all_goals omega

theorem Rectype_okA.freeTypesBounded {C : Context} {qt : RecType}
    {x : TypeIdx} (h : Rectype_okA C qt x) :
    FreeTypesBounded C (freeRecType qt) := by
  cases qt with
  | recr sts =>
      intro y hy
      cases h with
      | empty => simp [freeRecType, freeSubTypes, Free.empty] at hy
      | @cons C stHead stsTail xHead hst _ htail =>
          have _hpos := wtSubType_pos stHead
          simp only [freeRecType, freeSubTypes, Free.append] at hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hst.freeTypesBounded y hy
          · exact htail.freeTypesBounded y hy
      | rec2 hrec =>
          exact hrec.freeTypesBounded y (by simpa [freeRecType] using hy)
termination_by 2 * wtRecType qt + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRecType, wtSubTypes] at *
  all_goals omega

theorem Rectype_ok2A.freeTypesBounded {C : Context} {qt : RecType}
    {x : TypeIdx} {i : Nat} (h : Rectype_ok2A C qt x i) :
    FreeTypesBounded C (freeRecType qt) := by
  cases qt with
  | recr sts =>
      intro y hy
      cases h with
      | empty => simp [freeRecType, freeSubTypes, Free.empty] at hy
      | @cons C stHead stsTail xHead iHead hst htail =>
          have _hpos := wtSubType_pos stHead
          simp only [freeRecType, freeSubTypes, Free.append] at hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hst.freeTypesBounded y hy
          · exact htail.freeTypesBounded y hy
termination_by 2 * wtRecType qt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRecType, wtSubTypes] at *
  all_goals omega

theorem Deftype_okA.freeTypesBounded {C : Context} {dt : DefType}
    (h : Deftype_okA C dt) : FreeTypesBounded C (freeDefType dt) := by
  cases h with
  | mk hqt hi => simpa [freeDefType] using hqt.freeTypesBounded
termination_by 2 * wtDefType dt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtDefType] at *
  all_goals omega

end

def TypesBelow (limit : Nat) (f : Free) : Prop :=
  ∀ x ∈ f.types, x.val < limit

theorem typesBelow_append {limit : Nat} {a b : Free} :
    TypesBelow limit (Free.append a b) ↔
      TypesBelow limit a ∧ TypesBelow limit b := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by simp [Free.append, hx])
    · intro x hx
      exact h x (by simp [Free.append, hx])
  · rintro ⟨ha, hb⟩ x hx
    simp only [Free.append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ha x hx
    · exact hb x hx

theorem minus_idx_vars : ∀ (tvs : List TypeVar) (tus : List TypeUse),
    tvs.length = tus.length →
    (∀ tv ∈ tvs, ∃ x, tv = .idx x) →
    minusRecs tvs tus = (tvs, tus) := by
  intro tvs
  induction tvs with
  | nil =>
      intro tus hlen _
      cases tus <;> simp_all [minusRecs]
  | cons tv tvs ih =>
      intro tus hlen hall
      cases tus with
      | nil => simp at hlen
      | cons tu tus =>
          obtain ⟨x, rfl⟩ := hall tv (by simp)
          have htail := ih tus (by simpa using hlen)
            (fun tv htv => hall tv (by simp [htv]))
          simp [minusRecs, htail]

theorem minus_roll (base : TypeIdx) (n : Nat) :
    minusRecs
      ((List.range n).map
        (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
      ((List.range n).map TypeUse.recu) =
    (((List.range n).map
        (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j)))),
      ((List.range n).map TypeUse.recu)) := by
  apply minus_idx_vars
  · simp
  · intro tv htv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp htv
    exact ⟨_, rfl⟩

def rollTVars (base : TypeIdx) (n : Nat) : List TypeVar :=
  (List.range n).map
    (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j)))

def rollTUses (n : Nat) : List TypeUse :=
  (List.range n).map TypeUse.recu

mutual

theorem roll_typeUse_below : ∀ (tu : TypeUse) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → tu.isSyn = true →
    TypesBelow (base.val + n) (freeTypeUse tu) →
    TypesBelow base.val
      (freeTypeUse (substTypeUse tu (rollTVars base n) (rollTUses n)))
  | .idx y, base, n, hbound, _, hsrc => by
      simp only [substTypeUse, rollTVars, rollTUses]
      rw [substTypeVar_rollVars base y n hbound]
      split
      · intro z hz
        simp [freeTypeUse, Free.empty] at hz
      · rename_i hout
        intro z hz
        simp only [freeTypeUse, Free.ofTypeIdx, List.mem_singleton] at hz
        subst z
        have hy : y.val < base.val + n :=
          hsrc y (by simp [freeTypeUse, Free.ofTypeIdx])
        omega
  | .recu i, _, _, _, hsyn, _ => by simp [TypeUse.isSyn] at hsyn
  | .defd dt, _, _, _, hsyn, _ => by simp [TypeUse.isSyn] at hsyn

theorem roll_heapType_below : ∀ (ht : HeapType) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → ht.isSyn = true →
    TypesBelow (base.val + n) (freeHeapType ht) →
    TypesBelow base.val
      (freeHeapType (substHeapType ht (rollTVars base n) (rollTUses n)))
  | .abs _, _, _, _, _, _ => by
      intro x hx
      simp [substHeapType, freeHeapType, Free.empty] at hx
  | .use tu, base, n, hbound, hsyn, hsrc => by
      simpa [HeapType.isSyn, substHeapType, freeHeapType] using
        roll_typeUse_below tu base n hbound hsyn hsrc

theorem roll_refType_below : ∀ (rt : RefType) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → rt.isSyn = true →
    TypesBelow (base.val + n) (freeRefType rt) →
    TypesBelow base.val
      (freeRefType (substRefType rt (rollTVars base n) (rollTUses n)))
  | .ref nul ht, base, n, hbound, hsyn, hsrc => by
      simpa [RefType.isSyn, substRefType, freeRefType] using
        roll_heapType_below ht base n hbound hsyn hsrc

theorem roll_valType_below : ∀ (t : ValType) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → t.isSyn = true →
    TypesBelow (base.val + n) (freeValType t) →
    TypesBelow base.val
      (freeValType (substValType t (rollTVars base n) (rollTUses n)))
  | .num _, _, _, _, _, _ => by
      intro x hx
      simp [substValType, freeValType, Free.empty] at hx
  | .vec _, _, _, _, _, _ => by
      intro x hx
      simp [substValType, freeValType, Free.empty] at hx
  | .bot, _, _, _, hsyn, _ => by simp [ValType.isSyn] at hsyn
  | .ref rt, base, n, hbound, hsyn, hsrc => by
      simpa [ValType.isSyn, substValType, freeValType] using
        roll_refType_below rt base n hbound hsyn hsrc

theorem roll_storageType_below : ∀ (z : StorageType) (base : TypeIdx)
    (n : Nat), base.val + n ≤ 2 ^ 32 → z.isSyn = true →
    TypesBelow (base.val + n) (freeStorageType z) →
    TypesBelow base.val
      (freeStorageType (substStorageType z (rollTVars base n) (rollTUses n)))
  | .pack _, _, _, _, _, _ => by
      intro x hx
      simp [substStorageType, freeStorageType, Free.empty] at hx
  | .val t, base, n, hbound, hsyn, hsrc => by
      simpa [StorageType.isSyn, substStorageType, freeStorageType] using
        roll_valType_below t base n hbound hsyn hsrc

theorem roll_fieldType_below : ∀ (ft : FieldType) (base : TypeIdx)
    (n : Nat), base.val + n ≤ 2 ^ 32 → ft.isSyn = true →
    TypesBelow (base.val + n) (freeFieldType ft) →
    TypesBelow base.val
      (freeFieldType (substFieldType ft (rollTVars base n) (rollTUses n)))
  | .mk m z, base, n, hbound, hsyn, hsrc => by
      simpa [FieldType.isSyn, substFieldType, freeFieldType] using
        roll_storageType_below z base n hbound hsyn hsrc

end

theorem roll_valTypes_below : ∀ (ts : ValTypes) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (ValTypes.toList ts).all ValType.isSyn = true →
    TypesBelow (base.val + n) (freeValTypes ts) →
    TypesBelow base.val
      (freeValTypes (substValTypes ts (rollTVars base n) (rollTUses n)))
  | .nil, _, _, _, _, _ => by
      intro x hx
      simp [substValTypes, freeValTypes, Free.empty] at hx
  | .cons t ts, base, n, hbound, hsyn, hsrc => by
      rw [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      rw [freeValTypes, typesBelow_append] at hsrc
      simp only [substValTypes, freeValTypes, typesBelow_append]
      exact ⟨roll_valType_below t base n hbound hsyn.1 hsrc.1,
        roll_valTypes_below ts base n hbound hsyn.2 hsrc.2⟩

theorem roll_fieldTypes_below : ∀ (fts : FieldTypes) (base : TypeIdx)
    (n : Nat), base.val + n ≤ 2 ^ 32 →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    TypesBelow (base.val + n) (freeFieldTypes fts) →
    TypesBelow base.val
      (freeFieldTypes (substFieldTypes fts (rollTVars base n) (rollTUses n)))
  | .nil, _, _, _, _, _ => by
      intro x hx
      simp [substFieldTypes, freeFieldTypes, Free.empty] at hx
  | .cons ft fts, base, n, hbound, hsyn, hsrc => by
      rw [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      rw [freeFieldTypes, typesBelow_append] at hsrc
      simp only [substFieldTypes, freeFieldTypes, typesBelow_append]
      exact ⟨roll_fieldType_below ft base n hbound hsyn.1 hsrc.1,
        roll_fieldTypes_below fts base n hbound hsyn.2 hsrc.2⟩

theorem roll_typeUses_below : ∀ (tus : TypeUses) (base : TypeIdx)
    (n : Nat), base.val + n ≤ 2 ^ 32 →
    (TypeUses.toList tus).all TypeUse.isSyn = true →
    TypesBelow (base.val + n) (freeTypeUses tus) →
    TypesBelow base.val
      (freeTypeUses (substTypeUses tus (rollTVars base n) (rollTUses n)))
  | .nil, _, _, _, _, _ => by
      intro x hx
      simp [substTypeUses, freeTypeUses, Free.empty] at hx
  | .cons tu tus, base, n, hbound, hsyn, hsrc => by
      rw [TypeUses.toList, List.all_cons, Bool.and_eq_true] at hsyn
      rw [freeTypeUses, typesBelow_append] at hsrc
      simp only [substTypeUses, freeTypeUses, typesBelow_append]
      exact ⟨roll_typeUse_below tu base n hbound hsyn.1 hsrc.1,
        roll_typeUses_below tus base n hbound hsyn.2 hsrc.2⟩

theorem roll_compType_below : ∀ (ct : CompType) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → ct.isSyn = true →
    TypesBelow (base.val + n) (freeCompType ct) →
    TypesBelow base.val
      (freeCompType (substCompType ct (rollTVars base n) (rollTUses n)))
  | .struct fts, base, n, hbound, hsyn, hsrc => by
      simpa [CompType.isSyn, substCompType, freeCompType] using
        roll_fieldTypes_below fts base n hbound hsyn hsrc
  | .array ft, base, n, hbound, hsyn, hsrc => by
      simpa [CompType.isSyn, substCompType, freeCompType] using
        roll_fieldType_below ft base n hbound hsyn hsrc
  | .func dom cod, base, n, hbound, hsyn, hsrc => by
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      rw [freeCompType, typesBelow_append] at hsrc
      simp only [substCompType, freeCompType, typesBelow_append]
      exact ⟨roll_valTypes_below dom base n hbound hsyn.1 hsrc.1,
        roll_valTypes_below cod base n hbound hsyn.2 hsrc.2⟩

theorem roll_subType_below : ∀ (st : SubType) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 → st.isSyn = true →
    TypesBelow (base.val + n) (freeSubType st) →
    TypesBelow base.val
      (freeSubType (substSubType st (rollTVars base n) (rollTUses n)))
  | .sub fin tus ct, base, n, hbound, hsyn, hsrc => by
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      rw [freeSubType, typesBelow_append] at hsrc
      simp only [substSubType, freeSubType, typesBelow_append]
      exact ⟨roll_typeUses_below tus base n hbound hsyn.1 hsrc.1,
        roll_compType_below ct base n hbound hsyn.2 hsrc.2⟩

theorem roll_subTypes_below : ∀ (sts : SubTypes) (base : TypeIdx)
    (n : Nat), base.val + n ≤ 2 ^ 32 →
    (SubTypes.toList sts).all SubType.isSyn = true →
    TypesBelow (base.val + n) (freeSubTypes sts) →
    TypesBelow base.val
      (freeSubTypes (substSubTypes sts (rollTVars base n) (rollTUses n)))
  | .nil, _, _, _, _, _ => by
      intro x hx
      simp [substSubTypes, freeSubTypes, Free.empty] at hx
  | .cons st sts, base, n, hbound, hsyn, hsrc => by
      rw [SubTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      rw [freeSubTypes, typesBelow_append] at hsrc
      simp only [substSubTypes, freeSubTypes, typesBelow_append]
      exact ⟨roll_subType_below st base n hbound hsyn.1 hsrc.1,
        roll_subTypes_below sts base n hbound hsyn.2 hsrc.2⟩

theorem roll_recType_below (qt : RecType) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : qt.isSyn = true)
    (hsrc : TypesBelow (base.val + n) (freeRecType qt)) :
    TypesBelow base.val
      (freeRecType (substRecType qt (rollTVars base n) (rollTUses n))) := by
  cases qt with
  | recr sts =>
      simp only [substRecType]
      have hminus : minusRecs (rollTVars base n) (rollTUses n) =
          (rollTVars base n, rollTUses n) := by
        simpa [rollTVars, rollTUses] using minus_roll base n
      rw [hminus]
      exact roll_subTypes_below sts base n hbound
        (by simpa [RecType.isSyn] using hsyn)
        (by simpa [freeRecType] using hsrc)

/-- Every member produced by rolling one checked source group refers only to
the source prefix preceding that group. -/
theorem Type_okA.groupFreeBefore {C : Context} {td : TypeDef}
    {group : List DefType} (hsyn : td.isSyn = true)
    (h : Type_okA C td group) :
    ∀ (k : Nat) (dt : DefType), group[k]? = some dt →
      TypesBelow C.types.length (freeDefType dt) := by
  cases h with
  | mk hrange hbase hgroup hrect =>
      rename_i base
      cases td with
      | mk qt =>
          cases qt with
          | recr sts =>
              subst group
              have hqtSyn : (RecType.recr sts).isSyn = true := by
                simpa [TypeDef.isSyn] using hsyn
              have hbound : base.val + SubTypes.length sts ≤ 2 ^ 32 := by
                unfold TypeGroupRangeOk at hrange
                simpa [RecType.count, hbase] using hrange.2
              have hsource : TypesBelow (base.val + SubTypes.length sts)
                  (freeRecType (.recr sts)) := by
                intro x hx
                have hxlt := hrect.freeTypesBounded x hx
                simpa [Context.append, rollDt, rollRt,
                  SubTypes.length_substSubTypes, hbase] using hxlt
              have hrolled : TypesBelow base.val
                  (freeRecType (rollRt base (.recr sts))) := by
                simpa [rollRt, rollTVars, rollTUses, substRecType,
                  minus_roll] using
                  roll_recType_below (.recr sts) base (SubTypes.length sts)
                    hbound hqtSyn hsource
              intro k dt hlookup
              have hk : k < SubTypes.length sts := by
                have hk' := (List.getElem?_eq_some_iff.mp hlookup).1
                simpa [rollDt, rollRt, SubTypes.length_substSubTypes] using hk'
              have hcanonical : (rollDt base (.recr sts))[k]? =
                  some (.defd (rollRt base (.recr sts)) k) := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes, hk]
              have hdt : dt = .defd (rollRt base (.recr sts)) k :=
                Option.some.inj (hlookup.symm.trans hcanonical)
              subst dt
              simpa [freeDefType, hbase] using hrolled

/-- Causal source-order invariant for a stored type vector. -/
def StoredFreeBefore (dts : List DefType) : Prop :=
  ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
    TypesBelow i (freeDefType dt)

private theorem Types_okA.storedFreeBefore_interval {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true) (h : Types_okA C tds dts) :
    ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
      TypesBelow (C.types.length + i) (freeDefType dt) := by
  induction h with
  | empty =>
      intro i dt hlookup
      simp at hlookup
  | @cons C td tds head tail hhead htail ih =>
      have hsynParts : td.isSyn = true ∧ tds.all TypeDef.isSyn = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsyn
      intro i dt hlookup
      by_cases hi : i < head.length
      · have hheadLookup : head[i]? = some dt := by
          rw [List.getElem?_append_left hi] at hlookup
          exact hlookup
        have hb := hhead.groupFreeBefore hsynParts.1 i dt hheadLookup
        exact fun x hx => by
          have := hb x hx
          omega
      · have htailLookup : tail[i - head.length]? = some dt := by
          rw [List.getElem?_append_right (Nat.le_of_not_gt hi)] at hlookup
          exact hlookup
        have hb := ih hsynParts.2 (i - head.length) dt htailLookup
        intro x hx
        have := hb x hx
        simp only [Context.append, List.length_append] at this
        omega

theorem Types_okA.storedFreeBefore {tds : List TypeDef}
    {dts : List DefType} (hsyn : tds.all TypeDef.isSyn = true)
    (h : Types_okA Context.empty tds dts) : StoredFreeBefore dts := by
  intro i dt hlookup
  have hb := h.storedFreeBefore_interval hsyn i dt hlookup
  simpa [Context.empty] using hb

/-- Two closing environments agree on every source index used by `f`. -/
def ClosingEnvsAgree (f : Free) (us vs : List TypeUse) : Prop :=
  ∀ x ∈ f.types,
    substTypeVar (.idx x) (idxVars us.length) us =
      substTypeVar (.idx x) (idxVars vs.length) vs

theorem closingEnvsAgree_append {a b : Free} {us vs : List TypeUse} :
    ClosingEnvsAgree (Free.append a b) us vs ↔
      ClosingEnvsAgree a us vs ∧ ClosingEnvsAgree b us vs := by
  constructor
  · intro h
    exact ⟨(fun x hx => h x (by simp [Free.append, hx])),
      fun x hx => h x (by simp [Free.append, hx])⟩
  · rintro ⟨ha, hb⟩ x hx
    simp only [Free.append, List.mem_append] at hx
    exact hx.elim (ha x) (hb x)

theorem minus_idxVars (us : List TypeUse) :
    minusRecs (idxVars us.length) us = (idxVars us.length, us) := by
  apply minus_idx_vars
  · simp [idxVars]
  · intro tv htv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp htv
    exact ⟨_, rfl⟩

private theorem substTypeVar_recv_of_all_idx :
    ∀ (j : Nat) (tvs : List TypeVar) (tus : List TypeUse),
      (∀ tv ∈ tvs, ∃ x, tv = .idx x) →
      substTypeVar (.recv j) tvs tus = .recu j
  | _, [], _, _ => rfl
  | j, tv :: tvs, [], _ => rfl
  | j, tv :: tvs, tu :: tus, h => by
      obtain ⟨x, rfl⟩ := h tv (by simp)
      simp only [substTypeVar, reduceCtorEq, ↓reduceIte]
      exact substTypeVar_recv_of_all_idx j tvs tus
        (fun tv htv => h tv (by simp [htv]))

theorem substTypeVar_recv_idxVars (j : Nat) (us : List TypeUse) :
    substTypeVar (.recv j) (idxVars us.length) us = .recu j := by
  apply substTypeVar_recv_of_all_idx
  intro tv htv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp htv
  exact ⟨_, rfl⟩

theorem wtTypeUse_pos (tu : TypeUse) : 0 < wtTypeUse tu := by
  cases tu <;> simp [wtTypeUse] <;> omega

theorem wtFieldType_pos (ft : FieldType) : 0 < wtFieldType ft := by
  cases ft
  simp [wtFieldType]
  omega

theorem wtValType_pos (t : ValType) : 0 < wtValType t := by
  cases t <;> simp [wtValType] <;> omega

mutual

theorem subst_typeUse_env : ∀ (tu : TypeUse) (us vs : List TypeUse),
    ClosingEnvsAgree (freeTypeUse tu) us vs →
    substTypeUse tu (idxVars us.length) us =
      substTypeUse tu (idxVars vs.length) vs
  | .idx x, us, vs, h => h x (by simp [freeTypeUse, Free.ofTypeIdx])
  | .recu j, us, vs, _ => by
      simp [substTypeUse, substTypeVar_recv_idxVars]
  | .defd dt, us, vs, h => by
      simp only [substTypeUse]
      congr 1
      exact subst_defType_env dt us vs (by simpa [freeTypeUse] using h)
termination_by tu _ _ _ => 2 * wtTypeUse tu
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUse] at *
  all_goals omega

theorem subst_defType_env : ∀ (dt : DefType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeDefType dt) us vs →
    substAllDefType dt us = substAllDefType dt vs
  | .defd qt i, us, vs, h => by
      simp only [substAllDefType, substDefType]
      congr 1
      exact subst_recType_env qt us vs (by simpa [freeDefType] using h)
termination_by dt _ _ _ => 2 * wtDefType dt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtDefType] at *
  all_goals omega

theorem subst_recType_env : ∀ (qt : RecType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeRecType qt) us vs →
    substRecType qt (idxVars us.length) us =
      substRecType qt (idxVars vs.length) vs
  | .recr sts, us, vs, h => by
      simp only [substRecType, minus_idxVars]
      congr 1
      exact subst_subTypes_env sts us vs (by simpa [freeRecType] using h)
termination_by qt _ _ _ => 2 * wtRecType qt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRecType] at *
  all_goals omega

theorem subst_subTypes_env : ∀ (sts : SubTypes) (us vs : List TypeUse),
    ClosingEnvsAgree (freeSubTypes sts) us vs →
    substSubTypes sts (idxVars us.length) us =
      substSubTypes sts (idxVars vs.length) vs
  | .nil, _, _, _ => rfl
  | .cons st sts, us, vs, h => by
      rw [freeSubTypes, closingEnvsAgree_append] at h
      simp only [substSubTypes]
      rw [subst_subType_env st us vs h.1,
        subst_subTypes_env sts us vs h.2]
termination_by sts _ _ _ => 2 * wtSubTypes sts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubTypes] at *
  all_goals have := wtSubType_pos st
  all_goals omega

theorem subst_subType_env : ∀ (st : SubType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeSubType st) us vs →
    substSubType st (idxVars us.length) us =
      substSubType st (idxVars vs.length) vs
  | .sub fin sups ct, us, vs, h => by
      rw [freeSubType, closingEnvsAgree_append] at h
      simp only [substSubType]
      rw [subst_typeUses_env sups us vs h.1,
        subst_compType_env ct us vs h.2]
termination_by st _ _ _ => 2 * wtSubType st
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubType] at *
  all_goals omega

theorem subst_typeUses_env : ∀ (tus : TypeUses) (us vs : List TypeUse),
    ClosingEnvsAgree (freeTypeUses tus) us vs →
    substTypeUses tus (idxVars us.length) us =
      substTypeUses tus (idxVars vs.length) vs
  | .nil, _, _, _ => rfl
  | .cons tu tus, us, vs, h => by
      rw [freeTypeUses, closingEnvsAgree_append] at h
      simp only [substTypeUses]
      rw [subst_typeUse_env tu us vs h.1,
        subst_typeUses_env tus us vs h.2]
termination_by tus _ _ _ => 2 * wtTypeUses tus + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUses] at *
  all_goals have := wtTypeUse_pos tu
  all_goals omega

theorem subst_compType_env : ∀ (ct : CompType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeCompType ct) us vs →
    substCompType ct (idxVars us.length) us =
      substCompType ct (idxVars vs.length) vs
  | .struct fts, us, vs, h => by
      simp only [substCompType]
      congr 1
      exact subst_fieldTypes_env fts us vs (by simpa [freeCompType] using h)
  | .array ft, us, vs, h => by
      simp only [substCompType]
      congr 1
      exact subst_fieldType_env ft us vs (by simpa [freeCompType] using h)
  | .func dom cod, us, vs, h => by
      rw [freeCompType, closingEnvsAgree_append] at h
      simp only [substCompType]
      rw [subst_valTypes_env dom us vs h.1,
        subst_valTypes_env cod us vs h.2]
termination_by ct _ _ _ => 2 * wtCompType ct
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtCompType] at *
  all_goals omega

theorem subst_fieldTypes_env : ∀ (fts : FieldTypes) (us vs : List TypeUse),
    ClosingEnvsAgree (freeFieldTypes fts) us vs →
    substFieldTypes fts (idxVars us.length) us =
      substFieldTypes fts (idxVars vs.length) vs
  | .nil, _, _, _ => rfl
  | .cons ft fts, us, vs, h => by
      rw [freeFieldTypes, closingEnvsAgree_append] at h
      simp only [substFieldTypes]
      rw [subst_fieldType_env ft us vs h.1,
        subst_fieldTypes_env fts us vs h.2]
termination_by fts _ _ _ => 2 * wtFieldTypes fts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldTypes] at *
  all_goals have := wtFieldType_pos ft
  all_goals omega

theorem subst_fieldType_env : ∀ (ft : FieldType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeFieldType ft) us vs →
    substFieldType ft (idxVars us.length) us =
      substFieldType ft (idxVars vs.length) vs
  | .mk m z, us, vs, h => by
      simp only [substFieldType]
      congr 1
      exact subst_storageType_env z us vs (by simpa [freeFieldType] using h)
termination_by ft _ _ _ => 2 * wtFieldType ft
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldType] at *
  all_goals omega

theorem subst_storageType_env : ∀ (z : StorageType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeStorageType z) us vs →
    substStorageType z (idxVars us.length) us =
      substStorageType z (idxVars vs.length) vs
  | .pack _, _, _, _ => rfl
  | .val t, us, vs, h => by
      simp only [substStorageType]
      congr 1
      exact subst_valType_env t us vs (by simpa [freeStorageType] using h)
termination_by z _ _ _ => 2 * wtStorageType z
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtStorageType] at *
  all_goals omega

theorem subst_valTypes_env : ∀ (ts : ValTypes) (us vs : List TypeUse),
    ClosingEnvsAgree (freeValTypes ts) us vs →
    substValTypes ts (idxVars us.length) us =
      substValTypes ts (idxVars vs.length) vs
  | .nil, _, _, _ => rfl
  | .cons t ts, us, vs, h => by
      rw [freeValTypes, closingEnvsAgree_append] at h
      simp only [substValTypes]
      rw [subst_valType_env t us vs h.1,
        subst_valTypes_env ts us vs h.2]
termination_by ts _ _ _ => 2 * wtValTypes ts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValTypes] at *
  all_goals have := wtValType_pos t
  all_goals omega

theorem subst_valType_env : ∀ (t : ValType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeValType t) us vs →
    substValType t (idxVars us.length) us =
      substValType t (idxVars vs.length) vs
  | .num _, _, _, _ => rfl
  | .vec _, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .ref rt, us, vs, h => by
      simp only [substValType]
      congr 1
      exact subst_refType_env rt us vs (by simpa [freeValType] using h)
termination_by t _ _ _ => 2 * wtValType t
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValType] at *
  all_goals omega

theorem subst_refType_env : ∀ (rt : RefType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeRefType rt) us vs →
    substRefType rt (idxVars us.length) us =
      substRefType rt (idxVars vs.length) vs
  | .ref nul ht, us, vs, h => by
      simp only [substRefType]
      congr 1
      exact subst_heapType_env ht us vs (by simpa [freeRefType] using h)
termination_by rt _ _ _ => 2 * wtRefType rt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRefType] at *
  all_goals omega

theorem subst_heapType_env : ∀ (ht : HeapType) (us vs : List TypeUse),
    ClosingEnvsAgree (freeHeapType ht) us vs →
    substHeapType ht (idxVars us.length) us =
      substHeapType ht (idxVars vs.length) vs
  | .abs _, _, _, _ => rfl
  | .use tu, us, vs, h => by
      simp only [substHeapType]
      congr 1
      exact subst_typeUse_env tu us vs (by simpa [freeHeapType] using h)
termination_by ht _ _ _ => 2 * wtHeapType ht
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtHeapType] at *
  all_goals omega

end

mutual

theorem subst_typeUse_nil : ∀ tu : TypeUse,
    substTypeUse tu [] [] = tu
  | .idx _ => rfl
  | .recu _ => rfl
  | .defd dt => by
      simp only [substTypeUse]
      rw [subst_defType_nil dt]
termination_by tu => 2 * wtTypeUse tu
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUse] at *
  all_goals omega

theorem subst_defType_nil : ∀ dt : DefType,
    substDefType dt [] [] = dt
  | .defd qt i => by
      simp only [substDefType]
      rw [subst_recType_nil qt]
termination_by dt => 2 * wtDefType dt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtDefType] at *
  all_goals omega

theorem subst_recType_nil : ∀ qt : RecType,
    substRecType qt [] [] = qt
  | .recr sts => by
      simp only [substRecType, minusRecs]
      rw [subst_subTypes_nil sts]
termination_by qt => 2 * wtRecType qt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRecType] at *
  all_goals omega

theorem subst_subTypes_nil : ∀ sts : SubTypes,
    substSubTypes sts [] [] = sts
  | .nil => rfl
  | .cons st sts => by
      simp only [substSubTypes]
      rw [subst_subType_nil st, subst_subTypes_nil sts]
termination_by sts => 2 * wtSubTypes sts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubTypes] at *
  all_goals have := wtSubType_pos st
  all_goals omega

theorem subst_subType_nil : ∀ st : SubType,
    substSubType st [] [] = st
  | .sub fin sups ct => by
      simp only [substSubType]
      rw [subst_typeUses_nil sups, subst_compType_nil ct]
termination_by st => 2 * wtSubType st
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubType] at *
  all_goals omega

theorem subst_typeUses_nil : ∀ tus : TypeUses,
    substTypeUses tus [] [] = tus
  | .nil => rfl
  | .cons tu tus => by
      simp only [substTypeUses]
      rw [subst_typeUse_nil tu, subst_typeUses_nil tus]
termination_by tus => 2 * wtTypeUses tus + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUses] at *
  all_goals have := wtTypeUse_pos tu
  all_goals omega

theorem subst_compType_nil : ∀ ct : CompType,
    substCompType ct [] [] = ct
  | .struct fts => by
      simp only [substCompType]
      rw [subst_fieldTypes_nil fts]
  | .array ft => by
      simp only [substCompType]
      rw [subst_fieldType_nil ft]
  | .func dom cod => by
      simp only [substCompType]
      rw [subst_valTypes_nil dom, subst_valTypes_nil cod]
termination_by ct => 2 * wtCompType ct
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtCompType] at *
  all_goals omega

theorem subst_fieldTypes_nil : ∀ fts : FieldTypes,
    substFieldTypes fts [] [] = fts
  | .nil => rfl
  | .cons ft fts => by
      simp only [substFieldTypes]
      rw [subst_fieldType_nil ft, subst_fieldTypes_nil fts]
termination_by fts => 2 * wtFieldTypes fts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldTypes] at *
  all_goals have := wtFieldType_pos ft
  all_goals omega

theorem subst_fieldType_nil : ∀ ft : FieldType,
    substFieldType ft [] [] = ft
  | .mk m z => by
      simp only [substFieldType]
      rw [subst_storageType_nil z]
termination_by ft => 2 * wtFieldType ft
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldType] at *
  all_goals omega

theorem subst_storageType_nil : ∀ z : StorageType,
    substStorageType z [] [] = z
  | .pack _ => rfl
  | .val t => by
      simp only [substStorageType]
      rw [subst_valType_nil t]
termination_by z => 2 * wtStorageType z
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtStorageType] at *
  all_goals omega

theorem subst_valTypes_nil : ∀ ts : ValTypes,
    substValTypes ts [] [] = ts
  | .nil => rfl
  | .cons t ts => by
      simp only [substValTypes]
      rw [subst_valType_nil t, subst_valTypes_nil ts]
termination_by ts => 2 * wtValTypes ts + 1
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValTypes] at *
  all_goals have := wtValType_pos t
  all_goals omega

theorem subst_valType_nil : ∀ t : ValType,
    substValType t [] [] = t
  | .num _ => rfl
  | .vec _ => rfl
  | .bot => rfl
  | .ref rt => by
      simp only [substValType]
      rw [subst_refType_nil rt]
termination_by t => 2 * wtValType t
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValType] at *
  all_goals omega

theorem subst_refType_nil : ∀ rt : RefType,
    substRefType rt [] [] = rt
  | .ref nul ht => by
      simp only [substRefType]
      rw [subst_heapType_nil ht]
termination_by rt => 2 * wtRefType rt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRefType] at *
  all_goals omega

theorem subst_heapType_nil : ∀ ht : HeapType,
    substHeapType ht [] [] = ht
  | .abs _ => rfl
  | .use tu => by
      simp only [substHeapType]
      rw [subst_typeUse_nil tu]
termination_by ht => 2 * wtHeapType ht
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtHeapType] at *
  all_goals omega

end

private theorem substTypeVar_idxRange_prefix :
    ∀ (start : Nat) (pre suffix : List TypeUse) (x : TypeIdx),
      start + pre.length + suffix.length ≤ 2 ^ 32 →
      start ≤ x.val → x.val < start + pre.length →
      substTypeVar (.idx x)
          ((List.range' start pre.length).map
            (fun i => TypeVar.idx (TypeIdx.ofNat i))) pre =
        substTypeVar (.idx x)
          ((List.range' start (pre.length + suffix.length)).map
            (fun i => TypeVar.idx (TypeIdx.ofNat i))) (pre ++ suffix)
  | _, [], _, _, _, hlo, hlt => by
      simp only [List.length_nil, Nat.add_zero] at hlt
      omega
  | start, u :: pre, suffix, x, hbound, hlo, hhi => by
      simp only [List.length_cons] at hbound hhi ⊢
      rw [show pre.length + 1 + suffix.length =
        (pre.length + suffix.length) + 1 by omega]
      rw [List.range'_succ, List.range'_succ]
      simp only [List.map_cons, List.cons_append, substTypeVar]
      have hstart : start < 2 ^ 32 := by omega
      have hval : (TypeIdx.ofNat start).val = start :=
        TypeIdx.ofNat_val_of_lt start hstart
      by_cases hx : x.val = start
      · have heq : x = TypeIdx.ofNat start :=
          Subtype.ext (by simpa [hval] using hx)
        simp [heq]
      · have hne : x ≠ TypeIdx.ofNat start := by
          intro heq
          apply hx
          simpa [hval] using congrArg Subtype.val heq
        rw [if_neg (by simpa using hne), if_neg (by simpa using hne)]
        exact substTypeVar_idxRange_prefix (start + 1) pre suffix x
          (by omega) (by omega) (by omega)

theorem substTypeVar_idxVars_prefix {pre suffix : List TypeUse}
    {x : TypeIdx} (hbound : pre.length + suffix.length ≤ 2 ^ 32)
    (hx : x.val < pre.length) :
    substTypeVar (.idx x) (idxVars pre.length) pre =
      substTypeVar (.idx x) (idxVars (pre ++ suffix).length)
        (pre ++ suffix) := by
  simpa [idxVars, List.range_eq_range', List.length_append] using
    substTypeVar_idxRange_prefix 0 pre suffix x (by omega) (by omega)
      (by simpa using hx)

theorem closDefTypesAux_length (acc rest : List DefType) :
    (closDefTypesAux acc rest).length = acc.length + rest.length := by
  induction rest generalizing acc with
  | nil => simp [closDefTypesAux]
  | cons dt rest ih =>
      rw [closDefTypesAux, ih]
      simp
      omega

theorem closDefTypesAux_prefix (acc rest : List DefType) :
    ∃ suffix, closDefTypesAux acc rest = acc ++ suffix := by
  induction rest generalizing acc with
  | nil => exact ⟨[], by simp [closDefTypesAux]⟩
  | cons dt rest ih =>
      let closed := substAllDefType dt (acc.map TypeUse.defd)
      obtain ⟨suffix, hsuffix⟩ := ih (acc ++ [closed])
      refine ⟨closed :: suffix, ?_⟩
      rw [closDefTypesAux, hsuffix]
      simp [closed, List.append_assoc]

private theorem closingEnvsAgree_of_prefix {f : Free}
    {pre suffix : List DefType}
    (hbound : pre.length + suffix.length ≤ 2 ^ 32)
    (hfree : TypesBelow pre.length f) :
    ClosingEnvsAgree f (pre.map TypeUse.defd)
      ((pre ++ suffix).map TypeUse.defd) := by
  intro x hx
  have hxlt := hfree x hx
  simpa [List.map_append] using
    (substTypeVar_idxVars_prefix
      (pre := pre.map TypeUse.defd)
      (suffix := suffix.map TypeUse.defd)
      (x := x) (by simpa using hbound) (by simpa using hxlt))

/-- Closing a causal source list sequentially is pointwise equal to closing
each raw entry against the final closed environment. -/
private theorem closDefTypesAux_get_full :
    ∀ (acc rest : List DefType),
      (∀ (k : Nat) (dt : DefType), rest[k]? = some dt →
        TypesBelow (acc.length + k) (freeDefType dt)) →
      acc.length + rest.length ≤ 2 ^ 32 →
      ∀ (k : Nat) (dt : DefType), rest[k]? = some dt →
        (closDefTypesAux acc rest)[acc.length + k]? =
          some (substAllDefType dt
            ((closDefTypesAux acc rest).map TypeUse.defd))
  | acc, [], _, _, k, dt, hlookup => by simp at hlookup
  | acc, raw :: rest, hcausal, hbound, k, dt, hlookup => by
      let closed := substAllDefType raw (acc.map TypeUse.defd)
      have hfinal : closDefTypesAux acc (raw :: rest) =
          closDefTypesAux (acc ++ [closed]) rest := rfl
      obtain ⟨suffix, hsuffix⟩ :=
        closDefTypesAux_prefix (acc ++ [closed]) rest
      cases k with
      | zero =>
          have hdt : dt = raw := by simpa using Option.some.inj hlookup.symm
          subst dt
          have hfree := hcausal 0 raw (by simp)
          have hagree : ClosingEnvsAgree (freeDefType raw)
              (acc.map TypeUse.defd)
              ((closDefTypesAux acc (raw :: rest)).map TypeUse.defd) := by
            rw [hfinal, hsuffix]
            have hsuffixLen : suffix.length = rest.length := by
              have hlen := congrArg List.length hsuffix
              rw [closDefTypesAux_length] at hlen
              simp only [List.length_append, List.length_cons] at hlen
              omega
            have hb : acc.length + (closed :: suffix).length ≤ 2 ^ 32 := by
              simp only [List.length_cons, hsuffixLen, List.length_cons] at hbound ⊢
              omega
            simpa only [List.append_assoc] using
              (closingEnvsAgree_of_prefix
                (pre := acc) (suffix := closed :: suffix) hb
                (by simpa using hfree))
          have heq := subst_defType_env raw
            (acc.map TypeUse.defd)
            ((closDefTypesAux acc (raw :: rest)).map TypeUse.defd) hagree
          have hleft :
              (closDefTypesAux acc (raw :: rest))[acc.length]? = some closed := by
            rw [hfinal, hsuffix]
            simp
          rw [Nat.add_zero, hleft]
          exact congrArg some heq
      | succ k =>
          have htailLookup : rest[k]? = some dt := by
            simpa using hlookup
          have htailCausal : ∀ (j : Nat) (d : DefType),
              rest[j]? = some d →
                TypesBelow ((acc ++ [closed]).length + j) (freeDefType d) := by
            intro j d hj
            have hb := hcausal (j + 1) d (by simpa using hj)
            intro x hx
            have := hb x hx
            simp only [List.length_append, List.length_singleton]
            omega
          have htailBound : (acc ++ [closed]).length + rest.length ≤
              2 ^ 32 := by
            simp only [List.length_append, List.length_singleton]
            simp only [List.length_cons] at hbound
            omega
          have ih := closDefTypesAux_get_full (acc ++ [closed]) rest
            htailCausal htailBound k dt htailLookup
          rw [hfinal]
          have hidx : acc.length + (k + 1) =
              (acc ++ [closed]).length + k := by
            simp [List.length_append]
            omega
          rw [hidx]
          exact ih

theorem closDefTypes_get_full {dts : List DefType}
    (hcausal : StoredFreeBefore dts) (hbound : dts.length ≤ 2 ^ 32)
    {i : Nat} {dt : DefType} (hlookup : dts[i]? = some dt) :
    (closDefTypes dts)[i]? = some
      (substAllDefType dt ((closDefTypes dts).map TypeUse.defd)) := by
  simpa [closDefTypes] using
    closDefTypesAux_get_full [] dts
      (by simpa using hcausal) (by simpa using hbound) i dt hlookup

theorem Type_okA.groupEnd_le {C : Context} {td : TypeDef}
    {group : List DefType} (h : Type_okA C td group) :
    C.types.length + group.length ≤ 2 ^ 32 := by
  cases h with
  | mk hrange hbase hgroup hrect =>
      rename_i base
      unfold TypeGroupRangeOk at hrange
      subst group
      have hlen : (rollDt base td.rectype).length = td.rectype.count := by
        cases td with
        | mk qt =>
            cases qt with
            | recr sts =>
                simp [rollDt, rollRt, RecType.count,
                  SubTypes.length_substSubTypes]
      simpa [hbase, hlen] using hrange.2

theorem Types_okA.totalEnd_le {C : Context} {tds : List TypeDef}
    {dts : List DefType} (hC : C.types.length ≤ 2 ^ 32)
    (h : Types_okA C tds dts) : C.types.length + dts.length ≤ 2 ^ 32 := by
  induction h with
  | empty => simpa using hC
  | @cons C td tds head tail hhead htail ih =>
      have hprefix := hhead.groupEnd_le
      have hrest := ih (by simpa [Context.append] using hprefix)
      simpa [Context.append, List.length_append, Nat.add_assoc] using hrest

theorem Types_okA.outputLength_le {tds : List TypeDef}
    {dts : List DefType} (h : Types_okA Context.empty tds dts) :
    dts.length ≤ 2 ^ 32 := by
  simpa [Context.empty] using h.totalEnd_le (by simp [Context.empty])

def recvTVars (n : Nat) : List TypeVar :=
  (List.range n).map TypeVar.recv

def unrollTUses (qt : RecType) (n : Nat) : List TypeUse :=
  (List.range n).map (fun j => TypeUse.defd (.defd qt j))

private theorem minus_all_recv : ∀ (tvs : List TypeVar)
    (tus : List TypeUse),
    (∀ tv ∈ tvs, ∃ j, tv = .recv j) →
    minusRecs tvs tus = ([], []) := by
  intro tvs
  induction tvs with
  | nil => intro tus _; cases tus <;> rfl
  | cons tv tvs ih =>
      intro tus hall
      obtain ⟨j, htv⟩ := hall tv (by simp)
      subst tv
      cases tus with
      | nil => simp [minusRecs]
      | cons tu tus =>
          simp only [minusRecs]
          exact ih tus (fun tv htv => hall tv (by simp [htv]))

theorem minus_recvTVars (qt : RecType) (n : Nat) :
    minusRecs (recvTVars n) (unrollTUses qt n) = ([], []) := by
  apply minus_all_recv
  intro tv htv
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp htv
  exact ⟨_, rfl⟩

theorem substRecType_unroll_id (qt inner : RecType) (n : Nat) :
    substRecType inner (recvTVars n) (unrollTUses qt n) = inner := by
  cases inner with
  | recr sts =>
      simp only [substRecType, minus_recvTVars]
      exact congrArg RecType.recr (subst_subTypes_nil sts)

theorem substDefType_unroll_id (qt : RecType) (n : Nat) (dt : DefType) :
    substDefType dt (recvTVars n) (unrollTUses qt n) = dt := by
  cases dt with
  | defd inner i =>
      simp only [substDefType]
      rw [substRecType_unroll_id]

def closeUse (closed : List DefType) (tu : TypeUse) : TypeUse :=
  substTypeUse tu (idxVars closed.length) (closed.map TypeUse.defd)

private theorem substTypeVar_mem_or' : ∀ (tv : TypeVar)
    (tvs : List TypeVar) (tus : List TypeUse),
    substTypeVar tv tvs tus ∈ tus ∨
      substTypeVar tv tvs tus = tv.toTypeUse := by
  intro tv tvs
  induction tvs with
  | nil => intro tus; exact Or.inr rfl
  | cons tv₁ tvs ih =>
      intro tus
      cases tus with
      | nil => exact Or.inr rfl
      | cons tu₁ tus =>
          by_cases h : tv = tv₁
          · rw [substTypeVar, if_pos h]
            exact Or.inl (by simp)
          · rw [substTypeVar, if_neg h]
            rcases ih tus with hmem | heq
            · exact Or.inl (by simp [hmem])
            · exact Or.inr heq

theorem unroll_close_idx (closed : List DefType) (qt : RecType)
    (n : Nat) (x : TypeIdx) :
    substTypeUse (closeUse closed (.idx x))
        (recvTVars n) (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) =
      closeUse closed (.idx x) := by
  unfold closeUse
  simp only [substTypeUse]
  rcases substTypeVar_mem_or' (.idx x) (idxVars closed.length)
      (closed.map TypeUse.defd) with hmem | heq
  · obtain ⟨dt, _, hdt⟩ := List.mem_map.mp hmem
    rw [← hdt]
    simp only [substTypeUse]
    rw [substDefType_unroll_id]
  · rw [heq]
    simp only [TypeVar.toTypeUse, substTypeUse]
    simpa [recvTVars, unrollTUses] using
      substTypeVar_unrollIdxVars x n
        (substRecType qt (idxVars closed.length)
          (closed.map TypeUse.defd))

/-- Closing source indices and unrolling recursive variables commute on the
declared-super type uses exposed by `unrollDt`. -/
theorem commute_close_unroll_typeuse (closed : List DefType)
    (qt : RecType) (n : Nat) (tu : TypeUse) :
    closeUse closed
        (substTypeUse tu (recvTVars n) (unrollTUses qt n)) =
      substTypeUse (closeUse closed tu) (recvTVars n)
        (unrollTUses
          (substRecType qt (idxVars closed.length)
            (closed.map TypeUse.defd)) n) := by
  cases tu with
  | idx x =>
      rw [show substTypeUse (.idx x) (recvTVars n) (unrollTUses qt n) =
          .idx x by
        simpa [recvTVars, unrollTUses] using
          substTypeVar_unrollIdxVars x n qt]
      exact (unroll_close_idx closed qt n x).symm
  | recu j =>
      unfold closeUse
      simp only [substTypeUse]
      have hu : substTypeVar (.recv j) (recvTVars n) (unrollTUses qt n) =
          (if j < n then .defd (.defd qt j) else .recu j) := by
        simpa [recvTVars, unrollTUses] using
          substTypeVar_unrollRecVars j n qt
      have hc : substTypeVar (.recv j) (idxVars closed.length)
          (closed.map TypeUse.defd) = .recu j := by
        simpa using substTypeVar_recv_idxVars j (closed.map TypeUse.defd)
      have huClosed : substTypeVar (.recv j) (recvTVars n)
          (unrollTUses
            (substRecType qt (idxVars closed.length)
              (closed.map TypeUse.defd)) n) =
          if j < n then
            .defd (.defd
              (substRecType qt (idxVars closed.length)
                (closed.map TypeUse.defd)) j)
          else .recu j := by
        simpa [recvTVars, unrollTUses] using
          substTypeVar_unrollRecVars j n
            (substRecType qt (idxVars closed.length)
              (closed.map TypeUse.defd))
      rw [hu, hc]
      simp only [substTypeUse]
      rw [huClosed]
      split
      · rfl
      · simpa [substTypeUse] using hc
  | defd dt =>
      unfold closeUse
      simp only [substTypeUse]
      rw [substDefType_unroll_id]
      rw [substDefType_unroll_id]

@[simp] theorem TypeUses.toList_substTypeUses' :
    ∀ (tus : TypeUses) (tvs : List TypeVar) (repls : List TypeUse),
      TypeUses.toList (substTypeUses tus tvs repls) =
        (TypeUses.toList tus).map (fun tu => substTypeUse tu tvs repls)
  | .nil, _, _ => rfl
  | .cons tu tus, tvs, repls => by
      simp [substTypeUses, TypeUses.toList,
        TypeUses.toList_substTypeUses' tus tvs repls]

def superUses (dt : DefType) : List TypeUse :=
  match unrollDt dt with
  | some (.sub _ sups _) => TypeUses.toList sups
  | none => []

theorem unrollDt_recr_eq (sts : SubTypes) (i : Nat) :
    unrollDt (.defd (.recr sts) i) =
      (SubTypes.toList sts)[i]?.map (fun st =>
        substSubType st (recvTVars (SubTypes.length sts))
          (unrollTUses (.recr sts) (SubTypes.length sts))) := by
  simp [unrollDt, unrollRt, recvTVars, unrollTUses,
    SubTypes.getElem?_substSubTypes]

/-- The declared-super list of a closed defined type is the pointwise closure
of the original declared-super list. -/
theorem superUses_substAll (closed : List DefType) (dt : DefType) :
    superUses (substAllDefType dt (closed.map TypeUse.defd)) =
      (superUses dt).map (closeUse closed) := by
  cases dt with
  | defd qt i =>
      cases qt with
      | recr sts =>
          let closeUses := closed.map TypeUse.defd
          have hrec : substRecType (.recr sts) (idxVars closeUses.length)
              closeUses = .recr (substSubTypes sts
                (idxVars closeUses.length) closeUses) := by
            simp only [substRecType]
            rw [minus_idxVars]
          simp only [substAllDefType, substDefType]
          rw [hrec]
          simp only [superUses, unrollDt_recr_eq,
            SubTypes.length_substSubTypes]
          rw [SubTypes.getElem?_substSubTypes]
          cases hsource : (SubTypes.toList sts)[i]? with
          | none => simp
          | some st =>
              cases st with
              | sub fin sups ct =>
                  simp only [Option.map_some, substSubType]
                  simp only [TypeUses.toList_substTypeUses', List.map_map]
                  apply List.map_congr_left
                  intro tu htu
                  have hcomm := (commute_close_unroll_typeuse closed
                    (.recr sts) (SubTypes.length sts) tu).symm
                  have hrecClosed : substRecType (.recr sts)
                      (idxVars closed.length) (closed.map TypeUse.defd) =
                      .recr (substSubTypes sts (idxVars closed.length)
                        (closed.map TypeUse.defd)) := by
                    simpa [closeUses] using hrec
                  rw [hrecClosed] at hcomm
                  simpa [Function.comp_apply, closeUse, closeUses] using hcomm

private theorem substTypeVar_idxRange_get :
    ∀ (start : Nat) (us : List TypeUse) (x : TypeIdx) (tu : TypeUse),
      start + us.length ≤ 2 ^ 32 → start ≤ x.val →
      us[x.val - start]? = some tu →
      substTypeVar (.idx x)
          ((List.range' start us.length).map
            (fun j => TypeVar.idx (TypeIdx.ofNat j))) us = tu
  | _, [], _, _, _, _, hlookup => by simp at hlookup
  | start, u :: us, x, tu, hbound, hlo, hlookup => by
      simp only [List.length_cons] at hbound ⊢
      rw [List.range'_succ]
      simp only [List.map_cons, substTypeVar]
      have hstart : start < 2 ^ 32 := by omega
      have hval : (TypeIdx.ofNat start).val = start :=
        TypeIdx.ofNat_val_of_lt start hstart
      by_cases hx : x.val = start
      · have heq : x = TypeIdx.ofNat start :=
          Subtype.ext (by simpa [hval] using hx)
        rw [if_pos (by simp [heq])]
        have hzero : x.val - start = 0 := by omega
        have hut : u = tu := by simpa [hzero] using hlookup
        exact hut
      · have hne : x ≠ TypeIdx.ofNat start := by
          intro heq
          apply hx
          simpa [hval] using congrArg Subtype.val heq
        rw [if_neg (by simpa using hne)]
        have htail : us[x.val - (start + 1)]? = some tu := by
          have hpos : 0 < x.val - start := by omega
          have heq : x.val - start = (x.val - (start + 1)) + 1 := by omega
          rw [heq] at hlookup
          simpa using hlookup
        exact substTypeVar_idxRange_get (start + 1) us x tu
          (by omega) (by omega) htail

theorem substTypeVar_idxVars_get {us : List TypeUse} {x : TypeIdx}
    {tu : TypeUse} (hbound : us.length ≤ 2 ^ 32)
    (hlookup : us[x.val]? = some tu) :
    substTypeVar (.idx x) (idxVars us.length) us = tu := by
  have hx : x.val < us.length := (List.getElem?_eq_some_iff.mp hlookup).1
  simpa [idxVars, List.range_eq_range'] using
    substTypeVar_idxRange_get 0 us x tu (by omega) (by omega)
      (by simpa using hlookup)

private theorem substTypeVar_idxRange_out :
    ∀ (start : Nat) (us : List TypeUse) (x : TypeIdx),
      start + us.length ≤ 2 ^ 32 →
      (x.val < start ∨ start + us.length ≤ x.val) →
      substTypeVar (.idx x)
          ((List.range' start us.length).map
            (fun j => TypeVar.idx (TypeIdx.ofNat j))) us = .idx x
  | _, [], _, _, _ => rfl
  | start, u :: us, x, hbound, hout => by
      simp only [List.length_cons] at hbound hout ⊢
      rw [List.range'_succ]
      simp only [List.map_cons, substTypeVar]
      have hstart : start < 2 ^ 32 := by omega
      have hval : (TypeIdx.ofNat start).val = start :=
        TypeIdx.ofNat_val_of_lt start hstart
      have hne : x ≠ TypeIdx.ofNat start := by
        intro heq
        have hx : x.val = start := by
          simpa [hval] using congrArg Subtype.val heq
        omega
      rw [if_neg (by simpa using hne)]
      exact substTypeVar_idxRange_out (start + 1) us x
        (by omega) (by omega)

theorem substTypeVar_idxVars_out {us : List TypeUse} {x : TypeIdx}
    (hbound : us.length ≤ 2 ^ 32) (hout : us.length ≤ x.val) :
    substTypeVar (.idx x) (idxVars us.length) us = .idx x := by
  simpa [idxVars, List.range_eq_range'] using
    substTypeVar_idxRange_out 0 us x (by omega) (Or.inr (by omega))

theorem closDefTypes_lookup_clos {dts : List DefType}
    (hcausal : StoredFreeBefore dts) (hbound : dts.length ≤ 2 ^ 32)
    {i : Nat} {dt : DefType} (hlookup : dts[i]? = some dt) :
    (closDefTypes dts)[i]? = some
      (({ Context.empty with types := dts } : Context).closDefType dt) := by
  simpa [Context.closDefType, Context.closTypes] using
    closDefTypes_get_full hcausal hbound hlookup

theorem closeUse_idx_of_lookup {dts : List DefType}
    (hcausal : StoredFreeBefore dts) (hbound : dts.length ≤ 2 ^ 32)
    {x : TypeIdx} {dt : DefType} (hlookup : dts[x.val]? = some dt) :
    closeUse (closDefTypes dts) (.idx x) = .defd
      (({ Context.empty with types := dts } : Context).closDefType dt) := by
  have hclosed := closDefTypes_lookup_clos hcausal hbound hlookup
  have hlen : (closDefTypes dts).length = dts.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] dts
  have hmap : ((closDefTypes dts).map TypeUse.defd)[x.val]? =
      some (.defd
        (({ Context.empty with types := dts } : Context).closDefType dt)) := by
    rw [List.getElem?_map]
    simp [hclosed]
  unfold closeUse
  simp only [substTypeUse]
  simpa using
    (substTypeVar_idxVars_get
      (us := (closDefTypes dts).map TypeUse.defd)
      (x := x)
      (tu := .defd
        (({ Context.empty with types := dts } : Context).closDefType dt))
      (by simpa [hlen] using hbound) hmap)

theorem closeUse_idx_of_none {dts : List DefType}
    (hbound : dts.length ≤ 2 ^ 32) {x : TypeIdx}
    (hlookup : dts[x.val]? = none) :
    closeUse (closDefTypes dts) (.idx x) = .idx x := by
  have hx : dts.length ≤ x.val := by
    exact Nat.le_of_not_gt (fun hlt => by
      have := List.getElem?_eq_getElem hlt
      rw [hlookup] at this
      simp at this)
  have hlen : (closDefTypes dts).length = dts.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] dts
  unfold closeUse
  simp only [substTypeUse]
  simpa using
    (substTypeVar_idxVars_out
      (us := (closDefTypes dts).map TypeUse.defd) (x := x)
      (by simpa [hlen] using hbound) (by simpa [hlen] using hx))

theorem closeUse_defd {dts : List DefType} (dt : DefType) :
    closeUse (closDefTypes dts) (.defd dt) = .defd
      (({ Context.empty with types := dts } : Context).closDefType dt) := by
  simp only [closeUse, substTypeUse, Context.closDefType,
    Context.closTypes, substAllDefType, List.length_map]

theorem closeUse_recu {dts : List DefType} (j : Nat) :
    closeUse (closDefTypes dts) (.recu j) = .recu j := by
  unfold closeUse
  simp only [substTypeUse]
  simpa using substTypeVar_recv_idxVars j
    ((closDefTypes dts).map TypeUse.defd)

theorem rankedBefore_reach_close_eq {dts : List DefType}
    (hcausal : StoredFreeBefore dts) (hbound : dts.length ≤ 2 ^ 32)
    {i : Nat} {source target : TypeUse}
    (hranked : Context.TypeUse.RankedBeforeA
      ({ Context.empty with types := dts } : Context) i source)
    (heq : closeUse (closDefTypes dts) source =
      closeUse (closDefTypes dts) target) :
    ({ Context.empty with types := dts } : Context).reachDef 1
      (.use source)
      (({ Context.empty with types := dts } : Context).resolveIdx
        (.use target)) = true := by
  cases hranked with
  | @idx x sourceDt hx hsourceLookup =>
      have hsourceClose := closeUse_idx_of_lookup hcausal hbound
        hsourceLookup
      rw [hsourceClose] at heq
      cases target with
      | idx y =>
          cases htargetLookup : dts[y.val]? with
          | none =>
              have htargetClose := closeUse_idx_of_none hbound htargetLookup
              rw [htargetClose] at heq
              contradiction
          | some targetDt =>
              have htargetClose := closeUse_idx_of_lookup hcausal hbound
                htargetLookup
              rw [htargetClose] at heq
              have hclos :
                  (({ Context.empty with types := dts } : Context).closDefType
                    sourceDt) =
                  (({ Context.empty with types := dts } : Context).closDefType
                    targetDt) := TypeUse.defd.inj heq
              simp [Context.reachDef, Context.heapSupers, Context.resolveIdx,
                hsourceLookup, htargetLookup, Context.heapEq,
                Context.normHeapType, hclos]
      | recu j =>
          have htargetClose := closeUse_recu (dts := dts) j
          rw [htargetClose] at heq
          contradiction
      | defd targetDt =>
          have htargetClose := closeUse_defd (dts := dts) targetDt
          rw [htargetClose] at heq
          have hclos :
              (({ Context.empty with types := dts } : Context).closDefType
                sourceDt) =
              (({ Context.empty with types := dts } : Context).closDefType
                targetDt) := TypeUse.defd.inj heq
          simp [Context.reachDef, Context.heapSupers, Context.resolveIdx,
            hsourceLookup, Context.heapEq, Context.normHeapType, hclos]
  | @defd j sourceDt hj hsourceLookup =>
      have hsourceClose := closeUse_defd (dts := dts) sourceDt
      rw [hsourceClose] at heq
      cases target with
      | idx y =>
          cases htargetLookup : dts[y.val]? with
          | none =>
              have htargetClose := closeUse_idx_of_none hbound htargetLookup
              rw [htargetClose] at heq
              contradiction
          | some targetDt =>
              have htargetClose := closeUse_idx_of_lookup hcausal hbound
                htargetLookup
              rw [htargetClose] at heq
              have hclos :
                  (({ Context.empty with types := dts } : Context).closDefType
                    sourceDt) =
                  (({ Context.empty with types := dts } : Context).closDefType
                    targetDt) := TypeUse.defd.inj heq
              simp [Context.reachDef, Context.resolveIdx, htargetLookup,
                Context.heapEq, Context.normHeapType, hclos]
      | recu k =>
          have htargetClose := closeUse_recu (dts := dts) k
          rw [htargetClose] at heq
          contradiction
      | defd targetDt =>
          have htargetClose := closeUse_defd (dts := dts) targetDt
          rw [htargetClose] at heq
          have hclos :
              (({ Context.empty with types := dts } : Context).closDefType
                sourceDt) =
              (({ Context.empty with types := dts } : Context).closDefType
                targetDt) := TypeUse.defd.inj heq
          simp [Context.reachDef, Context.resolveIdx, Context.heapEq,
            Context.normHeapType, hclos]

theorem heapSupers_defd_superUses (C : Context) (dt : DefType) :
    C.heapSupers (.use (.defd dt)) = (superUses dt).map HeapType.use := by
  cases hu : unrollDt dt with
  | none => simp [Context.heapSupers, superUses, hu]
  | some st =>
      cases st
      simp [Context.heapSupers, superUses, hu]

theorem rankedBefore_of_superUse {C : Context}
    (hstored : Context.StoredTypeSupersRankedA C)
    {i : Nat} {raw : DefType} (hlookup : C.types[i]? = some raw)
    {tu : TypeUse} (hmem : tu ∈ superUses raw) :
    Context.TypeUse.RankedBeforeA C i tu := by
  unfold superUses at hmem
  cases hu : unrollDt raw with
  | none => simp [hu] at hmem
  | some st =>
      cases st with
      | sub fin sups ct =>
          exact hstored i raw hlookup hu tu (by simpa [hu] using hmem)

/-- The full source-closure certificate required by executable amended heap
subtyping follows from checked source syntax, rather than from an assumed
completeness proposition. -/
theorem Types_okA.sourceTypeClosureOkA {tds : List TypeDef}
    {dts : List DefType} (hsyn : tds.all TypeDef.isSyn = true)
    (h : Types_okA Context.empty tds dts) :
    Context.SourceTypeClosureOkA
      ({ Context.empty with types := dts } : Context) := by
  have hcausal := h.storedFreeBefore hsyn
  have hbound := h.outputLength_le
  have hstored := h.storedTypeSupersRankedA hsyn
  intro i raw d hlookup heq g hg
  rw [heapSupers_defd_superUses] at hg
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hg
  have hclosEq := heapEq_defd heq
  have hclosEq' : substAllDefType raw
        ((closDefTypes dts).map TypeUse.defd) =
      substAllDefType d ((closDefTypes dts).map TypeUse.defd) := by
    simpa [Context.closDefType, Context.closTypes] using hclosEq
  have htargetClosed : closeUse (closDefTypes dts) target ∈
      superUses (substAllDefType d
        ((closDefTypes dts).map TypeUse.defd)) := by
    rw [superUses_substAll]
    exact List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [← hclosEq'] at htargetClosed
  rw [superUses_substAll] at htargetClosed
  obtain ⟨source, hsource, hclose⟩ := List.mem_map.mp htargetClosed
  have hranked := rankedBefore_of_superUse hstored hlookup hsource
  refine ⟨.use source, ?_, ?_⟩
  · rw [heapSupers_defd_superUses]
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  · exact rankedBefore_reach_close_eq hcausal hbound hranked hclose

end WasmGemmGnaf.Wasm.Core
