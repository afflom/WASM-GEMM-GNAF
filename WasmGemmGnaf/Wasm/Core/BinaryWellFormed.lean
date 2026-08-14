/-
  Wasm/Core/BinaryWellFormed.lean --- values synthesized by the amended Core
  binary grammar satisfy every intrinsic Core syntax side condition.

  This file imports the declarative binary grammar only.  In particular, the
  theorem below is not obtained from either the executable decoder or the
  canonical encoder.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

/-! ## Floating immediates -/

omit authority in
theorem Bf32.wf_of {bs : Bytes} {p : F32} (h : Bf32 bs p) : FN.wf p = true := by
  rcases h with ⟨bl, hrep, hinv⟩
  have hlen : bl.length = 4 := by simpa using hrep.length
  let m : Nat := leNat bl % 2 ^ 23
  let e : Nat := leNat bl / 2 ^ 23 % 2 ^ 8
  let mag : FNMag 32 :=
    if e = 0 then .subnorm m
    else if e = 2 ^ 8 - 1 then (if m = 0 then .inf else .nan m)
    else .norm m ((e : Int) - ((2 ^ (8 - 1) - 1 : Nat) : Int))
  let decoded : FN 32 :=
    if leNat bl / 2 ^ (23 + 8) % 2 = 0 then .pos mag else .neg mag
  have hp : decoded = p := by
    apply Option.some.inj
    simpa [decoded, mag, m, e, invFbytes, signif, expon, hlen] using hinv
  rw [← hp]
  have hm : m < 2 ^ 23 := by
    exact Nat.mod_lt _ (two_pow_pos 23)
  have he : e < 2 ^ 8 := by
    exact Nat.mod_lt _ (two_pow_pos 8)
  have hmag : FNMag.wf mag = true := by
    unfold mag
    by_cases he0 : e = 0
    · simp [he0, FNMag.wf, signif, hm]
    · rw [if_neg he0]
      by_cases hemax : e = 2 ^ 8 - 1
      · rw [if_pos hemax]
        by_cases hm0 : m = 0
        · simp [hm0, FNMag.wf]
        · simp [hm0, FNMag.wf, signif, hm]; omega
      · rw [if_neg hemax]
        simp [FNMag.wf, signif, expon, hm]
        have helo : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
        have hehi : e ≤ 254 := by omega
        have heloI : (1 : Int) ≤ (e : Int) := Int.ofNat_le.mpr helo
        have hehiI : (e : Int) ≤ (254 : Int) := Int.ofNat_le.mpr hehi
        constructor
        · simpa using Int.sub_le_sub_right heloI 127
        · simpa using Int.sub_le_sub_right hehiI 127
  unfold decoded
  split <;> simpa [FN.wf] using hmag

omit authority in
theorem Bf64.wf_of {bs : Bytes} {p : F64} (h : Bf64 bs p) : FN.wf p = true := by
  rcases h with ⟨bl, hrep, hinv⟩
  have hlen : bl.length = 8 := by simpa using hrep.length
  let m : Nat := leNat bl % 2 ^ 52
  let e : Nat := leNat bl / 2 ^ 52 % 2 ^ 11
  let mag : FNMag 64 :=
    if e = 0 then .subnorm m
    else if e = 2 ^ 11 - 1 then (if m = 0 then .inf else .nan m)
    else .norm m ((e : Int) - ((2 ^ (11 - 1) - 1 : Nat) : Int))
  let decoded : FN 64 :=
    if leNat bl / 2 ^ (52 + 11) % 2 = 0 then .pos mag else .neg mag
  have hp : decoded = p := by
    apply Option.some.inj
    simpa [decoded, mag, m, e, invFbytes, signif, expon, hlen] using hinv
  rw [← hp]
  have hm : m < 2 ^ 52 := by
    exact Nat.mod_lt _ (two_pow_pos 52)
  have he : e < 2 ^ 11 := by
    exact Nat.mod_lt _ (two_pow_pos 11)
  have hmag : FNMag.wf mag = true := by
    unfold mag
    by_cases he0 : e = 0
    · simp [he0, FNMag.wf, signif, hm]
    · rw [if_neg he0]
      by_cases hemax : e = 2 ^ 11 - 1
      · rw [if_pos hemax]
        by_cases hm0 : m = 0
        · simp [hm0, FNMag.wf]
        · simp [hm0, FNMag.wf, signif, hm]; omega
      · rw [if_neg hemax]
        simp [FNMag.wf, signif, expon, hm]
        have helo : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
        have hehi : e ≤ 2046 := by omega
        have heloI : (1 : Int) ≤ (e : Int) := Int.ofNat_le.mpr helo
        have hehiI : (e : Int) ≤ (2046 : Int) := Int.ofNat_le.mpr hehi
        constructor
        · simpa using Int.sub_le_sub_right heloI 1023
        · simpa using Int.sub_le_sub_right hehiI 1023
  unfold decoded
  split <;> simpa [FN.wf] using hmag

/-! ## Instruction leaves -/

theorem BinstrParametric.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrParametric bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrControlFor.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrControlFor bs i) : Instr.wf i = true := by
  cases hr : authority.revision with
  | pinned =>
      simp [BinstrControlFor, hr] at h
      cases h <;> simp [Instr.wf]
  | amended =>
      simp [BinstrControlFor, hr] at h
      cases h with
      | ofPinned _ _ hp => cases hp <;> rfl
      | callRef => rfl
      | returnCallRef => rfl

theorem BinstrLocal.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrLocal bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrGlobal.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrGlobal bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrTable.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrTable bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrMemory.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrMemory bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf, LoadOp.wf, StoreOp.wf] <;> decide

theorem BinstrRef.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrRef bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrStruct.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrStruct bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrArray.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrArray bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrCast.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrCast bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrExtern.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrExtern bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrI31.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrI31 bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

omit authority in
theorem BinstrNumA.wf_of {bs : Bytes} {i : Instr}
    (h : @BinstrNumFor amendedBinaryAuthority bs i) : Instr.wf i = true := by
  change BinstrNum' bs i at h
  cases h
  case ofPinned =>
      rename_i hne hp
      cases hp
      all_goals simp_all [Instr.wf, Num_.wf, Unop.wf, Binop.wf, Testop.wf,
        Relop.wf, Cvtop.wf, pinnedBadPromote]
      all_goals try decide
      case f32Const => exact Bf32.wf_of (by assumption)
      case f64Const => exact Bf64.wf_of (by assumption)
  case f64PromoteF32 => simpa [Instr.wf] using correctedPromote_wf

theorem BinstrVecMem.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrVecMem bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf, VLoadOp.wf]
  case i8x16Shuffle =>
    have hlen := Rep.length (by assumption)
    simp_all [Shape.wf]
    exact (by decide)
  all_goals exact (by decide)

theorem BinstrVecRel.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrVecRel bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf, Shape.wf, VRelop.wf] <;> decide

theorem BinstrVecV128.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrVecV128 bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf]

theorem BinstrVecInt8And16.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrVecInt8And16 bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf, Shape.wf, VUnop.wf, VBinop.wf, VTernop.wf,
    VTestop.wf, VRelop.wf, VExtUnop.wf, VExtBinop.wf, VExtTernop.wf,
    VCvtop.wf] <;> decide

omit authority in
theorem BinstrVecInt32And64A.wf_of {bs : Bytes} {i : Instr}
    (h : @BinstrVecInt32And64For amendedBinaryAuthority bs i) : Instr.wf i = true := by
  change BinstrVecInt32And64' bs i at h
  cases h
  case ofPinned =>
      rename_i hp hne
      cases hp
      all_goals simp_all [Instr.wf, Shape.wf, VUnop.wf, VBinop.wf, VTernop.wf,
        VTestop.wf, VRelop.wf, VExtUnop.wf, VExtBinop.wf, VExtTernop.wf,
        VCvtop.wf, pinnedBadRelaxedDotAdd]
      all_goals exact of_decide_eq_true rfl
  case correctedRelaxedDotAdd => exact correctedRelaxedDotAdd_wf

theorem BinstrVecFloat.wf_of {bs : Bytes} {i : Instr}
    (h : BinstrVecFloat bs i) : Instr.wf i = true := by
  cases h <;> simp [Instr.wf, Shape.wf, VUnop.wf, VBinop.wf, VTernop.wf,
    VTestop.wf, VRelop.wf, VExtUnop.wf, VExtBinop.wf, VExtTernop.wf,
    VCvtop.wf] <;> decide

/-! ## Grammar lists -/

omit authority in
theorem Rep.all_of {α : Type} {G : Bytes → α → Prop} {P : α → Bool}
    (hP : ∀ {bs : Bytes} {x : α}, G bs x → P x = true)
    {n : Nat} {bs : Bytes} {xs : List α} (h : Rep G n bs xs) :
    xs.all P = true := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ hx _ ih => simp [hP hx, ih]

omit authority in
theorem Blist.all_of {α : Type} {G : Bytes → α → Prop} {P : α → Bool}
    (hP : ∀ {bs : Bytes} {x : α}, G bs x → P x = true)
    {bs : Bytes} {xs : List α} (h : Blist G bs xs) : xs.all P = true := by
  cases h with
  | mk _ _ _ _ _ hrep => exact Rep.all_of (G := G) (P := P) hP hrep

omit authority in
theorem ValTypes.wfList_ofList : ∀ l : List ValType,
    (ValTypes.ofList l).wfList = l.all ValType.wfList
  | [] => rfl
  | t :: ts => by
      simp [ValTypes.ofList, ValTypes.wfList, ValTypes.wfList_ofList ts]

omit authority in
theorem TypeUses.wfList_ofList : ∀ l : List TypeUse,
    (TypeUses.ofList l).wfList = l.all TypeUse.wfList
  | [] => rfl
  | tu :: tus => by
      simp [TypeUses.ofList, TypeUses.wfList, TypeUses.wfList_ofList tus]

omit authority in
theorem FieldTypes.wfList_ofList : ∀ l : List FieldType,
    (FieldTypes.ofList l).wfList = l.all FieldType.wfList
  | [] => rfl
  | ft :: fts => by
      simp [FieldTypes.ofList, FieldTypes.wfList, FieldTypes.wfList_ofList fts]

omit authority in
theorem SubTypes.wfList_ofList : ∀ l : List SubType,
    (SubTypes.ofList l).wfList = l.all SubType.wfList
  | [] => rfl
  | st :: sts => by
      simp [SubTypes.ofList, SubTypes.wfList, SubTypes.wfList_ofList sts]

omit authority in
theorem ValTypes.wfList_of_all {ts : ValTypes}
    (h : ts.toList.all ValType.wfList = true) : ts.wfList = true := by
  rw [← ValTypes.ofList_toList ts]
  rw [ValTypes.wfList_ofList]
  exact h

omit authority in
theorem TypeUses.wfList_of_all {tus : TypeUses}
    (h : tus.toList.all TypeUse.wfList = true) : tus.wfList = true := by
  rw [← TypeUses.ofList_toList tus]
  rw [TypeUses.wfList_ofList]
  exact h

omit authority in
theorem FieldTypes.wfList_of_all {fts : FieldTypes}
    (h : fts.toList.all FieldType.wfList = true) : fts.wfList = true := by
  rw [← FieldTypes.ofList_toList fts]
  rw [FieldTypes.wfList_ofList]
  exact h

omit authority in
theorem SubTypes.wfList_of_all {sts : SubTypes}
    (h : sts.toList.all SubType.wfList = true) : sts.wfList = true := by
  rw [← SubTypes.ofList_toList sts]
  rw [SubTypes.wfList_ofList]
  exact h

omit authority in
@[simp] theorem FieldTypes.length_toList : ∀ fts : FieldTypes,
    fts.toList.length = fts.length
  | .nil => rfl
  | .cons _ fts => by
      simp [FieldTypes.toList, FieldTypes.length, FieldTypes.length_toList fts]

omit authority in
@[simp] theorem SubTypes.length_toList : ∀ sts : SubTypes,
    sts.toList.length = sts.length
  | .nil => rfl
  | .cons _ sts => by
      simp [SubTypes.toList, SubTypes.length, SubTypes.length_toList sts]

/-! ## Type syntax synthesized by the grammar -/

theorem Bheaptype.syn_wfList_of {bs : Bytes} {ht : HeapType}
    (h : Bheaptype bs ht) : ht.isSyn = true ∧ ht.wfList = true := by
  cases h
  case abs =>
    rename_i ha
    cases ha <;> decide
  case idx => exact ⟨rfl, rfl⟩

theorem Breftype.syn_wfList_of {bs : Bytes} {rt : RefType}
    (h : Breftype bs rt) : rt.isSyn = true ∧ rt.wfList = true := by
  cases h with
  | null _ _ hh | nonNull _ _ hh => simpa [RefType.isSyn, RefType.wfList] using hh.syn_wfList_of
  | abs _ _ ha => cases ha <;> decide

theorem Bvaltype.syn_wfList_of {bs : Bytes} {t : ValType}
    (h : Bvaltype bs t) : t.isSyn = true ∧ t.wfList = true := by
  cases h
  case num => exact ⟨rfl, rfl⟩
  case vec => exact ⟨rfl, rfl⟩
  case ref =>
    rename_i _ hr
    simpa [ValType.isSyn, ValType.wfList] using hr.syn_wfList_of

theorem Bstoragetype.syn_wfList_of {bs : Bytes} {zt : StorageType}
    (h : Bstoragetype bs zt) : zt.isSyn = true ∧ zt.wfList = true := by
  cases h
  case val =>
    rename_i _ ht
    simpa [StorageType.isSyn, StorageType.wfList] using ht.syn_wfList_of
  case pack => exact ⟨rfl, rfl⟩

theorem Bfieldtype.syn_wfList_of {bs : Bytes} {ft : FieldType}
    (h : Bfieldtype bs ft) : ft.isSyn = true ∧ ft.wfList = true := by
  cases h with
  | mk _ _ _ _ hz _ => simpa [FieldType.isSyn, FieldType.wfList] using hz.syn_wfList_of

theorem Bcomptype.syn_wfList_of {bs : Bytes} {ct : CompType}
    (h : Bcomptype bs ct) : ct.isSyn = true ∧ ct.wfList = true := by
  cases h with
  | array _ _ hf =>
      simpa [CompType.isSyn, CompType.wfList] using hf.syn_wfList_of
  | struct _ fts hfs =>
      have hsyn : fts.toList.all FieldType.isSyn = true :=
        hfs.all_of (fun h => h.syn_wfList_of.1)
      have hwfAll : fts.toList.all FieldType.wfList = true :=
        hfs.all_of (fun h => h.syn_wfList_of.2)
      have hwf := FieldTypes.wfList_of_all hwfAll
      have hlen := hfs.length_lt
      rw [FieldTypes.length_toList] at hlen
      simp [CompType.isSyn, CompType.wfList, hsyn, hwf, hlen]
  | func _ _ dom cod hd hc =>
      have hds : dom.toList.all ValType.isSyn = true :=
        hd.all_of (fun h => h.syn_wfList_of.1)
      have hcs : cod.toList.all ValType.isSyn = true :=
        hc.all_of (fun h => h.syn_wfList_of.1)
      have hdwAll : dom.toList.all ValType.wfList = true :=
        hd.all_of (fun h => h.syn_wfList_of.2)
      have hcwAll : cod.toList.all ValType.wfList = true :=
        hc.all_of (fun h => h.syn_wfList_of.2)
      have hdw := ValTypes.wfList_of_all hdwAll
      have hcw := ValTypes.wfList_of_all hcwAll
      have hdl := hd.length_lt
      have hcl := hc.length_lt
      rw [ValTypes.length_toList] at hdl hcl
      simp [CompType.isSyn, CompType.wfList, hds, hcs, hdw, hcw, hdl, hcl]

theorem Bsubtype.syn_wfList_of {bs : Bytes} {st : SubType}
    (h : Bsubtype bs st) : st.isSyn = true ∧ st.wfList = true := by
  cases h with
  | finalSub _ _ xs tus ct _ hc heq | openSub _ _ xs tus ct _ hc heq =>
      have hct := hc.syn_wfList_of
      have htusSyn : tus.toList.all TypeUse.isSyn = true := by
        rw [heq]
        simp [TypeUse.isSyn]
      have htusWfAll : tus.toList.all TypeUse.wfList = true := by
        rw [heq]
        simp [TypeUse.wfList]
      have htusWf := TypeUses.wfList_of_all htusWfAll
      simp [SubType.isSyn, SubType.wfList, htusSyn, htusWf, hct]
  | bare _ _ hc =>
      have hct := hc.syn_wfList_of
      constructor
      · simpa [SubType.isSyn, TypeUses.toList, TypeUse.isSyn] using hct.1
      · simpa [SubType.wfList, TypeUses.wfList] using hct.2

theorem Brectype.syn_wfList_of {bs : Bytes} {rt : RecType}
    (h : Brectype bs rt) : rt.isSyn = true ∧ rt.wfList = true := by
  cases h with
  | recGroup _ sts hs =>
      have hsyn : sts.toList.all SubType.isSyn = true :=
        hs.all_of (fun h => h.syn_wfList_of.1)
      have hwfAll : sts.toList.all SubType.wfList = true :=
        hs.all_of (fun h => h.syn_wfList_of.2)
      have hwf := SubTypes.wfList_of_all hwfAll
      have hlen := hs.length_lt
      rw [SubTypes.length_toList] at hlen
      simp [RecType.isSyn, RecType.wfList, hsyn, hwf, hlen]
  | single _ st hs =>
      have hst := hs.syn_wfList_of
      constructor
      · simpa [RecType.isSyn, SubTypes.toList] using hst.1
      · simp [RecType.wfList, SubTypes.length, SubTypes.wfList, hst.2]

theorem Bglobaltype.isSyn_of {bs : Bytes} {gt : GlobalType}
    (h : Bglobaltype bs gt) : gt.isSyn = true := by
  cases h with
  | mk _ _ _ _ ht _ => simpa [GlobalType.isSyn] using ht.syn_wfList_of.1

theorem Btabletype.isSyn_of {bs : Bytes} {tt : TableType}
    (h : Btabletype bs tt) : tt.isSyn = true := by
  cases h with
  | mk _ _ _ _ _ hr _ => simpa [TableType.isSyn] using hr.syn_wfList_of.1

theorem Bexterntype.isSyn_of {bs : Bytes} {xt : ExternType}
    (h : Bexterntype bs xt) : xt.isSyn = true := by
  cases h with
  | func => rfl
  | table _ _ ht => simpa [ExternType.isSyn] using ht.isSyn_of
  | mem => rfl
  | global _ _ hg => simpa [ExternType.isSyn] using hg.isSyn_of
  | tag _ _ hj => cases hj; rfl

theorem Bblocktype.isSyn_of {bs : Bytes} {bt : BlockType}
    (h : Bblocktype bs bt) : bt.isSyn = true := by
  cases h with
  | empty => rfl
  | val _ _ ht => simpa [BlockType.isSyn] using ht.syn_wfList_of.1
  | idx => rfl

/-! ## Instruction `/syn` invariant and recursive closure -/

theorem BinstrParametric.isSyn_of {bs : Bytes} {i : Instr}
    (h : BinstrParametric bs i) : Instr.isSyn i = true := by
  cases h with
  | unreachable | nop | drop | select => rfl
  | selectT _ ts hts =>
      have hs : ts.all ValType.isSyn = true :=
        hts.all_of (fun h => h.syn_wfList_of.1)
      simpa [Instr.isSyn, hs]

theorem BinstrControlFor.isSyn_of {bs : Bytes} {i : Instr}
    (h : BinstrControlFor bs i) : Instr.isSyn i = true := by
  cases hr : authority.revision with
  | pinned =>
      simp [BinstrControlFor, hr] at h
      cases h <;> rfl
  | amended =>
      simp [BinstrControlFor, hr] at h
      cases h
      case ofPinned =>
        rename_i hp
        cases hp <;> rfl
      case callRef => rfl
      case returnCallRef => rfl

theorem BinstrRef.isSyn_of {bs : Bytes} {i : Instr}
    (h : BinstrRef bs i) : Instr.isSyn i = true := by
  cases h with
  | null _ _ hh => simpa [Instr.isSyn] using hh.syn_wfList_of.1
  | isNull | func | eq | asNonNull | brOnNull | brOnNonNull => rfl

theorem BinstrCast.isSyn_of {bs : Bytes} {i : Instr}
    (h : BinstrCast bs i) : Instr.isSyn i = true := by
  cases h with
  | test _ _ _ _ hh =>
      simpa [Instr.isSyn, RefType.isSyn] using hh.syn_wfList_of.1
  | testNull _ _ _ _ hh =>
      simpa [Instr.isSyn, RefType.isSyn] using hh.syn_wfList_of.1
  | cast _ _ _ _ hh =>
      simpa [Instr.isSyn, RefType.isSyn] using hh.syn_wfList_of.1
  | castNull _ _ _ _ hh =>
      simpa [Instr.isSyn, RefType.isSyn] using hh.syn_wfList_of.1
  | brOnCast _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
      have hs₁ := h₁.syn_wfList_of.1
      have hs₂ := h₂.syn_wfList_of.1
      simp [Instr.isSyn, RefType.isSyn, hs₁, hs₂]
  | brOnCastFail _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
      have hs₁ := h₁.syn_wfList_of.1
      have hs₂ := h₂.syn_wfList_of.1
      simp [Instr.isSyn, RefType.isSyn, hs₁, hs₂]

omit authority in
theorem BinstrNumA.isSyn_of {bs : Bytes} {i : Instr}
    (h : @BinstrNumFor amendedBinaryAuthority bs i) : Instr.isSyn i = true := by
  change BinstrNum' bs i at h
  cases h
  case ofPinned =>
    rename_i _ hp
    cases hp <;> rfl
  case f64PromoteF32 => rfl

omit authority in
theorem BinstrVecInt32And64A.isSyn_of {bs : Bytes} {i : Instr}
    (h : @BinstrVecInt32And64For amendedBinaryAuthority bs i) : Instr.isSyn i = true := by
  change BinstrVecInt32And64' bs i at h
  cases h
  case ofPinned =>
    rename_i hp _
    cases hp <;> rfl
  case correctedRelaxedDotAdd => rfl

omit authority in
theorem BinstrA.wf_isSyn_of {bs : Bytes} {i : Instr}
    (h : @Binstr amendedBinaryAuthority bs i) :
    Instr.wf i = true ∧ Instr.isSyn i = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Binstr bs i at h
  induction h using Binstr.rec
      (motive_2 := fun _ ins _ =>
        InstrSeq.wf (InstrSeq.ofList ins) = true ∧
        InstrSeq.isSyn (InstrSeq.ofList ins) = true) with
  | block _ _ _ _ hbt _ ih | loop _ _ _ _ hbt _ ih =>
      have hsyn := hbt.isSyn_of
      simpa [Instr.wf, Instr.isSyn] using ⟨ih.1, hsyn, ih.2⟩
  | ifThen _ _ _ _ hbt _ ih =>
      have hsyn := hbt.isSyn_of
      exact
        ⟨by simp [Instr.wf, InstrSeq.wf, ih.1],
         by simp [Instr.isSyn, InstrSeq.isSyn, hsyn, ih.2]⟩
  | ifElse _ _ _ _ _ _ hbt _ _ ih₁ ih₂ =>
      have hsyn := hbt.isSyn_of
      simp [Instr.wf, Instr.isSyn, hsyn, ih₁, ih₂]
  | tryTable _ _ _ _ _ _ hbt _ _ ih =>
      have hsyn := hbt.isSyn_of
      simpa [Instr.wf, Instr.isSyn] using ⟨ih.1, hsyn, ih.2⟩
  | ofParametric _ _ hp => exact ⟨hp.wf_of, hp.isSyn_of⟩
  | ofControl _ _ hc => exact ⟨hc.wf_of, hc.isSyn_of⟩
  | ofLocal _ _ hl => exact ⟨hl.wf_of, by cases hl <;> rfl⟩
  | ofGlobal _ _ hg => exact ⟨hg.wf_of, by cases hg <;> rfl⟩
  | ofTable _ _ ht => exact ⟨ht.wf_of, by cases ht <;> rfl⟩
  | ofMemory _ _ hm => exact ⟨hm.wf_of, by cases hm <;> rfl⟩
  | ofRef _ _ hr => exact ⟨hr.wf_of, hr.isSyn_of⟩
  | ofStruct _ _ hs => exact ⟨hs.wf_of, by cases hs <;> rfl⟩
  | ofArray _ _ ha => exact ⟨ha.wf_of, by cases ha <;> rfl⟩
  | ofCast _ _ hc => exact ⟨hc.wf_of, hc.isSyn_of⟩
  | ofExtern _ _ he => exact ⟨he.wf_of, by cases he <;> rfl⟩
  | ofI31 _ _ hi => exact ⟨hi.wf_of, by cases hi <;> rfl⟩
  | ofNum _ _ hn => exact ⟨BinstrNumA.wf_of hn, BinstrNumA.isSyn_of hn⟩
  | ofVecMem _ _ hv => exact ⟨hv.wf_of, by cases hv <;> rfl⟩
  | ofVecRel _ _ hv => exact ⟨hv.wf_of, by cases hv <;> rfl⟩
  | ofVecV128 _ _ hv => exact ⟨hv.wf_of, by cases hv <;> rfl⟩
  | ofVecInt8And16 _ _ hv => exact ⟨hv.wf_of, by cases hv <;> rfl⟩
  | ofVecInt32And64 _ _ hv =>
      exact ⟨BinstrVecInt32And64A.wf_of hv, BinstrVecInt32And64A.isSyn_of hv⟩
  | ofVecFloat _ _ hv => exact ⟨hv.wf_of, by cases hv <;> rfl⟩
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ ih₁ ih₂ =>
      exact
        ⟨by simp [InstrSeq.ofList, InstrSeq.wf, ih₁.1, ih₂.1],
         by simp [InstrSeq.ofList, InstrSeq.isSyn, ih₁.2, ih₂.2]⟩

omit authority in
theorem BinstrsA.wf_isSyn_of {bs : Bytes} {ins : List Instr}
    (h : @Binstrs amendedBinaryAuthority bs ins) :
    InstrSeq.wf (InstrSeq.ofList ins) = true ∧
    InstrSeq.isSyn (InstrSeq.ofList ins) = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Binstrs bs ins at h
  have hblock :
      Binstr
        (tb 0x02 :: ([tb 0x40] ++ bs ++ [tb 0x0B]))
        (.block (.result none) (InstrSeq.ofList ins)) :=
    Binstr.block [tb 0x40] bs (.result none) ins Bblocktype.empty h
  simpa [Instr.wf, Instr.isSyn, BlockType.isSyn] using
    BinstrA.wf_isSyn_of hblock

omit authority in
theorem BexprA.wf_isSyn_of {bs : Bytes} {e : Expr}
    (h : @Bexpr amendedBinaryAuthority bs e) :
    InstrSeq.wf e = true ∧ InstrSeq.isSyn e = true := by
  cases h with
  | mk _ _ hs => exact BinstrsA.wf_isSyn_of hs

/-! ## Module entries -/

omit authority in
theorem Bsection.blist_all_of {α : Type} {G : Bytes → α → Prop}
    {P : α → Bool} (hP : ∀ {bs : Bytes} {x : α}, G bs x → P x = true)
    {n : Nat} {bs : Bytes} {xs : List α}
    (h : Bsection n (Blist G) bs xs) : xs.all P = true := by
  cases h with
  | absent => rfl
  | present _ _ _ _ _ hxs _ =>
      exact Blist.all_of (G := G) (P := P) (fun h => hP h) hxs

omit authority in
theorem List.all_flatten_eq {α : Type} (P : α → Bool) :
    ∀ xss : List (List α), xss.flatten.all P = xss.all (fun xs => xs.all P)
  | [] => rfl
  | xs :: xss => by simp [List.all_flatten_eq P xss]

omit authority in
theorem List.zipWith_all_of_right {α β γ : Type} (f : α → β → γ)
    (P : β → Bool) (Q : γ → Bool)
    (hf : ∀ x y, P y = true → Q (f x y) = true) :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      ys.all P = true → (List.zipWith f xs ys).all Q = true
  | [], [], _, _ => rfl
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hall => by
      have hlen' : xs.length = ys.length := by simp at hlen; exact hlen
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp only [List.zipWith, List.all_cons, Bool.and_eq_true]
      exact ⟨hf x y hall.1, List.zipWith_all_of_right f P Q hf hlen' hall.2⟩

theorem Btype.wf_isSyn_of {bs : Bytes} {td : TypeDef}
    (h : Btype bs td) : TypeDef.wf td = true ∧ TypeDef.isSyn td = true := by
  cases h with
  | mk _ hrt =>
      have hq := hrt.syn_wfList_of
      exact ⟨by simpa [TypeDef.wf] using hq.2,
        by simpa [TypeDef.isSyn] using hq.1⟩

theorem Bimport.isSyn_of {bs : Bytes} {im : Import}
    (h : Bimport bs im) : Import.isSyn im = true := by
  cases h with
  | mk _ _ _ _ _ _ _ _ hxt => simpa [Import.isSyn] using hxt.isSyn_of

theorem Btag.isSyn_of {bs : Bytes} {tag : Tag}
    (h : Btag bs tag) : Tag.isSyn tag = true := by
  cases h with
  | mk _ hj => cases hj; rfl

omit authority in
theorem refFuncExprs.wf_isSyn (ys : List FuncIdx) :
    (refFuncExprs ys).all InstrSeq.wf = true ∧
    (refFuncExprs ys).all InstrSeq.isSyn = true := by
  induction ys with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ ys ih =>
      simpa [refFuncExprs, InstrSeq.wf, Instr.wf, InstrSeq.isSyn, Instr.isSyn]
        using ih

omit authority in
theorem nullRefExpr.wf_isSyn (ht : HeapType) (hsyn : ht.isSyn = true) :
    InstrSeq.wf (.cons (.refNull ht) .nil) = true ∧
    InstrSeq.isSyn (.cons (.refNull ht) .nil) = true := by
  simp [InstrSeq.wf, Instr.wf, InstrSeq.isSyn, Instr.isSyn, hsyn]

omit authority in
theorem BtableA.wf_isSyn_of {bs : Bytes} {table : Table}
    (h : @Btable amendedBinaryAuthority bs table) :
    Table.wf table = true ∧ Table.isSyn table = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Btable bs table at h
  cases h with
  | shorthand _ tt nul ht htt heq =>
      have httsyn := htt.isSyn_of
      have hht : ht.isSyn = true := by
        simpa [TableType.isSyn, heq, RefType.isSyn] using httsyn
      have hinit := nullRefExpr.wf_isSyn ht hht
      exact ⟨by simpa [Table.wf] using hinit.1,
        by simp [Table.isSyn, httsyn, hinit.2]⟩
  | withInit _ _ _ _ htt he =>
      have httsyn := htt.isSyn_of
      have he' := BexprA.wf_isSyn_of he
      exact ⟨by simpa [Table.wf] using he'.1,
        by simp [Table.isSyn, httsyn, he'.2]⟩

omit authority in
theorem BglobalA.wf_isSyn_of {bs : Bytes} {global : Global}
    (h : @Bglobal amendedBinaryAuthority bs global) :
    Global.wf global = true ∧ Global.isSyn global = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Bglobal bs global at h
  cases h with
  | mk _ _ _ _ hgt he =>
      have hgtsyn := hgt.isSyn_of
      have he' := BexprA.wf_isSyn_of he
      exact ⟨by simpa [Global.wf] using he'.1,
        by simp [Global.isSyn, hgtsyn, he'.2]⟩

theorem Blocals.isSyn_of {bs : Bytes} {locals : List Local}
    (h : Blocals bs locals) :
    locals.all (fun l => l.valtype.isSyn) = true := by
  cases h with
  | mk _ _ n t _ ht =>
      have htsyn := ht.syn_wfList_of.1
      simp [htsyn]

omit authority in
theorem BfuncA.wf_isSyn_of {bs : Bytes} {code : Code}
    (h : @Bfunc amendedBinaryAuthority bs code) :
    InstrSeq.wf code.2 = true ∧
    (code.1.all (fun l => l.valtype.isSyn) && InstrSeq.isSyn code.2) = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Bfunc bs code at h
  cases h with
  | mk _ _ locss e hlocals he _ =>
      have hlocalRuns : locss.all (fun ls => ls.all (fun l => l.valtype.isSyn)) = true :=
        hlocals.all_of (fun h => h.isSyn_of)
      have hlocalSyn : locss.flatten.all (fun l => l.valtype.isSyn) = true := by
        rw [List.all_flatten_eq]
        exact hlocalRuns
      have he' := BexprA.wf_isSyn_of he
      exact ⟨he'.1, by simp [hlocalSyn, he'.2]⟩

omit authority in
theorem BcodeA.wf_isSyn_of {bs : Bytes} {code : Code}
    (h : @Bcode amendedBinaryAuthority bs code) :
    InstrSeq.wf code.2 = true ∧
    (code.1.all (fun l => l.valtype.isSyn) && InstrSeq.isSyn code.2) = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Bcode bs code at h
  cases h with
  | mk _ _ _ _ _ hf _ => exact BfuncA.wf_isSyn_of hf

omit authority in
theorem BdataA.wf_isSyn_of {bs : Bytes} {data : Data}
    (h : @Bdata amendedBinaryAuthority bs data) :
    Data.wf data = true ∧ Data.isSyn data = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Bdata bs data at h
  cases h with
  | activeZero _ _ _ _ _ _ _ he _ _ =>
      have he' := BexprA.wf_isSyn_of he
      exact ⟨by simpa [Data.wf, DataMode.wf] using he'.1,
        by simpa [Data.isSyn, DataMode.isSyn] using he'.2⟩
  | passive => exact ⟨rfl, rfl⟩
  | active _ _ _ _ _ _ _ _ _ he _ =>
      have he' := BexprA.wf_isSyn_of he
      exact ⟨by simpa [Data.wf, DataMode.wf] using he'.1,
        by simpa [Data.isSyn, DataMode.isSyn] using he'.2⟩

omit authority in
theorem BelemA.wf_isSyn_of {bs : Bytes} {elem : Elem}
    (h : @Belem amendedBinaryAuthority bs elem) :
    Elem.wf elem = true ∧ Elem.isSyn elem = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Belem bs elem at h
  cases h with
  | activeFuncrefZero _ _ _ e ys _ _ he _ _ =>
      have he' := BexprA.wf_isSyn_of he
      have hi := refFuncExprs.wf_isSyn ys
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hi.1, he'.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hi.2, he'.2]⟩
  | passiveFuncref _ _ _ _ ys _ hk _ =>
      cases hk
      have hi := refFuncExprs.wf_isSyn ys
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hi.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hi.2]⟩
  | activeFuncref _ _ _ _ _ _ e _ ys _ _ he hk _ =>
      cases hk
      have he' := BexprA.wf_isSyn_of he
      have hi := refFuncExprs.wf_isSyn ys
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hi.1, he'.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hi.2, he'.2]⟩
  | declareFuncref _ _ _ _ ys _ hk _ =>
      cases hk
      have hi := refFuncExprs.wf_isSyn ys
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hi.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hi.2]⟩
  | activeExprZero _ _ _ e es _ _ he hes _ =>
      have he' := BexprA.wf_isSyn_of he
      have hiwf := Blist.all_of (G := Bexpr) (P := InstrSeq.wf)
        (fun h => (BexprA.wf_isSyn_of h).1) hes
      have hisyn := Blist.all_of (G := Bexpr) (P := InstrSeq.isSyn)
        (fun h => (BexprA.wf_isSyn_of h).2) hes
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hiwf, he'.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hisyn, he'.2]⟩
  | passiveExpr _ _ _ _ _ _ hrt hes =>
      have hrtsyn := hrt.syn_wfList_of.1
      have hiwf := Blist.all_of (G := Bexpr) (P := InstrSeq.wf)
        (fun h => (BexprA.wf_isSyn_of h).1) hes
      have hisyn := Blist.all_of (G := Bexpr) (P := InstrSeq.isSyn)
        (fun h => (BexprA.wf_isSyn_of h).2) hes
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hiwf],
         by simp [Elem.isSyn, ElemMode.isSyn, hrtsyn, hisyn]⟩
  | activeExpr _ _ _ _ _ e es _ _ he hes =>
      have he' := BexprA.wf_isSyn_of he
      have hiwf := Blist.all_of (G := Bexpr) (P := InstrSeq.wf)
        (fun h => (BexprA.wf_isSyn_of h).1) hes
      have hisyn := Blist.all_of (G := Bexpr) (P := InstrSeq.isSyn)
        (fun h => (BexprA.wf_isSyn_of h).2) hes
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hiwf, he'.1],
         by simp [Elem.isSyn, ElemMode.isSyn, RefType.isSyn, HeapType.isSyn,
           AbsHeapType.isSyn, hisyn, he'.2]⟩
  | declareExpr _ _ _ _ _ _ hrt hes =>
      have hrtsyn := hrt.syn_wfList_of.1
      have hiwf := Blist.all_of (G := Bexpr) (P := InstrSeq.wf)
        (fun h => (BexprA.wf_isSyn_of h).1) hes
      have hisyn := Blist.all_of (G := Bexpr) (P := InstrSeq.isSyn)
        (fun h => (BexprA.wf_isSyn_of h).2) hes
      exact
        ⟨by simp [Elem.wf, ElemMode.wf, hiwf],
         by simp [Elem.isSyn, ElemMode.isSyn, hrtsyn, hisyn]⟩

/-! ## Whole-module closure -/

omit authority in
private theorem BmoduleA.wf_of_sections
    {bty bim btg bgl bta bel bco bda : Bytes}
    {types : List TypeDef} {imports : List Import} {tags : List Tag}
    {globals : List Global} {mems : List Mem} {tables : List Table}
    {typeidxs : List TypeIdx} {codes : List Code} {funcs : List Func}
    {datas : List Data} {elems : List Elem} {start : Option Start}
    {exports : List Export}
    (htypes : @Btypesec amendedBinaryAuthority bty types)
    (himports : @Bimportsec amendedBinaryAuthority bim imports)
    (htags : Btagsec btg tags)
    (hglobals : @Bglobalsec amendedBinaryAuthority bgl globals)
    (htables : @Btablesec amendedBinaryAuthority bta tables)
    (helems : @Belemsec amendedBinaryAuthority bel elems)
    (hcodes : @Bcodesec amendedBinaryAuthority bco codes)
    (hdatas : @Bdatasec amendedBinaryAuthority bda datas)
    (hlength : typeidxs.length = codes.length)
    (hfuncs : funcs = List.zipWith
      (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes) :
    Module.wf
      { types := types, imports := imports, tags := tags, globals := globals,
        mems := mems, tables := tables, funcs := funcs, datas := datas,
        elems := elems, start := start, exports := exports } = true := by
  letI : BinaryAuthority := amendedBinaryAuthority
  change Btypesec bty types at htypes
  change Bimportsec bim imports at himports
  change Btagsec btg tags at htags
  change Bglobalsec bgl globals at hglobals
  change Btablesec bta tables at htables
  change Belemsec bel elems at helems
  change Bcodesec bco codes at hcodes
  change Bdatasec bda datas at hdatas
  have htypesWf : types.all TypeDef.wf = true :=
    Bsection.blist_all_of (G := Btype) (P := TypeDef.wf)
      (fun h => (Btype.wf_isSyn_of h).1) htypes
  have htypesSyn : types.all TypeDef.isSyn = true :=
    Bsection.blist_all_of (G := Btype) (P := TypeDef.isSyn)
      (fun h => (Btype.wf_isSyn_of h).2) htypes
  have himportsSyn : imports.all Import.isSyn = true :=
    Bsection.blist_all_of (G := Bimport) (P := Import.isSyn)
      (fun h => Bimport.isSyn_of h) himports
  have htagsSyn : tags.all Tag.isSyn = true :=
    Bsection.blist_all_of (G := Btag) (P := Tag.isSyn)
      (fun h => Btag.isSyn_of h) htags
  have hglobalsWf : globals.all Global.wf = true :=
    Bsection.blist_all_of (G := Bglobal) (P := Global.wf)
      (fun h => (BglobalA.wf_isSyn_of h).1) hglobals
  have hglobalsSyn : globals.all Global.isSyn = true :=
    Bsection.blist_all_of (G := Bglobal) (P := Global.isSyn)
      (fun h => (BglobalA.wf_isSyn_of h).2) hglobals
  have htablesWf : tables.all Table.wf = true :=
    Bsection.blist_all_of (G := Btable) (P := Table.wf)
      (fun h => (BtableA.wf_isSyn_of h).1) htables
  have htablesSyn : tables.all Table.isSyn = true :=
    Bsection.blist_all_of (G := Btable) (P := Table.isSyn)
      (fun h => (BtableA.wf_isSyn_of h).2) htables
  have helemsWf : elems.all Elem.wf = true :=
    Bsection.blist_all_of (G := Belem) (P := Elem.wf)
      (fun h => (BelemA.wf_isSyn_of h).1) helems
  have helemsSyn : elems.all Elem.isSyn = true :=
    Bsection.blist_all_of (G := Belem) (P := Elem.isSyn)
      (fun h => (BelemA.wf_isSyn_of h).2) helems
  have hdatasWf : datas.all Data.wf = true :=
    Bsection.blist_all_of (G := Bdata) (P := Data.wf)
      (fun h => (BdataA.wf_isSyn_of h).1) hdatas
  have hdatasSyn : datas.all Data.isSyn = true :=
    Bsection.blist_all_of (G := Bdata) (P := Data.isSyn)
      (fun h => (BdataA.wf_isSyn_of h).2) hdatas
  let codeWf : Code → Bool := fun c => InstrSeq.wf c.2
  let codeSyn : Code → Bool := fun c =>
    c.1.all (fun l => l.valtype.isSyn) && InstrSeq.isSyn c.2
  have hcodesWf : codes.all codeWf = true :=
    Bsection.blist_all_of (G := Bcode) (P := codeWf)
      (fun h => (BcodeA.wf_isSyn_of h).1) hcodes
  have hcodesSyn : codes.all codeSyn = true :=
    Bsection.blist_all_of (G := Bcode) (P := codeSyn)
      (fun h => (BcodeA.wf_isSyn_of h).2) hcodes
  let mkFunc : TypeIdx → Code → Func := fun x c =>
    { typeidx := x, locals := c.1, body := c.2 }
  have hfuncsWfZip :
      (List.zipWith mkFunc typeidxs codes).all Func.wf = true :=
    List.zipWith_all_of_right mkFunc codeWf Func.wf
      (fun _ _ h => by simpa [mkFunc, codeWf, Func.wf] using h)
      hlength hcodesWf
  have hfuncsSynZip :
      (List.zipWith mkFunc typeidxs codes).all Func.isSyn = true :=
    List.zipWith_all_of_right mkFunc codeSyn Func.isSyn
      (fun _ _ h => by simpa [mkFunc, codeSyn, Func.isSyn] using h)
      hlength hcodesSyn
  have hfuncsWf : funcs.all Func.wf = true := by
    simpa [hfuncs, mkFunc] using hfuncsWfZip
  have hfuncsSyn : funcs.all Func.isSyn = true := by
    simpa [hfuncs, mkFunc] using hfuncsSynZip
  simp [Module.wf, Module.isSyn, htypesWf, htypesSyn, himportsSyn, htagsSyn,
    hglobalsWf, hglobalsSyn, htablesWf, htablesSyn, hfuncsWf, hfuncsSyn,
    hdatasWf, hdatasSyn, helemsWf, helemsSyn]

omit authority in
/-- Every abstract module synthesized by the exact amended declarative binary
grammar satisfies all intrinsic Core syntax side conditions. -/
theorem BmoduleA.wf_of {bs : Bytes} {m : Module}
    (h : @Bmodule amendedBinaryAuthority bs m) : Module.wf m = true := by
  cases h
  apply BmoduleA.wf_of_sections <;> assumption

end WasmGemmGnaf.Wasm.Core.Binary
