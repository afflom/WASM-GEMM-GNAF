/-
  Wasm/Core/EncodeComplete.lean --- completeness of the canonical encoder
  against the independent Core 3.0 binary grammar.

  This file contains only reverse implications from grammar derivations to
  encoder success.  The length component is load-bearing: the grammar bounds a
  section (and a code body) by the length of the bytes in its derivation,
  whereas the encoder first chooses canonical bytes and then checks their
  length.  Showing that canonical component encodings are no longer than the
  corresponding grammar witnesses transfers those bounds without an
  assumption about the module being encodable.
-/
import WasmGemmGnaf.Wasm.Core.Encode

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

/-- A canonical component encoder succeeds on every value derived by its
independent grammar, and its chosen bytes are no longer than the derivation's
bytes. -/
def CompleteLe {α : Type} (f : α → Option Bytes) (G : Bytes → α → Prop) : Prop :=
  ∀ {w : Bytes} {x : α}, G w x → ∃ out, f x = some out ∧ out.length ≤ w.length

theorem catO_some {a b : Bytes} {x y : Option Bytes}
    (hx : x = some a) (hy : y = some b) : catO x y = some (a ++ b) := by
  simp [catO, hx, hy]

theorem consO_some {a : Bytes} {x : Option Bytes} {b : Byte}
    (hx : x = some a) : consO b x = some (b :: a) := by
  simp [consO, hx]

/-- Either successful alternative supplies a successful result no longer than
its candidate, because `orO` retains the shorter result when both succeed. -/
theorem orO_left_le {x y : Option Bytes} {a : Bytes} (h : x = some a) :
    ∃ out, orO x y = some out ∧ out.length ≤ a.length := by
  subst x
  cases y with
  | none => exact ⟨a, rfl, Nat.le_refl _⟩
  | some b =>
      by_cases hab : a.length ≤ b.length
      · exact ⟨a, by simp [orO, hab], Nat.le_refl _⟩
      · exact ⟨b, by simp [orO, hab], by omega⟩

theorem orO_right_le {x y : Option Bytes} {b : Bytes} (h : y = some b) :
    ∃ out, orO x y = some out ∧ out.length ≤ b.length := by
  subst y
  cases x with
  | none => exact ⟨b, rfl, Nat.le_refl _⟩
  | some a =>
      by_cases hab : a.length ≤ b.length
      · exact ⟨a, by simp [orO, hab], hab⟩
      · exact ⟨b, by simp [orO, hab], Nat.le_refl _⟩

theorem orO_lift_left {x y : Option Bytes} {w : Bytes}
    (h : ∃ a, x = some a ∧ a.length ≤ w.length) :
    ∃ out, orO x y = some out ∧ out.length ≤ w.length := by
  obtain ⟨a, ha, hal⟩ := h
  obtain ⟨out, hout, hlea⟩ := orO_left_le ha
  exact ⟨out, hout, Nat.le_trans hlea hal⟩

theorem orO_lift_right {x y : Option Bytes} {w : Bytes}
    (h : ∃ b, y = some b ∧ b.length ≤ w.length) :
    ∃ out, orO x y = some out ∧ out.length ≤ w.length := by
  obtain ⟨b, hb, hbl⟩ := h
  obtain ⟨out, hout, hleb⟩ := orO_right_le hb
  exact ⟨out, hout, Nat.le_trans hleb hbl⟩

/-- Minimal unsigned LEB length is monotone in the encoded natural. -/
theorem lebU_length_mono {a b : Nat} (hab : a ≤ b) :
    (lebU a).length ≤ (lebU b).length := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
      rw [lebU_eq a, lebU_eq b]
      by_cases hb : b < 0x80
      · have ha : a < 0x80 := by omega
        simp [ha, hb]
      · have hb' : ¬b < 0x80 := hb
        rw [if_neg hb']
        by_cases ha : a < 0x80
        · rw [if_pos ha]
          simp
        · rw [if_neg ha]
          simp only [List.length_cons]
          have hdiv : a / 0x80 ≤ b / 0x80 := Nat.div_le_div_right hab
          have hlt : b / 0x80 < b := Nat.div_lt_self (by omega) (by omega)
          exact Nat.add_le_add_right (ih (b / 0x80) hlt hdiv) 1

/-- The pinned non-negative signed encoding is no longer than any verbatim
`Bs33` derivation of the same value. -/
theorem lebSPinned_minimal_nonneg {w : Bytes} {n : Nat} (h : Bs33 w (n : Int)) :
    (lebSPinned n).length ≤ w.length := by
  unfold Bs33 at h
  generalize hz : (n : Int) = z at h
  cases h with
  | pos b hb64 hbN =>
      have hv : n = b.val := by omega
      unfold lebSPinned
      rw [if_pos (by omega)]
      simp
  | neg b hb64 hb128 hbN =>
      have hbv : b.val < 128 := by simpa using hb128
      omega
  | more b tail i hb128 hN hi =>
      have hbv : b.val < 256 := b.property
      have hn : n = 128 * i + (b.val - 128) := by
        have h7 : (2 : Int) ^ 7 = 128 := by decide
        rw [h7] at *
        omega
      unfold lebSPinned
      by_cases hn64 : n < 0x40
      · rw [if_pos hn64]
        simp
      · rw [if_neg hn64]
        have hdiv : n / 0x80 = i := by omega
        rw [hdiv]
        simpa using Nat.add_le_add_right (lebU_minimal hi) 1

/-- At every fuel, the amended positive signed encoder is no longer than an
amended signed derivation of the same non-negative value. -/
theorem BsN'_length_pos {N : Nat} {w : Bytes} {z : Int} (h : BsN' N w z) :
    0 < w.length := by
  cases h <;> simp

theorem lebSAmendedAux_minimal_nonneg : ∀ (fuel : Nat) {N : Nat} {w : Bytes}
    {n : Nat}, BsN' N w (n : Int) →
      (lebSAmendedAux fuel n).length ≤ w.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro N w n h
      have hw := BsN'_length_pos h
      simp [lebSAmendedAux]
      omega
  | succ fuel ih =>
      intro N w n h
      simp only [lebSAmendedAux]
      by_cases hn64 : n < 0x40
      · rw [if_pos hn64]
        have hw := BsN'_length_pos h
        simp
        omega
      · rw [if_neg hn64]
        generalize hz : (n : Int) = z at h
        cases h with
        | pos N b hb64 hbN => omega
        | neg N b hb64 hb128 hbN => omega
        | more N b tail i hb128 hN hi =>
            have hbv : b.val < 256 := b.property
            have hi0 : 0 ≤ i := by omega
            have hcast : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hi0
            have hdiv : n / 0x80 = i.toNat := by
              have h7 : (2 : Int) ^ 7 = 128 := by decide
              rw [h7] at hz
              omega
            have htail : BsN' (N - 7) tail ((i.toNat : Nat) : Int) := by
              simpa [hcast] using hi
            rw [hdiv]
            simpa using Nat.add_le_add_right (ih htail) 1

theorem lebSAmended_minimal_nonneg {w : Bytes} {n : Nat}
    (h : Bs33' w (n : Int)) : (lebSAmended n).length ≤ w.length := by
  exact lebSAmendedAux_minimal_nonneg 5 h

/-- The selected signed encoding is minimal for either finite authority. -/
theorem lebS_minimal_nonneg {w : Bytes} {n : Nat}
    (h : Bs33For w (n : Int)) : (lebS n).length ≤ w.length := by
  cases hr : authority.revision with
  | pinned =>
      simp [Bs33For, hr] at h
      simpa [lebS, hr] using lebSPinned_minimal_nonneg h
  | amended =>
      simp [Bs33For, hr] at h
      simpa [lebS, hr] using lebSAmended_minimal_nonneg h

/-- Reverse completeness and length minimality lift pointwise through a fixed
repetition. -/
theorem encRep_completeLe {α : Type} {G : Bytes → α → Prop}
    {f : α → Option Bytes} (hf : CompleteLe f G) :
    ∀ {n : Nat} {w : Bytes} {xs : List α}, Rep G n w xs →
      ∃ out, encRep f xs = some out ∧ out.length ≤ w.length := by
  unfold CompleteLe at hf
  intro n w xs h
  induction h with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons wb x wr xr k hx _ ih =>
      obtain ⟨bx, hbx, hlx⟩ := hf hx
      obtain ⟨br, hbr, hlr⟩ := ih
      refine ⟨bx ++ br, catO_some hbx hbr, ?_⟩
      simp only [List.length_append]
      omega

/-- Reverse completeness and length minimality for the grammar's counted
lists. -/
theorem encList_completeLe {α : Type} {G : Bytes → α → Prop}
    {f : α → Option Bytes} (hf : CompleteLe f G) : CompleteLe (encList f) (Blist G) := by
  unfold CompleteLe at hf ⊢
  intro w xs h
  cases h with
  | mk bn body n xs hn hrep =>
      have hlen : xs.length = n.val := hrep.length
      have hlt : xs.length < 2 ^ 32 := by simpa [hlen] using n.property
      obtain ⟨out, hout, hle⟩ :=
        encRep_completeLe (f := f) (G := G) hf hrep
      refine ⟨lebU xs.length ++ out, ?_, ?_⟩
      · simp [encList, hlt, catO, hout]
      · simp only [List.length_append]
        have hleb : (lebU xs.length).length ≤ bn.length := by
          rw [hlen]
          exact lebU_minimal hn
        omega

/-- A canonical payload whose length is bounded by a present section witness
passes the encoder's section-size check.  An absent witness forces the empty
semantic list, for which the canonical list-section encoder omits the section. -/
theorem encListSection_complete {α : Type} {G : Bytes → α → Prop}
    {f : α → Option Bytes} (hf : CompleteLe f G) {N : Nat}
    {w : Bytes} {xs : List α} (h : Bsection N (Blist G) w xs) :
    ∃ out, encListSection N f xs = some out := by
  unfold CompleteLe at hf
  cases h with
  | absent => exact ⟨[], rfl⟩
  | present blen body len xs hlen hbody heq =>
      cases xs with
      | nil => exact ⟨[], rfl⟩
      | cons x xr =>
          obtain ⟨payload, hpayload, hle⟩ :=
            encList_completeLe (f := f) (G := G) hf hbody
          have hw : body.length < 2 ^ 32 := by
            rw [← heq]
            exact len.property
          have hp : payload.length < 2 ^ 32 := Nat.lt_of_le_of_lt hle hw
          refine ⟨tb N :: (lebU payload.length ++ payload), ?_⟩
          simp [encListSection, hpayload, encSectionBody, hp]

/-! ## Values and types -/

theorem encIdx_completeLe : CompleteLe encIdx Bu32 := by
  intro w x h
  exact ⟨lebU x.val, rfl, lebU_minimal h⟩

theorem encByte_completeLe : CompleteLe encByte Bbyte := by
  intro w x h
  cases h
  exact ⟨[x], rfl, by simp⟩

theorem Rep.Bbyte_length {n : Nat} {w : Bytes} {bl : List Byte}
    (h : Rep Bbyte n w bl) : w.length = n := by
  induction h with
  | nil => rfl
  | cons b x bs xs k hx hxs ih =>
      cases hx
      simp [ih]

theorem f32Mag_magOf (sg e m : Nat) (he : e < 2 ^ 8) (hm : m < 2 ^ 23) :
    f32Mag sg (magOf32 e m) = some (sg, e, m) := by
  have he256 : e < 256 := by simpa using he
  have h255 : (2 : Nat) ^ 8 - 1 = 255 := by decide
  have h127 : ((2 ^ (8 - 1) - 1 : Nat) : Int) = 127 := by decide
  unfold magOf32
  by_cases he0 : e = 0
  · subst e
    simp [f32Mag, hm]
  · rw [if_neg he0]
    by_cases heMax : e = 2 ^ 8 - 1
    · rw [if_pos heMax]
      rw [h255] at heMax
      subst e
      by_cases hm0 : m = 0
      · subst m
        simp [f32Mag]
      · simp [f32Mag, hm, hm0]
    · rw [if_neg heMax]
      have heNe : e ≠ 255 := by simpa [h255] using heMax
      have hcond : m < 2 ^ 23 ∧
          1 ≤ (e : Int) - 127 + 127 ∧ (e : Int) - 127 + 127 ≤ 254 := by
        exact ⟨hm, by omega, by omega⟩
      simp only [f32Mag, f32NormFields, h127]
      rw [if_pos hcond]
      have hcast : ((e : Int) - 127 + 127).toNat = e := by omega
      rw [hcast]

theorem f64Mag_magOf (sg e m : Nat) (he : e < 2 ^ 11) (hm : m < 2 ^ 52) :
    f64Mag sg (magOf64 e m) = some (sg, e, m) := by
  have he2048 : e < 2048 := by simpa using he
  have h2047 : (2 : Nat) ^ 11 - 1 = 2047 := by decide
  have h1023 : ((2 ^ (11 - 1) - 1 : Nat) : Int) = 1023 := by decide
  unfold magOf64
  by_cases he0 : e = 0
  · subst e
    simp [f64Mag, hm]
  · rw [if_neg he0]
    by_cases heMax : e = 2 ^ 11 - 1
    · rw [if_pos heMax]
      rw [h2047] at heMax
      subst e
      by_cases hm0 : m = 0
      · subst m
        simp [f64Mag]
      · simp [f64Mag, hm, hm0]
    · rw [if_neg heMax]
      have heNe : e ≠ 2047 := by simpa [h2047] using heMax
      have hcond : m < 2 ^ 52 ∧
          1 ≤ (e : Int) - 1023 + 1023 ∧ (e : Int) - 1023 + 1023 ≤ 2046 := by
        exact ⟨hm, by omega, by omega⟩
      simp only [f64Mag, f64NormFields, h1023]
      rw [if_pos hcond]
      have hcast : ((e : Int) - 1023 + 1023).toNat = e := by omega
      rw [hcast]

theorem f32Fields_magOf (s e m : Nat) (hs : s < 2) (he : e < 2 ^ 8)
    (hm : m < 2 ^ 23) :
    f32Fields (if s = 0 then .pos (magOf32 e m) else .neg (magOf32 e m)) =
      some (s, e, m) := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simpa [f32Fields] using f32Mag_magOf 0 e m he hm
  · simpa [f32Fields] using f32Mag_magOf 1 e m he hm

theorem f64Fields_magOf (s e m : Nat) (hs : s < 2) (he : e < 2 ^ 11)
    (hm : m < 2 ^ 52) :
    f64Fields (if s = 0 then .pos (magOf64 e m) else .neg (magOf64 e m)) =
      some (s, e, m) := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simpa [f64Fields] using f64Mag_magOf 0 e m he hm
  · simpa [f64Fields] using f64Mag_magOf 1 e m he hm

theorem encF32_completeLe : CompleteLe encF32 Bf32 := by
  intro w v h
  obtain ⟨bl, hrep, hinv⟩ := h
  have hbl : bl.length = 4 := by simpa using hrep.length
  have hw : w.length = 4 := by simpa using hrep.Bbyte_length
  simp only [invFbytes, signif, expon, hbl, if_pos] at hinv
  let n := leNat bl
  let m := n % 2 ^ 23
  let e := n / 2 ^ 23 % 2 ^ 8
  let s := n / 2 ^ (23 + 8) % 2
  have hm : m < 2 ^ 23 := Nat.mod_lt _ (two_pow_pos 23)
  have he : e < 2 ^ 8 := Nat.mod_lt _ (two_pow_pos 8)
  have hs : s < 2 := Nat.mod_lt _ (by decide)
  change some (if s = 0 then .pos (magOf32 e m) else .neg (magOf32 e m)) = some v at hinv
  injection hinv with hv
  subst v
  refine ⟨bytesLE 4 (s * 2 ^ 31 + e * 2 ^ 23 + m), ?_, ?_⟩
  · simp [encF32, f32Fields_magOf s e m hs he hm]
  · rw [bytesLE_length, hw]
    exact Nat.le_refl 4

theorem encF64_completeLe : CompleteLe encF64 Bf64 := by
  intro w v h
  obtain ⟨bl, hrep, hinv⟩ := h
  have hbl : bl.length = 8 := by simpa using hrep.length
  have hw : w.length = 8 := by simpa using hrep.Bbyte_length
  simp only [invFbytes, signif, expon, hbl, if_pos] at hinv
  let n := leNat bl
  let m := n % 2 ^ 52
  let e := n / 2 ^ 52 % 2 ^ 11
  let s := n / 2 ^ (52 + 11) % 2
  have hm : m < 2 ^ 52 := Nat.mod_lt _ (two_pow_pos 52)
  have he : e < 2 ^ 11 := Nat.mod_lt _ (two_pow_pos 11)
  have hs : s < 2 := Nat.mod_lt _ (by decide)
  change some (if s = 0 then .pos (magOf64 e m) else .neg (magOf64 e m)) = some v at hinv
  injection hinv with hv
  subst v
  refine ⟨bytesLE 8 (s * 2 ^ 63 + e * 2 ^ 52 + m), ?_, ?_⟩
  · simp [encF64, f64Fields_magOf s e m hs he hm]
  · rw [bytesLE_length, hw]
    exact Nat.le_refl 8

theorem encAbsHeapType_completeLe {w : Bytes} {a : AbsHeapType}
    (h : Babsheaptype w (.abs a)) :
    ∃ out, encAbsHeapType a = some out ∧ out.length ≤ w.length := by
  cases a <;> cases h <;> simp [encAbsHeapType]

theorem encHeapType_completeLe : CompleteLe encHeapType Bheaptype := by
  intro w ht h
  cases h with
  | abs ht ha =>
      cases ht with
      | abs a => exact encAbsHeapType_completeLe ha
      | use tu => cases ha
  | idx i x hi hnonneg heq =>
      have hi' : i = (x.val : Int) := heq.symm
      subst i
      exact ⟨lebS x.val, rfl, lebS_minimal_nonneg hi⟩

theorem encRefType_completeLe : CompleteLe encRefType Breftype := by
  intro w rt h
  cases h with
  | null wh ht hh =>
      cases ht with
      | abs a =>
          obtain ⟨out, hout, hle⟩ := encHeapType_completeLe hh
          exact ⟨out, by simpa [encRefType, encHeapType] using hout, by simp; omega⟩
      | use tu =>
          obtain ⟨out, hout, hle⟩ := encHeapType_completeLe hh
          exact ⟨tb 0x63 :: out, by simp [encRefType, consO, hout], by simp; omega⟩
  | nonNull wh ht hh =>
      obtain ⟨out, hout, hle⟩ := encHeapType_completeLe hh
      exact ⟨tb 0x64 :: out, by simp [encRefType, consO, hout], by simp; omega⟩
  | abs wh ht ha =>
      cases ht with
      | abs a =>
          obtain ⟨out, hout, hle⟩ := encAbsHeapType_completeLe ha
          exact ⟨out, by simpa [encRefType] using hout, hle⟩
      | use tu => cases ha

theorem encValType_completeLe : CompleteLe encValType Bvaltype := by
  intro w t h
  cases h with
  | num nt hn =>
      cases hn <;> exact ⟨_, rfl, by simp [encNumType]⟩
  | vec vt hv =>
      cases hv
      exact ⟨_, rfl, by simp [encVecType]⟩
  | ref rt hr => exact encRefType_completeLe hr

theorem encResultType_completeLe : CompleteLe encResultType Bresulttype := by
  intro w ts h
  exact encList_completeLe (f := encValType) (G := Bvaltype)
    encValType_completeLe h

theorem encStorageType_completeLe : CompleteLe encStorageType Bstoragetype := by
  intro w zt h
  cases h with
  | val t ht => exact encValType_completeLe ht
  | pack pt hp =>
      cases hp <;> exact ⟨_, rfl, by simp [encStorageType, encPackType]⟩

theorem encFieldType_completeLe : CompleteLe encFieldType Bfieldtype := by
  intro w ft h
  cases h with
  | mk bz bm zt mo hz hm =>
      obtain ⟨out, hout, hle⟩ := encStorageType_completeLe hz
      cases hm with
      | const =>
          exact ⟨out ++ [tb 0x00], by simp [encFieldType, encMut, catO, hout], by simp; omega⟩
      | mutable =>
          exact ⟨out ++ [tb 0x01], by simp [encFieldType, encMut, catO, hout], by simp; omega⟩

theorem encCompType_completeLe : CompleteLe encCompType Bcomptype := by
  intro w ct h
  cases h with
  | array wf ft hf =>
      obtain ⟨out, hout, hle⟩ := encFieldType_completeLe hf
      exact ⟨tb 0x5E :: out, by simp [encCompType, consO, hout], by simp; omega⟩
  | struct wf fts hf =>
      obtain ⟨out, hout, hle⟩ :=
        encList_completeLe (f := encFieldType) (G := Bfieldtype)
          encFieldType_completeLe hf
      exact ⟨tb 0x5F :: out, by simp [encCompType, consO, hout], by simp; omega⟩
  | func bdom bcod dom cod hdom hcod =>
      obtain ⟨od, hd, hld⟩ := encResultType_completeLe hdom
      obtain ⟨oc, hc, hlc⟩ := encResultType_completeLe hcod
      have hcat : catO (encResultType dom) (encResultType cod) = some (od ++ oc) :=
        catO_some hd hc
      have hcons : consO (tb 0x60)
          (catO (encResultType dom) (encResultType cod)) =
          some (tb 0x60 :: (od ++ oc)) := consO_some hcat
      exact ⟨tb 0x60 :: (od ++ oc),
        by simpa [encCompType] using hcons, by simp; omega⟩

theorem typeIdxsOf_map_idx : ∀ xs : List TypeIdx,
    typeIdxsOf (xs.map TypeUse.idx) = some xs
  | [] => rfl
  | x :: xs => by simp [typeIdxsOf, typeIdxsOf_map_idx xs]

theorem encSubType_completeLe : CompleteLe encSubType Bsubtype := by
  intro w st h
  cases h with
  | finalSub bx bc xs tus ct hxs hct hmap =>
      cases tus with
      | nil =>
          obtain ⟨oc, hc, hlc⟩ := encCompType_completeLe hct
          exact ⟨oc, by simpa [encSubType] using hc, by simp; omega⟩
      | cons tu rest =>
          have hidx : typeIdxsOf (TypeUses.cons tu rest).toList = some xs := by
            rw [hmap]
            exact typeIdxsOf_map_idx xs
          obtain ⟨ox, hx, hlx⟩ :=
            encList_completeLe (f := encIdx) (G := Bu32) encIdx_completeLe hxs
          obtain ⟨oc, hc, hlc⟩ := encCompType_completeLe hct
          have hcat : catO (encList encIdx xs) (encCompType ct) = some (ox ++ oc) :=
            catO_some hx hc
          have hcons : consO (tb 0x4F) (catO (encList encIdx xs) (encCompType ct)) =
              some (tb 0x4F :: (ox ++ oc)) := consO_some hcat
          exact ⟨tb 0x4F :: (ox ++ oc), by simpa [encSubType, hidx] using hcons,
            by simp; omega⟩
  | openSub bx bc xs tus ct hxs hct hmap =>
      have hidx : typeIdxsOf tus.toList = some xs := by
        rw [hmap]
        exact typeIdxsOf_map_idx xs
      obtain ⟨ox, hx, hlx⟩ :=
        encList_completeLe (f := encIdx) (G := Bu32) encIdx_completeLe hxs
      obtain ⟨oc, hc, hlc⟩ := encCompType_completeLe hct
      have hcat : catO (encList encIdx xs) (encCompType ct) = some (ox ++ oc) :=
        catO_some hx hc
      have hcons : consO (tb 0x50) (catO (encList encIdx xs) (encCompType ct)) =
          some (tb 0x50 :: (ox ++ oc)) := consO_some hcat
      exact ⟨tb 0x50 :: (ox ++ oc), by simpa [encSubType, hidx] using hcons,
        by simp; omega⟩
  | bare bc ct hct =>
      exact encCompType_completeLe hct

theorem Rep.member_witness_le {α : Type} {G : Bytes → α → Prop}
    {n : Nat} {w : Bytes} {xs : List α} (h : Rep G n w xs) {x : α}
    (hx : x ∈ xs) : ∃ bx, G bx x ∧ bx.length ≤ w.length := by
  induction h with
  | nil => simp at hx
  | cons b y bs ys k hy hys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b, hy, by simp⟩
      · obtain ⟨bx, hbx, hle⟩ := ih hx
        exact ⟨bx, hbx, by simp; omega⟩

theorem Blist.member_witness_le {α : Type} {G : Bytes → α → Prop}
    {w : Bytes} {xs : List α} (h : Blist G w xs) {x : α} (hx : x ∈ xs) :
    ∃ bx, G bx x ∧ bx.length ≤ w.length := by
  cases h with
  | mk bn body n xs hn hrep =>
      obtain ⟨bx, hbx, hle⟩ := hrep.member_witness_le hx
      exact ⟨bx, hbx, by simp; omega⟩

theorem encRecType_completeLe : CompleteLe encRecType Brectype := by
  intro w qt h
  cases h with
  | recGroup body sts hs =>
      cases sts with
      | nil =>
          obtain ⟨out, hout, hle⟩ :=
            encList_completeLe (f := encSubType) (G := Bsubtype)
              encSubType_completeLe hs
          exact ⟨tb 0x4E :: out, by simp [encRecType, consO, hout], by simp; omega⟩
      | cons st rest =>
          cases rest with
          | nil =>
              obtain ⟨bst, hst, hlst⟩ := hs.member_witness_le (by
                exact List.Mem.head _)
              obtain ⟨out, hout, hle⟩ := encSubType_completeLe hst
              exact ⟨out, by simpa [encRecType] using hout, by simp; omega⟩
          | cons st' rest' =>
              obtain ⟨out, hout, hle⟩ :=
                encList_completeLe (f := encSubType) (G := Bsubtype)
                  encSubType_completeLe hs
              exact ⟨tb 0x4E :: out, by simp [encRecType, consO, hout], by simp; omega⟩
  | single body st hs =>
      exact encSubType_completeLe hs

theorem encLimits_length_le {w : Bytes} {at' : AddrType} {lim : Limits}
    (h : Blimits w (at', lim)) : (encLimits at' lim).length ≤ w.length := by
  cases h with
  | i32Min bs n hn =>
      simpa [encLimits] using Nat.add_le_add_right (lebU_minimal hn) 1
  | i32MinMax b₁ b₂ n m hn hm =>
      have h₁ := lebU_minimal hn
      have h₂ := lebU_minimal hm
      simp [encLimits]
      omega
  | i64Min bs n hn =>
      simpa [encLimits] using Nat.add_le_add_right (lebU_minimal hn) 1
  | i64MinMax b₁ b₂ n m hn hm =>
      have h₁ := lebU_minimal hn
      have h₂ := lebU_minimal hm
      simp [encLimits]
      omega

theorem encTagType_completeLe : CompleteLe encTagType Btagtype := by
  intro w jt h
  cases h with
  | mk bs x hx =>
      exact ⟨tb 0x00 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩

theorem encGlobalType_completeLe : CompleteLe encGlobalType Bglobaltype := by
  intro w gt h
  cases h with
  | mk bt bm t mo ht hm =>
      obtain ⟨out, hout, hle⟩ := encValType_completeLe ht
      cases hm with
      | const =>
          exact ⟨out ++ [tb 0x00], by simp [encGlobalType, encMut, catO, hout], by simp; omega⟩
      | mutable =>
          exact ⟨out ++ [tb 0x01], by simp [encGlobalType, encMut, catO, hout], by simp; omega⟩

theorem encMemType_length_le {w : Bytes} {mt : MemType} (h : Bmemtype w mt) :
    (encMemType mt).length ≤ w.length := by
  cases h with
  | mk at' lim hl => exact encLimits_length_le hl

theorem encTableType_completeLe : CompleteLe encTableType Btabletype := by
  intro w tt h
  cases h with
  | mk br bl rt at' lim hr hl =>
      obtain ⟨orr, hrr, hlr⟩ := encRefType_completeLe hr
      have hll := encLimits_length_le hl
      exact ⟨orr ++ encLimits at' lim,
        by simp [encTableType, catO, hrr], by simp; omega⟩

theorem encExternType_completeLe : CompleteLe encExternType Bexterntype := by
  intro w xt h
  cases h with
  | func bs x hx =>
      exact ⟨tb 0x00 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | table bs tt ht =>
      obtain ⟨out, hout, hle⟩ := encTableType_completeLe ht
      exact ⟨tb 0x01 :: out, by simp [encExternType, consO, hout], by simp; omega⟩
  | mem bs mt hm =>
      exact ⟨tb 0x02 :: encMemType mt, rfl, by
        have hle := encMemType_length_le hm
        simp
        omega⟩
  | global bs gt hg =>
      obtain ⟨out, hout, hle⟩ := encGlobalType_completeLe hg
      exact ⟨tb 0x03 :: out, by simp [encExternType, consO, hout], by simp; omega⟩
  | tag bs jt hj =>
      obtain ⟨out, hout, hle⟩ := encTagType_completeLe hj
      exact ⟨tb 0x04 :: out, by simp [encExternType, consO, hout], by simp; omega⟩

/-! ## Non-expression module fields -/

theorem encName_completeLe : CompleteLe encName Bname := by
  intro w nm h
  cases h with
  | mk bl nm hbl heq =>
      obtain ⟨out, hout, hle⟩ :=
        encList_completeLe (f := encByte) (G := Bbyte) encByte_completeLe hbl
      rw [← heq] at hout
      exact ⟨out, by simpa [encName, encByteList] using hout, hle⟩

theorem encTypeDef_completeLe : CompleteLe encTypeDef Btype := by
  intro w td h
  cases h with
  | mk qt hq => exact encRecType_completeLe hq

theorem encTypeSec_complete {w : Bytes} {ts : List TypeDef} (h : Btypesec w ts) :
    ∃ out, encTypeSec ts = some out := by
  unfold Btypesec at h
  exact encListSection_complete (N := 1) (f := encTypeDef) (G := Btype)
    encTypeDef_completeLe h

theorem encImport_completeLe : CompleteLe encImport Bimport := by
  intro w im h
  cases h with
  | mk b₁ b₂ b₃ nm₁ nm₂ xt hn₁ hn₂ hxt =>
      obtain ⟨o₁, ho₁, hl₁⟩ := encName_completeLe hn₁
      obtain ⟨o₂, ho₂, hl₂⟩ := encName_completeLe hn₂
      obtain ⟨o₃, ho₃, hl₃⟩ := encExternType_completeLe hxt
      have h12 : catO (encName nm₁) (encName nm₂) = some (o₁ ++ o₂) :=
        catO_some ho₁ ho₂
      have h123 : catO (catO (encName nm₁) (encName nm₂)) (encExternType xt) =
          some ((o₁ ++ o₂) ++ o₃) := catO_some h12 ho₃
      exact ⟨(o₁ ++ o₂) ++ o₃, by simpa [encImport] using h123, by simp; omega⟩

theorem encImportSec_complete {w : Bytes} {ims : List Import} (h : Bimportsec w ims) :
    ∃ out, encImportSec ims = some out := by
  unfold Bimportsec at h
  exact encListSection_complete (N := 2) (f := encImport) (G := Bimport)
    encImport_completeLe h

theorem encFuncSec_complete {w : Bytes} {xs : List TypeIdx} (h : Bfuncsec w xs) :
    ∃ out, encFuncSec xs = some out := by
  unfold Bfuncsec at h
  exact encListSection_complete (N := 3) (f := encIdx) (G := Btypeidx)
    encIdx_completeLe h

theorem encMem_completeLe : CompleteLe encMem Bmem := by
  intro w mm h
  cases h with
  | mk mt hm =>
      exact ⟨encMemType mt, rfl, encMemType_length_le hm⟩

theorem encMemSec_complete {w : Bytes} {ms : List Mem} (h : Bmemsec w ms) :
    ∃ out, encMemSec ms = some out := by
  unfold Bmemsec at h
  exact encListSection_complete (N := 5) (f := encMem) (G := Bmem)
    encMem_completeLe h

theorem encTag_completeLe : CompleteLe encTag Btag := by
  intro w tg h
  cases h with
  | mk jt hj => exact encTagType_completeLe hj

theorem encTagSec_complete {w : Bytes} {ts : List Tag} (h : Btagsec w ts) :
    ∃ out, encTagSec ts = some out := by
  unfold Btagsec at h
  exact encListSection_complete (N := 13) (f := encTag) (G := Btag)
    encTag_completeLe h

theorem encExternIdx_completeLe : CompleteLe encExternIdx Bexternidx := by
  intro w xx h
  cases h with
  | func bs x hx =>
      exact ⟨tb 0x00 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | table bs x hx =>
      exact ⟨tb 0x01 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | mem bs x hx =>
      exact ⟨tb 0x02 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | global bs x hx =>
      exact ⟨tb 0x03 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | tag bs x hx =>
      exact ⟨tb 0x04 :: lebU x.val, rfl,
        by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩

theorem encExport_completeLe : CompleteLe encExport Bexport := by
  intro w ex h
  cases h with
  | mk bn bx nm xx hn hx =>
      obtain ⟨on, hon, hln⟩ := encName_completeLe hn
      obtain ⟨ox, hox, hlx⟩ := encExternIdx_completeLe hx
      exact ⟨on ++ ox, by simp [encExport, catO, hon, hox], by simp; omega⟩

theorem encExportSec_complete {w : Bytes} {exs : List Export} (h : Bexportsec w exs) :
    ∃ out, encExportSec exs = some out := by
  unfold Bexportsec at h
  exact encListSection_complete (N := 7) (f := encExport) (G := Bexport)
    encExport_completeLe h

theorem encStartSec_complete {w : Bytes} {so : Option Start} (h : Bstartsec w so) :
    ∃ out, encStartSec so = some out := by
  cases h with
  | absent hs => exact ⟨[], rfl⟩
  | present s hs =>
      cases hs with
      | present blen body len xs hlen hbody heq =>
          cases hbody with
          | mk x hi =>
              have hcanon := lebU_minimal hi
              have hw : body.length < 2 ^ 32 := by
                rw [← heq]
                exact len.property
              have hc : (lebU x.val).length < 2 ^ 32 := Nat.lt_of_le_of_lt hcanon hw
              exact ⟨tb 8 :: (lebU (lebU x.val).length ++ lebU x.val), by
                simp [encStartSec, encSectionBody, hc]⟩

/-! ## Instruction operands -/

theorem pre_length_le {p k : Nat} {w : Bytes} (h : Bprefixed p k w) :
    (pre p k).length ≤ w.length := by
  obtain ⟨bn, rfl, x, hx, rfl⟩ := h
  simpa [pre] using Nat.add_le_add_right (lebU_minimal hx) 1

theorem encBlockType_completeLe : CompleteLe encBlockType Bblocktype := by
  intro w bt h
  cases h with
  | empty => exact ⟨[tb 0x40], rfl, Nat.le_refl 1⟩
  | val bs t ht => exact encValType_completeLe ht
  | idx bs i x hi hnonneg heq =>
      have hi' : i = (x.val : Int) := heq.symm
      subst i
      exact ⟨lebS x.val, rfl, lebS_minimal_nonneg hi⟩

theorem encCatch_completeLe : CompleteLe encCatch Bcatch := by
  intro w c h
  cases h with
  | tag bx bl x l hx hl =>
      exact ⟨tb 0x00 :: (lebU x.val ++ lebU l.val), rfl, by
        have hxl := lebU_minimal hx
        have hll := lebU_minimal hl
        simp
        omega⟩
  | tagRef bx bl x l hx hl =>
      exact ⟨tb 0x01 :: (lebU x.val ++ lebU l.val), rfl, by
        have hxl := lebU_minimal hx
        have hll := lebU_minimal hl
        simp
        omega⟩
  | all bl l hl =>
      exact ⟨tb 0x02 :: lebU l.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩
  | allRef bl l hl =>
      exact ⟨tb 0x03 :: lebU l.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩

theorem encMemArg_completeLe {w : Bytes} {x : MemIdx} {ao : MemArg}
    (h : Bmemarg w (x, ao)) :
    ∃ out, encMemArg x ao = some out ∧ out.length ≤ w.length := by
  cases h with
  | mem0 bn bm n m x hn hm hn6 hx =>
      refine ⟨lebU n.val ++ lebU m.val, ?_, ?_⟩
      · simp [encMemArg, hn6, hx]
      · have hnl := lebU_minimal hn
        have hml := lebU_minimal hm
        simp
        omega
  | memx bn bx bm n a m x hn hxi hm hn6 hn7 ha =>
      have ha6 : a.val < 2 ^ 6 := by
        have hnval : n.val < 2 ^ 32 := n.property
        omega
      have haneq : a.val + 2 ^ 6 = n.val := by omega
      by_cases hx0 : x.val = 0
      · refine ⟨lebU a.val ++ lebU m.val, ?_, ?_⟩
        · simp [encMemArg, ha6, hx0]
        · have hal := lebU_length_mono (show a.val ≤ n.val by omega)
          have hnl := lebU_minimal hn
          have hml := lebU_minimal hm
          simp
          omega
      · refine ⟨lebU n.val ++ lebU x.val ++ lebU m.val, ?_, ?_⟩
        · simp [encMemArg, ha6, hx0, haneq]
        · have hnl := lebU_minimal hn
          have hxl := lebU_minimal hxi
          have hml := lebU_minimal hm
          simp
          omega

theorem encCastOp_completeLe : CompleteLe
    (fun p : CastOp => some (encCastOp p.1 p.2)) Bcastop := by
  intro w p h
  cases h <;> exact ⟨_, rfl, Nat.le_refl 1⟩

theorem encLaneIdx_completeLe : CompleteLe
    (fun i : LaneIdx => some (encLaneIdx i)) Blaneidx := by
  intro w i h
  cases h
  exact ⟨encLaneIdx i, rfl, Nat.le_refl 1⟩

/-! ## Non-recursive instruction fragments -/

theorem encInstrParam_completeLe : CompleteLe encInstrParam BinstrParametric := by
  intro w i h
  cases h with
  | unreachable => exact ⟨_, rfl, Nat.le_refl 1⟩
  | nop => exact ⟨_, rfl, Nat.le_refl 1⟩
  | drop => exact ⟨_, rfl, Nat.le_refl 1⟩
  | select => exact ⟨_, rfl, Nat.le_refl 1⟩
  | selectT bs ts hts =>
      obtain ⟨out, hout, hle⟩ :=
        encList_completeLe (f := encValType) (G := Bvaltype)
          encValType_completeLe hts
      exact ⟨tb 0x1C :: out, by simp [encInstrParam, consO, hout], by simp; omega⟩

theorem encInstrCtlBase_completeLe : CompleteLe encInstrCtlBase BinstrControl := by
  intro w i h
  cases h with
  | throw bs x hx =>
      exact ⟨tb 0x08 :: lebU x.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | throwRef => exact ⟨_, rfl, Nat.le_refl 1⟩
  | br bs l hl =>
      exact ⟨tb 0x0C :: lebU l.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩
  | brIf bs l hl =>
      exact ⟨tb 0x0D :: lebU l.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩
  | brTable bl bn ls l hls hl =>
      obtain ⟨ol, hol, hlel⟩ :=
        encList_completeLe (f := encIdx) (G := Blabelidx) encIdx_completeLe hls
      exact ⟨tb 0x0E :: (ol ++ lebU l.val), by
        simp [encInstrCtlBase, catO, consO, hol], by
        have hlen := lebU_minimal hl
        simp
        omega⟩

  | ret => exact ⟨_, rfl, Nat.le_refl 1⟩
  | call bs x hx =>
      exact ⟨tb 0x10 :: lebU x.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | callIndirect by' bx y x hy hx =>
      exact ⟨tb 0x11 :: (lebU y.val ++ lebU x.val), rfl, by
        have hyl := lebU_minimal hy
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | returnCall bs x hx =>
      exact ⟨tb 0x12 :: lebU x.val, rfl, by
        simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | returnCallIndirect by' bx y x hy hx =>
      exact ⟨tb 0x13 :: (lebU y.val ++ lebU x.val), rfl, by
        have hyl := lebU_minimal hy
        have hxl := lebU_minimal hx
        simp
        omega⟩

theorem encInstrCtl_of_base_completeLe {w : Bytes} {i : Instr}
    (h : BinstrControl w i) :
    ∃ out, encInstrCtl i = some out ∧ out.length ≤ w.length := by
  obtain ⟨out, hout, hle⟩ := encInstrCtlBase_completeLe h
  obtain ⟨chosen, hchosen, hlchosen⟩ :=
    orO_left_le (y := encInstrCtlAmended i) hout
  exact ⟨chosen, by simpa [encInstrCtl] using hchosen,
    Nat.le_trans hlchosen hle⟩

theorem encInstrCtl_completeLe : CompleteLe encInstrCtl BinstrControlFor := by
  intro w i h
  cases hr : authority.revision with
  | pinned =>
      simp [BinstrControlFor, hr] at h
      exact encInstrCtl_of_base_completeLe h
  | amended =>
      simp [BinstrControlFor, hr] at h
      cases h with
      | ofPinned bs instr hp => exact encInstrCtl_of_base_completeLe hp
      | callRef bs x hx =>
          exact ⟨tb 0x14 :: lebU x.val, by
            simp [encInstrCtl, encInstrCtlBase, encInstrCtlAmended, orO, hr], by
            simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
      | returnCallRef bs x hx =>
          exact ⟨tb 0x15 :: lebU x.val, by
            simp [encInstrCtl, encInstrCtlBase, encInstrCtlAmended, orO, hr], by
            simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
theorem encInstrLoc_completeLe : CompleteLe encInstrLoc BinstrLocal := by
  intro w i h
  cases h <;> rename_i bs x hx <;>
    exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩

theorem encInstrGlob_completeLe : CompleteLe encInstrGlob BinstrGlobal := by
  intro w i h
  cases h <;> rename_i bs x hx <;>
    exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩

theorem encInstrTbl_completeLe : CompleteLe encInstrTbl BinstrTable := by
  intro w i h
  cases h with
  | get bs x hx =>
      exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | set bs x hx =>
      exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | init bo by' bx y x ho hy hx =>
      exact ⟨pre 0xFC 12 ++ lebU y.val ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hyl := lebU_minimal hy
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | elemDrop bo bx x ho hx =>
      exact ⟨pre 0xFC 13 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | copy bo b₁ b₂ x₁ x₂ ho h₁ h₂ =>
      exact ⟨pre 0xFC 14 ++ lebU x₁.val ++ lebU x₂.val, rfl, by
        have hol := pre_length_le ho
        have hl₁ := lebU_minimal h₁
        have hl₂ := lebU_minimal h₂
        simp
        omega⟩
  | grow bo bx x ho hx =>
      exact ⟨pre 0xFC 15 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | size bo bx x ho hx =>
      exact ⟨pre 0xFC 16 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | fill bo bx x ho hx =>
      exact ⟨pre 0xFC 17 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩

theorem encInstrMem_memArg {i : Instr} {op : Byte} {bm : Bytes}
    {x : MemIdx} {ao : MemArg} (heq : encInstrMem i = consO op (encMemArg x ao))
    (h : Bmemarg bm (x, ao)) :
    ∃ out, encInstrMem i = some out ∧ out.length ≤ (op :: bm).length := by
  obtain ⟨out, hout, hle⟩ := encMemArg_completeLe h
  exact ⟨op :: out, by rw [heq]; exact consO_some hout, by simp; omega⟩

theorem encInstrMem_idx {i : Instr} {op : Byte} {bs : Bytes} {x : U32}
    (heq : encInstrMem i = some (op :: lebU x.val)) (h : Bu32 bs x) :
    ∃ out, encInstrMem i = some out ∧ out.length ≤ (op :: bs).length :=
  ⟨op :: lebU x.val, heq, by
    simpa using Nat.add_le_add_right (lebU_minimal h) 1⟩

theorem encInstrMem_completeLe : CompleteLe encInstrMem BinstrMemory := by
  intro w i h
  cases h with
  | i32Load bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load bm x ao hm => exact encInstrMem_memArg rfl hm
  | f32Load bm x ao hm => exact encInstrMem_memArg rfl hm
  | f64Load bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Load8S bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Load8U bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Load16S bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Load16U bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load8S bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load8U bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load16S bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load16U bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load32S bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Load32U bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Store bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Store bm x ao hm => exact encInstrMem_memArg rfl hm
  | f32Store bm x ao hm => exact encInstrMem_memArg rfl hm
  | f64Store bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Store8 bm x ao hm => exact encInstrMem_memArg rfl hm
  | i32Store16 bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Store8 bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Store16 bm x ao hm => exact encInstrMem_memArg rfl hm
  | i64Store32 bm x ao hm => exact encInstrMem_memArg rfl hm
  | size bs x hx => exact encInstrMem_idx rfl hx
  | grow bs x hx => exact encInstrMem_idx rfl hx
  | init bo by' bx y x ho hy hx =>
      exact ⟨pre 0xFC 8 ++ lebU y.val ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hyl := lebU_minimal hy
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | dataDrop bo bx x ho hx =>
      exact ⟨pre 0xFC 9 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩
  | copy bo b₁ b₂ x₁ x₂ ho h₁ h₂ =>
      exact ⟨pre 0xFC 10 ++ lebU x₁.val ++ lebU x₂.val, rfl, by
        have hol := pre_length_le ho
        have hl₁ := lebU_minimal h₁
        have hl₂ := lebU_minimal h₂
        simp
        omega⟩
  | fill bo bx x ho hx =>
      exact ⟨pre 0xFC 11 ++ lebU x.val, rfl, by
        have hol := pre_length_le ho
        have hxl := lebU_minimal hx
        simp
        omega⟩

theorem encInstrRef_completeLe : CompleteLe encInstrRef BinstrRef := by
  intro w i h
  cases h with
  | null bs ht hh =>
      obtain ⟨out, hout, hle⟩ := encHeapType_completeLe hh
      exact ⟨tb 0xD0 :: out, by simp [encInstrRef, consO, hout], by simp; omega⟩
  | isNull => exact ⟨_, rfl, Nat.le_refl 1⟩
  | func bs x hx =>
      exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hx) 1⟩
  | eq => exact ⟨_, rfl, Nat.le_refl 1⟩
  | asNonNull => exact ⟨_, rfl, Nat.le_refl 1⟩
  | brOnNull bs l hl =>
      exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩
  | brOnNonNull bs l hl =>
      exact ⟨_, rfl, by simpa using Nat.add_le_add_right (lebU_minimal hl) 1⟩

theorem encPre0_completeLe {f : Instr → Option Bytes} {i : Instr}
    {p k : Nat} {bo : Bytes} (heq : f i = some (pre p k))
    (ho : Bprefixed p k bo) :
    ∃ out, f i = some out ∧ out.length ≤ bo.length :=
  ⟨pre p k, heq, pre_length_le ho⟩

theorem encPre1_completeLe {f : Instr → Option Bytes} {i : Instr}
    {p k : Nat} {bo bx : Bytes} {x : U32}
    (heq : f i = some (pre p k ++ lebU x.val))
    (ho : Bprefixed p k bo) (hx : Bu32 bx x) :
    ∃ out, f i = some out ∧ out.length ≤ (bo ++ bx).length :=
  ⟨pre p k ++ lebU x.val, heq, by
    have hol := pre_length_le ho
    have hxl := lebU_minimal hx
    simp
    omega⟩

theorem encPre2_completeLe {f : Instr → Option Bytes} {i : Instr}
    {p k : Nat} {bo bx by' : Bytes} {x y : U32}
    (heq : f i = some (pre p k ++ lebU x.val ++ lebU y.val))
    (ho : Bprefixed p k bo) (hx : Bu32 bx x) (hy : Bu32 by' y) :
    ∃ out, f i = some out ∧ out.length ≤ (bo ++ bx ++ by').length :=
  ⟨pre p k ++ lebU x.val ++ lebU y.val, heq, by
    have hol := pre_length_le ho
    have hxl := lebU_minimal hx
    have hyl := lebU_minimal hy
    simp
    omega⟩

theorem encInstrStr_completeLe : CompleteLe encInstrStr BinstrStruct := by
  intro w i h
  cases h with
  | new bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | newDefault bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | get bo bx bi x n ho hx hn => exact encPre2_completeLe rfl ho hx hn
  | getS bo bx bi x n ho hx hn => exact encPre2_completeLe rfl ho hx hn
  | getU bo bx bi x n ho hx hn => exact encPre2_completeLe rfl ho hx hn
  | set bo bx bi x n ho hx hn => exact encPre2_completeLe rfl ho hx hn

theorem encInstrArr_completeLe : CompleteLe encInstrArr BinstrArray := by
  intro w i h
  cases h with
  | new bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | newDefault bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | newFixed bo bx bn x n ho hx hn => exact encPre2_completeLe rfl ho hx hn
  | newData bo bx by' x y ho hx hy => exact encPre2_completeLe rfl ho hx hy
  | newElem bo bx by' x y ho hx hy => exact encPre2_completeLe rfl ho hx hy
  | get bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | getS bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | getU bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | set bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | len bo ho => exact encPre0_completeLe rfl ho
  | fill bo bx x ho hx => exact encPre1_completeLe rfl ho hx
  | copy bo b₁ b₂ x₁ x₂ ho h₁ h₂ => exact encPre2_completeLe rfl ho h₁ h₂
  | initData bo bx by' x y ho hx hy => exact encPre2_completeLe rfl ho hx hy
  | initElem bo bx by' x y ho hx hy => exact encPre2_completeLe rfl ho hx hy

theorem encInstrCast_heap {i : Instr} {k : Nat} {bo bh : Bytes}
    {ht : HeapType} (heq : encInstrCast i = catO (some (pre 0xFB k)) (encHeapType ht))
    (ho : Bprefixed 0xFB k bo) (hh : Bheaptype bh ht) :
    ∃ out, encInstrCast i = some out ∧ out.length ≤ (bo ++ bh).length := by
  obtain ⟨oh, hoh, hleh⟩ := encHeapType_completeLe hh
  refine ⟨pre 0xFB k ++ oh, ?_, ?_⟩
  · rw [heq]
    exact catO_some rfl hoh
  · have hlo := pre_length_le ho
    simp
    omega

theorem encInstrCast_completeLe : CompleteLe encInstrCast BinstrCast := by
  intro w i h
  cases h with
  | test bo bh ht ho hh => exact encInstrCast_heap rfl ho hh
  | testNull bo bh ht ho hh => exact encInstrCast_heap rfl ho hh
  | cast bo bh ht ho hh => exact encInstrCast_heap rfl ho hh
  | castNull bo bh ht ho hh => exact encInstrCast_heap rfl ho hh
  | brOnCast bo bc bl b₁ b₂ n₁ n₂ l ht₁ ht₂ ho hc hl h₁ h₂ =>
      obtain ⟨o₁, ho₁, hle₁⟩ := encHeapType_completeLe h₁
      obtain ⟨o₂, ho₂, hle₂⟩ := encHeapType_completeLe h₂
      refine ⟨pre 0xFB 24 ++ encCastOp n₁ n₂ ++ lebU l.val ++ o₁ ++ o₂, ?_, ?_⟩
      · simp [encInstrCast, catO, ho₁, ho₂]
      · have hlo := pre_length_le ho
        have hll := lebU_minimal hl
        cases hc <;> simp [encCastOp] at * <;> omega
  | brOnCastFail bo bc bl b₁ b₂ n₁ n₂ l ht₁ ht₂ ho hc hl h₁ h₂ =>
      obtain ⟨o₁, ho₁, hle₁⟩ := encHeapType_completeLe h₁
      obtain ⟨o₂, ho₂, hle₂⟩ := encHeapType_completeLe h₂
      refine ⟨pre 0xFB 25 ++ encCastOp n₁ n₂ ++ lebU l.val ++ o₁ ++ o₂, ?_, ?_⟩
      · simp [encInstrCast, catO, ho₁, ho₂]
      · have hlo := pre_length_le ho
        have hll := lebU_minimal hl
        cases hc <;> simp [encCastOp] at * <;> omega

theorem encInstrExt_completeLe : CompleteLe encInstrExt BinstrExtern := by
  intro w i h
  cases h with
  | anyConvertExtern ho => exact encPre0_completeLe rfl ho
  | externConvertAny ho => exact encPre0_completeLe rfl ho

theorem encInstrI31_completeLe : CompleteLe encInstrI31 BinstrI31 := by
  intro w i h
  cases h with
  | refI31 ho => exact encPre0_completeLe rfl ho
  | getS ho => exact encPre0_completeLe rfl ho
  | getU ho => exact encPre0_completeLe rfl ho

theorem encInstrNum_i32Const {bs : Bytes} {n : U32} (h : Bu32 bs n) :
    ∃ out, encInstrNum (.const .i32 n) = some out ∧
      out.length ≤ (tb 0x41 :: bs).length :=
  ⟨tb 0x41 :: lebU n.val, rfl, by
    simpa using Nat.add_le_add_right (lebU_minimal h) 1⟩

theorem encInstrNum_i64Const {bs : Bytes} {n : U64} (h : Bu64 bs n) :
    ∃ out, encInstrNum (.const .i64 n) = some out ∧
      out.length ≤ (tb 0x42 :: bs).length :=
  ⟨tb 0x42 :: lebU n.val, rfl, by
    simpa using Nat.add_le_add_right (lebU_minimal h) 1⟩

theorem encInstrNum_f32Const {bs : Bytes} {p : F32} (h : Bf32 bs p) :
    ∃ out, encInstrNum (.const .f32 p) = some out ∧
      out.length ≤ (tb 0x43 :: bs).length := by
  obtain ⟨out, hout, hle⟩ := encF32_completeLe h
  refine ⟨tb 0x43 :: out, ?_, by simp; omega⟩
  change orO (consO (tb 0x43) (encF32 p)) _ = _
  rw [consO_some hout]
  rfl

theorem encInstrNum_f64Const {bs : Bytes} {p : F64} (h : Bf64 bs p) :
    ∃ out, encInstrNum (.const .f64 p) = some out ∧
      out.length ≤ (tb 0x44 :: bs).length := by
  obtain ⟨out, hout, hle⟩ := encF64_completeLe h
  refine ⟨tb 0x44 :: out, ?_, by simp; omega⟩
  change orO (consO (tb 0x44) (encF64 p)) _ = _
  rw [consO_some hout]
  rfl

theorem encInstrNum_completeLe : CompleteLe encInstrNum BinstrNumFor := by
  intro w i h
  cases hr : authority.revision with
  | pinned =>
      simp [BinstrNumFor, hr] at h
      cases h
      case i32Const bs n hn => exact encInstrNum_i32Const hn
      case i64Const bs n hn => exact encInstrNum_i64Const hn
      case f32Const bs p hp => exact encInstrNum_f32Const hp
      case f64Const bs p hp => exact encInstrNum_f64Const hp
      case f32PromoteF64 => exact ⟨[tb 0xBB], by simp [encInstrNum, encInstrNumC,
          encInstrNumOp, encCvtopN, encCvtopNBase, encCvtopNPromote, orO, hr],
          Nat.le_refl 1⟩
      all_goals first
        | exact encPre0_completeLe (f := encInstrNum) rfl (by assumption)
        | exact ⟨_, rfl, Nat.le_refl 1⟩
  | amended =>
      simp [BinstrNumFor, hr] at h
      cases h with
      | f64PromoteF32 => exact ⟨[tb 0xBB], by simp [encInstrNum, encInstrNumOp,
          encInstrNumC, encCvtopN, encCvtopNBase, encCvtopNPromote, orO, hr],
          Nat.le_refl 1⟩
      | ofPinned bs instr hp hne =>
          cases hp
          case i32Const bs n hn => exact encInstrNum_i32Const hn
          case i64Const bs n hn => exact encInstrNum_i64Const hn
          case f32Const bs p hp => exact encInstrNum_f32Const hp
          case f64Const bs p hp => exact encInstrNum_f64Const hp
          case f32PromoteF64 => exact absurd rfl hne
          all_goals first
            | exact encPre0_completeLe (f := encInstrNum) rfl (by assumption)
            | exact ⟨_, rfl, Nat.le_refl 1⟩

theorem encInstrVec_mem {i : Instr} {k : Nat} {bo bm : Bytes}
    {x : MemIdx} {ao : MemArg} (heq : encInstrVecImm i = encFDMem k x ao)
    (ho : Bprefixed 0xFD k bo) (hm : Bmemarg bm (x, ao)) :
    ∃ out, encInstrVec i = some out ∧ out.length ≤ (bo ++ bm).length := by
  obtain ⟨om, hom, hlem⟩ := encMemArg_completeLe hm
  have himm : encInstrVecImm i = some (pre 0xFD k ++ om) := by
    rw [heq]
    simp [encFDMem, catO, hom]
  obtain ⟨chosen, hchosen, hlchosen⟩ :=
    orO_left_le (y := encInstrVec0 i) himm
  refine ⟨chosen, by simpa [encInstrVec] using hchosen, ?_⟩
  have hlo := pre_length_le ho
  simp at hlchosen ⊢
  omega

theorem encInstrVec_memLane {i : Instr} {k : Nat} {bo bm bi : Bytes}
    {x : MemIdx} {ao : MemArg} {l : LaneIdx}
    (heq : encInstrVecImm i = encFDMemLane k x ao l)
    (ho : Bprefixed 0xFD k bo) (hm : Bmemarg bm (x, ao))
    (hl : Blaneidx bi l) :
    ∃ out, encInstrVec i = some out ∧
      out.length ≤ (bo ++ bm ++ bi).length := by
  obtain ⟨om, hom, hlem⟩ := encMemArg_completeLe hm
  have himm : encInstrVecImm i = some (pre 0xFD k ++ om ++ encLaneIdx l) := by
    rw [heq]
    simp [encFDMemLane, encFDMem, catO, hom]
  obtain ⟨chosen, hchosen, hlchosen⟩ :=
    orO_left_le (y := encInstrVec0 i) himm
  refine ⟨chosen, by simpa [encInstrVec] using hchosen, ?_⟩
  have hlo := pre_length_le ho
  cases hl
  simp [encLaneIdx] at hlchosen ⊢
  omega

theorem encInstrVec_lane {i : Instr} {k : Nat} {bo bi : Bytes}
    {l : LaneIdx}
    (heq : encInstrVecImm i = some (pre 0xFD k ++ encLaneIdx l))
    (ho : Bprefixed 0xFD k bo) (hl : Blaneidx bi l) :
    ∃ out, encInstrVec i = some out ∧ out.length ≤ (bo ++ bi).length := by
  obtain ⟨chosen, hchosen, hlchosen⟩ :=
    orO_left_le (y := encInstrVec0 i) heq
  refine ⟨chosen, by simpa [encInstrVec] using hchosen, ?_⟩
  have hlo := pre_length_le ho
  cases hl
  simp [encLaneIdx] at hlchosen ⊢
  omega

theorem encLaneIdxs_length (ls : List LaneIdx) :
    (encLaneIdxs ls).length = ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [encLaneIdxs, encLaneIdx, ih]

theorem Rep.Blaneidx_bytes_length {n : Nat} {w : Bytes} {ls : List LaneIdx}
    (h : Rep Blaneidx n w ls) : w.length = n := by
  induction h with
  | nil => rfl
  | cons b l bs ls k hl hls ih =>
      cases hl
      simp [ih]

theorem encInstrVecMem_completeLe : CompleteLe encInstrVec BinstrVecMem := by
  intro w i h
  cases h with
  | v128Load bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load8x8S bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load8x8U bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load16x4S bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load16x4U bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load32x2S bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load32x2U bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load8Splat bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load16Splat bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load32Splat bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load64Splat bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Store bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load8Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Load16Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Load32Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Load64Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Store8Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Store16Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Store32Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Store64Lane bo bm bi x ao l ho hm hl => exact encInstrVec_memLane rfl ho hm hl
  | v128Load32Zero bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Load64Zero bo bm x ao ho hm => exact encInstrVec_mem rfl ho hm
  | v128Const bo bb bl c ho hb hc =>
      have himm : encInstrVecImm (.vconst .v128 c) =
          some (pre 0xFD 12 ++ bytesLE 16 c.val) := by
        simp [encInstrVecImm]
      obtain ⟨chosen, hchosen, hlchosen⟩ :=
        orO_left_le (y := encInstrVec0 (.vconst .v128 c)) himm
      refine ⟨chosen, by simpa [encInstrVec] using hchosen, ?_⟩
      have hlo := pre_length_le ho
      have hbb : bb.length = 16 := by simpa using hb.Bbyte_length
      simp [bytesLE_length] at hlchosen
      simp
      omega
  | i8x16Shuffle bo bl ls ho hls =>
      have hlen : ls.length = 16 := hls.length
      have himm : encInstrVecImm (.vshuffle bshI8x16 ls) =
          some (pre 0xFD 13 ++ encLaneIdxs ls) := by
        simp [encInstrVecImm, hlen]
      obtain ⟨chosen, hchosen, hlchosen⟩ :=
        orO_left_le (y := encInstrVec0 (.vshuffle bshI8x16 ls)) himm
      refine ⟨chosen, by simpa [encInstrVec] using hchosen, ?_⟩
      have hlo := pre_length_le ho
      have hbl : bl.length = 16 := hls.Blaneidx_bytes_length
      simp [encLaneIdxs_length, hlen] at hlchosen
      simp [hbl]
      omega
  | i8x16Swizzle _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i8x16RelaxedSwizzle _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i8x16Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i16x8Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i32x4Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i64x2Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | f32x4Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | f64x2Splat _ => exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | i8x16ExtractLaneS bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i8x16ExtractLaneU bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i8x16ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i16x8ExtractLaneS bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i16x8ExtractLaneU bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i16x8ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i32x4ExtractLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i32x4ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i64x2ExtractLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | i64x2ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | f32x4ExtractLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | f32x4ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | f64x2ExtractLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl
  | f64x2ReplaceLane bo bi l ho hl => exact encInstrVec_lane rfl ho hl

theorem encInstrVecRel_completeLe : CompleteLe encInstrVec BinstrVecRel := by
  intro w i h
  cases h <;> exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)

theorem encInstrVecV128_completeLe : CompleteLe encInstrVec BinstrVecV128 := by
  intro w i h
  cases h <;> exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)

theorem encInstrVecInt8And16_completeLe :
    CompleteLe encInstrVec BinstrVecInt8And16 := by
  intro w i h
  cases h <;> exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)

theorem encInstrVecInt32And64_completeLe :
    CompleteLe encInstrVec BinstrVecInt32And64For := by
  intro w i h
  cases hr : authority.revision with
  | pinned =>
      simp [BinstrVecInt32And64For, hr] at h
      cases h
      case i32x4RelaxedDotAddI16x8S =>
        have hc : pinnedBadRelaxedDotAdd ≠
            (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s) : Instr) := by
          decide
        have hzero : encInstrVec0 pinnedBadRelaxedDotAdd =
            some (pre 0xFD 275) := by
          simp only [encInstrVec0, if_neg hc, if_pos rfl, hr, if_true]
        have himm : encInstrVecImm pinnedBadRelaxedDotAdd = none := by rfl
        have henc : encInstrVec pinnedBadRelaxedDotAdd =
            some (pre 0xFD 275) := by
          simp only [encInstrVec, himm, hzero, orO]
        exact encPre0_completeLe (f := encInstrVec) henc (by assumption)
      all_goals exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
  | amended =>
      simp [BinstrVecInt32And64For, hr] at h
      cases h with
      | ofPinned _ hp hne =>
          cases hp
          case i32x4RelaxedDotAddI16x8S => exact (hne rfl).elim
          all_goals exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)
      | correctedRelaxedDotAdd hbo =>
          have hzero : encInstrVec0
              (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s) : Instr) =
              some (pre 0xFD 275) := by
            simp only [encInstrVec0, if_pos rfl, hr, if_true]
          have himm : encInstrVecImm
              (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s) : Instr) = none := by
            rfl
          exact encPre0_completeLe (f := encInstrVec) (by
            simp only [encInstrVec, himm, hzero, orO]) hbo

theorem encInstrVecFloat_completeLe : CompleteLe encInstrVec BinstrVecFloat := by
  intro w i h
  cases h <;> exact encPre0_completeLe (f := encInstrVec) rfl (by assumption)


theorem encInstrFlat_param_completeLe {w : Bytes} {i : Instr} (h : BinstrParametric w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_left; exact encInstrParam_completeLe h

theorem encInstrFlat_control_completeLe {w : Bytes} {i : Instr} (h : BinstrControlFor w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_left
  exact encInstrCtl_completeLe h

theorem encInstrFlat_local_completeLe {w : Bytes} {i : Instr} (h : BinstrLocal w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_left; exact encInstrLoc_completeLe h

theorem encInstrFlat_global_completeLe {w : Bytes} {i : Instr} (h : BinstrGlobal w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_left; exact encInstrGlob_completeLe h

theorem encInstrFlat_table_completeLe {w : Bytes} {i : Instr} (h : BinstrTable w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_left
  exact encInstrTbl_completeLe h

theorem encInstrFlat_memory_completeLe {w : Bytes} {i : Instr} (h : BinstrMemory w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_left; exact encInstrMem_completeLe h

theorem encInstrFlat_ref_completeLe {w : Bytes} {i : Instr} (h : BinstrRef w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_left; exact encInstrRef_completeLe h

theorem encInstrFlat_struct_completeLe {w : Bytes} {i : Instr} (h : BinstrStruct w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_left
  exact encInstrStr_completeLe h

theorem encInstrFlat_array_completeLe {w : Bytes} {i : Instr} (h : BinstrArray w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_left; exact encInstrArr_completeLe h

theorem encInstrFlat_cast_completeLe {w : Bytes} {i : Instr} (h : BinstrCast w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_left; exact encInstrCast_completeLe h

theorem encInstrFlat_extern_completeLe {w : Bytes} {i : Instr} (h : BinstrExtern w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_left
  exact encInstrExt_completeLe h

theorem encInstrFlat_i31_completeLe {w : Bytes} {i : Instr} (h : BinstrI31 w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_left; exact encInstrI31_completeLe h

theorem encInstrFlat_num_completeLe {w : Bytes} {i : Instr} (h : BinstrNumFor w i) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_left; exact encInstrNum_completeLe h

theorem encInstrFlat_vec_completeLe {w : Bytes} {i : Instr}
    (h : ∃ out, encInstrVec i = some out ∧ out.length ≤ w.length) :
    ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length := by
  unfold encInstrFlat; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; apply orO_lift_right
  apply orO_lift_right; apply orO_lift_right; exact h

theorem encInstr_of_rec_completeLe {w : Bytes} {i : Instr}
    (h : ∃ out, encInstrRec i = some out ∧ out.length ≤ w.length) :
    ∃ out, encInstr i = some out ∧ out.length ≤ w.length := by
  unfold encInstr; exact orO_lift_left h

theorem encInstr_of_flat_completeLe {w : Bytes} {i : Instr}
    (h : ∃ out, encInstrFlat i = some out ∧ out.length ≤ w.length) :
    ∃ out, encInstr i = some out ∧ out.length ≤ w.length := by
  unfold encInstr; exact orO_lift_right h

theorem enc_complete_aux : ∀ n : Nat,
    (∀ {w : Bytes} {i : Instr}, instrSize i ≤ n → Binstr w i →
      ∃ out, encInstr i = some out ∧ out.length ≤ w.length) ∧
    (∀ {w : Bytes} {ins : List Instr},
      instrsSize (InstrSeq.ofList ins) ≤ n → Binstrs w ins →
      ∃ out, encInstrs (InstrSeq.ofList ins) = some out ∧
        out.length ≤ w.length) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    constructor
    · intro w i hsize h
      cases h with
        | block bbt bin bt ins hbt hins =>
            obtain ⟨obt, hobt, hlebt⟩ := encBlockType_completeLe hbt
            obtain ⟨oin, hoin, hlein⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) hins
            apply encInstr_of_rec_completeLe
            refine ⟨tb 0x02 :: (obt ++ oin ++ [tb 0x0B]), ?_, ?_⟩
            · simp [encInstrRec, catO, consO, hobt, hoin]
            · simp; omega
        | loop bbt bin bt ins hbt hins =>
            obtain ⟨obt, hobt, hlebt⟩ := encBlockType_completeLe hbt
            obtain ⟨oin, hoin, hlein⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) hins
            apply encInstr_of_rec_completeLe
            refine ⟨tb 0x03 :: (obt ++ oin ++ [tb 0x0B]), ?_, ?_⟩
            · simp [encInstrRec, catO, consO, hobt, hoin]
            · simp; omega
        | ifThen bbt bin bt ins hbt hins =>
            obtain ⟨obt, hobt, hlebt⟩ := encBlockType_completeLe hbt
            obtain ⟨oin, hoin, hlein⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) hins
            apply encInstr_of_rec_completeLe
            refine ⟨tb 0x04 :: (obt ++ oin ++ [tb 0x0B]), ?_, ?_⟩
            · simp [encInstrRec, catO, consO, hobt, hoin]
            · simp; omega
        | ifElse bbt b₁ b₂ bt ins₁ ins₂ hbt h₁ h₂ =>
            obtain ⟨obt, hobt, hlebt⟩ := encBlockType_completeLe hbt
            obtain ⟨o₁, ho₁, hle₁⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins₁)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) h₁
            obtain ⟨o₂, ho₂, hle₂⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins₂)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) h₂
            cases ins₂ with
            | nil =>
                apply encInstr_of_rec_completeLe
                refine ⟨tb 0x04 :: (obt ++ o₁ ++ [tb 0x0B]), ?_, ?_⟩
                · simp [InstrSeq.ofList, encInstrRec, catO, consO, hobt, ho₁]
                · simp; omega
            | cons j js =>
                apply encInstr_of_rec_completeLe
                refine ⟨tb 0x04 :: (obt ++ o₁ ++ [tb 0x05] ++ o₂ ++ [tb 0x0B]), ?_, ?_⟩
                · change encInstrs (InstrSeq.cons j (InstrSeq.ofList js)) = some o₂ at ho₂
                  simp [InstrSeq.ofList, encInstrRec, catO, consO, hobt, ho₁, ho₂]
                · simp; omega
        | tryTable bbt bc bin bt cs ins hbt hcs hins =>
            obtain ⟨obt, hobt, hlebt⟩ := encBlockType_completeLe hbt
            obtain ⟨ocs, hocs, hlecs⟩ := encList_completeLe
              (f := encCatch) (G := Bcatch) encCatch_completeLe hcs
            obtain ⟨oin, hoin, hlein⟩ :=
              (ih (instrsSize (InstrSeq.ofList ins)) (by simp [instrSize] at hsize; omega)).2
                (Nat.le_refl _) hins
            apply encInstr_of_rec_completeLe
            refine ⟨tb 0x1F :: (obt ++ ocs ++ oin ++ [tb 0x0B]), ?_, ?_⟩
            · simp [encInstrRec, catO, consO, hobt, hocs, hoin]
            · simp; omega
        | ofParametric bs i hp => exact encInstr_of_flat_completeLe (encInstrFlat_param_completeLe hp)
        | ofControl bs i hc => exact encInstr_of_flat_completeLe (encInstrFlat_control_completeLe hc)
        | ofLocal bs i hl => exact encInstr_of_flat_completeLe (encInstrFlat_local_completeLe hl)
        | ofGlobal bs i hg => exact encInstr_of_flat_completeLe (encInstrFlat_global_completeLe hg)
        | ofTable bs i ht => exact encInstr_of_flat_completeLe (encInstrFlat_table_completeLe ht)
        | ofMemory bs i hm => exact encInstr_of_flat_completeLe (encInstrFlat_memory_completeLe hm)
        | ofRef bs i hr => exact encInstr_of_flat_completeLe (encInstrFlat_ref_completeLe hr)
        | ofStruct bs i hs => exact encInstr_of_flat_completeLe (encInstrFlat_struct_completeLe hs)
        | ofArray bs i ha => exact encInstr_of_flat_completeLe (encInstrFlat_array_completeLe ha)
        | ofCast bs i hc => exact encInstr_of_flat_completeLe (encInstrFlat_cast_completeLe hc)
        | ofExtern bs i he => exact encInstr_of_flat_completeLe (encInstrFlat_extern_completeLe he)
        | ofI31 bs i hi => exact encInstr_of_flat_completeLe (encInstrFlat_i31_completeLe hi)
        | ofNum bs i hn => exact encInstr_of_flat_completeLe (encInstrFlat_num_completeLe hn)
        | ofVecMem bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecMem_completeLe hv))
        | ofVecRel bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecRel_completeLe hv))
        | ofVecV128 bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecV128_completeLe hv))
        | ofVecInt8And16 bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecInt8And16_completeLe hv))
        | ofVecInt32And64 bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecInt32And64_completeLe hv))
        | ofVecFloat bs i hv => exact encInstr_of_flat_completeLe (encInstrFlat_vec_completeLe (encInstrVecFloat_completeLe hv))
    · intro w ins hsize h
      cases h with
      | nil => exact ⟨[], rfl, Nat.le_refl 0⟩
      | cons b bs i is hi his =>
          change instrSize i + instrsSize (InstrSeq.ofList is) + 1 ≤ n at hsize
          have hisize : instrSize i < n := by
            omega
          have hrsize : instrsSize (InstrSeq.ofList is) < n := by
            omega
          obtain ⟨oi, hoi, hlei⟩ :=
            (ih (instrSize i) hisize).1 (Nat.le_refl _) hi
          obtain ⟨ois, hois, hleis⟩ :=
            (ih (instrsSize (InstrSeq.ofList is)) hrsize).2 (Nat.le_refl _) his
          refine ⟨oi ++ ois, ?_, ?_⟩
          · change catO (encInstr i) (encInstrs (InstrSeq.ofList is)) = _
            exact catO_some hoi hois
          · simp; omega

theorem encInstr_completeLe {w : Bytes} {i : Instr} (h : Binstr w i) :
    ∃ out, encInstr i = some out ∧ out.length ≤ w.length :=
  (enc_complete_aux (instrSize i)).1 (Nat.le_refl _) h

theorem encInstrs_completeLe {w : Bytes} {ins : List Instr} (h : Binstrs w ins) :
    ∃ out, encInstrs (InstrSeq.ofList ins) = some out ∧ out.length ≤ w.length :=
  (enc_complete_aux (instrsSize (InstrSeq.ofList ins))).2 (Nat.le_refl _) h

theorem encExpr_completeLe : CompleteLe encExpr Bexpr := by
  intro w e h
  cases h with
  | mk bs ins hins =>
      obtain ⟨out, hout, hle⟩ := encInstrs_completeLe hins
      exact ⟨out ++ [tb 0x0B], by simp [encExpr, catO, hout], by simp; omega⟩

theorem lebU_div_add_le (a b : Nat) : (a + b) / 128 ≤ a / 128 + b := by
  apply (Nat.div_le_iff_le_mul (k := 128) (x := a + b) (y := a / 128 + b)
    (by decide)).2
  have hm := Nat.mod_add_div a 128
  have hmlt := Nat.mod_lt a (by decide : 0 < 128)
  omega

theorem lebU_add_length_le (a b : Nat) :
    (lebU (a + b)).length ≤ (lebU a).length + (lebU b).length := by
  induction s : a + b using Nat.strongRecOn generalizing a b with
  | _ s ih =>
      subst s
      rw [lebU_eq (a + b)]
      by_cases hs : a + b < 0x80
      · rw [if_pos hs]
        have ha : a < 0x80 := by omega
        have hb : b < 0x80 := by omega
        rw [lebU_eq a, if_pos ha, lebU_eq b, if_pos hb]
        simp only [List.length_singleton]
        omega
      · rw [if_neg hs]
        by_cases ha : a < 0x80
        · by_cases hb : b < 0x80
          · rw [lebU_eq a, if_pos ha, lebU_eq b, if_pos hb]
            have hq : (a + b) / 0x80 < 0x80 := by omega
            rw [lebU_eq ((a + b) / 0x80), if_pos hq]
            simp only [List.length_cons, List.length_singleton, List.length_nil]
            omega
          · have hle : (a + b) / 0x80 ≤ b / 0x80 + a := by
              simpa [Nat.add_comm] using lebU_div_add_le b a
            have hlt : b / 0x80 + a < a + b := by
              have hbdiv : b / 0x80 < b := Nat.div_lt_self (by omega) (by omega)
              omega
            have hi := ih (b / 0x80 + a) hlt (b / 0x80) a (by omega)
            have hm := lebU_length_mono hle
            have hia : (lebU (b / 0x80 + a)).length ≤
                (lebU (b / 0x80)).length + 1 := by
              rw [lebU_eq a, if_pos ha] at hi
              simpa only [List.length_singleton] using hi
            have hq := Nat.le_trans hm hia
            rw [lebU_eq a, if_pos ha, lebU_eq b, if_neg hb]
            simpa only [List.length_cons, List.length_singleton, List.length_nil,
              Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using Nat.add_le_add_right hq 1
        · have hle : (a + b) / 0x80 ≤ a / 0x80 + b := lebU_div_add_le a b
          have hlt : a / 0x80 + b < a + b := by
            have hadiv : a / 0x80 < a := Nat.div_lt_self (by omega) (by omega)
            omega
          have hi := ih (a / 0x80 + b) hlt (a / 0x80) b (by omega)
          have hm := lebU_length_mono hle
          have hq := Nat.le_trans hm hi
          rw [lebU_eq a, if_neg ha]
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using Nat.add_le_add_left hq 1

def mergeLocalRun : List Local → List (List Local) → List (List Local)
  | [], rss => rss
  | r, [] => [r]
  | r, [] :: rss => r :: [] :: rss
  | (l :: ls), ((h :: hs) :: rss) =>
      if l = h then ((l :: ls) ++ (h :: hs)) :: rss
      else (l :: ls) :: (h :: hs) :: rss

theorem allLocalEq_append (l : Local) : ∀ xs ys,
    allLocalEq l xs = true → allLocalEq l ys = true →
      allLocalEq l (xs ++ ys) = true
  | [], ys, _, hy => hy
  | x :: xs, ys, hx, hy => by
      simp only [allLocalEq] at hx ⊢
      split at hx
      · rename_i hxl
        subst x
        change (if l = l then allLocalEq l (xs ++ ys) else false) = true
        rw [if_pos rfl]
        exact allLocalEq_append l xs ys hx hy
      · contradiction

theorem LocalRunOK.tail {l : Local} {ls : List Local}
    (h : LocalRunOK (l :: ls)) : allLocalEq l ls = true := h

theorem LocalRunOK.cons_tail {l : Local} {ls : List Local}
    (h : LocalRunOK (l :: ls)) : allLocalEq l (l :: ls) = true := by
  simp [allLocalEq, h.tail]

theorem allLocalEq_mem {l x : Local} {xs : List Local}
    (h : allLocalEq l xs = true) (hx : x ∈ xs) : x = l := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
      simp only [allLocalEq] at h
      split at h
      · rename_i hyl
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hyl
        · exact ih h hx
      · contradiction

theorem mergeLocalRun_prepend (l : Local) {r : List Local}
    (hr : LocalRunOK r) (hl : ∀ h, h ∈ r → l = h) (rss : List (List Local))
    (hcanon : LocalRunsOK rss) :
    prependLocalRun l (mergeLocalRun r rss) = mergeLocalRun (l :: r) rss := by
  cases r with
  | nil => contradiction
  | cons h hs =>
      have hlh : l = h := hl h (by simp)
      subst h
      cases rss with
      | nil => simp [mergeLocalRun, prependLocalRun]
      | cons s ss =>
          cases s with
          | nil =>
              have hf : False := hcanon [] (by simp)
              contradiction
          | cons x xs =>
              simp only [mergeLocalRun, prependLocalRun]
              by_cases hlx : l = x
              · simp [hlx]
              · simp [hlx]

theorem localRuns_append_uniform (r ls : List Local) (hr : LocalRunOK r) :
    localRuns (r ++ ls) = mergeLocalRun r (localRuns ls) := by
  induction r with
  | nil => contradiction
  | cons l r ih =>
      cases r with
      | nil =>
          cases hrs : localRuns ls with
          | nil => simp [localRuns, hrs, mergeLocalRun, prependLocalRun]
          | cons s ss =>
              cases s with
              | nil =>
                  have hf : False := localRuns_ok ls [] (by simp [hrs])
                  contradiction
              | cons x xs => simp [localRuns, hrs, mergeLocalRun, prependLocalRun]
      | cons h hs =>
          have hlh : l = h := by
            have hx : h = l ∧ allLocalEq l hs = true := by
              simpa [LocalRunOK, allLocalEq] using hr
            exact hx.1.symm
          subst h
          have htail : LocalRunOK (l :: hs) := by
            simpa [LocalRunOK, allLocalEq] using hr
          have hall : ∀ h, h ∈ (l :: hs) → l = h := by
            intro h hh
            rcases List.mem_cons.mp hh with rfl | hh
            · rfl
            · exact (allLocalEq_mem htail hh).symm
          change prependLocalRun l (localRuns ((l :: hs) ++ ls)) =
            mergeLocalRun (l :: l :: hs) (localRuns ls)
          rw [ih htail]
          exact mergeLocalRun_prepend l htail hall (localRuns ls) (localRuns_ok ls)

theorem encLocalRun_append_completeLe {l : Local} {xs ys : List Local}
    {bout₁ bout₂ : Bytes}
    (hx : LocalRunOK (l :: xs)) (hy : LocalRunOK (l :: ys))
    (hlen : ((l :: xs) ++ (l :: ys)).length < 2 ^ 32)
    (hbx : encLocalRun (l :: xs) = some bout₁)
    (hby : encLocalRun (l :: ys) = some bout₂) :
    ∃ out, encLocalRun ((l :: xs) ++ (l :: ys)) = some out ∧
      out.length ≤ bout₁.length + bout₂.length := by
  have hlenx : (l :: xs).length < 2 ^ 32 := by simp at hlen ⊢; omega
  have hleny : (l :: ys).length < 2 ^ 32 := by simp at hlen ⊢; omega
  have hsame : allLocalEq l (xs ++ l :: ys) = true :=
    allLocalEq_append l xs (l :: ys) hx.tail hy.cons_tail
  cases hv : encValType l.valtype with
  | none =>
      have : encLocalRun (l :: xs) = none := by
        simp only [encLocalRun]
        rw [if_pos hx.tail, if_pos hlenx, hv]
        rfl
      rw [this] at hbx
      contradiction
  | some v =>
      have hex : encLocalRun (l :: xs) = some (lebU (l :: xs).length ++ v) := by
        simp only [encLocalRun]
        rw [if_pos hx.tail, if_pos hlenx, hv]
        rfl
      have hey : encLocalRun (l :: ys) = some (lebU (l :: ys).length ++ v) := by
        simp only [encLocalRun]
        rw [if_pos hy.tail, if_pos hleny, hv]
        rfl
      have hexy : encLocalRun ((l :: xs) ++ (l :: ys)) =
          some (lebU ((l :: xs) ++ (l :: ys)).length ++ v) := by
        have hlen' : (l :: (xs ++ l :: ys)).length < 2 ^ 32 := by
          simpa only [List.cons_append] using hlen
        simp only [List.cons_append, encLocalRun]
        rw [if_pos hsame, if_pos hlen', hv]
        rfl
      rw [hex] at hbx
      rw [hey] at hby
      injection hbx with hbx
      injection hby with hby
      subst bout₁
      subst bout₂
      refine ⟨lebU ((l :: xs) ++ (l :: ys)).length ++ v, hexy, ?_⟩
      have hleb := lebU_add_length_le (l :: xs).length (l :: ys).length
      simp only [List.length_append] at hleb ⊢
      omega

theorem encRep_mergeLocalRun_completeLe {r : List Local}
    {rss : List (List Local)} {br bs : Bytes}
    (hr : LocalRunOK r) (hrs : LocalRunsOK rss)
    (hlen : (r ++ rss.flatten).length < 2 ^ 32)
    (hbr : encLocalRun r = some br)
    (hbs : encRep encLocalRun rss = some bs) :
    ∃ out, encRep encLocalRun (mergeLocalRun r rss) = some out ∧
      out.length ≤ br.length + bs.length := by
  cases r with
  | nil => contradiction
  | cons l ls =>
      cases rss with
      | nil =>
          simp only [encRep] at hbs
          injection hbs with hbs
          subst bs
          refine ⟨br, ?_, by simp⟩
          simp [mergeLocalRun, encRep, hbr, catO]
      | cons s ss =>
          have hsok : LocalRunOK s := hrs s (by simp)
          cases s with
          | nil => contradiction
          | cons h hs =>
              simp only [mergeLocalRun]
              by_cases heq : l = h
              · subst h
                rw [if_pos rfl]
                obtain ⟨bhead, brest, hbhead, hbrest, hbseq⟩ := catO_eq hbs
                have hpair : ((l :: ls) ++ (l :: hs)).length < 2 ^ 32 := by
                  simp only [List.flatten_cons, List.length_append] at hlen ⊢
                  omega
                obtain ⟨bm, hbm, hmble⟩ := encLocalRun_append_completeLe hr hsok
                  hpair hbr hbhead
                refine ⟨bm ++ brest, catO_some hbm hbrest, ?_⟩
                subst bs
                simp only [List.length_append]
                omega
              · rw [if_neg heq]
                exact ⟨br ++ bs, catO_some hbr hbs, by simp⟩

theorem allLocalEq_replicate_self (l : Local) : ∀ n : Nat,
    allLocalEq l (List.replicate n l) = true
  | 0 => rfl
  | n + 1 => by
      simp [List.replicate_succ, allLocalEq, allLocalEq_replicate_self l n]

theorem encLocalRun_completeLe_of_nonempty {w : Bytes} {r : List Local}
    (h : Blocals w r) (hne : r ≠ []) (hlen : r.length < 2 ^ 32) :
    ∃ out, encLocalRun r = some out ∧ out.length ≤ w.length := by
  cases h with
  | mk bn bt n t hn ht =>
      have hn0 : n.val ≠ 0 := by
        intro hn0
        apply hne
        simp [hn0]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      obtain ⟨ov, hov, hlev⟩ := encValType_completeLe ht
      refine ⟨lebU n.val ++ ov, ?_, ?_⟩
      · have hlen' : (List.replicate n.val ({ valtype := t } : Local)).length <
            2 ^ 32 := hlen
        rw [hk] at hlen' ⊢
        simp only [List.replicate_succ, encLocalRun]
        have hlen'' : (({ valtype := t } : Local) ::
            List.replicate k { valtype := t }).length < 2 ^ 32 := by
          simpa only [List.replicate_succ] using hlen'
        rw [if_pos (allLocalEq_replicate_self _ _), if_pos hlen'', hov]
        simp only [catO, List.length_cons, List.length_replicate]
      · simp only [List.length_append]
        have hlu := lebU_minimal hn
        omega

theorem mergeLocalRun_length_le (r : List Local) (rss : List (List Local)) :
    (mergeLocalRun r rss).length ≤ rss.length + 1 := by
  cases r with
  | nil => simp [mergeLocalRun]
  | cons l ls =>
      cases rss with
      | nil => simp [mergeLocalRun]
      | cons s ss =>
          cases s with
          | nil => simp [mergeLocalRun]
          | cons h hs =>
              simp only [mergeLocalRun]
              split <;> simp

theorem encRep_localRuns_completeLe {n : Nat} {w : Bytes}
    {rss : List (List Local)} (h : Rep Blocals n w rss)
    (hlen : rss.flatten.length < 2 ^ 32) :
    ∃ out, encRep encLocalRun (localRuns rss.flatten) = some out ∧
      out.length ≤ w.length ∧ (localRuns rss.flatten).length ≤ rss.length := by
  induction h with
  | nil => exact ⟨[], rfl, by simp, by simp [localRuns]⟩
  | cons wb r wr rs k hr _ ih =>
      simp only [List.flatten_cons] at hlen ⊢
      have hrestlen : rs.flatten.length < 2 ^ 32 := by
        simp only [List.length_append] at hlen
        omega
      obtain ⟨orest, horest, hlrest, hcountrest⟩ := ih hrestlen
      by_cases hre : r = []
      · subst r
        refine ⟨orest, ?_, ?_, ?_⟩
        · simpa [localRuns] using horest
        · simp only [List.length_append]
          omega
        · simpa [Nat.add_comm] using
            Nat.le_trans hcountrest (Nat.le_add_left rs.length 1)
      · have hrunlen : r.length < 2 ^ 32 := by
          simp only [List.length_append] at hlen
          omega
        obtain ⟨orun, horun, hlrun⟩ := encLocalRun_completeLe_of_nonempty hr hre hrunlen
        have hrok : LocalRunOK r := by
          cases hr with
          | mk bn bt nu t hnu ht =>
              have hnu0 : nu.val ≠ 0 := by
                intro hzero
                apply hre
                simp [hzero]
              obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hnu0
              simp [LocalRunOK, hq, List.replicate_succ,
                allLocalEq_replicate_self]
        rw [localRuns_append_uniform r rs.flatten hrok]
        have hmergeLen : (r ++ (localRuns rs.flatten).flatten).length < 2 ^ 32 := by
          rw [localRuns_flatten]
          exact hlen
        obtain ⟨out, hout, houtle⟩ := encRep_mergeLocalRun_completeLe hrok
          (localRuns_ok rs.flatten) hmergeLen horun horest
        refine ⟨out, hout, ?_, ?_⟩
        · simp only [List.length_append]
          omega
        · exact Nat.le_trans (mergeLocalRun_length_le r (localRuns rs.flatten))
            (Nat.add_le_add_right hcountrest 1)

theorem encList_localRuns_completeLe {w : Bytes} {rss : List (List Local)}
    (h : Blist Blocals w rss) (hlen : rss.flatten.length < 2 ^ 32) :
    ∃ out, encList encLocalRun (localRuns rss.flatten) = some out ∧
      out.length ≤ w.length := by
  cases h with
  | mk bn body n rss hn hrep =>
      obtain ⟨obody, hobody, hlebody, hcountruns⟩ :=
        encRep_localRuns_completeLe hrep hlen
      have hcount : (localRuns rss.flatten).length < 2 ^ 32 := by
        have hrlen : rss.length = n.val := hrep.length
        have hnlt := n.property
        omega
      refine ⟨lebU (localRuns rss.flatten).length ++ obody, ?_, ?_⟩
      · simp [encList, hcount, hobody, catO]
      · have hrlen : rss.length = n.val := hrep.length
        have hmono := lebU_length_mono hcountruns
        have hmin := lebU_minimal hn
        rw [hrlen] at hmono
        simp only [List.length_append]
        omega

theorem encFuncBody_completeLe : CompleteLe encFuncBody Bfunc := by
  intro w c h
  cases h with
  | mk bl be locss e hloc he hguard =>
      obtain ⟨oloc, holoc, hleloc⟩ := encList_localRuns_completeLe hloc hguard
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      refine ⟨oloc ++ oe, ?_, ?_⟩
      · change (if locss.flatten.length < 2 ^ 32 then
          catO (encList encLocalRun (localRuns locss.flatten)) (encExpr e)
          else Option.none) = some (oloc ++ oe)
        rw [if_pos hguard]
        exact catO_some holoc hoe
      · simp only [List.length_append]
        omega

theorem encTable_completeLe : CompleteLe encTable Btable := by
  intro w t h
  cases h with
  | shorthand bs tt nul ht htt helem =>
      obtain ⟨ad, lim, elem⟩ := tt
      cases elem with
      | ref nul' ht' =>
          simp only [TableType.elem] at helem
          injection helem with hnul hht
          subst nul'; subst ht'
          obtain ⟨out, hout, hle⟩ := encTableType_completeLe htt
          exact ⟨out, by simpa [encTable] using hout, hle⟩
  | withInit bt be tt e htt he =>
      obtain ⟨ad, lim, elem⟩ := tt
      cases elem with
      | ref nul ht =>
          obtain ⟨ot, hot, hlet⟩ := encTableType_completeLe htt
          by_cases hinit : e = .cons (.refNull ht) .nil
          · subst e
            exact ⟨ot, by simp [encTable, hot], by simp; omega⟩
          · obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
            exact ⟨tb 0x40 :: tb 0x00 :: (ot ++ oe),
              by simp [encTable, hinit, hot, hoe, catO, consO], by simp; omega⟩

theorem encGlobal_completeLe : CompleteLe encGlobal Bglobal := by
  intro w g h
  cases h with
  | mk bg be gt e hgt he =>
      obtain ⟨og, hog, hleg⟩ := encGlobalType_completeLe hgt
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      exact ⟨og ++ oe, by simp [encGlobal, hog, hoe, catO], by simp; omega⟩

theorem encData_completeLe : CompleteLe encData Bdata := by
  intro w d h
  cases h with
  | activeZero bt be bb e bl x htag he hbl hx =>
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨ob, hob, hleb⟩ := encList_completeLe
        (f := encByte) (G := Bbyte) encByte_completeLe hbl
      have htagle : (lebU 0).length ≤ bt.length := by
        rcases htag with ⟨u, hu, huv⟩
        rw [← huv]
        exact lebU_minimal hu
      exact ⟨lebU 0 ++ oe ++ ob,
        by simp [encData, hx, hoe, hob, encByteList, catO], by simp; omega⟩
  | passive bt bb bl htag hbl =>
      obtain ⟨ob, hob, hleb⟩ := encList_completeLe
        (f := encByte) (G := Bbyte) encByte_completeLe hbl
      have htagle : (lebU 1).length ≤ bt.length := by
        rcases htag with ⟨u, hu, huv⟩
        rw [← huv]
        exact lebU_minimal hu
      exact ⟨lebU 1 ++ ob,
        by simp [encData, hob, encByteList, catO], by simp; omega⟩
  | active bt bx be bb x e bl htag hx he hbl =>
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨ob, hob, hleb⟩ := encList_completeLe
        (f := encByte) (G := Bbyte) encByte_completeLe hbl
      have htagle : (lebU 2).length ≤ bt.length := by
        rcases htag with ⟨u, hu, huv⟩
        rw [← huv]
        exact lebU_minimal hu
      by_cases hx0 : x.val = 0
      · exact ⟨lebU 0 ++ oe ++ ob,
          by simp [encData, hx0, hoe, hob, encByteList, catO], by
            have htag0 : (lebU 0).length ≤ bt.length := by
              exact Nat.le_trans (lebU_length_mono (by omega)) htagle
            simp only [List.length_append]
            omega⟩
      · obtain ⟨ox, hox, hlex⟩ := encIdx_completeLe hx
        have hxbytes : lebU x.val = ox := by simpa [encIdx] using hox
        rw [← hxbytes] at hlex
        exact ⟨lebU 2 ++ lebU x.val ++ oe ++ ob,
          by simp [encData, hx0, hoe, hob, encByteList, catO], by simp; omega⟩

theorem lebU_Bu32lit_minimal {k : Nat} {w : Bytes} (h : Bu32lit k w) :
    (lebU k).length ≤ w.length := by
  rcases h with ⟨u, hu, huv⟩
  rw [← huv]
  exact lebU_minimal hu

theorem funcIdxsOf_refFuncExprs : ∀ ys : List FuncIdx,
    funcIdxsOf (refFuncExprs ys) = some ys
  | [] => rfl
  | y :: ys => by
      change (match some y, funcIdxsOf (refFuncExprs ys) with
        | some z, some zs => some (z :: zs)
        | _, _ => Option.none) = some (y :: ys)
      rw [funcIdxsOf_refFuncExprs ys]

theorem encElem_completeLe : CompleteLe encElem Belem := by
  intro w e h
  cases h with
  | activeFuncrefZero bt be by' off ys x htag he hys hx =>
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨oy, hoy, hley⟩ := encList_completeLe
        (f := encIdx) (G := Bu32) encIdx_completeLe hys
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_left
      exact ⟨lebU 0 ++ oe ++ oy, by
        simp [encElemBase, hx, funcIdxsOf_refFuncExprs, hoe, hoy, catO], by simp; omega⟩
  | passiveFuncref bt bk by' rt ys htag hkind hys =>
      cases hkind
      obtain ⟨oy, hoy, hley⟩ := encList_completeLe
        (f := encIdx) (G := Bu32) encIdx_completeLe hys
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_right
      exact ⟨lebU 1 ++ [tb 0x00] ++ oy, by
        simp [encElemFunc, funcIdxsOf_refFuncExprs, hoy, catO], by simp; omega⟩
  | activeFuncref bt bx be bk by' x off rt ys htag hx he hkind hys =>
      cases hkind
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨oy, hoy, hley⟩ := encList_completeLe
        (f := encIdx) (G := Bu32) encIdx_completeLe hys
      have htagle := lebU_Bu32lit_minimal htag
      have hxle := lebU_minimal hx
      apply orO_lift_right
      exact ⟨lebU 2 ++ lebU x.val ++ oe ++ [tb 0x00] ++ oy, by
        simp [encElemFunc, funcIdxsOf_refFuncExprs, hoe, hoy, catO,
          List.append_assoc], by simp; omega⟩
  | declareFuncref bt bk by' rt ys htag hkind hys =>
      cases hkind
      obtain ⟨oy, hoy, hley⟩ := encList_completeLe
        (f := encIdx) (G := Bu32) encIdx_completeLe hys
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_right
      exact ⟨lebU 3 ++ [tb 0x00] ++ oy, by
        simp [encElemFunc, funcIdxsOf_refFuncExprs, hoy, catO], by simp; omega⟩
  | activeExprZero bt be bl off es x htag he hes hx =>
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨oes, hoes, hlees⟩ := encList_completeLe
        (f := encExpr) (G := Bexpr) encExpr_completeLe hes
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_left
      exact ⟨lebU 4 ++ oe ++ oes, by
        simp [encElemBase, hx, hoe, hoes, catO], by simp; omega⟩
  | passiveExpr bt br bl rt es htag hrt hes =>
      obtain ⟨ort, hort, hlert⟩ := encRefType_completeLe hrt
      obtain ⟨oes, hoes, hlees⟩ := encList_completeLe
        (f := encExpr) (G := Bexpr) encExpr_completeLe hes
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_left
      exact ⟨lebU 5 ++ ort ++ oes, by
        simp [encElemBase, hort, hoes, catO], by simp; omega⟩
  | activeExpr bt bx be bl x off es htag hx he hes =>
      obtain ⟨oe, hoe, hlee⟩ := encExpr_completeLe he
      obtain ⟨oes, hoes, hlees⟩ := encList_completeLe
        (f := encExpr) (G := Bexpr) encExpr_completeLe hes
      have htagle := lebU_Bu32lit_minimal htag
      by_cases hx0 : x.val = 0
      · apply orO_lift_left
        exact ⟨lebU 4 ++ oe ++ oes, by
          simp [encElemBase, hx0, hoe, hoes, catO], by
            have htag4 : (lebU 4).length ≤ bt.length :=
              Nat.le_trans (lebU_length_mono (by omega)) htagle
            simp only [List.length_append]
            omega⟩
      · have hxle := lebU_minimal hx
        apply orO_lift_left
        exact ⟨lebU 6 ++ lebU x.val ++ oe ++ oes, by
          simp [encElemBase, hx0, hoe, hoes, catO], by simp; omega⟩
  | declareExpr bt br bl rt es htag hrt hes =>
      obtain ⟨ort, hort, hlert⟩ := encRefType_completeLe hrt
      obtain ⟨oes, hoes, hlees⟩ := encList_completeLe
        (f := encExpr) (G := Bexpr) encExpr_completeLe hes
      have htagle := lebU_Bu32lit_minimal htag
      apply orO_lift_left
      exact ⟨lebU 7 ++ ort ++ oes, by
        simp [encElemBase, hort, hoes, catO], by simp; omega⟩

theorem encCode_completeLe : CompleteLe encCode Bcode := by
  intro w c h
  cases h with
  | mk blen body len c hlen hbody heq =>
      obtain ⟨payload, hpayload, hlepayload⟩ := encFuncBody_completeLe hbody
      have hbodylt : body.length < 2 ^ 32 := by
        rw [← heq]
        exact len.property
      have hpayloadlt : payload.length < 2 ^ 32 :=
        Nat.lt_of_le_of_lt hlepayload hbodylt
      have hlelen : (lebU payload.length).length ≤ blen.length := by
        have hmono := lebU_length_mono hlepayload
        have hmin := lebU_minimal hlen
        rw [heq] at hmin
        omega
      refine ⟨lebU payload.length ++ payload, ?_, ?_⟩
      · simp [encCode, hpayload, encSized, hpayloadlt]
      · simp only [List.length_append]
        omega

theorem Bsection_Blist_length_lt {α : Type} {G : Bytes → α → Prop}
    {N : Nat} {w : Bytes} {xs : List α} (h : Bsection N (Blist G) w xs) :
    xs.length < 2 ^ 32 := by
  cases h with
  | absent => simpa using (by decide : 0 < 2 ^ 32)
  | present blen body len xs hlen hbody heq =>
      cases hbody with
      | mk bn bs n xs hn hrep =>
          rw [hrep.length]
          exact n.property

theorem Bsection_Blist_leb_length_lt {α : Type} {G : Bytes → α → Prop}
    {N : Nat} {w : Bytes} {xs : List α} (h : Bsection N (Blist G) w xs) :
    (lebU xs.length).length < 2 ^ 32 := by
  cases h with
  | absent => simpa using (by decide : (lebU 0).length < 2 ^ 32)
  | present blen body len xs hlen hbody heq =>
      have hbodylt : body.length < 2 ^ 32 := by
        rw [← heq]
        exact len.property
      cases hbody with
      | mk bn bs n xs hn hrep =>
          have hcanon : (lebU xs.length).length ≤ bn.length := by
            rw [hrep.length]
            exact lebU_minimal hn
          simp only [List.length_append] at hbodylt
          omega

theorem encTableSec_complete {w : Bytes} {xs : List Table}
    (h : Btablesec w xs) : ∃ out, encTableSec xs = some out :=
  encListSection_complete (f := encTable) (G := Btable) encTable_completeLe h

theorem encGlobalSec_complete {w : Bytes} {xs : List Global}
    (h : Bglobalsec w xs) : ∃ out, encGlobalSec xs = some out :=
  encListSection_complete (f := encGlobal) (G := Bglobal) encGlobal_completeLe h

theorem encElemSec_complete {w : Bytes} {xs : List Elem}
    (h : Belemsec w xs) : ∃ out, encElemSec xs = some out :=
  encListSection_complete (f := encElem) (G := Belem) encElem_completeLe h

theorem encCodeSec_complete {w : Bytes} {xs : List Code}
    (h : Bcodesec w xs) : ∃ out, encCodeSec xs = some out :=
  encListSection_complete (f := encCode) (G := Bcode) encCode_completeLe h

theorem encDataSec_complete {w : Bytes} {xs : List Data}
    (h : Bdatasec w xs) : ∃ out, encDataSec xs = some out :=
  encListSection_complete (f := encData) (G := Bdata) encData_completeLe h

theorem encDataCntSec_complete {m : Module} {w : Bytes}
    (hdata : Bdatasec w m.datas) : ∃ out, encDataCntSec m = some out := by
  have hlen := Bsection_Blist_length_lt hdata
  have hleblen := Bsection_Blist_leb_length_lt hdata
  by_cases hneed : needsDataCnt m
  · exact ⟨tb 12 :: (lebU (lebU m.datas.length).length ++ lebU m.datas.length), by
      simp [encDataCntSec, hneed, hlen, encSectionBody, hleblen]⟩
  · exact ⟨[], by simp [encDataCntSec, hneed]⟩

theorem funcSplits_zip (xs : List TypeIdx) (cs : List Code)
    (hlen : xs.length = cs.length) :
    funcTypeIdxs (List.zipWith
      (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) xs cs) = xs ∧
    funcCodes (List.zipWith
      (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) xs cs) = cs := by
  induction xs generalizing cs with
  | nil =>
      cases cs with
      | nil => exact ⟨rfl, rfl⟩
      | cons c cs => simp at hlen
  | cons x xs ih =>
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have htail : xs.length = cs.length := by simp at hlen; exact hlen
          obtain ⟨h₁, h₂⟩ := ih cs htail
          have hp₁ : List.zipWith (fun (x : TypeIdx) (_ : Code) => x) xs cs = xs := by
            simpa [funcTypeIdxs] using h₁
          have hp₂ : List.zipWith (fun (_ : TypeIdx) (c : Code) => (c.1, c.2)) xs cs = cs := by
            simpa [funcCodes] using h₂
          exact ⟨by simp [funcTypeIdxs, hp₁], by simp [funcCodes, hp₂]⟩

theorem Bmodule_typesec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Btypesec bs m.types := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_importsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bimportsec bs m.imports := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_tablesec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Btablesec bs m.tables := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_memsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bmemsec bs m.mems := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_tagsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Btagsec bs m.tags := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_globalsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bglobalsec bs m.globals := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_exportsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bexportsec bs m.exports := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_startsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bstartsec bs m.start := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_elemsec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Belemsec bs m.elems := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_datasec_exists {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bs, Bdatasec bs m.datas := by cases h; exact ⟨_, by assumption⟩

theorem Bmodule_func_code_raw {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ (xs : List TypeIdx) (cs : List Code) (bfu bco : Bytes),
      Bfuncsec bfu xs ∧ Bcodesec bco cs ∧ xs.length = cs.length ∧
      m.funcs = List.zipWith
        (fun (x : TypeIdx) (c : Code) =>
          ({ typeidx := x, locals := c.1, body := c.2 } : Func)) xs cs := by
  cases h
  refine ⟨_, _, _, _, by assumption, by assumption, by assumption, by assumption⟩

theorem Bmodule_func_code_secs {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ bfu bco, Bfuncsec bfu (funcTypeIdxs m.funcs) ∧
      Bcodesec bco (funcCodes m.funcs) := by
  obtain ⟨xs, cs, bfu, bco, hfu, hco, hlen, hfuncs⟩ := Bmodule_func_code_raw h
  obtain ⟨hxs, hcs⟩ := funcSplits_zip xs cs hlen
  rw [hfuncs, hxs, hcs]
  exact ⟨bfu, bco, hfu, hco⟩

theorem encModule_complete {w : Bytes} {m : Module} (h : Bmodule w m) :
    ∃ out, encModule m = some out := by
  obtain ⟨_, hty⟩ := Bmodule_typesec_exists h
  obtain ⟨_, him⟩ := Bmodule_importsec_exists h
  obtain ⟨_, hta⟩ := Bmodule_tablesec_exists h
  obtain ⟨_, hme⟩ := Bmodule_memsec_exists h
  obtain ⟨_, htg⟩ := Bmodule_tagsec_exists h
  obtain ⟨_, hgl⟩ := Bmodule_globalsec_exists h
  obtain ⟨_, hex⟩ := Bmodule_exportsec_exists h
  obtain ⟨_, hst⟩ := Bmodule_startsec_exists h
  obtain ⟨_, hel⟩ := Bmodule_elemsec_exists h
  obtain ⟨_, hda⟩ := Bmodule_datasec_exists h
  obtain ⟨_, _, hfu, hco⟩ := Bmodule_func_code_secs h
  obtain ⟨oty, hoty⟩ := encTypeSec_complete hty
  obtain ⟨oim, hoim⟩ := encImportSec_complete him
  obtain ⟨ofu, hofu⟩ := encFuncSec_complete hfu
  obtain ⟨ota, hota⟩ := encTableSec_complete hta
  obtain ⟨ome, home⟩ := encMemSec_complete hme
  obtain ⟨otg, hotg⟩ := encTagSec_complete htg
  obtain ⟨ogl, hogl⟩ := encGlobalSec_complete hgl
  obtain ⟨oex, hoex⟩ := encExportSec_complete hex
  obtain ⟨ost, host⟩ := encStartSec_complete hst
  obtain ⟨oel, hoel⟩ := encElemSec_complete hel
  obtain ⟨odc, hodc⟩ := encDataCntSec_complete (m := m) hda
  obtain ⟨oco, hoco⟩ := encCodeSec_complete hco
  obtain ⟨oda, hoda⟩ := encDataSec_complete hda
  refine ⟨magicBytes ++ versionBytes ++ oty ++ oim ++ ofu ++ ota ++ ome ++ otg ++
    ogl ++ oex ++ ost ++ oel ++ odc ++ oco ++ oda, ?_⟩
  simp [encModule, hoty, hoim, hofu, hota, home, hotg, hogl, hoex, host,
    hoel, hodc, hoco, hoda, catO, List.append_assoc]

omit authority in
/-- Exact amended reverse completeness, with a constructive success witness. -/
theorem encModuleA_complete {w : Bytes} {m : Module} (h : BmoduleA w m) :
    ∃ out, encModuleA m = some out := by
  simpa [encModuleA] using
    (@encModule_complete amendedBinaryAuthority w m h)

omit authority in
/-- Every amended grammar derivation reaches the encoder's successful branch. -/
theorem BmoduleA_encodableA {w : Bytes} {m : Module} (h : BmoduleA w m) :
    encodableA m = true := by
  obtain ⟨out, hout⟩ := encModuleA_complete h
  simp [encodableA, hout]

omit authority in
/-- The total amended encoder is sound without a separately supplied success
premise whenever an amended grammar derivation is available. -/
theorem BmoduleA_encodeA_BmoduleA {w : Bytes} {m : Module} (h : BmoduleA w m) :
    BmoduleA (encodeBytesA m) m :=
  encodeA_BmoduleA m (BmoduleA_encodableA h)

end WasmGemmGnaf.Wasm.Core.Binary
