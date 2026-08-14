/-
  Wasm/Core/DecodeTypes.lean --- the executable decoder for
  `5.2-binary.types.spectec`, proved sound and complete against
  `Wasm/Core/BinaryGrammar/Types.lean`.

  Each production `Bxxx` of the grammar gets a parser `decXxx` with

      decXxx_sound    : Sound Bxxx decXxx
      decXxx_complete : Complete Bxxx decXxx

  and nothing else.  Where a production is a choice between alternatives that
  begin with different bytes, the decoder switches on the byte and the
  completeness proof discharges the choice by showing the OTHER alternatives
  cannot begin with that byte -- which is a fact about the pinned grammar, not
  an assumption about the decoder.  The one place this takes an argument is
  `Bheaptype` / `Bblocktype`, where the alternatives are an absolute heap type
  and a NON-NEGATIVE `Bs33`; `Bs33_head` below is the lemma that separates them.
-/
import WasmGemmGnaf.Wasm.Core.DecodeUtf8
import WasmGemmGnaf.Wasm.Core.DecodeParserAmended

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Number, vector and packed types -/

/-- `grammar Bnumtype`, as an opcode table. -/
def numtypeOf : Nat → Option NumType
  | 0x7C => some .f64
  | 0x7D => some .f32
  | 0x7E => some .i64
  | 0x7F => some .i32
  | _ => none

/-- `grammar Bnumtype : numtype`. -/
def decNumtype : Step NumType
  | [] => .error .eof
  | b :: r =>
      match numtypeOf b.val with
      | some t => .ok (t, r)
      | none => .error .opcode

theorem numtypeOf_lt {v : Nat} {t : NumType} (h : numtypeOf v = some t) : v < 0x100 := by
  unfold numtypeOf at h; split at h <;> first | omega | simp at h

theorem numtypeOf_sound {v : Nat} {t : NumType} (h : numtypeOf v = some t) :
    Bnumtype [tb v] t := by
  unfold numtypeOf at h
  split at h
  · cases h; exact Bnumtype.f64
  · cases h; exact Bnumtype.f32
  · cases h; exact Bnumtype.i64
  · cases h; exact Bnumtype.i32
  · simp at h

theorem decNumtype_sound : Sound Bnumtype decNumtype := by
  intro bs t r h
  cases bs with
  | nil => simp [decNumtype] at h
  | cons b bs =>
      rw [decNumtype] at h
      split at h
      · rename_i t' ht
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (numtypeOf_lt ht) rfl]
        exact numtypeOf_sound ht
      · simp at h

theorem decNumtype_complete : Complete Bnumtype decNumtype := by
  intro b t r h
  cases h <;> rfl

/-- `grammar Bvectype : vectype`. -/
def decVectype : Step VecType
  | [] => .error .eof
  | b :: r => if b.val = 0x7B then .ok (.v128, r) else .error .opcode

theorem decVectype_sound : Sound Bvectype decVectype := by
  intro bs t r h
  cases bs with
  | nil => simp [decVectype] at h
  | cons b bs =>
      rw [decVectype] at h
      split at h
      · rename_i hb
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (by decide) hb]
        exact Bvectype.v128
      · simp at h

theorem decVectype_complete : Complete Bvectype decVectype := by
  intro b t r h
  cases h <;> rfl

/-- `grammar Bpacktype`, as an opcode table. -/
def packtypeOf : Nat → Option PackType
  | 0x77 => some .i16
  | 0x78 => some .i8
  | _ => none

/-- `grammar Bpacktype : packtype`. -/
def decPacktype : Step PackType
  | [] => .error .eof
  | b :: r =>
      match packtypeOf b.val with
      | some t => .ok (t, r)
      | none => .error .opcode

theorem packtypeOf_lt {v : Nat} {t : PackType} (h : packtypeOf v = some t) : v < 0x100 := by
  unfold packtypeOf at h; split at h <;> first | omega | simp at h

theorem packtypeOf_sound {v : Nat} {t : PackType} (h : packtypeOf v = some t) :
    Bpacktype [tb v] t := by
  unfold packtypeOf at h
  split at h
  · cases h; exact Bpacktype.i16
  · cases h; exact Bpacktype.i8
  · simp at h

theorem decPacktype_sound : Sound Bpacktype decPacktype := by
  intro bs t r h
  cases bs with
  | nil => simp [decPacktype] at h
  | cons b bs =>
      rw [decPacktype] at h
      split at h
      · rename_i t' ht
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (packtypeOf_lt ht) rfl]
        exact packtypeOf_sound ht
      · simp at h

theorem decPacktype_complete : Complete Bpacktype decPacktype := by
  intro b t r h
  cases h <;> rfl

/-! ## Heap types

`Babsheaptype` occupies `0x69` .. `0x74`; the other alternative of `Bheaptype`
is a `Bs33` constrained to be non-negative, whose first byte is therefore below
`0x40` or at least `0x80`.  The two ranges are disjoint, and `Bs33_head` is what
says so. -/

/-- `grammar Babsheaptype`, as an opcode table. -/
def absheaptypeOf : Nat → Option HeapType
  | 0x69 => some (.abs .exn)
  | 0x6A => some (.abs .array)
  | 0x6B => some (.abs .struct)
  | 0x6C => some (.abs .i31)
  | 0x6D => some (.abs .eq)
  | 0x6E => some (.abs .any)
  | 0x6F => some (.abs .extern)
  | 0x70 => some (.abs .func)
  | 0x71 => some (.abs .none)
  | 0x72 => some (.abs .noextern)
  | 0x73 => some (.abs .nofunc)
  | 0x74 => some (.abs .noexn)
  | _ => none

theorem absheaptypeOf_lt {v : Nat} {ht : HeapType} (h : absheaptypeOf v = some ht) :
    v < 0x100 := by
  unfold absheaptypeOf at h; split at h <;> first | omega | simp at h

theorem absheaptypeOf_range {v : Nat} {ht : HeapType} (h : absheaptypeOf v = some ht) :
    0x40 ≤ v ∧ v < 0x80 := by
  unfold absheaptypeOf at h; split at h <;> first | omega | simp at h

theorem absheaptypeOf_sound {v : Nat} {ht : HeapType} (h : absheaptypeOf v = some ht) :
    Babsheaptype [tb v] ht := by
  unfold absheaptypeOf at h
  split at h
  · cases h; exact Babsheaptype.exn
  · cases h; exact Babsheaptype.array
  · cases h; exact Babsheaptype.struct
  · cases h; exact Babsheaptype.i31
  · cases h; exact Babsheaptype.eq
  · cases h; exact Babsheaptype.any
  · cases h; exact Babsheaptype.extern
  · cases h; exact Babsheaptype.func
  · cases h; exact Babsheaptype.none
  · cases h; exact Babsheaptype.noextern
  · cases h; exact Babsheaptype.nofunc
  · cases h; exact Babsheaptype.noexn
  · simp at h

/-- `grammar Babsheaptype : heaptype`. -/
def decAbsheaptype : Step HeapType
  | [] => .error .eof
  | b :: r =>
      match absheaptypeOf b.val with
      | some ht => .ok (ht, r)
      | none => .error .opcode

theorem decAbsheaptype_sound : Sound Babsheaptype decAbsheaptype := by
  intro bs ht r h
  cases bs with
  | nil => simp [decAbsheaptype] at h
  | cons b bs =>
      rw [decAbsheaptype] at h
      split at h
      · rename_i ht' hht
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (absheaptypeOf_lt hht) rfl]
        exact absheaptypeOf_sound hht
      · simp at h

theorem decAbsheaptype_complete : Complete Babsheaptype decAbsheaptype := by
  intro b ht r h
  cases h <;> rfl

/-- A non-negative `Bs33` begins with a byte below `0x40` or at least `0x80`.
This is the fact that separates the two alternatives of `Bheaptype` and the
three of `Bblocktype`; without it a decoder would have to guess. -/
theorem Bs33_head {bs : Bytes} {i : Int} (h : Bs33 bs i) (hi : 0 ≤ i) :
    ∃ b t, bs = b :: t ∧ (b.val < 0x40 ∨ 0x80 ≤ b.val) := by
  cases h with
  | pos n h1 h2 => exact ⟨n, [], rfl, Or.inl (by omega)⟩
  | neg n h1 h2 h3 =>
      exfalso
      have : (n.val : Int) - (2 : Int) ^ 7 < 0 := by
        have : (n.val : Int) < (2 : Int) ^ 7 := by exact_mod_cast h2
        omega
      omega
  | more n bs i h1 h2 h3 => exact ⟨n, bs, rfl, Or.inr (by omega)⟩

theorem Bs33'_head {bs : Bytes} {i : Int} (h : Bs33' bs i) (hi : 0 ≤ i) :
    ∃ b t, bs = b :: t ∧ (b.val < 0x40 ∨ 0x80 ≤ b.val) := by
  cases h
  case pos n h1 h2 => exact ⟨n, [], rfl, Or.inl (by omega)⟩
  case neg n h1 h2 h3 =>
    exfalso
    have : (n.val : Int) - (2 : Int) ^ 7 < 0 := by
      have : (n.val : Int) < (2 : Int) ^ 7 := by exact_mod_cast h2
      omega
    omega
  case more n bs i h1 h2 h3 => exact ⟨n, bs, rfl, Or.inr (by omega)⟩

theorem Bs33For_head [authority : BinaryAuthority]
    {bs : Bytes} {i : Int} (h : Bs33For bs i) (hi : 0 ≤ i) :
    ∃ b t, bs = b :: t ∧ (b.val < 0x40 ∨ 0x80 ≤ b.val) := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact Bs33_head h hi
      | amended => exact Bs33'_head h hi

/-- The `_IDX` alternative of `Bheaptype` and of `Bblocktype`. -/
def decS33Idx [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (TypeIdx × Bytes) :=
  match decS33For bs with
  | .error e => .error e
  | .ok (i, r) =>
      if h : 0 ≤ i ∧ i.toNat < 2 ^ 32 then .ok (⟨i.toNat, h.2⟩, r) else .error .range

theorem decS33Idx_sound [authority : BinaryAuthority]
    {bs : Bytes} {x : TypeIdx} {r : Bytes}
    (h : decS33Idx bs = .ok (x, r)) :
    ∃ b i, bs = b ++ r ∧ Bs33For b i ∧ 0 ≤ i ∧ (x.val : Int) = i := by
  rw [decS33Idx] at h
  split at h
  · simp at h
  · rename_i i r' hi
    split at h
    · rename_i hcond
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b, hb, hd⟩ := decS33For_sound bs i r' hi
      refine ⟨b, i, by rw [hb, h2], hd, hcond.1, ?_⟩
      rw [← h1]
      exact Int.toNat_of_nonneg hcond.1
    · simp at h

theorem decS33Idx_complete [authority : BinaryAuthority]
    {b : Bytes} {i : Int} {x : TypeIdx} (r : Bytes)
    (hd : Bs33For b i) (hi : 0 ≤ i) (hx : (x.val : Int) = i) :
    decS33Idx (b ++ r) = .ok (x, r) := by
  have hnat : i.toNat = x.val := by omega
  have hcond : 0 ≤ i ∧ i.toNat < 2 ^ 32 := ⟨hi, by rw [hnat]; exact x.property⟩
  rw [decS33Idx, decS33For_complete b i r hd]
  show (if h : 0 ≤ i ∧ i.toNat < 2 ^ 32 then
          Except.ok ((⟨i.toNat, h.2⟩ : TypeIdx), r) else Except.error Fault.range)
        = Except.ok (x, r)
  rw [dif_pos hcond]
  have hx2 : (⟨i.toNat, hcond.2⟩ : TypeIdx) = x := Subtype.ext hnat
  rw [hx2]

/-- `grammar Bheaptype : heaptype`. -/
def decHeaptype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (HeapType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val < 0x40 ∨ 0x80 ≤ b.val then
        (match decS33Idx bs with
         | .error e => .error e
         | .ok (x, r') => .ok (.use (.idx x), r'))
      else
        (match absheaptypeOf b.val with
         | some ht => .ok (ht, r)
         | none => .error .opcode)

theorem decHeaptype_sound [authority : BinaryAuthority] : Sound Bheaptype decHeaptype := by
  intro bs ht r h
  cases bs with
  | nil => simp [decHeaptype] at h
  | cons b bs =>
      rw [decHeaptype] at h
      split at h
      · split at h
        · simp at h
        · rename_i x r' hx
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, i, hbb, hs, hnn, hval⟩ := decS33Idx_sound hx
          exact ⟨bb, by rw [hbb, h2], by rw [← h1]; exact Bheaptype.idx bb i x hs hnn hval⟩
      · split at h
        · rename_i ht' hht
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          refine ⟨[b], by rw [← h2]; rfl, ?_⟩
          rw [← h1, byte_eq_tb (absheaptypeOf_lt hht) rfl]
          exact Bheaptype.abs _ _ (absheaptypeOf_sound hht)
        · simp at h

theorem decHeaptype_complete [authority : BinaryAuthority] : Complete Bheaptype decHeaptype := by
  intro b ht r h
  cases h with
  | abs _ht habs =>
      cases habs <;> rfl
  | idx i x hs hnn hval =>
      obtain ⟨b0, t0, hb0, hrange⟩ := Bs33For_head hs hnn
      subst hb0
      show decHeaptype (b0 :: (t0 ++ r)) = _
      rw [decHeaptype, if_pos hrange]
      show (match decS33Idx ((b0 :: t0) ++ r) with
            | Except.error e => Except.error e
            | Except.ok (x, r') => Except.ok (HeapType.use (.idx x), r'))
          = Except.ok (HeapType.use (.idx x), r)
      simp only [decS33Idx_complete r hs hnn hval]

/-! ## Reference and value types -/

/-- `grammar Breftype : reftype`. -/
def decReftype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (RefType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x63 then
        (match decHeaptype r with
         | .error e => .error e
         | .ok (ht, r') => .ok (.ref (some .null) ht, r'))
      else if b.val = 0x64 then
        (match decHeaptype r with
         | .error e => .error e
         | .ok (ht, r') => .ok (.ref none ht, r'))
      else
        (match absheaptypeOf b.val with
         | some ht => .ok (.ref (some .null) ht, r)
         | none => .error .opcode)

theorem decReftype_sound [authority : BinaryAuthority] : Sound Breftype decReftype := by
  intro bs rt r h
  cases bs with
  | nil => simp [decReftype] at h
  | cons b bs =>
      rw [decReftype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i ht r' hht
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decHeaptype_sound bs ht r' hht
          refine ⟨b :: bb, by rw [hbb, h2]; rfl, ?_⟩
          rw [← h1, byte_eq_tb (by decide) hb]
          exact Breftype.null bb ht hd
      · rename_i hb
        split at h
        · rename_i hb'
          split at h
          · simp at h
          · rename_i ht r' hht
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decHeaptype_sound bs ht r' hht
            refine ⟨b :: bb, by rw [hbb, h2]; rfl, ?_⟩
            rw [← h1, byte_eq_tb (by decide) hb']
            exact Breftype.nonNull bb ht hd
        · split at h
          · rename_i ht hht
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
            refine ⟨[b], by rw [← h2]; rfl, ?_⟩
            rw [← h1, byte_eq_tb (absheaptypeOf_lt hht) rfl]
            exact Breftype.abs _ _ (absheaptypeOf_sound hht)
          · simp at h

theorem decReftype_complete [authority : BinaryAuthority] : Complete Breftype decReftype := by
  intro b rt r h
  cases h with
  | null bs ht hd =>
      show decReftype (tb 0x63 :: (bs ++ r)) = _
      simp [decReftype, tb, Byte.ofNat, decHeaptype_complete bs ht r hd]
  | nonNull bs ht hd =>
      show decReftype (tb 0x64 :: (bs ++ r)) = _
      simp [decReftype, tb, Byte.ofNat, decHeaptype_complete bs ht r hd]
  | abs _bs ht hd => cases hd <;> rfl

/-- `grammar Bvaltype : valtype`. -/
def decValtype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (ValType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      match numtypeOf b.val with
      | some nt => .ok (.num nt, r)
      | none =>
          if b.val = 0x7B then .ok (.vec .v128, r)
          else
            (match decReftype (b :: r) with
             | .error e => .error e
             | .ok (rt, r') => .ok (.ref rt, r'))

theorem decValtype_sound [authority : BinaryAuthority] : Sound Bvaltype decValtype := by
  intro bs t r h
  cases bs with
  | nil => simp [decValtype] at h
  | cons b bs =>
      rw [decValtype] at h
      split at h
      · rename_i nt hnt
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (numtypeOf_lt hnt) rfl]
        exact Bvaltype.num _ _ (numtypeOf_sound hnt)
      · split at h
        · rename_i hb
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          refine ⟨[b], by rw [← h2]; rfl, ?_⟩
          rw [← h1, byte_eq_tb (by decide) hb]
          exact Bvaltype.vec _ _ Bvectype.v128
        · split at h
          · simp at h
          · rename_i rt r' hrt
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decReftype_sound (b :: bs) rt r' hrt
            exact ⟨bb, by rw [hbb, h2], by rw [← h1]; exact Bvaltype.ref bb rt hd⟩

theorem decValtype_complete [authority : BinaryAuthority] : Complete Bvaltype decValtype := by
  intro b t r h
  have key : ∀ (b0 : Bytes) (rt : RefType), Breftype b0 rt →
      decValtype (b0 ++ r) = .ok (.ref rt, r) := by
    intro b0 rt hr
    have hhead : ∃ v t, b0 = v :: t ∧ numtypeOf v.val = none ∧ ¬ (v.val = 0x7B) := by
      cases hr with
      | null bs ht _ => exact ⟨tb 0x63, bs, rfl, by decide, by decide⟩
      | nonNull bs ht _ => exact ⟨tb 0x64, bs, rfl, by decide, by decide⟩
      | abs _bs ht ha => cases ha <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)
    obtain ⟨v, t, hb0, hnum, hvb⟩ := hhead
    subst hb0
    show decValtype (v :: (t ++ r)) = _
    have hstep : decReftype (v :: (t ++ r)) = .ok (rt, r) :=
      decReftype_complete (v :: t) rt r hr
    rw [decValtype, hnum, if_neg hvb]
    simp only [hstep]
  cases h with
  | num nt hd => cases hd <;> rfl
  | vec vt hd => cases hd <;> rfl
  | ref rt hd => exact key b rt hd

/-- `grammar Bresulttype : resulttype`. -/
def decResulttype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (ValTypes × Bytes) :=
  match decList decValtype bs with
  | .error e => .error e
  | .ok (ts, r) => .ok (ValTypes.ofList ts, r)

theorem decResulttype_sound [authority : BinaryAuthority] : Sound Bresulttype decResulttype := by
  intro bs ts r h
  rw [decResulttype] at h
  split at h
  · simp at h
  · rename_i l r' hl
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decList_sound decValtype_sound bs l r' hl
    refine ⟨b, by rw [hb, h2], ?_⟩
    show Blist Bvaltype b ts.toList
    rw [← h1, ValTypes.toList_ofList]
    exact hd

theorem decResulttype_complete [authority : BinaryAuthority] : Complete Bresulttype decResulttype := by
  intro b ts r h
  simp only [decResulttype, decList_complete decValtype_complete b ts.toList r h,
    ValTypes.ofList_toList]

/-! ## Mutability, storage and field types -/

/-- `grammar Bmut : mut?`. -/
def decMut : Step (Option Mut)
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then .ok (none, r)
      else if b.val = 0x01 then .ok (some .mut, r)
      else .error .opcode

theorem decMut_sound : Sound Bmut decMut := by
  intro bs m r h
  cases bs with
  | nil => simp [decMut] at h
  | cons b bs =>
      rw [decMut] at h
      split at h
      · rename_i hb
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (by decide) hb]
        exact Bmut.const
      · split at h
        · rename_i hb
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          refine ⟨[b], by rw [← h2]; rfl, ?_⟩
          rw [← h1, byte_eq_tb (by decide) hb]
          exact Bmut.mutable
        · simp at h

theorem decMut_complete : Complete Bmut decMut := by
  intro b m r h
  cases h <;> rfl

/-- `grammar Bstoragetype : storagetype`. -/
def decStoragetype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (StorageType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      match packtypeOf b.val with
      | some pt => .ok (.pack pt, r)
      | none =>
          (match decValtype (b :: r) with
           | .error e => .error e
           | .ok (t, r') => .ok (.val t, r'))

theorem decStoragetype_sound [authority : BinaryAuthority] : Sound Bstoragetype decStoragetype := by
  intro bs zt r h
  cases bs with
  | nil => simp [decStoragetype] at h
  | cons b bs =>
      rw [decStoragetype] at h
      split at h
      · rename_i pt hpt
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← h2]; rfl, ?_⟩
        rw [← h1, byte_eq_tb (packtypeOf_lt hpt) rfl]
        exact Bstoragetype.pack _ _ (packtypeOf_sound hpt)
      · split at h
        · simp at h
        · rename_i t r' ht
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decValtype_sound (b :: bs) t r' ht
          exact ⟨bb, by rw [hbb, h2], by rw [← h1]; exact Bstoragetype.val bb t hd⟩

theorem decStoragetype_complete [authority : BinaryAuthority] : Complete Bstoragetype decStoragetype := by
  intro b zt r h
  cases h with
  | pack pt hd => cases hd <;> rfl
  | val t hd =>
      have hhead : ∃ v u, b = v :: u ∧ packtypeOf v.val = none := by
        cases hd with
        | num nt hn => cases hn <;> (refine ⟨_, [], rfl, ?_⟩ <;> decide)
        | vec vt hv => cases hv <;> (refine ⟨_, [], rfl, ?_⟩ <;> decide)
        | ref rt hr =>
            cases hr with
            | null bs ht _ => exact ⟨tb 0x63, bs, rfl, by decide⟩
            | nonNull bs ht _ => exact ⟨tb 0x64, bs, rfl, by decide⟩
            | abs _bs ht ha => cases ha <;> (refine ⟨_, [], rfl, ?_⟩ <;> decide)
      obtain ⟨v, u, hb, hpk⟩ := hhead
      subst hb
      show decStoragetype (v :: (u ++ r)) = _
      have hstep : decValtype (v :: (u ++ r)) = .ok (t, r) :=
        decValtype_complete (v :: u) t r hd
      rw [decStoragetype, hpk]
      simp only [hstep]

/-- `grammar Bfieldtype : fieldtype`. -/
def decFieldtype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (FieldType × Bytes) :=
  match decStoragetype bs with
  | .error e => .error e
  | .ok (zt, r) =>
      match decMut r with
      | .error e => .error e
      | .ok (mo, r') => .ok (.mk mo zt, r')

theorem decFieldtype_sound [authority : BinaryAuthority] : Sound Bfieldtype decFieldtype := by
  intro bs ft r h
  rw [decFieldtype] at h
  split at h
  · simp at h
  · rename_i zt r1 hz
    split at h
    · simp at h
    · rename_i mo r2 hm
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b1, hb1, hd1⟩ := decStoragetype_sound bs zt r1 hz
      obtain ⟨b2, hb2, hd2⟩ := decMut_sound r1 mo r2 hm
      refine ⟨b1 ++ b2, by rw [hb1, hb2, h2, List.append_assoc], ?_⟩
      rw [← h1]
      exact Bfieldtype.mk b1 b2 zt mo hd1 hd2

theorem decFieldtype_complete [authority : BinaryAuthority] : Complete Bfieldtype decFieldtype := by
  intro b ft r h
  cases h with
  | mk bz bm zt mo hz hm =>
      rw [List.append_assoc]
      simp [decFieldtype, decStoragetype_complete bz zt (bm ++ r) hz,
        decMut_complete bm mo r hm]

/-! ## Composite, sub and recursive types -/

/-- `grammar Bcomptype : comptype`. -/
def decComptype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (CompType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x5E then
        (match decFieldtype r with
         | .error e => .error e
         | .ok (ft, r') => .ok (.array ft, r'))
      else if b.val = 0x5F then
        (match decList decFieldtype r with
         | .error e => .error e
         | .ok (fts, r') => .ok (.struct (FieldTypes.ofList fts), r'))
      else if b.val = 0x60 then
        (match decResulttype r with
         | .error e => .error e
         | .ok (t₁, r₁) =>
             match decResulttype r₁ with
             | .error e => .error e
             | .ok (t₂, r₂) => .ok (.func t₁ t₂, r₂))
      else .error .opcode

theorem decComptype_sound [authority : BinaryAuthority] : Sound Bcomptype decComptype := by
  intro bs ct r h
  cases bs with
  | nil => simp [decComptype] at h
  | cons b bs =>
      rw [decComptype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i ft r' hft
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decFieldtype_sound bs ft r' hft
          refine ⟨b :: bb, by rw [hbb, h2]; rfl, ?_⟩
          rw [← h1, byte_eq_tb (by decide) hb]
          exact Bcomptype.array bb ft hd
      · split at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i fts r' hfts
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decList_sound decFieldtype_sound bs fts r' hfts
            refine ⟨b :: bb, by rw [hbb, h2]; rfl, ?_⟩
            rw [← h1, byte_eq_tb (by decide) hb]
            refine Bcomptype.struct bb (FieldTypes.ofList fts) ?_
            rw [FieldTypes.toList_ofList]
            exact hd
        · split at h
          · rename_i hb
            split at h
            · simp at h
            · rename_i t₁ r₁ h₁
              split at h
              · simp at h
              · rename_i t₂ r₂ h₂
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                obtain ⟨b₁, hb₁, hd₁⟩ := decResulttype_sound bs t₁ r₁ h₁
                obtain ⟨b₂, hb₂, hd₂⟩ := decResulttype_sound r₁ t₂ r₂ h₂
                refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
                rw [← hv, byte_eq_tb (by decide) hb]
                exact Bcomptype.func b₁ b₂ t₁ t₂ hd₁ hd₂
          · simp at h

theorem decComptype_complete [authority : BinaryAuthority] : Complete Bcomptype decComptype := by
  intro b ct r h
  cases h with
  | array bs ft hd =>
      show decComptype (tb 0x5E :: (bs ++ r)) = _
      simp [decComptype, tb, Byte.ofNat, decFieldtype_complete bs ft r hd]
  | struct bs fts hd =>
      show decComptype (tb 0x5F :: (bs ++ r)) = _
      simp [decComptype, tb, Byte.ofNat,
        decList_complete decFieldtype_complete bs fts.toList r hd,
        FieldTypes.ofList_toList]
  | func b₁ b₂ t₁ t₂ hd₁ hd₂ =>
      show decComptype (tb 0x60 :: ((b₁ ++ b₂) ++ r)) = _
      rw [List.append_assoc]
      simp [decComptype, tb, Byte.ofNat,
        decResulttype_complete b₁ t₁ (b₂ ++ r) hd₁,
        decResulttype_complete b₂ t₂ r hd₂]

/-- `grammar Bsubtype : subtype`. -/
def decSubtype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (SubType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x4F then
        (match decList decIdx r with
         | .error e => .error e
         | .ok (xs, r₁) =>
             match decComptype r₁ with
             | .error e => .error e
             | .ok (ct, r₂) =>
                 .ok (.sub (some .final) (TypeUses.ofList (xs.map TypeUse.idx)) ct, r₂))
      else if b.val = 0x50 then
        (match decList decIdx r with
         | .error e => .error e
         | .ok (xs, r₁) =>
             match decComptype r₁ with
             | .error e => .error e
             | .ok (ct, r₂) =>
                 .ok (.sub none (TypeUses.ofList (xs.map TypeUse.idx)) ct, r₂))
      else
        (match decComptype (b :: r) with
         | .error e => .error e
         | .ok (ct, r') => .ok (.sub (some .final) .nil ct, r'))

theorem decSubtype_sound [authority : BinaryAuthority] : Sound Bsubtype decSubtype := by
  intro bs st r h
  cases bs with
  | nil => simp [decSubtype] at h
  | cons b bs =>
      rw [decSubtype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i xs r₁ h₁
          split at h
          · simp at h
          · rename_i ct r₂ h₂
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨b₁, hb₁, hd₁⟩ := decList_sound decIdx_sound bs xs r₁ h₁
            obtain ⟨b₂, hb₂, hd₂⟩ := decComptype_sound r₁ ct r₂ h₂
            refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
            rw [← hv, byte_eq_tb (by decide) hb]
            exact Bsubtype.finalSub b₁ b₂ xs (TypeUses.ofList (xs.map TypeUse.idx)) ct
              hd₁ hd₂ (TypeUses.toList_ofList _)
      · split at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i xs r₁ h₁
            split at h
            · simp at h
            · rename_i ct r₂ h₂
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨b₁, hb₁, hd₁⟩ := decList_sound decIdx_sound bs xs r₁ h₁
              obtain ⟨b₂, hb₂, hd₂⟩ := decComptype_sound r₁ ct r₂ h₂
              refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Bsubtype.openSub b₁ b₂ xs (TypeUses.ofList (xs.map TypeUse.idx)) ct
                hd₁ hd₂ (TypeUses.toList_ofList _)
        · split at h
          · simp at h
          · rename_i ct r' hct
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decComptype_sound (b :: bs) ct r' hct
            exact ⟨bb, by rw [hbb, hr], by rw [← hv]; exact Bsubtype.bare bb ct hd⟩

/-- The first byte of a `Bcomptype` is `0x5E`, `0x5F` or `0x60`, so the `bare`
alternative of `Bsubtype` never collides with `0x4F` or `0x50`. -/
theorem Bcomptype_head [authority : BinaryAuthority]
    {bs : Bytes} {ct : CompType} (h : Bcomptype bs ct) :
    ∃ b t, bs = b :: t ∧ (b.val = 0x5E ∨ b.val = 0x5F ∨ b.val = 0x60) := by
  cases h with
  | array bb ft _ => exact ⟨tb 0x5E, bb, rfl, Or.inl (by decide)⟩
  | struct bb fts _ => exact ⟨tb 0x5F, bb, rfl, Or.inr (Or.inl (by decide))⟩
  | func b₁ b₂ t₁ t₂ _ _ =>
      exact ⟨tb 0x60, b₁ ++ b₂, rfl, Or.inr (Or.inr (by decide))⟩

theorem decSubtype_complete [authority : BinaryAuthority] : Complete Bsubtype decSubtype := by
  intro b st r h
  cases h with
  | finalSub bx bc xs tus ct hx hc htus =>
      show decSubtype (tb 0x4F :: ((bx ++ bc) ++ r)) = _
      have htus' : TypeUses.ofList (xs.map TypeUse.idx) = tus := by
        rw [← htus, TypeUses.ofList_toList]
      rw [List.append_assoc]
      simp [decSubtype, tb, Byte.ofNat,
        decList_complete decIdx_complete bx xs (bc ++ r) hx,
        decComptype_complete bc ct r hc, htus']
  | openSub bx bc xs tus ct hx hc htus =>
      show decSubtype (tb 0x50 :: ((bx ++ bc) ++ r)) = _
      have htus' : TypeUses.ofList (xs.map TypeUse.idx) = tus := by
        rw [← htus, TypeUses.ofList_toList]
      rw [List.append_assoc]
      simp [decSubtype, tb, Byte.ofNat,
        decList_complete decIdx_complete bx xs (bc ++ r) hx,
        decComptype_complete bc ct r hc, htus']
  | bare _bc ct hc =>
      obtain ⟨b0, t0, hb0, hrange⟩ := Bcomptype_head hc
      subst hb0
      show decSubtype (b0 :: (t0 ++ r)) = _
      have h1 : ¬ (b0.val = 0x4F) := by omega
      have h2 : ¬ (b0.val = 0x50) := by omega
      have hstep : decComptype (b0 :: (t0 ++ r)) = .ok (ct, r) :=
        decComptype_complete (b0 :: t0) ct r hc
      rw [decSubtype, if_neg h1, if_neg h2]
      simp only [hstep]

/-- `grammar Brectype : rectype`. -/
def decRectype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (RecType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x4E then
        (match decList decSubtype r with
         | .error e => .error e
         | .ok (sts, r') => .ok (.recr (SubTypes.ofList sts), r'))
      else
        (match decSubtype (b :: r) with
         | .error e => .error e
         | .ok (st, r') => .ok (.recr (.cons st .nil), r'))

theorem decRectype_sound [authority : BinaryAuthority] : Sound Brectype decRectype := by
  intro bs qt r h
  cases bs with
  | nil => simp [decRectype] at h
  | cons b bs =>
      rw [decRectype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i sts r' hsts
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decList_sound decSubtype_sound bs sts r' hsts
          refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
          rw [← hv, byte_eq_tb (by decide) hb]
          refine Brectype.recGroup bb (SubTypes.ofList sts) ?_
          rw [SubTypes.toList_ofList]
          exact hd
      · split at h
        · simp at h
        · rename_i st r' hst
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decSubtype_sound (b :: bs) st r' hst
          exact ⟨bb, by rw [hbb, hr], by rw [← hv]; exact Brectype.single bb st hd⟩

/-- The first byte of a `Bsubtype` is `0x4F`, `0x50`, `0x5E`, `0x5F` or `0x60`,
never `0x4E`, so the `single` alternative of `Brectype` never collides. -/
theorem Bsubtype_head [authority : BinaryAuthority]
    {bs : Bytes} {st : SubType} (h : Bsubtype bs st) :
    ∃ b t, bs = b :: t ∧ b.val ≠ 0x4E := by
  cases h with
  | finalSub bx bc _ _ _ _ _ => exact ⟨tb 0x4F, bx ++ bc, rfl, by decide⟩
  | openSub bx bc _ _ _ _ _ => exact ⟨tb 0x50, bx ++ bc, rfl, by decide⟩
  | bare _bc ct hc =>
      obtain ⟨b0, t0, hb0, hrange⟩ := Bcomptype_head hc
      exact ⟨b0, t0, hb0, by omega⟩

theorem decRectype_complete [authority : BinaryAuthority] : Complete Brectype decRectype := by
  intro b qt r h
  cases h with
  | recGroup bs sts hd =>
      show decRectype (tb 0x4E :: (bs ++ r)) = _
      simp [decRectype, tb, Byte.ofNat,
        decList_complete decSubtype_complete bs sts.toList r hd, SubTypes.ofList_toList]
  | single _bs st hd =>
      obtain ⟨b0, t0, hb0, hne⟩ := Bsubtype_head hd
      subst hb0
      show decRectype (b0 :: (t0 ++ r)) = _
      have hstep : decSubtype (b0 :: (t0 ++ r)) = .ok (st, r) :=
        decSubtype_complete (b0 :: t0) st r hd
      rw [decRectype, if_neg hne]
      simp only [hstep]

/-! ## External types -/

/-- `grammar Blimits : (addrtype, limits)`. -/
def decLimits (bs : Bytes) : Except Fault ((AddrType × Limits) × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then
        (match decU64 r with
         | .error e => .error e
         | .ok (n, r') => .ok ((.i32, { min := n, max := none }), r'))
      else if b.val = 0x01 then
        (match decU64 r with
         | .error e => .error e
         | .ok (n, r₁) =>
             match decU64 r₁ with
             | .error e => .error e
             | .ok (m, r₂) => .ok ((.i32, { min := n, max := some m }), r₂))
      else if b.val = 0x04 then
        (match decU64 r with
         | .error e => .error e
         | .ok (n, r') => .ok ((.i64, { min := n, max := none }), r'))
      else if b.val = 0x05 then
        (match decU64 r with
         | .error e => .error e
         | .ok (n, r₁) =>
             match decU64 r₁ with
             | .error e => .error e
             | .ok (m, r₂) => .ok ((.i64, { min := n, max := some m }), r₂))
      else .error .opcode

theorem decLimits_sound : Sound Blimits decLimits := by
  intro bs al r h
  cases bs with
  | nil => simp [decLimits] at h
  | cons b bs =>
      rw [decLimits] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i n r' hn
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decU64_sound bs n r' hn
          refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
          rw [← hv, byte_eq_tb (by decide) hb]
          exact Blimits.i32Min bb n hd
      · split at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i n r₁ hn
            split at h
            · simp at h
            · rename_i m r₂ hm
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨b₁, hb₁, hd₁⟩ := decU64_sound bs n r₁ hn
              obtain ⟨b₂, hb₂, hd₂⟩ := decU64_sound r₁ m r₂ hm
              refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Blimits.i32MinMax b₁ b₂ n m hd₁ hd₂
        · split at h
          · rename_i hb
            split at h
            · simp at h
            · rename_i n r' hn
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨bb, hbb, hd⟩ := decU64_sound bs n r' hn
              refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Blimits.i64Min bb n hd
          · split at h
            · rename_i hb
              split at h
              · simp at h
              · rename_i n r₁ hn
                split at h
                · simp at h
                · rename_i m r₂ hm
                  obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨b₁, hb₁, hd₁⟩ := decU64_sound bs n r₁ hn
                  obtain ⟨b₂, hb₂, hd₂⟩ := decU64_sound r₁ m r₂ hm
                  refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
                  rw [← hv, byte_eq_tb (by decide) hb]
                  exact Blimits.i64MinMax b₁ b₂ n m hd₁ hd₂
            · simp at h

theorem decLimits_complete : Complete Blimits decLimits := by
  intro b al r h
  cases h with
  | i32Min bs n hd =>
      show decLimits (tb 0x00 :: (bs ++ r)) = _
      simp [decLimits, tb, Byte.ofNat, decU64_complete bs n r hd]
  | i32MinMax b₁ b₂ n m hd₁ hd₂ =>
      show decLimits (tb 0x01 :: ((b₁ ++ b₂) ++ r)) = _
      rw [List.append_assoc]
      simp [decLimits, tb, Byte.ofNat,
        decU64_complete b₁ n (b₂ ++ r) hd₁, decU64_complete b₂ m r hd₂]
  | i64Min bs n hd =>
      show decLimits (tb 0x04 :: (bs ++ r)) = _
      simp [decLimits, tb, Byte.ofNat, decU64_complete bs n r hd]
  | i64MinMax b₁ b₂ n m hd₁ hd₂ =>
      show decLimits (tb 0x05 :: ((b₁ ++ b₂) ++ r)) = _
      rw [List.append_assoc]
      simp [decLimits, tb, Byte.ofNat,
        decU64_complete b₁ n (b₂ ++ r) hd₁, decU64_complete b₂ m r hd₂]

/-- `grammar Btagtype : tagtype`. -/
def decTagtype (bs : Bytes) : Except Fault (TagType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then
        (match decIdx r with
         | .error e => .error e
         | .ok (x, r') => .ok (.idx x, r'))
      else .error .opcode

theorem decTagtype_sound : Sound Btagtype decTagtype := by
  intro bs jt r h
  cases bs with
  | nil => simp [decTagtype] at h
  | cons b bs =>
      rw [decTagtype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i x r' hx
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decIdx_sound bs x r' hx
          refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
          rw [← hv, byte_eq_tb (by decide) hb]
          exact Btagtype.mk bb x hd
      · simp at h

theorem decTagtype_complete : Complete Btagtype decTagtype := by
  intro b jt r h
  cases h with
  | mk bs x hd =>
      show decTagtype (tb 0x00 :: (bs ++ r)) = _
      simp [decTagtype, tb, Byte.ofNat, decIdx_complete bs x r hd]

/-- `grammar Bglobaltype : globaltype`. -/
def decGlobaltype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (GlobalType × Bytes) :=
  match decValtype bs with
  | .error e => .error e
  | .ok (t, r₁) =>
      match decMut r₁ with
      | .error e => .error e
      | .ok (mo, r₂) => .ok ({ mutability := mo, valtype := t }, r₂)

theorem decGlobaltype_sound [authority : BinaryAuthority] : Sound Bglobaltype decGlobaltype := by
  intro bs gt r h
  rw [decGlobaltype] at h
  split at h
  · simp at h
  · rename_i t r₁ ht
    split at h
    · simp at h
    · rename_i mo r₂ hm
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b₁, hb₁, hd₁⟩ := decValtype_sound bs t r₁ ht
      obtain ⟨b₂, hb₂, hd₂⟩ := decMut_sound r₁ mo r₂ hm
      refine ⟨b₁ ++ b₂, by rw [hb₁, hb₂, hr]; simp, ?_⟩
      rw [← hv]
      exact Bglobaltype.mk b₁ b₂ t mo hd₁ hd₂

theorem decGlobaltype_complete [authority : BinaryAuthority] : Complete Bglobaltype decGlobaltype := by
  intro b gt r h
  cases h with
  | mk bt bm t mo ht hm =>
      rw [List.append_assoc]
      simp [decGlobaltype, decValtype_complete bt t (bm ++ r) ht,
        decMut_complete bm mo r hm]

/-- `grammar Bmemtype : memtype`. -/
def decMemtype (bs : Bytes) : Except Fault (MemType × Bytes) :=
  match decLimits bs with
  | .error e => .error e
  | .ok ((at', lim), r) => .ok ({ addr := at', lim := lim }, r)

theorem decMemtype_sound : Sound Bmemtype decMemtype := by
  intro bs mt r h
  rw [decMemtype] at h
  split at h
  · simp at h
  · rename_i at' lim r' hl
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨bb, hbb, hd⟩ := decLimits_sound bs (at', lim) r' hl
    exact ⟨bb, by rw [hbb, hr], by rw [← hv]; exact Bmemtype.mk bb at' lim hd⟩

theorem decMemtype_complete : Complete Bmemtype decMemtype := by
  intro b mt r h
  cases h with
  | mk at' lim hd => simp [decMemtype, decLimits_complete b (at', lim) r hd]

/-- `grammar Btabletype : tabletype`. -/
def decTabletype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (TableType × Bytes) :=
  match decReftype bs with
  | .error e => .error e
  | .ok (rt, r₁) =>
      match decLimits r₁ with
      | .error e => .error e
      | .ok ((at', lim), r₂) => .ok ({ addr := at', lim := lim, elem := rt }, r₂)

theorem decTabletype_sound [authority : BinaryAuthority] : Sound Btabletype decTabletype := by
  intro bs tt r h
  rw [decTabletype] at h
  split at h
  · simp at h
  · rename_i rt r₁ hrt
    split at h
    · simp at h
    · rename_i at' lim r₂ hl
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b₁, hb₁, hd₁⟩ := decReftype_sound bs rt r₁ hrt
      obtain ⟨b₂, hb₂, hd₂⟩ := decLimits_sound r₁ (at', lim) r₂ hl
      refine ⟨b₁ ++ b₂, by rw [hb₁, hb₂, hr]; simp, ?_⟩
      rw [← hv]
      exact Btabletype.mk b₁ b₂ rt at' lim hd₁ hd₂

theorem decTabletype_complete [authority : BinaryAuthority] : Complete Btabletype decTabletype := by
  intro b tt r h
  cases h with
  | mk br bl rt at' lim hr hl =>
      rw [List.append_assoc]
      simp [decTabletype, decReftype_complete br rt (bl ++ r) hr,
        decLimits_complete bl (at', lim) r hl]

/-- `grammar Bexterntype : externtype`. -/
def decExterntype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (ExternType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then
        (match decIdx r with
         | .error e => .error e
         | .ok (x, r') => .ok (.func (.idx x), r'))
      else if b.val = 0x01 then
        (match decTabletype r with
         | .error e => .error e
         | .ok (tt, r') => .ok (.table tt, r'))
      else if b.val = 0x02 then
        (match decMemtype r with
         | .error e => .error e
         | .ok (mt, r') => .ok (.mem mt, r'))
      else if b.val = 0x03 then
        (match decGlobaltype r with
         | .error e => .error e
         | .ok (gt, r') => .ok (.global gt, r'))
      else if b.val = 0x04 then
        (match decTagtype r with
         | .error e => .error e
         | .ok (jt, r') => .ok (.tag jt, r'))
      else .error .opcode

theorem decExterntype_sound [authority : BinaryAuthority] : Sound Bexterntype decExterntype := by
  intro bs xt r h
  cases bs with
  | nil => simp [decExterntype] at h
  | cons b bs =>
      rw [decExterntype] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i x r' hx
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bb, hbb, hd⟩ := decIdx_sound bs x r' hx
          refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
          rw [← hv, byte_eq_tb (by decide) hb]
          exact Bexterntype.func bb x hd
      · split at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i tt r' ht
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decTabletype_sound bs tt r' ht
            refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
            rw [← hv, byte_eq_tb (by decide) hb]
            exact Bexterntype.table bb tt hd
        · split at h
          · rename_i hb
            split at h
            · simp at h
            · rename_i mt r' ht
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨bb, hbb, hd⟩ := decMemtype_sound bs mt r' ht
              refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Bexterntype.mem bb mt hd
          · split at h
            · rename_i hb
              split at h
              · simp at h
              · rename_i gt r' ht
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                obtain ⟨bb, hbb, hd⟩ := decGlobaltype_sound bs gt r' ht
                refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
                rw [← hv, byte_eq_tb (by decide) hb]
                exact Bexterntype.global bb gt hd
            · split at h
              · rename_i hb
                split at h
                · simp at h
                · rename_i jt r' ht
                  obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨bb, hbb, hd⟩ := decTagtype_sound bs jt r' ht
                  refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
                  rw [← hv, byte_eq_tb (by decide) hb]
                  exact Bexterntype.tag bb jt hd
              · simp at h

theorem decExterntype_complete [authority : BinaryAuthority] : Complete Bexterntype decExterntype := by
  intro b xt r h
  cases h with
  | func bs x hd =>
      show decExterntype (tb 0x00 :: (bs ++ r)) = _
      simp [decExterntype, tb, Byte.ofNat, decIdx_complete bs x r hd]
  | table bs tt hd =>
      show decExterntype (tb 0x01 :: (bs ++ r)) = _
      simp [decExterntype, tb, Byte.ofNat, decTabletype_complete bs tt r hd]
  | mem bs mt hd =>
      show decExterntype (tb 0x02 :: (bs ++ r)) = _
      simp [decExterntype, tb, Byte.ofNat, decMemtype_complete bs mt r hd]
  | global bs gt hd =>
      show decExterntype (tb 0x03 :: (bs ++ r)) = _
      simp [decExterntype, tb, Byte.ofNat, decGlobaltype_complete bs gt r hd]
  | tag bs jt hd =>
      show decExterntype (tb 0x04 :: (bs ++ r)) = _
      simp [decExterntype, tb, Byte.ofNat, decTagtype_complete bs jt r hd]

/-! ## External indices (`5.1`) -/

/-- `grammar Bexternidx : externidx`. -/
def decExternidx (bs : Bytes) : Except Fault (ExternIdx × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      match decIdx r with
      | .error e => .error e
      | .ok (x, r') =>
          if b.val = 0x00 then .ok (.func x, r')
          else if b.val = 0x01 then .ok (.table x, r')
          else if b.val = 0x02 then .ok (.mem x, r')
          else if b.val = 0x03 then .ok (.global x, r')
          else if b.val = 0x04 then .ok (.tag x, r')
          else .error .opcode

theorem decExternidx_sound : Sound Bexternidx decExternidx := by
  intro bs xx r h
  cases bs with
  | nil => simp [decExternidx] at h
  | cons b bs =>
      rw [decExternidx] at h
      split at h
      · simp at h
      · rename_i x r' hx
        obtain ⟨bb, hbb, hd⟩ := decIdx_sound bs x r' hx
        split at h
        · rename_i hb
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
          rw [← hv, byte_eq_tb (by decide) hb]
          exact Bexternidx.func bb x hd
        · split at h
          · rename_i hb
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
            rw [← hv, byte_eq_tb (by decide) hb]
            exact Bexternidx.table bb x hd
          · split at h
            · rename_i hb
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Bexternidx.mem bb x hd
            · split at h
              · rename_i hb
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
                rw [← hv, byte_eq_tb (by decide) hb]
                exact Bexternidx.global bb x hd
              · split at h
                · rename_i hb
                  obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                  refine ⟨b :: bb, by rw [hbb, hr]; rfl, ?_⟩
                  rw [← hv, byte_eq_tb (by decide) hb]
                  exact Bexternidx.tag bb x hd
                · simp at h

theorem decExternidx_complete : Complete Bexternidx decExternidx := by
  intro b xx r h
  cases h with
  | func bs x hd =>
      show decExternidx (tb 0x00 :: (bs ++ r)) = _
      simp [decExternidx, tb, Byte.ofNat, decIdx_complete bs x r hd]
  | table bs x hd =>
      show decExternidx (tb 0x01 :: (bs ++ r)) = _
      simp [decExternidx, tb, Byte.ofNat, decIdx_complete bs x r hd]
  | mem bs x hd =>
      show decExternidx (tb 0x02 :: (bs ++ r)) = _
      simp [decExternidx, tb, Byte.ofNat, decIdx_complete bs x r hd]
  | global bs x hd =>
      show decExternidx (tb 0x03 :: (bs ++ r)) = _
      simp [decExternidx, tb, Byte.ofNat, decIdx_complete bs x r hd]
  | tag bs x hd =>
      show decExternidx (tb 0x04 :: (bs ++ r)) = _
      simp [decExternidx, tb, Byte.ofNat, decIdx_complete bs x r hd]

end WasmGemmGnaf.Wasm.Core.Decode
