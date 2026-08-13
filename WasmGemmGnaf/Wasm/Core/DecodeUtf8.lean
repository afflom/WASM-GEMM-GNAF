/-
  Wasm/Core/DecodeUtf8.lean --- the inverse of `$utf8`, and `grammar Bname`.

  `grammar Bname : name = | b*:Blist(Bbyte) => name  -- if $utf8(name) = b*`
  (`5.1-binary.values.spectec`).  The side condition is an EQUATION on the
  encoder, so a decoder for names has to invert `utf8` -- the function
  `Core/Values.lean` defines (rather than assumes) for `def $utf8(char*)`.

  WHAT IS PROVED HERE.  `utf8Decode` is a two-sided inverse of `utf8` on its
  image:

      utf8Decode_sound    : utf8Decode bl = some cs -> utf8 cs = bl
      utf8Decode_complete : utf8Decode (utf8 cs) = some cs

  Soundness is what lets the decoder produce a `name` at all; completeness is
  what stops it rejecting a name the grammar accepts.  Together they say the
  decoder accepts EXACTLY the byte sequences that are `$utf8` of something:
  overlong forms, surrogates and code points above `U+10FFFF` are rejected,
  because `utf8` never produces them and `char` excludes them.

  The decoder is fuelled by the length of its input rather than by well-founded
  recursion on it, so that its defining equations stay first-order and the two
  theorems above are ordinary inductions.
-/
import WasmGemmGnaf.Wasm.Core.DecodeParser

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Scalar values -/

/-- A code point as a `char`, or `none` if it is a surrogate or out of range. -/
def mkChar (n : Nat) : Option UChar :=
  if h : n ≤ 0xD7FF ∨ (0xE000 ≤ n ∧ n ≤ 0x10FFFF) then some ⟨n, h⟩ else none

theorem mkChar_val {n : Nat} {c : UChar} (h : mkChar n = some c) : c.val = n := by
  rw [mkChar] at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · simp at h

theorem mkChar_self (c : UChar) : mkChar c.val = some c := by
  rw [mkChar, dif_pos c.property]

/-! ## The three multi-byte continuations

Each carries its own minimality bound, so an overlong encoding has no decoding,
as it has no `utf8` preimage. -/

/-- The continuation of a two-byte form. -/
def utf8Cont1 (v0 : Nat) (rest : List Byte) : Option (UChar × List Byte) :=
  match rest with
  | b1 :: rest1 =>
      if 0x80 ≤ b1.val ∧ b1.val < 0xC0 ∧
          0x80 ≤ (v0 - 0xC0) * 0x40 + (b1.val - 0x80) then
        (mkChar ((v0 - 0xC0) * 0x40 + (b1.val - 0x80))).map (fun c => (c, rest1))
      else none
  | [] => none

/-- The continuation of a three-byte form. -/
def utf8Cont2 (v0 : Nat) (rest : List Byte) : Option (UChar × List Byte) :=
  match rest with
  | b1 :: b2 :: rest2 =>
      if 0x80 ≤ b1.val ∧ b1.val < 0xC0 ∧ 0x80 ≤ b2.val ∧ b2.val < 0xC0 ∧
          0x800 ≤ (v0 - 0xE0) * 0x1000 + (b1.val - 0x80) * 0x40 + (b2.val - 0x80) then
        (mkChar ((v0 - 0xE0) * 0x1000 + (b1.val - 0x80) * 0x40
          + (b2.val - 0x80))).map (fun c => (c, rest2))
      else none
  | _ => none

/-- The continuation of a four-byte form. -/
def utf8Cont3 (v0 : Nat) (rest : List Byte) : Option (UChar × List Byte) :=
  match rest with
  | b1 :: b2 :: b3 :: rest3 =>
      if 0x80 ≤ b1.val ∧ b1.val < 0xC0 ∧ 0x80 ≤ b2.val ∧ b2.val < 0xC0 ∧
          0x80 ≤ b3.val ∧ b3.val < 0xC0 ∧
          0x10000 ≤ (v0 - 0xF0) * 0x40000 + (b1.val - 0x80) * 0x1000
            + (b2.val - 0x80) * 0x40 + (b3.val - 0x80) then
        (mkChar ((v0 - 0xF0) * 0x40000 + (b1.val - 0x80) * 0x1000
          + (b2.val - 0x80) * 0x40 + (b3.val - 0x80))).map (fun c => (c, rest3))
      else none
  | _ => none

/-- Decode the leading scalar value of a byte sequence, or fail. -/
def utf8Char? (bs : List Byte) : Option (UChar × List Byte) :=
  match bs with
  | [] => none
  | b0 :: r0 =>
      if b0.val < 0x80 then (mkChar b0.val).map (fun c => (c, r0))
      else if b0.val < 0xC0 then none
      else if b0.val < 0xE0 then utf8Cont1 b0.val r0
      else if b0.val < 0xF0 then utf8Cont2 b0.val r0
      else if b0.val < 0xF8 then utf8Cont3 b0.val r0
      else none

/-! ### Each continuation consumes what it reads -/

theorem utf8Cont1_lt {v0 : Nat} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (h : utf8Cont1 v0 r0 = some (c, rest)) : rest.length < r0.length := by
  cases r0 with
  | nil => simp [utf8Cont1] at h
  | cons b1 rest1 =>
      rw [utf8Cont1] at h
      split at h
      · cases hm : mkChar ((v0 - 0xC0) * 0x40 + (b1.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have : rest = rest1 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            simp only [this, List.length_cons]
            omega
      · simp at h

theorem utf8Cont2_lt {v0 : Nat} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (h : utf8Cont2 v0 r0 = some (c, rest)) : rest.length < r0.length := by
  match r0 with
  | [] => simp [utf8Cont2] at h
  | [b1] => simp [utf8Cont2] at h
  | b1 :: b2 :: rest2 =>
      rw [utf8Cont2] at h
      split at h
      · cases hm : mkChar ((v0 - 0xE0) * 0x1000 + (b1.val - 0x80) * 0x40
            + (b2.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have : rest = rest2 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            simp only [this, List.length_cons]
            omega
      · simp at h

theorem utf8Cont3_lt {v0 : Nat} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (h : utf8Cont3 v0 r0 = some (c, rest)) : rest.length < r0.length := by
  match r0 with
  | [] => simp [utf8Cont3] at h
  | [b1] => simp [utf8Cont3] at h
  | [b1, b2] => simp [utf8Cont3] at h
  | b1 :: b2 :: b3 :: rest3 =>
      rw [utf8Cont3] at h
      split at h
      · cases hm : mkChar ((v0 - 0xF0) * 0x40000 + (b1.val - 0x80) * 0x1000
            + (b2.val - 0x80) * 0x40 + (b3.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have : rest = rest3 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            simp only [this, List.length_cons]
            omega
      · simp at h

/-- A decoded scalar value consumes at least one byte. -/
theorem utf8Char?_lt {bs : List Byte} {c : UChar} {rest : List Byte}
    (h : utf8Char? bs = some (c, rest)) : rest.length < bs.length := by
  cases bs with
  | nil => simp [utf8Char?] at h
  | cons b0 r0 =>
      rw [utf8Char?] at h
      split at h
      · cases hm : mkChar b0.val with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have : rest = r0 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            simp only [this, List.length_cons]
            omega
      · split at h
        · simp at h
        · split at h
          · have := utf8Cont1_lt h; simp; omega
          · split at h
            · have := utf8Cont2_lt h; simp; omega
            · split at h
              · have := utf8Cont3_lt h; simp; omega
              · simp at h

/-! ### Each continuation reads back what `utf8Char` writes -/

theorem utf8Cont1_sound {b0 : Byte} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (hlo : 0xC0 ≤ b0.val) (hhi : b0.val < 0xE0)
    (h : utf8Cont1 b0.val r0 = some (c, rest)) : b0 :: r0 = utf8Char c ++ rest := by
  cases r0 with
  | nil => simp [utf8Cont1] at h
  | cons b1 rest1 =>
      rw [utf8Cont1] at h
      split at h
      · rename_i hcond
        cases hm : mkChar ((b0.val - 0xC0) * 0x40 + (b1.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have hc : c' = c := by simpa using (Prod.mk.inj (Option.some.inj h)).1
            have hr : rest = rest1 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            have hval : c.val = (b0.val - 0xC0) * 0x40 + (b1.val - 0x80) := by
              rw [← hc]; exact mkChar_val hm
            have hb1 := hcond.1
            have hb1' := hcond.2.1
            have hvlo : 0x80 ≤ c.val := by omega
            have hvhi : c.val < 0x800 := by omega
            have hd0 : 0xC0 + c.val / 0x40 = b0.val := by omega
            have hd1 : 0x80 + c.val % 0x40 = b1.val := by omega
            have e0 : Byte.ofNat (0xC0 + c.val / 0x40) = b0 :=
              Subtype.ext (by rw [Byte.ofNat, hd0]; exact Nat.mod_eq_of_lt b0.property)
            have e1 : Byte.ofNat (0x80 + c.val % 0x40) = b1 :=
              Subtype.ext (by rw [Byte.ofNat, hd1]; exact Nat.mod_eq_of_lt b1.property)
            have hnot : ¬ (c.val < 0x80) := by omega
            rw [hr, utf8Char]
            simp only [hnot, if_false, hvhi, if_pos, e0, e1]
            rfl
      · simp at h

theorem utf8Cont2_sound {b0 : Byte} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (hlo : 0xE0 ≤ b0.val) (hhi : b0.val < 0xF0)
    (h : utf8Cont2 b0.val r0 = some (c, rest)) : b0 :: r0 = utf8Char c ++ rest := by
  match r0 with
  | [] => simp [utf8Cont2] at h
  | [b1] => simp [utf8Cont2] at h
  | b1 :: b2 :: rest2 =>
      rw [utf8Cont2] at h
      split at h
      · rename_i hcond
        cases hm : mkChar ((b0.val - 0xE0) * 0x1000 + (b1.val - 0x80) * 0x40
            + (b2.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have hc : c' = c := by simpa using (Prod.mk.inj (Option.some.inj h)).1
            have hr : rest = rest2 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            have hval : c.val = (b0.val - 0xE0) * 0x1000 + (b1.val - 0x80) * 0x40
                + (b2.val - 0x80) := by rw [← hc]; exact mkChar_val hm
            have hb1 := hcond.1
            have hb1' := hcond.2.1
            have hb2 := hcond.2.2.1
            have hb2' := hcond.2.2.2.1
            have hmin := hcond.2.2.2.2
            have hvhi : c.val < 0x10000 := by omega
            have hd0 : 0xE0 + c.val / 0x1000 = b0.val := by omega
            have hd1 : 0x80 + c.val / 0x40 % 0x40 = b1.val := by omega
            have hd2 : 0x80 + c.val % 0x40 = b2.val := by omega
            have e0 : Byte.ofNat (0xE0 + c.val / 0x1000) = b0 :=
              Subtype.ext (by rw [Byte.ofNat, hd0]; exact Nat.mod_eq_of_lt b0.property)
            have e1 : Byte.ofNat (0x80 + c.val / 0x40 % 0x40) = b1 :=
              Subtype.ext (by rw [Byte.ofNat, hd1]; exact Nat.mod_eq_of_lt b1.property)
            have e2 : Byte.ofNat (0x80 + c.val % 0x40) = b2 :=
              Subtype.ext (by rw [Byte.ofNat, hd2]; exact Nat.mod_eq_of_lt b2.property)
            have hn0 : ¬ (c.val < 0x80) := by omega
            have hn1 : ¬ (c.val < 0x800) := by omega
            rw [hr, utf8Char]
            simp only [hn0, if_false, hn1, hvhi, if_pos, e0, e1, e2]
            rfl
      · simp at h

theorem utf8Cont3_sound {b0 : Byte} {r0 : List Byte} {c : UChar} {rest : List Byte}
    (hlo : 0xF0 ≤ b0.val) (hhi : b0.val < 0xF8)
    (h : utf8Cont3 b0.val r0 = some (c, rest)) : b0 :: r0 = utf8Char c ++ rest := by
  match r0 with
  | [] => simp [utf8Cont3] at h
  | [b1] => simp [utf8Cont3] at h
  | [b1, b2] => simp [utf8Cont3] at h
  | b1 :: b2 :: b3 :: rest3 =>
      rw [utf8Cont3] at h
      split at h
      · rename_i hcond
        cases hm : mkChar ((b0.val - 0xF0) * 0x40000 + (b1.val - 0x80) * 0x1000
            + (b2.val - 0x80) * 0x40 + (b3.val - 0x80)) with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have hc : c' = c := by simpa using (Prod.mk.inj (Option.some.inj h)).1
            have hr : rest = rest3 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            have hval : c.val = (b0.val - 0xF0) * 0x40000 + (b1.val - 0x80) * 0x1000
                + (b2.val - 0x80) * 0x40 + (b3.val - 0x80) := by
              rw [← hc]; exact mkChar_val hm
            have hb1 := hcond.1
            have hb1' := hcond.2.1
            have hb2 := hcond.2.2.1
            have hb2' := hcond.2.2.2.1
            have hb3 := hcond.2.2.2.2.1
            have hb3' := hcond.2.2.2.2.2.1
            have hmin := hcond.2.2.2.2.2.2
            have hd0 : 0xF0 + c.val / 0x40000 = b0.val := by omega
            have hd1 : 0x80 + c.val / 0x1000 % 0x40 = b1.val := by omega
            have hd2 : 0x80 + c.val / 0x40 % 0x40 = b2.val := by omega
            have hd3 : 0x80 + c.val % 0x40 = b3.val := by omega
            have e0 : Byte.ofNat (0xF0 + c.val / 0x40000) = b0 :=
              Subtype.ext (by rw [Byte.ofNat, hd0]; exact Nat.mod_eq_of_lt b0.property)
            have e1 : Byte.ofNat (0x80 + c.val / 0x1000 % 0x40) = b1 :=
              Subtype.ext (by rw [Byte.ofNat, hd1]; exact Nat.mod_eq_of_lt b1.property)
            have e2 : Byte.ofNat (0x80 + c.val / 0x40 % 0x40) = b2 :=
              Subtype.ext (by rw [Byte.ofNat, hd2]; exact Nat.mod_eq_of_lt b2.property)
            have e3 : Byte.ofNat (0x80 + c.val % 0x40) = b3 :=
              Subtype.ext (by rw [Byte.ofNat, hd3]; exact Nat.mod_eq_of_lt b3.property)
            have hn0 : ¬ (c.val < 0x80) := by omega
            have hn1 : ¬ (c.val < 0x800) := by omega
            have hn2 : ¬ (c.val < 0x10000) := by omega
            rw [hr, utf8Char]
            simp only [hn0, if_false, hn1, hn2, e0, e1, e2, e3]
            rfl
      · simp at h

/-- What `utf8Char?` accepts, `utf8Char` produces. -/
theorem utf8Char?_sound {bs : List Byte} {c : UChar} {rest : List Byte}
    (h : utf8Char? bs = some (c, rest)) : bs = utf8Char c ++ rest := by
  cases bs with
  | nil => simp [utf8Char?] at h
  | cons b0 r0 =>
      rw [utf8Char?] at h
      split at h
      · rename_i h0
        cases hm : mkChar b0.val with
        | none => rw [hm] at h; simp at h
        | some c' =>
            rw [hm] at h
            have hc : c' = c := by simpa using (Prod.mk.inj (Option.some.inj h)).1
            have hr : rest = r0 := by simpa using ((Prod.mk.inj (Option.some.inj h)).2).symm
            have hval : c.val = b0.val := by rw [← hc]; exact mkChar_val hm
            have e0 : Byte.ofNat c.val = b0 :=
              Subtype.ext (by rw [Byte.ofNat, hval]; exact Nat.mod_eq_of_lt b0.property)
            have hlt : c.val < 0x80 := by omega
            rw [hr, utf8Char]
            simp only [hlt, if_pos, e0]
            rfl
      · rename_i h0
        split at h
        · simp at h
        · rename_i h1
          split at h
          · exact utf8Cont1_sound (by omega) (by assumption) h
          · rename_i h2
            split at h
            · exact utf8Cont2_sound (by omega) (by assumption) h
            · rename_i h3
              split at h
              · exact utf8Cont3_sound (by omega) (by assumption) h
              · simp at h

/-- What `utf8Char` produces, `utf8Char?` accepts -- reading back the same
scalar value and leaving the rest of the input alone. -/
theorem utf8Char?_complete (c : UChar) (rest : List Byte) :
    utf8Char? (utf8Char c ++ rest) = some (c, rest) := by
  have hc := c.property
  rcases Nat.lt_or_ge c.val 0x80 with h1 | h1
  · rw [utf8Char]
    simp only [h1, if_pos]
    show utf8Char? (Byte.ofNat c.val :: rest) = _
    have hv : (Byte.ofNat c.val).val = c.val := Nat.mod_eq_of_lt (by omega)
    rw [utf8Char?]
    simp only [hv, h1, if_pos, mkChar_self c]
    rfl
  · rcases Nat.lt_or_ge c.val 0x800 with h2 | h2
    · rw [utf8Char]
      have hn0 : ¬ (c.val < 0x80) := by omega
      simp only [hn0, if_false, h2, if_pos]
      show utf8Char? (Byte.ofNat (0xC0 + c.val / 0x40) ::
        Byte.ofNat (0x80 + c.val % 0x40) :: rest) = _
      have hv0 : (Byte.ofNat (0xC0 + c.val / 0x40)).val = 0xC0 + c.val / 0x40 :=
        Nat.mod_eq_of_lt (by omega)
      have hv1 : (Byte.ofNat (0x80 + c.val % 0x40)).val = 0x80 + c.val % 0x40 :=
        Nat.mod_eq_of_lt (by omega)
      have hs0 : ¬ ((0xC0 + c.val / 0x40) < 0x80) := by omega
      have hs1 : ¬ ((0xC0 + c.val / 0x40) < 0xC0) := by omega
      have hs2 : (0xC0 + c.val / 0x40) < 0xE0 := by omega
      rw [utf8Char?]
      simp only [hv0, hs0, if_false, hs1, hs2, if_pos]
      rw [utf8Cont1]
      have hcond : 0x80 ≤ (Byte.ofNat (0x80 + c.val % 0x40)).val ∧
          (Byte.ofNat (0x80 + c.val % 0x40)).val < 0xC0 ∧
          0x80 ≤ (0xC0 + c.val / 0x40 - 0xC0) * 0x40
            + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) :=
        ⟨by simp only [hv1]; omega, by simp only [hv1]; omega, by simp only [hv1]; omega⟩
      have hval : (0xC0 + c.val / 0x40 - 0xC0) * 0x40
          + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) = c.val := by
        rw [hv1]; omega
      rw [if_pos hcond, hval, mkChar_self c]
      rfl
    · rcases Nat.lt_or_ge c.val 0x10000 with h3 | h3
      · rw [utf8Char]
        have hn0 : ¬ (c.val < 0x80) := by omega
        have hn1 : ¬ (c.val < 0x800) := by omega
        simp only [hn0, if_false, hn1, h3, if_pos]
        show utf8Char? (Byte.ofNat (0xE0 + c.val / 0x1000) ::
          Byte.ofNat (0x80 + c.val / 0x40 % 0x40) ::
          Byte.ofNat (0x80 + c.val % 0x40) :: rest) = _
        have hv0 : (Byte.ofNat (0xE0 + c.val / 0x1000)).val = 0xE0 + c.val / 0x1000 :=
          Nat.mod_eq_of_lt (by omega)
        have hv1 : (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val
            = 0x80 + c.val / 0x40 % 0x40 := Nat.mod_eq_of_lt (by omega)
        have hv2 : (Byte.ofNat (0x80 + c.val % 0x40)).val = 0x80 + c.val % 0x40 :=
          Nat.mod_eq_of_lt (by omega)
        have hs0 : ¬ ((0xE0 + c.val / 0x1000) < 0x80) := by omega
        have hs1 : ¬ ((0xE0 + c.val / 0x1000) < 0xC0) := by omega
        have hs2 : ¬ ((0xE0 + c.val / 0x1000) < 0xE0) := by omega
        have hs3 : (0xE0 + c.val / 0x1000) < 0xF0 := by omega
        rw [utf8Char?]
        simp only [hv0, hs0, if_false, hs1, hs2, hs3, if_pos]
        rw [utf8Cont2]
        have hcond : 0x80 ≤ (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val ∧
            (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val < 0xC0 ∧
            0x80 ≤ (Byte.ofNat (0x80 + c.val % 0x40)).val ∧
            (Byte.ofNat (0x80 + c.val % 0x40)).val < 0xC0 ∧
            0x800 ≤ (0xE0 + c.val / 0x1000 - 0xE0) * 0x1000
              + ((Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val - 0x80) * 0x40
              + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) :=
          ⟨by simp only [hv1, hv2]; omega, by simp only [hv1, hv2]; omega, by simp only [hv1, hv2]; omega,
            by simp only [hv1, hv2]; omega, by simp only [hv1, hv2]; omega⟩
        have hval : (0xE0 + c.val / 0x1000 - 0xE0) * 0x1000
            + ((Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val - 0x80) * 0x40
            + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) = c.val := by
          rw [hv1, hv2]; omega
        rw [if_pos hcond, hval, mkChar_self c]
        rfl
      · rw [utf8Char]
        have hn0 : ¬ (c.val < 0x80) := by omega
        have hn1 : ¬ (c.val < 0x800) := by omega
        have hn2 : ¬ (c.val < 0x10000) := by omega
        have hmax : c.val ≤ 0x10FFFF := by omega
        simp only [hn0, if_false, hn1, hn2]
        show utf8Char? (Byte.ofNat (0xF0 + c.val / 0x40000) ::
          Byte.ofNat (0x80 + c.val / 0x1000 % 0x40) ::
          Byte.ofNat (0x80 + c.val / 0x40 % 0x40) ::
          Byte.ofNat (0x80 + c.val % 0x40) :: rest) = _
        have hv0 : (Byte.ofNat (0xF0 + c.val / 0x40000)).val = 0xF0 + c.val / 0x40000 :=
          Nat.mod_eq_of_lt (by omega)
        have hv1 : (Byte.ofNat (0x80 + c.val / 0x1000 % 0x40)).val
            = 0x80 + c.val / 0x1000 % 0x40 := Nat.mod_eq_of_lt (by omega)
        have hv2 : (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val
            = 0x80 + c.val / 0x40 % 0x40 := Nat.mod_eq_of_lt (by omega)
        have hv3 : (Byte.ofNat (0x80 + c.val % 0x40)).val = 0x80 + c.val % 0x40 :=
          Nat.mod_eq_of_lt (by omega)
        have hs0 : ¬ ((0xF0 + c.val / 0x40000) < 0x80) := by omega
        have hs1 : ¬ ((0xF0 + c.val / 0x40000) < 0xC0) := by omega
        have hs2 : ¬ ((0xF0 + c.val / 0x40000) < 0xE0) := by omega
        have hs3 : ¬ ((0xF0 + c.val / 0x40000) < 0xF0) := by omega
        have hs4 : (0xF0 + c.val / 0x40000) < 0xF8 := by omega
        rw [utf8Char?]
        simp only [hv0, hs0, if_false, hs1, hs2, hs3, hs4, if_pos]
        rw [utf8Cont3]
        have hcond : 0x80 ≤ (Byte.ofNat (0x80 + c.val / 0x1000 % 0x40)).val ∧
            (Byte.ofNat (0x80 + c.val / 0x1000 % 0x40)).val < 0xC0 ∧
            0x80 ≤ (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val ∧
            (Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val < 0xC0 ∧
            0x80 ≤ (Byte.ofNat (0x80 + c.val % 0x40)).val ∧
            (Byte.ofNat (0x80 + c.val % 0x40)).val < 0xC0 ∧
            0x10000 ≤ (0xF0 + c.val / 0x40000 - 0xF0) * 0x40000
              + ((Byte.ofNat (0x80 + c.val / 0x1000 % 0x40)).val - 0x80) * 0x1000
              + ((Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val - 0x80) * 0x40
              + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) :=
          ⟨by simp only [hv1, hv2, hv3]; omega, by simp only [hv1, hv2, hv3]; omega,
            by simp only [hv1, hv2, hv3]; omega, by simp only [hv1, hv2, hv3]; omega,
            by simp only [hv1, hv2, hv3]; omega, by simp only [hv1, hv2, hv3]; omega,
            by simp only [hv1, hv2, hv3]; omega⟩
        have hval : (0xF0 + c.val / 0x40000 - 0xF0) * 0x40000
            + ((Byte.ofNat (0x80 + c.val / 0x1000 % 0x40)).val - 0x80) * 0x1000
            + ((Byte.ofNat (0x80 + c.val / 0x40 % 0x40)).val - 0x80) * 0x40
            + ((Byte.ofNat (0x80 + c.val % 0x40)).val - 0x80) = c.val := by
          rw [hv1, hv2, hv3]; omega
        rw [if_pos hcond, hval, mkChar_self c]
        rfl

/-! ## Whole byte sequences -/

/-- `$utf8` inverted, fuelled by a step count. -/
def utf8DecodeN : Nat → List Byte → Option (List UChar)
  | 0, bl => if bl.isEmpty then some [] else none
  | n + 1, bl =>
      match utf8Char? bl with
      | none => if bl.isEmpty then some [] else none
      | some (c, rest) => (utf8DecodeN n rest).map (fun cs => c :: cs)

/-- `$utf8` inverted: the scalar values whose UTF-8 encoding is `bl`, if any.
One step per byte is always enough, because every step consumes a byte. -/
def utf8Decode (bl : List Byte) : Option (List UChar) := utf8DecodeN bl.length bl

theorem utf8DecodeN_sound : ∀ (n : Nat) (bl : List Byte) (cs : List UChar),
    utf8DecodeN n bl = some cs → utf8 cs = bl := by
  intro n
  induction n with
  | zero =>
      intro bl cs h
      rw [utf8DecodeN] at h
      split at h
      · rename_i he
        have hcs : cs = [] := (Option.some.inj h).symm
        cases bl with
        | nil => rw [hcs]; rfl
        | cons _ _ => simp at he
      · simp at h
  | succ n ih =>
      intro bl cs h
      rw [utf8DecodeN] at h
      split at h
      · split at h
        · rename_i he
          have hcs : cs = [] := (Option.some.inj h).symm
          cases bl with
          | nil => rw [hcs]; rfl
          | cons _ _ => simp at he
        · simp at h
      · rename_i c rest hsome
        cases hd : utf8DecodeN n rest with
        | none => rw [hd] at h; simp at h
        | some cs' =>
            rw [hd] at h
            have hcs : cs = c :: cs' := by simpa using h.symm
            rw [hcs, utf8, List.flatMap_cons, ← utf8, ih rest cs' hd]
            exact (utf8Char?_sound hsome).symm

theorem utf8Decode_sound (bl : List Byte) (cs : List UChar)
    (h : utf8Decode bl = some cs) : utf8 cs = bl :=
  utf8DecodeN_sound bl.length bl cs h

/-- Every scalar value contributes at least one byte. -/
theorem length_le_utf8 : ∀ cs : List UChar, cs.length ≤ (utf8 cs).length := by
  intro cs
  induction cs with
  | nil => simp [utf8]
  | cons c cs ih =>
      have hflat : utf8 (c :: cs) = utf8Char c ++ utf8 cs := by
        rw [utf8, List.flatMap_cons, ← utf8]
      have hone : 1 ≤ (utf8Char c).length := by
        rw [utf8Char]
        split
        · simp
        · split
          · simp
          · split <;> simp
      rw [hflat]
      simp only [List.length_append, List.length_cons]
      omega

theorem utf8DecodeN_complete : ∀ (cs : List UChar) (n : Nat), cs.length ≤ n →
    utf8DecodeN n (utf8 cs) = some cs := by
  intro cs
  induction cs with
  | nil =>
      intro n _
      cases n with
      | zero => rfl
      | succ n => rw [utf8]; simp [utf8DecodeN, utf8Char?]
  | cons c cs ih =>
      intro n hn
      cases n with
      | zero => simp at hn
      | succ n =>
          have hflat : utf8 (c :: cs) = utf8Char c ++ utf8 cs := by
            rw [utf8, List.flatMap_cons, ← utf8]
          rw [hflat, utf8DecodeN, utf8Char?_complete c (utf8 cs)]
          show Option.map (fun cs => c :: cs) (utf8DecodeN n (utf8 cs)) = some (c :: cs)
          rw [ih n (by simp at hn; omega)]
          rfl

theorem utf8Decode_complete (cs : List UChar) : utf8Decode (utf8 cs) = some cs :=
  utf8DecodeN_complete cs (utf8 cs).length (length_le_utf8 cs)

/-! ## `grammar Bname` -/

/-- `grammar Bname : name`. -/
def decName (bs : Bytes) : Except Fault (Name × Bytes) :=
  match decList readByte bs with
  | .error e => .error e
  | .ok (bl, r) =>
      match utf8Decode bl with
      | none => .error .utf8
      | some cs =>
          if hlen : (utf8 cs).length < 2 ^ 32 then .ok (⟨cs, hlen⟩, r) else .error .range

theorem decName_sound : Sound Bname decName := by
  intro bs nm r h
  rw [decName] at h
  split at h
  · simp at h
  · rename_i bl r' hbl
    split at h
    · simp at h
    · rename_i cs hcs
      split at h
      · obtain ⟨hnm, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨b, hb, hd⟩ := decList_sound readByte_sound bs bl r' hbl
        refine ⟨b, by rw [hb, hr], Bname.mk b bl nm hd ?_⟩
        rw [← hnm]
        exact utf8Decode_sound bl cs hcs
      · simp at h

theorem decName_complete : Complete Bname decName := by
  intro b nm r h
  cases h with
  | mk bl _nm hlist hutf8 =>
      rw [decName, decList_complete readByte_complete b bl r hlist, ← hutf8]
      show (match utf8Decode (utf8 nm.val) with
        | none => Except.error Fault.utf8
        | some cs =>
            if hlen : (utf8 cs).length < 2 ^ 32 then
              Except.ok ((⟨cs, hlen⟩ : Name), r)
            else Except.error Fault.range) = Except.ok (nm, r)
      rw [utf8Decode_complete nm.val]
      show (if hlen : (utf8 nm.val).length < 2 ^ 32 then
              Except.ok ((⟨nm.val, hlen⟩ : Name), r)
            else Except.error Fault.range) = Except.ok (nm, r)
      rw [dif_pos nm.property]

end WasmGemmGnaf.Wasm.Core.Decode
