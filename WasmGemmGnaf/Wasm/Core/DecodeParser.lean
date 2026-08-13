/-
  Wasm/Core/DecodeParser.lean --- the parsing skeleton of the executable Core 3.0
  decoder, and the values layer of `5.1-binary.values.spectec`.

  WHAT THIS FILE IS FOR.  `Wasm/Core/BinaryGrammar/` carries the pinned binary
  format as a RELATION, `Bmodule : Bytes -> Module -> Prop`, transcribed from the
  vendored `5.*-binary.*.spectec` and mentioning no decoder.  This file starts
  the other side: a total, computable decoder, together with the two properties
  that make it worth having.

  THE TWO PROPERTIES.  For a step parser `p : Bytes -> Except Fault (a x Bytes)`
  and a grammar `G : Bytes -> a -> Prop`:

      Sound G p     : p bs = ok (x, r) -> exists b, bs = b ++ r /\ G b x
      Complete G p  : G b x -> p (b ++ r) = ok (x, r)

  `Sound` says the decoder invents nothing: whatever prefix it consumed really
  does derive the value it returned.  `Complete` says the decoder misses
  nothing, and in the strong "prefix" form that composes: it must consume
  EXACTLY the derivation's bytes and hand the rest back untouched.

  A USEFUL COROLLARY, PROVED ONCE.  A grammar with a sound and complete step
  parser is prefix-deterministic (`det_of_sound_complete`): two derivations that
  agree on a byte sequence up to a suffix agree on the value and on the split.
  That is what lets the module layer reason about a greedy decoder without
  assuming determinism anywhere.

  NOTHING HERE IS AXIOMATIC.  Every parser is a `def` by structural or bounded
  recursion; there is no `partial`, no `sorry`, no `native_decide`.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Faults

The decoder is total: every byte sequence either decodes or produces one of
these.  The constructors are diagnostic only -- no theorem below depends on
WHICH fault is produced, only on the fact that a fault is not `ok`. -/

/-- Why a decode failed. -/
inductive Fault where
  /-- input ended in the middle of a production -/
  | eof
  /-- an LEB128 field ran past its width bound -/
  | leb
  /-- no production of the grammar has this opcode -/
  | opcode
  /-- a byte sequence that is not the UTF-8 encoding of any name -/
  | utf8
  /-- a section's declared length disagrees with its contents -/
  | section_
  /-- a numeric field out of the range its sort admits -/
  | range
  /-- a side condition of the pinned production failed -/
  | side
  /-- bytes left over after the last section -/
  | trailing
  deriving DecidableEq, Repr, Inhabited

/-- A step parser: consumes a prefix of the input and returns the rest. -/
abbrev Step (α : Type) : Type := Bytes → Except Fault (α × Bytes)

/-- `p` derives only what the grammar `G` derives. -/
def Sound {α : Type} (G : Bytes → α → Prop) (p : Step α) : Prop :=
  ∀ bs x r, p bs = .ok (x, r) → ∃ b, bs = b ++ r ∧ G b x

/-- `p` derives everything the grammar `G` derives, consuming exactly the
derivation's bytes.  Stated with an arbitrary suffix `r`, which is what makes it
compose through concatenation. -/
def Complete {α : Type} (G : Bytes → α → Prop) (p : Step α) : Prop :=
  ∀ (b : Bytes) (x : α) (r : Bytes), G b x → p (b ++ r) = .ok (x, r)

/-- A grammar with a sound and complete step parser is prefix-deterministic.
Nothing below assumes determinism; it is derived here, once, from the two
properties that are actually proved. -/
theorem det_of_sound_complete {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (hs : Sound G p) (hc : Complete G p)
    {b₁ b₂ r₁ r₂ : Bytes} {x₁ x₂ : α}
    (h₁ : G b₁ x₁) (h₂ : G b₂ x₂) (heq : b₁ ++ r₁ = b₂ ++ r₂) :
    x₁ = x₂ ∧ b₁ = b₂ ∧ r₁ = r₂ := by
  have e₁ : p (b₁ ++ r₁) = .ok (x₁, r₁) := hc b₁ x₁ r₁ h₁
  have e₂ : p (b₁ ++ r₁) = .ok (x₂, r₂) := by rw [heq]; exact hc b₂ x₂ r₂ h₂
  have : (Except.ok (x₁, r₁) : Except Fault (α × Bytes)) = .ok (x₂, r₂) := by
    rw [← e₁, ← e₂]
  have hx : x₁ = x₂ ∧ r₁ = r₂ := by
    have := Except.ok.inj this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  refine ⟨hx.1, ?_, hx.2⟩
  have : b₁ ++ r₁ = b₂ ++ r₁ := by rw [heq, hx.2]
  exact List.append_cancel_right this
  -- `hs` is not needed for the argument, but the statement is only interesting
  -- when `p` is sound: without soundness `p` could be `fun bs => .ok (junk, bs)`.

/-! ## Byte primitives -/

/-- `tb` on a literal below `0x100` is the identity on the value. -/
theorem tb_val (n : Nat) (h : n < 0x100) : (tb n).val = n :=
  Nat.mod_eq_of_lt h

/-- Recover a terminal byte from its value. -/
theorem byte_eq_tb {b : Byte} {n : Nat} (hn : n < 0x100) (h : b.val = n) : b = tb n :=
  Subtype.ext (by rw [h, tb_val n hn])

/-- Read one byte. -/
def readByte : Step Byte
  | [] => .error .eof
  | b :: bs => .ok (b, bs)

theorem readByte_sound : Sound Bbyte readByte := by
  intro bs x r h
  cases bs with
  | nil => simp [readByte] at h
  | cons b bs =>
      simp [readByte] at h
      exact ⟨[b], by simp [h.1, h.2], h.1 ▸ Bbyte.mk b⟩

theorem readByte_complete : Complete Bbyte readByte := by
  intro b x r h
  cases h
  rfl

/-- Consume the terminal byte `0xNN`. -/
def expectByte (n : Nat) : Bytes → Except Fault Bytes
  | [] => .error .eof
  | b :: bs => if b.val = n then .ok bs else .error .opcode

theorem expectByte_ok {n : Nat} {bs r : Bytes} (hn : n < 0x100)
    (h : expectByte n bs = .ok r) : bs = tb n :: r := by
  cases bs with
  | nil => simp [expectByte] at h
  | cons b bs =>
      simp only [expectByte] at h
      split at h
      · rename_i hb
        have hbs : bs = r := by simpa using h
        rw [← hbs, byte_eq_tb hn hb]
      · simp at h

theorem expectByte_eq (n : Nat) (hn : n < 0x100) (r : Bytes) :
    expectByte n (tb n :: r) = .ok r := by
  simp [expectByte, tb_val n hn]

/-! ## Bounded permissive LEB128

`BuN(N)` and `BsN(N)` of `5.1-binary.values.spectec`, transcribed as decoders.
Non-minimal encodings inside the width bound are ACCEPTED, exactly as the pinned
grammar accepts them; the bound is the descending `N`. -/

/-- `grammar BuN(N)` as a decoder. -/
def decUN : Nat → Bytes → Except Fault (Nat × Bytes)
  | _, [] => .error .eof
  | N, n :: rest =>
      if n.val < 2 ^ 7 then
        (if n.val < 2 ^ N then .ok (n.val, rest) else .error .leb)
      else
        if 7 < N then
          match decUN (N - 7) rest with
          | .error e => .error e
          | .ok (m, r) => .ok (2 ^ 7 * m + (n.val - 2 ^ 7), r)
        else .error .leb

theorem decUN_lt : ∀ (bs : Bytes) (N v : Nat) (r : Bytes),
    decUN N bs = .ok (v, r) → v < 2 ^ N := by
  intro bs
  induction bs with
  | nil => intro N v r h; simp [decUN] at h
  | cons b bs ih =>
      intro N v r h
      rw [decUN] at h
      split at h
      · split at h
        · rename_i hlt
          have : v = b.val := by simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
          omega
        · simp at h
      · split at h
        · rename_i hN
          split at h
          · simp at h
          · rename_i m r' hm
            have hv : v = 2 ^ 7 * m + (b.val - 2 ^ 7) := by
              simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
            have hlt := ih (N - 7) m r' hm
            have hsplit : (2 : Nat) ^ 7 * 2 ^ (N - 7) = 2 ^ N := by
              rw [← Nat.pow_add]; congr 1; omega
            have h1 : 2 ^ 7 * (m + 1) ≤ 2 ^ 7 * 2 ^ (N - 7) := Nat.mul_le_mul_left _ hlt
            have h2 : 2 ^ 7 * (m + 1) = 2 ^ 7 * m + 2 ^ 7 := by rw [Nat.mul_add, Nat.mul_one]
            have hb : b.val < 0x100 := b.property
            omega
        · simp at h

theorem decUN_sound (N : Nat) : Sound (BuN N) (decUN N) := by
  intro bs
  induction bs generalizing N with
  | nil => intro v r h; simp [decUN] at h
  | cons b bs ih =>
      intro v r h
      rw [decUN] at h
      split at h
      · rename_i hb
        split at h
        · rename_i hN
          have hv : v = b.val := by simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
          have hr : bs = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
          exact ⟨[b], by simp [hr], by rw [hv]; exact BuN.last N b hb hN⟩
        · simp at h
      · rename_i hb
        split at h
        · rename_i hN
          split at h
          · simp at h
          · rename_i m r' hm
            have hv : v = 2 ^ 7 * m + (b.val - 2 ^ 7) := by
              simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
            have hr : r' = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
            obtain ⟨b', hb', hd⟩ := ih (N - 7) m r' hm
            refine ⟨b :: b', by simp [hb', hr], ?_⟩
            rw [hv]
            exact BuN.more N b b' m (by omega) hN hd
        · simp at h

theorem decUN_complete (N : Nat) : Complete (BuN N) (decUN N) := by
  intro b v r h
  induction h generalizing r with
  | last N n hlt hN =>
      show decUN N (n :: r) = _
      rw [decUN]
      simp [hlt, hN]
  | more N n bs m hge hN _ ih =>
      show decUN N (n :: (bs ++ r)) = _
      rw [decUN]
      have hnot : ¬ (n.val < 2 ^ 7) := by omega
      simp only [hnot, if_false, hN, if_true]
      rw [ih r]

/-- `grammar BsN(N)` as a decoder, transcribed with the pinned source's
continuation into `BuN`, defect and all (see `BinaryGrammar/Values.lean`). -/
def decSN (N : Nat) (bs : Bytes) : Except Fault (Int × Bytes) :=
  match bs with
  | [] => .error .eof
  | n :: rest =>
      if n.val < 2 ^ 6 then
        (if n.val < 2 ^ (N - 1) then .ok ((n.val : Int), rest) else .error .leb)
      else if n.val < 2 ^ 7 then
        (if (2 : Int) ^ 7 - (2 : Int) ^ (N - 1) ≤ (n.val : Int)
          then .ok ((n.val : Int) - (2 : Int) ^ 7, rest)
          else .error .leb)
      else
        if 7 < N then
          match decUN (N - 7) rest with
          | .error e => .error e
          | .ok (i, r) => .ok ((2 : Int) ^ 7 * (i : Int) + ((n.val : Int) - (2 : Int) ^ 7), r)
        else .error .leb

theorem decSN_sound (N : Nat) : Sound (BsN N) (decSN N) := by
  intro bs v r h
  cases bs with
  | nil => simp [decSN] at h
  | cons b bs =>
      rw [decSN] at h
      split at h
      · rename_i hb
        split at h
        · rename_i hN
          have hv : v = (b.val : Int) := by simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
          have hr : bs = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
          exact ⟨[b], by simp [hr], by rw [hv]; exact BsN.pos N b hb hN⟩
        · simp at h
      · rename_i hb
        split at h
        · rename_i hb7
          split at h
          · rename_i hN
            have hv : v = (b.val : Int) - (2 : Int) ^ 7 := by
              simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
            have hr : bs = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
            exact ⟨[b], by simp [hr], by rw [hv]; exact BsN.neg N b (by omega) hb7 hN⟩
          · simp at h
        · rename_i hb7
          split at h
          · rename_i hN
            split at h
            · simp at h
            · rename_i i r' hi
              have hv : v = (2 : Int) ^ 7 * (i : Int) + ((b.val : Int) - (2 : Int) ^ 7) := by
                simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
              have hr : r' = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
              obtain ⟨b', hb', hd⟩ := decUN_sound (N - 7) bs i r' hi
              refine ⟨b :: b', by simp [hb', hr], ?_⟩
              rw [hv]
              exact BsN.more N b b' i (by omega) hN hd
          · simp at h

theorem decSN_complete (N : Nat) : Complete (BsN N) (decSN N) := by
  intro b v r h
  cases h with
  | pos n h1 h2 =>
      show decSN N (n :: r) = _
      rw [decSN, if_pos h1, if_pos h2]
  | neg n h1 h2 h3 =>
      show decSN N (n :: r) = _
      have hnot : ¬ (n.val < 2 ^ 6) := by omega
      rw [decSN, if_neg hnot, if_pos h2, if_pos h3]
  | more n bs i h1 h2 h3 =>
      show decSN N (n :: (bs ++ r)) = _
      have hnot6 : ¬ (n.val < 2 ^ 6) := by omega
      have hnot7 : ¬ (n.val < 2 ^ 7) := by omega
      rw [decSN, if_neg hnot6, if_neg hnot7, if_pos h2,
        decUN_complete (N - 7) bs i r h3]

/-! ## The named width instances -/

/-- `grammar Bu32 : u32`. -/
def decU32 (bs : Bytes) : Except Fault (U32 × Bytes) :=
  match decUN 32 bs with
  | .error e => .error e
  | .ok (v, r) => if hv : v < 2 ^ 32 then .ok (⟨v, hv⟩, r) else .error .leb

theorem decU32_sound : Sound Bu32 decU32 := by
  intro bs x r h
  rw [decU32] at h
  split at h
  · simp at h
  · rename_i v r' hv
    split at h
    · obtain ⟨hxv, hrr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b, hb, hd⟩ := decUN_sound 32 bs v r' hv
      refine ⟨b, by rw [hb, hrr], ?_⟩
      show BuN 32 b x.val
      rw [← hxv]
      exact hd
    · simp at h

theorem decU32_complete : Complete Bu32 decU32 := by
  intro b x r h
  have h' : decUN 32 (b ++ r) = .ok (x.val, r) := decUN_complete 32 b x.val r h
  simp only [decU32, h', dif_pos x.property]

/-- `grammar Bu64 : u64`. -/
def decU64 (bs : Bytes) : Except Fault (U64 × Bytes) :=
  match decUN 64 bs with
  | .error e => .error e
  | .ok (v, r) => if hv : v < 2 ^ 64 then .ok (⟨v, hv⟩, r) else .error .leb

theorem decU64_sound : Sound Bu64 decU64 := by
  intro bs x r h
  rw [decU64] at h
  split at h
  · simp at h
  · rename_i v r' hv
    split at h
    · obtain ⟨hxv, hrr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b, hb, hd⟩ := decUN_sound 64 bs v r' hv
      refine ⟨b, by rw [hb, hrr], ?_⟩
      show BuN 64 b x.val
      rw [← hxv]
      exact hd
    · simp at h

theorem decU64_complete : Complete Bu64 decU64 := by
  intro b x r h
  have h' : decUN 64 (b ++ r) = .ok (x.val, r) := decUN_complete 64 b x.val r h
  simp only [decU64, h', dif_pos x.property]

/-- `grammar Bs33 : s33`, valued in `Int` for the reason `BsN` records. -/
def decS33 : Step Int := decSN 33

theorem decS33_sound : Sound Bs33 decS33 := decSN_sound 33
theorem decS33_complete : Complete Bs33 decS33 := decSN_complete 33

/-! ## A `Bu32` pinned to a literal, and prefixed opcodes -/

/-- `k:Bu32` with `k` a literal: the selector of a prefixed opcode, or the tag
of an element or data segment.  Non-minimal encodings of `k` are accepted, as
the grammar accepts them. -/
def decU32lit (k : Nat) (bs : Bytes) : Except Fault Bytes :=
  match decU32 bs with
  | .error e => .error e
  | .ok (x, r) => if x.val = k then .ok r else .error .opcode

theorem decU32lit_sound {k : Nat} {bs r : Bytes} (h : decU32lit k bs = .ok r) :
    ∃ b, bs = b ++ r ∧ Bu32lit k b := by
  rw [decU32lit] at h
  split at h
  · simp at h
  · rename_i x r' hx
    split at h
    · rename_i hk
      have hr : r' = r := by simpa using h
      obtain ⟨b, hb, hd⟩ := decU32_sound bs x r' hx
      exact ⟨b, by rw [hb, hr], ⟨x, hd, hk⟩⟩
    · simp at h

theorem decU32lit_complete {k : Nat} {b : Bytes} (r : Bytes) (h : Bu32lit k b) :
    decU32lit k (b ++ r) = .ok r := by
  obtain ⟨x, hx, hk⟩ := h
  simp only [decU32lit, decU32_complete b x r hx, hk, if_pos]

/-- `0xPP k:Bu32`: the shape of every `0xFB` / `0xFC` / `0xFD` opcode. -/
def decPrefixed (p k : Nat) (bs : Bytes) : Except Fault Bytes :=
  match expectByte p bs with
  | .error e => .error e
  | .ok bs' => decU32lit k bs'

theorem decPrefixed_sound {p k : Nat} (hp : p < 0x100) {bs r : Bytes}
    (h : decPrefixed p k bs = .ok r) : ∃ b, bs = b ++ r ∧ Bprefixed p k b := by
  rw [decPrefixed] at h
  split at h
  · simp at h
  · rename_i bs' hbs'
    have hsplit := expectByte_ok hp hbs'
    obtain ⟨b, hb, hd⟩ := decU32lit_sound h
    exact ⟨tb p :: b, by rw [hsplit, hb]; rfl, ⟨b, rfl, hd⟩⟩

theorem decPrefixed_complete {p k : Nat} (hp : p < 0x100) {b : Bytes} (r : Bytes)
    (h : Bprefixed p k b) : decPrefixed p k (b ++ r) = .ok r := by
  obtain ⟨bn, hbn, hd⟩ := h
  subst hbn
  show decPrefixed p k (tb p :: (bn ++ r)) = .ok r
  simp only [decPrefixed, expectByte_eq p hp, decU32lit_complete r hd]

/-! ## Repetition and lists -/

/-- `(el:BX)^n`. -/
def decRep {α : Type} (p : Step α) : Nat → Step (List α)
  | 0, bs => .ok ([], bs)
  | k + 1, bs =>
      match p bs with
      | .error e => .error e
      | .ok (x, bs') =>
          match decRep p k bs' with
          | .error e => .error e
          | .ok (xs, bs'') => .ok (x :: xs, bs'')

theorem decRep_sound {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (hp : Sound G p) (n : Nat) : Sound (Rep G n) (decRep p n) := by
  induction n with
  | zero =>
      intro bs xs r h
      simp [decRep] at h
      exact ⟨[], by simp [h.2], h.1 ▸ Rep.nil⟩
  | succ k ih =>
      intro bs xs r h
      rw [decRep] at h
      split at h
      · simp at h
      · rename_i x bs' hx
        split at h
        · simp at h
        · rename_i ys bs'' hys
          have hxs : xs = x :: ys := by simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
          have hr : bs'' = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
          obtain ⟨b₁, hb₁, hd₁⟩ := hp bs x bs' hx
          obtain ⟨b₂, hb₂, hd₂⟩ := ih bs' ys bs'' hys
          refine ⟨b₁ ++ b₂, ?_, ?_⟩
          · rw [hb₁, hb₂, hr, List.append_assoc]
          · rw [hxs]; exact Rep.cons b₁ x b₂ ys k hd₁ hd₂

theorem decRep_complete {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (hp : Complete G p) (n : Nat) : Complete (Rep G n) (decRep p n) := by
  intro b xs r h
  induction h generalizing r with
  | nil => rfl
  | cons b₁ x b₂ ys k hd₁ _ ih =>
      have hassoc : (b₁ ++ b₂) ++ r = b₁ ++ (b₂ ++ r) := List.append_assoc _ _ _
      rw [hassoc]
      simp only [decRep, hp b₁ x (b₂ ++ r) hd₁, ih r]

/-- `grammar Blist(BX)`: a `Bu32` count and that many elements. -/
def decList {α : Type} (p : Step α) (bs : Bytes) : Except Fault (List α × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (n, bs') => decRep p n.val bs'

theorem decList_sound {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (hp : Sound G p) : Sound (Blist G) (decList p) := by
  intro bs xs r h
  rw [decList] at h
  split at h
  · simp at h
  · rename_i n bs' hn
    obtain ⟨b₁, hb₁, hd₁⟩ := decU32_sound bs n bs' hn
    obtain ⟨b₂, hb₂, hd₂⟩ := decRep_sound hp n.val bs' xs r h
    exact ⟨b₁ ++ b₂, by rw [hb₁, hb₂, List.append_assoc], Blist.mk b₁ b₂ n xs hd₁ hd₂⟩

theorem decList_complete {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (hp : Complete G p) : Complete (Blist G) (decList p) := by
  intro b xs r h
  cases h with
  | mk bn bs n _ys hn hrep =>
      have hassoc : (bn ++ bs) ++ r = bn ++ (bs ++ r) := List.append_assoc _ _ _
      rw [hassoc]
      simp only [decList, decU32_complete bn n (bs ++ r) hn]
      exact decRep_complete hp n.val bs xs r hrep

/-! ## Raw bytes -/

/-- `Rep Bbyte n` consumes exactly the bytes it produces. -/
theorem Rep_Bbyte_eq : ∀ {n : Nat} {bs : Bytes} {bl : List Byte},
    Rep Bbyte n bs bl → bs = bl := by
  intro n bs bl h
  induction h with
  | nil => rfl
  | cons b x bs xs k hb _ ih => cases hb; simp [ih]

/-- Conversely, any byte list is its own `Rep Bbyte`. -/
theorem Rep_Bbyte_self : ∀ bl : List Byte, Rep Bbyte bl.length bl bl := by
  intro bl
  induction bl with
  | nil => exact Rep.nil
  | cons b bs ih =>
      exact Rep.cons [b] b bs bs bs.length (Bbyte.mk b) ih

theorem Star_Bbyte_self (bl : List Byte) : Star Bbyte bl bl := ⟨bl.length, Rep_Bbyte_self bl⟩

/-- `(b:Bbyte)^n`, as a decoder. -/
def decBytes (n : Nat) : Step (List Byte) := decRep readByte n

theorem decBytes_sound (n : Nat) : Sound (Rep Bbyte n) (decBytes n) :=
  decRep_sound readByte_sound n

theorem decBytes_complete (n : Nat) : Complete (Rep Bbyte n) (decBytes n) :=
  decRep_complete readByte_complete n

/-! ## Floating point -/

/-- `grammar BfN(N) : fN(N)`. -/
def decFN (N : Nat) (bs : Bytes) : Except Fault (FN N × Bytes) :=
  match decBytes (N / 8) bs with
  | .error e => .error e
  | .ok (bl, r) =>
      match invFbytes N bl with
      | none => .error .range
      | some v => .ok (v, r)

theorem decFN_sound (N : Nat) : Sound (BfN N) (decFN N) := by
  intro bs v r h
  rw [decFN] at h
  split at h
  · simp at h
  · rename_i bl r' hbl
    split at h
    · simp at h
    · rename_i w hw
      have hv : v = w := by simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
      have hr : r' = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
      obtain ⟨b, hb, hd⟩ := decBytes_sound (N / 8) bs bl r' hbl
      exact ⟨b, by rw [hb, hr], ⟨bl, hd, by rw [hw, hv]⟩⟩

theorem decFN_complete (N : Nat) : Complete (BfN N) (decFN N) := by
  intro b v r h
  obtain ⟨bl, hrep, hinv⟩ := h
  simp only [decFN, decBytes_complete (N / 8) b bl r hrep, hinv]

/-- `grammar Bf32 : f32`. -/
def decF32 : Step F32 := decFN 32
/-- `grammar Bf64 : f64`. -/
def decF64 : Step F64 := decFN 64

theorem decF32_sound : Sound Bf32 decF32 := decFN_sound 32
theorem decF32_complete : Complete Bf32 decF32 := decFN_complete 32
theorem decF64_sound : Sound Bf64 decF64 := decFN_sound 64
theorem decF64_complete : Complete Bf64 decF64 := decFN_complete 64

/-! ## Indices

Every index sort of `5.1` is `x:Bu32 => x`, so one parser serves them all; the
named aliases below exist so that the instruction layer reads like the source. -/

/-- `grammar Btypeidx` and its ten siblings. -/
def decIdx : Step Idx := decU32

theorem decIdx_sound : Sound Bu32 decIdx := decU32_sound
theorem decIdx_complete : Complete Bu32 decIdx := decU32_complete

/-- `grammar Blaneidx : laneidx = | l:Bbyte => l`. -/
def decLaneIdx (bs : Bytes) : Except Fault (LaneIdx × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: rest => .ok (⟨b.val, b.property⟩, rest)

theorem decLaneIdx_sound : Sound Blaneidx decLaneIdx := by
  intro bs x r h
  cases bs with
  | nil => simp [decLaneIdx] at h
  | cons b bs =>
      rw [decLaneIdx] at h
      have hx : x = (⟨b.val, b.property⟩ : LaneIdx) := by
        simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
      have hr : bs = r := by simpa using (Prod.mk.inj (Except.ok.inj h)).2
      exact ⟨[b], by simp [hr], Blaneidx.mk b x (by rw [hx])⟩

theorem decLaneIdx_complete : Complete Blaneidx decLaneIdx := by
  intro b x r h
  cases h with
  | mk bb _ll hl =>
      show decLaneIdx (bb :: r) = _
      have hb : (⟨bb.val, bb.property⟩ : LaneIdx) = x := Subtype.ext hl.symm
      simp only [decLaneIdx, hb]

end WasmGemmGnaf.Wasm.Core.Decode
