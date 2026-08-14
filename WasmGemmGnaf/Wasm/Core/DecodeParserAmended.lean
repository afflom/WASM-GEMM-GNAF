/-
  The executable AMD-007 / DEV-007 signed-LEB repair and its independent
  soundness/completeness proofs.

  The pinned parser in `DecodeParser.lean` deliberately follows the defective
  vendored production.  This parser follows the amended `Binary.BsN'`
  relation, recursively decoding the signed continuation.
-/
import WasmGemmGnaf.Wasm.Core.DecodeParser
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.ValuesAmended

set_option autoImplicit false
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-- The amended signed bounded LEB128 parser. -/
def decSN' (N : Nat) (bs : Bytes) : Except Fault (Int × Bytes) :=
  match bs with
  | [] => .error .eof
  | n :: rest =>
      if n.val < 2 ^ 6 then
        if n.val < 2 ^ (N - 1) then .ok ((n.val : Int), rest) else .error .leb
      else if n.val < 2 ^ 7 then
        if (2 : Int) ^ 7 - (2 : Int) ^ (N - 1) ≤ (n.val : Int) then
          .ok ((n.val : Int) - (2 : Int) ^ 7, rest)
        else .error .leb
      else if 7 < N then
        match decSN' (N - 7) rest with
        | .error e => .error e
        | .ok (i, r) =>
            .ok ((2 : Int) ^ 7 * i + ((n.val : Int) - (2 : Int) ^ 7), r)
      else .error .leb
termination_by N
decreasing_by omega

theorem decSN'_sound (N : Nat) : Sound (BsN' N) (decSN' N) := by
  intro bs
  induction bs generalizing N with
  | nil => intro v r h; simp [decSN'] at h
  | cons b bs ih =>
      intro v r h
      rw [decSN'] at h
      split at h
      · rename_i hb
        split at h
        · rename_i hN
          have hv : v = (b.val : Int) := by
            simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
          have hr : bs = r := by
            simpa using (Prod.mk.inj (Except.ok.inj h)).2
          exact ⟨[b], by simp [hr], by rw [hv]; exact BsN'.pos N b hb hN⟩
        · simp at h
      · rename_i hb
        split at h
        · rename_i hb7
          split at h
          · rename_i hN
            have hv : v = (b.val : Int) - (2 : Int) ^ 7 := by
              simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
            have hr : bs = r := by
              simpa using (Prod.mk.inj (Except.ok.inj h)).2
            exact ⟨[b], by simp [hr], by rw [hv]; exact BsN'.neg N b (by omega) hb7 hN⟩
          · simp at h
        · rename_i hb7
          split at h
          · rename_i hN
            split at h
            · simp at h
            · rename_i i r' hi
              have hv :
                  v = (2 : Int) ^ 7 * i + ((b.val : Int) - (2 : Int) ^ 7) := by
                simpa using ((Prod.mk.inj (Except.ok.inj h)).1).symm
              have hr : r' = r := by
                simpa using (Prod.mk.inj (Except.ok.inj h)).2
              obtain ⟨b', hb', hd⟩ := ih (N - 7) i r' hi
              refine ⟨b :: b', by simp [hb', hr], ?_⟩
              rw [hv]
              exact BsN'.more N b b' i (by omega) hN hd
          · simp at h

theorem decSN'_complete (N : Nat) : Complete (BsN' N) (decSN' N) := by
  intro b v r h
  induction h generalizing r with
  | pos N n h1 h2 =>
      show decSN' N (n :: r) = _
      rw [decSN', if_pos h1, if_pos h2]
  | neg N n h1 h2 h3 =>
      show decSN' N (n :: r) = _
      have hnot : ¬n.val < 2 ^ 6 := by omega
      rw [decSN', if_neg hnot, if_pos h2, if_pos h3]
  | more N n bs i h1 h2 _ ih =>
      show decSN' N (n :: (bs ++ r)) = _
      have hnot6 : ¬n.val < 2 ^ 6 := by omega
      have hnot7 : ¬n.val < 2 ^ 7 := by omega
      rw [decSN', if_neg hnot6, if_neg hnot7, if_pos h2, ih r]

/-- The amended signed-33 parser used by heap and block type indices. -/
def decS33' : Step Int := decSN' 33

theorem decS33'_sound : Sound Bs33' decS33' := decSN'_sound 33
theorem decS33'_complete : Complete Bs33' decS33' := decSN'_complete 33

/-! ## One authority-parameterized signed leaf -/

/-- The signed-33 parser selected by the same finite authority as the
declarative grammar.  The global instance keeps existing calls pinned. -/
def decS33For [authority : BinaryAuthority] : Step Int :=
  match authority.revision with
  | .pinned => decS33
  | .amended => decS33'

theorem decS33For_sound [authority : BinaryAuthority] :
    Sound Bs33For decS33For := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact decS33_sound
      | amended => exact decS33'_sound

theorem decS33For_complete [authority : BinaryAuthority] :
    Complete Bs33For decS33For := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact decS33_complete
      | amended => exact decS33'_complete

@[simp] theorem decS33For_pinned :
    @decS33For pinnedBinaryAuthority = decS33 := rfl

@[simp] theorem decS33For_amended :
    @decS33For amendedBinaryAuthority = decS33' := rfl

/-- Prefix determinism of the amended grammar. -/
theorem BsN'_det {N : Nat} {b₁ b₂ r₁ r₂ : Bytes} {i₁ i₂ : Int}
    (h₁ : BsN' N b₁ i₁) (h₂ : BsN' N b₂ i₂)
    (heq : b₁ ++ r₁ = b₂ ++ r₂) :
    i₁ = i₂ ∧ b₁ = b₂ ∧ r₁ = r₂ :=
  det_of_sound_complete (decSN'_sound N) (decSN'_complete N) h₁ h₂ heq

/-- In particular, the amended relation does not retain the pinned positive
interpretation of the two-byte defect witness. -/
theorem not_BsN'_two_byte_positive :
    ¬BsN' 14 [Byte.ofNat 0xFF, Byte.ofNat 0x7E] 16255 := by
  intro h
  have hv := (BsN'_det BsN'_two_byte_negative h
    (r₁ := []) (r₂ := []) rfl).1
  omega

end WasmGemmGnaf.Wasm.Core.Decode
