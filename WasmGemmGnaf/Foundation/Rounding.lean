import WasmGemmGnaf.Foundation.FloatBits

set_option autoImplicit false

/-! Exact executable round-to-nearest, ties-to-even arithmetic shared by the
Core numeric semantics and the GEMM arithmetic contracts. -/

namespace WasmGemmGnaf.Foundation

/-! ## Round to nearest, ties to even (SPEC §8.2)

"All floating modes use round-to-nearest, ties-to-even". -/

/-- Round `den * q + r` divided by `den` to the nearest integer, ties to even. -/
def rneCore (den q r : Nat) : Nat :=
  if 2 * r < den then q
  else if den < 2 * r then q + 1
  else if q % 2 = 0 then q else q + 1

/-- Round `num / den` to the nearest natural, ties to even. -/
def rneNat (num den : Nat) : Nat := rneCore den (num / den) (num % den)

/-- Round a rational `num / den` to the nearest integer, ties to even.  Rounding
is sign-symmetric, as IEEE round-to-nearest requires. -/
def rne (num : Int) (den : Nat) : Int :=
  if 0 ≤ num then (rneNat num.toNat den : Int) else -((rneNat (-num).toNat den : Nat) : Int)

theorem rneCore_le (den q r : Nat) : q ≤ rneCore den q r ∧ rneCore den q r ≤ q + 1 := by
  unfold rneCore
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- The rounded value is within one half-unit of the exact quotient: both
`2·value ≤ (2·N+1)·den` and `2·N·den ≤ 2·value + den` hold. -/
theorem rneCore_spec (den q r : Nat) (hden : 0 < den) (hr : r < den) :
    2 * (den * q + r) ≤ (2 * rneCore den q r + 1) * den ∧
      2 * rneCore den q r * den ≤ 2 * (den * q + r) + den := by
  have key : ∀ a : Nat, (2 * a + 1) * den = 2 * (den * a) + den := by
    intro a
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm a den]
  have key2 : ∀ a : Nat, 2 * a * den = 2 * (den * a) := by
    intro a
    rw [Nat.mul_assoc, Nat.mul_comm a den]
  have hs : den * (q + 1) = den * q + den := Nat.mul_succ den q
  have k1 := key q
  have k2 := key (q + 1)
  have k3 := key2 q
  have k4 := key2 (q + 1)
  unfold rneCore
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem rneNat_spec (num den : Nat) (hden : 0 < den) :
    2 * num ≤ (2 * rneNat num den + 1) * den ∧
      2 * rneNat num den * den ≤ 2 * num + den := by
  have hnum : den * (num / den) + num % den = num := Nat.div_add_mod num den
  have hr : num % den < den := Nat.mod_lt _ hden
  have h := rneCore_spec den (num / den) (num % den) hden hr
  rw [hnum] at h
  exact h

/-- Ties really go to even. -/
theorem rneCore_tie_even (den q r : Nat) (h : 2 * r = den) :
    rneCore den q r % 2 = 0 := by
  unfold rneCore
  rw [if_neg (by omega), if_neg (by omega)]
  split <;> omega

theorem rneNat_tie_even (num den : Nat) (h : 2 * (num % den) = den) :
    rneNat num den % 2 = 0 :=
  rneCore_tie_even den (num / den) (num % den) h

theorem rneCore_exact (den q : Nat) (hden : 0 < den) : rneCore den q 0 = q := by
  unfold rneCore
  rw [if_pos (by omega)]

theorem rneNat_of_dvd (num den : Nat) (hden : 0 < den) (h : num % den = 0) :
    rneNat num den = num / den := by
  simp only [rneNat, h]
  exact rneCore_exact den (num / den) hden

@[simp] theorem rneNat_zero (den : Nat) (hden : 0 < den) : rneNat 0 den = 0 := by
  simp [rneNat, rneCore, hden]

@[simp] theorem rne_zero (den : Nat) (hden : 0 < den) : rne 0 den = 0 := by
  simp [rne, rneNat_zero den hden]

/-- Rounding is sign-symmetric. -/
theorem rne_neg (num : Int) (den : Nat) (hden : 0 < den) :
    rne (-num) den = - rne num den := by
  rcases Int.lt_trichotomy num 0 with h | h | h
  · rw [rne, rne, if_pos (by omega), if_neg (by omega)]
    simp
  · subst h
    simp [rne_zero den hden]
  · rw [rne, rne, if_neg (by omega), if_pos (by omega)]
    simp


end WasmGemmGnaf.Foundation
