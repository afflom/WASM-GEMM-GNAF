import WasmGemmGnaf.Foundation.Rounding

set_option autoImplicit false
set_option exponentiation.threshold 400
set_option maxRecDepth 8000

/-!
# Exact binary floating arithmetic

This neutral executable kernel owns exact dyadics, finite IEEE decoding, and
round-to-nearest-ties-to-even.  Both Core numerics and GEMM import it downward;
it imports neither WebAssembly nor the GEMM problem layer.
-/

namespace WasmGemmGnaf.Foundation

/-! ## Bit length

Used by the rounding function to locate the binade of an exact dyadic.  The
fuel argument makes the recursion structural, so the definition reduces in the
kernel; `bitLen_lt` and `le_bitLen` prove it really is the binary length. -/

/-- Fuelled binary length. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLenAux fuel (n / 2) + 1

/-- Binary length: the least `w` with `n < 2 ^ w`. -/
def bitLen (n : Nat) : Nat := bitLenAux n n

theorem bitLenAux_zero : ∀ fuel : Nat, bitLenAux fuel 0 = 0 := by
  intro fuel; cases fuel <;> simp [bitLenAux]

theorem bitLenAux_pos : ∀ (fuel n : Nat), n ≤ fuel → 0 < n → 0 < bitLenAux fuel n := by
  intro fuel
  cases fuel with
  | zero => intro n h hp; omega
  | succ f =>
    intro n _ hp
    have hn : ¬ n = 0 := by omega
    simp [bitLenAux, hn]

theorem bitLenAux_lt : ∀ (fuel n : Nat), n ≤ fuel → n < 2 ^ bitLenAux fuel n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n h
    have hz : n = 0 := by omega
    subst hz
    simp [bitLenAux]
  | succ f ih =>
    intro n h
    by_cases hn : n = 0
    · subst hn; simp [bitLenAux]
    · have hhalf : n / 2 ≤ f := by omega
      have := ih (n / 2) hhalf
      have hb : bitLenAux (f + 1) n = bitLenAux f (n / 2) + 1 := by
        simp [bitLenAux, hn]
      rw [hb, Nat.pow_succ]
      omega

theorem le_bitLenAux : ∀ (fuel n : Nat), n ≤ fuel → 0 < n →
    2 ^ (bitLenAux fuel n - 1) ≤ n := by
  intro fuel
  induction fuel with
  | zero => intro n h hp; omega
  | succ f ih =>
    intro n h hp
    have hn : ¬ n = 0 := by omega
    have hb : bitLenAux (f + 1) n = bitLenAux f (n / 2) + 1 := by
      simp [bitLenAux, hn]
    rw [hb]
    by_cases hh : n / 2 = 0
    · rw [hh, bitLenAux_zero]
      simpa using hp
    · have hhalf : n / 2 ≤ f := by omega
      have hle := ih (n / 2) hhalf (by omega)
      have hbpos : 0 < bitLenAux f (n / 2) := bitLenAux_pos f (n / 2) hhalf (by omega)
      have hpow : 2 * 2 ^ (bitLenAux f (n / 2) - 1) = 2 ^ bitLenAux f (n / 2) := by
        rw [← Nat.pow_succ']
        congr 1
        omega
      simp only [Nat.add_sub_cancel]
      omega

/-- `n` is strictly below `2 ^ bitLen n`. -/
theorem bitLen_lt (n : Nat) : n < 2 ^ bitLen n := bitLenAux_lt n n (Nat.le_refl n)

/-- `bitLen` is not larger than it must be. -/
theorem le_bitLen {n : Nat} (h : 0 < n) : 2 ^ (bitLen n - 1) ≤ n :=
  le_bitLenAux n n (Nat.le_refl n) h

theorem bitLen_zero : bitLen 0 = 0 := rfl
theorem bitLen_one : bitLen 1 = 1 := rfl

/-- The minimum number of bits a mathematical integer needs in the declared
signedness (SPEC §8.3's checked-overflow detail). -/
def bitsRequired (signed : Bool) (z : Int) : Nat :=
  if signed then
    (if 0 ≤ z then bitLen z.toNat + 1 else bitLen (-z - 1).toNat + 1)
  else
    (if z < 0 then 2 ^ 64 - 1 else bitLen z.toNat)

/-! ## Exact dyadic values

An exact binary value `num · 2 ^ exp`.  Products and sums of dyadics are exact;
this is the carrier both float modes reduce through. -/

/-- An exact dyadic rational `num · 2 ^ exp`. -/
structure Dyadic where
  /-- Signed numerator. -/
  num : Int
  /-- Binary exponent. -/
  exp : Int
  deriving DecidableEq, Repr, Inhabited

namespace Dyadic

/-- Exact zero. -/
def zero : Dyadic := ⟨0, 0⟩

/-- Exact product. -/
def mul (a b : Dyadic) : Dyadic := ⟨a.num * b.num, a.exp + b.exp⟩

/-- Exact sum, at the finer of the two exponents. -/
def add (a b : Dyadic) : Dyadic :=
  let e := min a.exp b.exp
  ⟨a.num * 2 ^ (a.exp - e).toNat + b.num * 2 ^ (b.exp - e).toNat, e⟩

@[simp] theorem zero_num : zero.num = 0 := rfl

theorem mul_num (a b : Dyadic) : (a.mul b).num = a.num * b.num := rfl

theorem add_zero_left (b : Dyadic) (h : 0 ≤ b.exp) :
    (zero.add b).num = b.num * 2 ^ b.exp.toNat := by
  simp only [add, zero, Int.zero_mul, Int.zero_add]
  have : min (0 : Int) b.exp = 0 := by omega
  simp [this]

end Dyadic

/-! ## Exact float values

A decoded operand is either the NaN class, a signed infinity, or an exact
finite dyadic.  The definitions below give the neutral IEEE special-value
tables used by every higher layer. -/

/-- An exactly represented floating operand or intermediate. -/
inductive EVal
  /-- A NaN (payload already canonicalized). -/
  | nan
  /-- A signed infinity. -/
  | inf (sign : Bool)
  /-- An exact finite dyadic. -/
  | num (d : Dyadic)
  deriving DecidableEq, Repr, Inhabited

/-- Exact product of two operands: IEEE special-value cases followed by exact
dyadic multiplication. -/
def evalMul : EVal → EVal → EVal
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf s, .inf t => .inf (xor s t)
  | .inf s, .num d => if d.num = 0 then .nan else .inf (xor s (decide (d.num < 0)))
  | .num d, .inf t => if d.num = 0 then .nan else .inf (xor (decide (d.num < 0)) t)
  | .num a, .num b => .num (a.mul b)

/-- Exact sum of two operands: the special-value table, then the exact dyadic
sum. -/
def evalAdd : EVal → EVal → EVal
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf s, .inf t => if s = t then .inf s else .nan
  | .inf s, .num _ => .inf s
  | .num _, .inf t => .inf t
  | .num a, .num b => .num (a.add b)

/-- `0 × infinity` is a NaN, as SPEC §8.2 requires. -/
theorem evalMul_zero_inf (s : Bool) : evalMul (.num Dyadic.zero) (.inf s) = .nan := rfl

/-- Adding opposite infinities is a NaN. -/
theorem evalAdd_opposite_inf : evalAdd (.inf true) (.inf false) = .nan := rfl

/-- Adding equal-signed infinities is that infinity. -/
theorem evalAdd_same_inf (s : Bool) : evalAdd (.inf s) (.inf s) = .inf s := by
  cases s <;> rfl

/-! ## Decoding a stored pattern to an exact value -/

/-- Signed embedding of a magnitude. -/
def signedNat (s : Bool) (v : Nat) : Int := if s then -(v : Int) else (v : Int)

/-- The exponent of the subnormal binade of a format. -/
def subnormalExp (f : FloatFormat) : Int := 1 - (f.bias : Int) - (f.mantBits : Int)

/-- Decode a stored bit pattern of format `f` to its exact value. -/
def evalOfBits (f : FloatFormat) (bits : Nat) : EVal :=
  match f.decode bits with
  | .nan _ _ _ => .nan
  | .infinity s => .inf s
  | .zero _ => .num Dyadic.zero
  | .subnormal s m => .num ⟨signedNat s m, subnormalExp f⟩
  | .normal s e m =>
      .num ⟨signedNat s (2 ^ f.mantBits + m), (e : Int) - (f.bias : Int) - (f.mantBits : Int)⟩

/-! ## Round-to-nearest, ties-to-even, into a format

Gradual underflow, IEEE sign rules for nonzero results, overflow to signed
infinity, and positive sign for an exact zero sum. -/

/-- `round (N · 2 ^ exp / 2 ^ q)`, ties to even.  Exact when `q ≤ exp`. -/
def roundShift (N : Nat) (exp q : Int) : Nat :=
  if q ≤ exp then N * 2 ^ (exp - q).toNat else rneNat N (2 ^ (q - exp).toNat)

/-- The exact numerator and positive power-of-two denominator rounded by
`roundShift`. -/
def roundShiftRatio (N : Nat) (exp q : Int) : Nat × Nat :=
  if q ≤ exp then (N * 2 ^ (exp - q).toNat, 1)
  else (N, 2 ^ (q - exp).toNat)

/-- `roundShift` is nearest to its exact scaled quotient: the two inequalities
say its error is at most one half unit. -/
theorem roundShift_spec (N : Nat) (exp q : Int) :
    let p := roundShiftRatio N exp q
    2 * p.1 ≤ (2 * roundShift N exp q + 1) * p.2 ∧
      2 * roundShift N exp q * p.2 ≤ 2 * p.1 + p.2 := by
  by_cases h : q ≤ exp
  · simp [roundShiftRatio, roundShift, h]
  · simp only [roundShiftRatio, roundShift, h, ↓reduceIte]
    exact rneNat_spec N (2 ^ (q - exp).toNat) (Nat.two_pow_pos _)

/-- At an exact half-unit, `roundShift` selects an even significand. -/
theorem roundShift_tie_even (N : Nat) (exp q : Int) (h : ¬ q ≤ exp)
    (htie : 2 * (N % 2 ^ (q - exp).toNat) = 2 ^ (q - exp).toNat) :
    roundShift N exp q % 2 = 0 := by
  simp only [roundShift, h, ↓reduceIte]
  exact rneNat_tie_even N (2 ^ (q - exp).toNat) htie

/-- Assemble a rounded significand at quantum `q0`, including carry,
subnormal encoding, and overflow to infinity.  All three exact arithmetic
kernels use this one boundary function. -/
def packRoundedSignificand (f : FloatFormat) (neg : Bool) (sig0 : Nat)
    (q0 : Int) : Nat :=
  let carried := decide (sig0 = 2 ^ (f.mantBits + 1))
  let sig := if carried then 2 ^ f.mantBits else sig0
  let q := if carried then q0 + 1 else q0
  if sig = 0 then f.pack neg 0 0
  else if sig < 2 ^ f.mantBits then f.pack neg 0 sig
  else
    let E : Int := q + (f.mantBits : Int) + (f.bias : Int)
    if (f.expMax : Int) ≤ E then f.pack neg f.expMax 0
    else f.pack neg E.toNat (sig - 2 ^ f.mantBits)

@[simp] theorem packRoundedSignificand_zero (f : FloatFormat) (neg : Bool)
    (q0 : Int) : packRoundedSignificand f neg 0 q0 = f.pack neg 0 0 := by
  have hpow : (0 : Nat) < 2 ^ (f.mantBits + 1) := Nat.two_pow_pos _
  have hne : ¬ (0 : Nat) = 2 ^ (f.mantBits + 1) := Nat.ne_of_lt hpow
  simp [packRoundedSignificand, hne]

/-- A nonzero rounded significand below the implicit leading bit is encoded as
a subnormal. -/
theorem packRoundedSignificand_subnormal (f : FloatFormat) (neg : Bool)
    (sig0 : Nat) (q0 : Int) (hpos : 0 < sig0) (hlt : sig0 < 2 ^ f.mantBits) :
    packRoundedSignificand f neg sig0 q0 = f.pack neg 0 sig0 := by
  have hpow : 2 ^ f.mantBits < 2 ^ (f.mantBits + 1) := by
    rw [Nat.pow_succ]
    have := Nat.two_pow_pos f.mantBits
    omega
  have hc : ¬ sig0 = 2 ^ (f.mantBits + 1) := by omega
  simp [packRoundedSignificand, hc, Nat.ne_of_gt hpos, hlt]

/-- A noncarrying significand with its implicit leading bit and an exponent
below the all-ones field is encoded as the corresponding finite normal. -/
theorem packRoundedSignificand_normal (f : FloatFormat) (neg : Bool)
    (sig0 : Nat) (q0 : Int) (hpos : 0 < sig0)
    (hlead : 2 ^ f.mantBits ≤ sig0)
    (hcarry : sig0 ≠ 2 ^ (f.mantBits + 1))
    (hE : ¬ (f.expMax : Int) ≤ q0 + (f.mantBits : Int) + (f.bias : Int)) :
    packRoundedSignificand f neg sig0 q0 =
      f.pack neg (q0 + (f.mantBits : Int) + (f.bias : Int)).toNat
        (sig0 - 2 ^ f.mantBits) := by
  simp [packRoundedSignificand, hcarry, Nat.ne_of_gt hpos,
    Nat.not_lt_of_ge hlead, hE]

/-- Reaching or crossing the all-ones exponent field produces signed
infinity; no finite out-of-range encoding is emitted. -/
theorem packRoundedSignificand_overflow (f : FloatFormat) (neg : Bool)
    (sig0 : Nat) (q0 : Int) (hpos : 0 < sig0)
    (hlead : 2 ^ f.mantBits ≤ sig0)
    (hcarry : sig0 ≠ 2 ^ (f.mantBits + 1))
    (hE : (f.expMax : Int) ≤ q0 + (f.mantBits : Int) + (f.bias : Int)) :
    packRoundedSignificand f neg sig0 q0 = f.pack neg f.expMax 0 := by
  simp [packRoundedSignificand, hcarry, Nat.ne_of_gt hpos,
    Nat.not_lt_of_ge hlead, hE]

/-- If carrying creates the next binade and that binade reaches the all-ones
exponent, the exact IEEE overflow result is signed infinity. -/
theorem packRoundedSignificand_carry_overflow (f : FloatFormat) (neg : Bool)
    (q0 : Int)
    (hE : (f.expMax : Int) ≤ q0 + 1 + (f.mantBits : Int) + (f.bias : Int)) :
    packRoundedSignificand f neg (2 ^ (f.mantBits + 1)) q0 =
      f.pack neg f.expMax 0 := by
  simp [packRoundedSignificand, hE]

/-- Round an exact dyadic into `f`. -/
def roundDyadic (f : FloatFormat) (d : Dyadic) : Nat :=
  if d.num = 0 then f.pack false 0 0
  else
    let neg := decide (d.num < 0)
    let N := d.num.natAbs
    let emin : Int := subnormalExp f
    let e : Int := (bitLen N : Int) - 1 + d.exp
    let q0 : Int := max emin (e - (f.mantBits : Int))
    let s0 : Nat := roundShift N d.exp q0
    packRoundedSignificand f neg s0 q0

/-- Every nonzero dyadic reaches the shared boundary packer through a
significand satisfying `roundShift_spec`. -/
theorem roundDyadic_eq_packRoundedSignificand (f : FloatFormat) (d : Dyadic)
    (hnz : d.num ≠ 0) :
    roundDyadic f d =
      let neg := decide (d.num < 0)
      let N := d.num.natAbs
      let e : Int := (bitLen N : Int) - 1 + d.exp
      let q0 : Int := max (subnormalExp f) (e - (f.mantBits : Int))
      packRoundedSignificand f neg (roundShift N d.exp q0) q0 := by
  simp [roundDyadic, hnz]

theorem roundDyadic_significand_spec (f : FloatFormat) (d : Dyadic) :
    let N := d.num.natAbs
    let e : Int := (bitLen N : Int) - 1 + d.exp
    let q0 : Int := max (subnormalExp f) (e - (f.mantBits : Int))
    let p := roundShiftRatio N d.exp q0
    2 * p.1 ≤ (2 * roundShift N d.exp q0 + 1) * p.2 ∧
      2 * roundShift N d.exp q0 * p.2 ≤ 2 * p.1 + p.2 := by
  exact roundShift_spec d.num.natAbs d.exp _

/-- Encode an exact value in `f`: the canonical quiet NaN for a NaN, the signed
infinity for an infinity, and the rounded pattern for a finite value. -/
def roundToFormat (f : FloatFormat) : EVal → Nat
  | .nan => f.canonicalQuietNaN
  | .inf s => f.pack s f.expMax 0
  | .num d => roundDyadic f d

/-- Every released deterministic mode canonicalizes its NaN output: no
unobserved payload freedom remains (SPEC §8.2). -/
theorem roundToFormat_nan (f : FloatFormat) :
    roundToFormat f .nan = f.canonicalQuietNaN := rfl

theorem roundToFormat_binary32_nan :
    roundToFormat FloatFormat.binary32 .nan = 0x7fc00000 := by decide

theorem roundToFormat_binary64_nan :
    roundToFormat FloatFormat.binary64 .nan = 0x7ff8000000000000 := by decide

/-- Exact `+0` rounds to `+0`. -/
theorem roundDyadic_zero (f : FloatFormat) : roundDyadic f Dyadic.zero = f.pack false 0 0 :=
  rfl

/-- Round a product of two `src`-format patterns into `dst`. -/
def fMulTo (srcA srcB dst : FloatFormat) (x y : Nat) : Nat :=
  roundToFormat dst (evalMul (evalOfBits srcA x) (evalOfBits srcB y))

/-- Round a sum of two `src`-format patterns into `dst`. -/
def fAddTo (src dst : FloatFormat) (x y : Nat) : Nat :=
  roundToFormat dst (evalAdd (evalOfBits src x) (evalOfBits src y))

/-- Round a `src`-format pattern into `dst`. -/
def fConv (src dst : FloatFormat) (x : Nat) : Nat :=
  roundToFormat dst (evalOfBits src x)

end WasmGemmGnaf.Foundation
