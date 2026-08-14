/-
  The one released implementation of the Core 3.0 numeric builtins.

  The SpecTec transcription in `Numerics.lean` intentionally leaves prose-level
  builtins as fields.  This file closes that boundary with exact, terminating
  Lean definitions.  Scalar floating operations use the full pinned profile:
  every allowed NaN sign and payload is enumerated.  Relaxed SIMD is rejected by
  the release profile; its implementation-defined choices are nevertheless fixed
  to alternative zero, the deterministic-profile choice.
-/
import WasmGemmGnaf.Foundation.ExactFloat
import WasmGemmGnaf.Wasm.Core.Numerics

set_option autoImplicit false
set_option exponentiation.threshold 400
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

open WasmGemmGnaf.Foundation

namespace ConcreteNumerics

/-! ## Width-independent representation utilities -/

/-- The two scalar formats admitted by Core 3.0. -/
def floatFormat? : Nat → Option FloatFormat
  | 32 => some FloatFormat.binary32
  | 64 => some FloatFormat.binary64
  | _ => none

def withSign {N : Nat} (sign : Bool) (mag : FNMag N) : FN N :=
  if sign then .neg mag else .pos mag

def fnSign {N : Nat} : FN N → Bool
  | .pos _ => false
  | .neg _ => true

def fnMag {N : Nat} : FN N → FNMag N
  | .pos mag | .neg mag => mag

def fnWithSign {N : Nat} (sign : Bool) (x : FN N) : FN N :=
  withSign sign (fnMag x)

def fnNeg {N : Nat} (x : FN N) : FN N := fnWithSign (!(fnSign x)) x

def fnAbs {N : Nat} (x : FN N) : FN N := fnWithSign false x

def fnCopySign {N : Nat} (x y : FN N) : FN N := fnWithSign (fnSign y) x

def fnIsNaN {N : Nat} (x : FN N) : Bool :=
  match fnMag x with
  | .nan _ => true
  | _ => false

def fnIsInf {N : Nat} (x : FN N) : Bool :=
  match fnMag x with
  | .inf => true
  | _ => false

def fnIsZero {N : Nat} (x : FN N) : Bool :=
  match fnMag x with
  | .subnorm 0 => true
  | _ => false

def fnNaNPayload? {N : Nat} (x : FN N) : Option Nat :=
  match fnMag x with
  | .nan m => some m
  | _ => none

/-- Structural Core float to its IEEE bit pattern.  The semantic callers only
pass `FN.wf` values; the total extension is deliberately not used to validate a
literal. -/
def fnBitsWith {N : Nat} (f : FloatFormat) (x : FN N) : Nat :=
  let s := fnSign x
  match fnMag x with
  | .norm m e => f.pack s (e + (f.bias : Int)).toNat m
  | .subnorm m => f.pack s 0 m
  | .inf => f.pack s f.expMax 0
  | .nan m => f.pack s f.expMax m

/-- IEEE bits back to the abstract Core float syntax. -/
def fnOfBitsWith {N : Nat} (f : FloatFormat) (bits : Nat) : FN N :=
  match f.decode bits with
  | .zero s => withSign s (.subnorm 0)
  | .subnormal s m => withSign s (.subnorm m)
  | .normal s e m => withSign s (.norm m ((e : Int) - (f.bias : Int)))
  | .infinity s => withSign s .inf
  | .nan s _ m => withSign s (.nan m)

def fnBits? {N : Nat} (x : FN N) : Option Nat :=
  (floatFormat? N).map (fun f => fnBitsWith f x)

def fnOfBits (N bits : Nat) : FN N :=
  match floatFormat? N with
  | some f => fnOfBitsWith f bits
  | none => .pos (.subnorm 0)

def bitValue : Bit → Nat
  | .b0 => 0
  | .b1 => 1

/-- Inverse of the source's most-significant-bit-first `$ibits_N`. -/
def invIbits (N : Nat) (bits : List Bit) : IN N :=
  Numerics.ofNatWrap N (bits.foldl (fun n b => 2 * n + bitValue b) 0)

/-- Little-endian bytes of an integer bit pattern. -/
def ibytes (N : Nat) (i : IN N) : List Byte :=
  (List.range (N / 8)).map (fun k => Byte.ofNat (i.val / 2 ^ (8 * k)))

def nbytes : (nt : NumType) → Num_ nt → List Byte
  | .i32, i => ibytes 32 i
  | .i64, i => ibytes 64 i
  | .f32, x => ibytes 32 (Numerics.ofNatWrap 32 (fnBitsWith FloatFormat.binary32 x))
  | .f64, x => ibytes 64 (Numerics.ofNatWrap 64 (fnBitsWith FloatFormat.binary64 x))

def vbytes : (vt : VecType) → VecLit vt.toVnn → List Byte
  | .v128, v => ibytes 128 v

def zbytes : (zt : StorageType) → Lit_ zt → List Byte
  | .val (.num nt), c => nbytes nt c
  | .val (.vec vt), c => vbytes vt c
  | .val (.ref _), c => nomatch c
  | .val .bot, c => nomatch c
  | .pack pt, c => ibytes pt.size c

/-! ## Integer builtins -/

def trailingZerosAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 1 then 0 else trailingZerosAux fuel (n / 2) + 1

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => n % 2 + popcountAux fuel (n / 2)

def bitReverse (N : Nat) (i : IN N) : IN N :=
  Numerics.ofNatWrap N
    ((List.range N).foldl (fun acc k => 2 * acc + i.val / 2 ^ k % 2) 0)

def iclz (N : Nat) (i : IN N) : IN N :=
  Numerics.ofNatWrap N (N - bitLen i.val)

def ictz (N : Nat) (i : IN N) : IN N :=
  Numerics.ofNatWrap N (if i.val = 0 then N else trailingZerosAux N i.val)

def ipopcnt (N : Nat) (i : IN N) : IN N :=
  Numerics.ofNatWrap N (popcountAux N i.val)

def inot (N : Nat) (i : IN N) : IN N :=
  Numerics.ofNatWrap N (2 ^ N - 1 - i.val)

def iand (N : Nat) (x y : IN N) : IN N :=
  Numerics.ofNatWrap N (Nat.land x.val y.val)

def iandnot (N : Nat) (x y : IN N) : IN N :=
  iand N x (inot N y)

def ior (N : Nat) (x y : IN N) : IN N :=
  Numerics.ofNatWrap N (Nat.lor x.val y.val)

def ixor (N : Nat) (x y : IN N) : IN N :=
  Numerics.ofNatWrap N (Nat.xor x.val y.val)

def shiftCount (N n : Nat) : Nat := if N = 0 then 0 else n % N

def ishl (N : Nat) (x : IN N) (count : U32) : IN N :=
  Numerics.ofNatWrap N (x.val * 2 ^ shiftCount N count.val)

def ishr (N : Nat) (sx : Sx) (x : IN N) (count : U32) : IN N :=
  let k := shiftCount N count.val
  match sx with
  | .u => Numerics.ofNatWrap N (x.val / 2 ^ k)
  | .s => Numerics.inv_signed_ N (Int.ediv (Numerics.signed_ N x) (2 ^ k : Nat))

def irotl (N : Nat) (x count : IN N) : IN N :=
  if N = 0 then inZero N
  else
    let k := count.val % N
    Numerics.ofNatWrap N (x.val * 2 ^ k + x.val / 2 ^ (N - k))

def irotr (N : Nat) (x count : IN N) : IN N :=
  if N = 0 then inZero N
  else
    let k := count.val % N
    Numerics.ofNatWrap N (x.val / 2 ^ k + x.val * 2 ^ (N - k))

def ibitselect (N : Nat) (x y mask : IN N) : IN N :=
  ior N (iand N x mask) (iand N y (inot N mask))

def iavgr (N : Nat) (sx : Sx) (x y : IN N) : IN N :=
  match sx with
  | .u => Numerics.ofNatWrap N ((x.val + y.val + 1) / 2)
  | .s => Numerics.inv_signed_ N
      (Int.ediv (Numerics.signed_ N x + Numerics.signed_ N y + 1) 2)

def iq15mulrSat (N : Nat) (sx : Sx) (x y : IN N) : IN N :=
  match sx with
  | .s =>
      let z := Int.ediv (Numerics.signed_ N x * Numerics.signed_ N y + 2 ^ 14) (2 ^ 15)
      Numerics.inv_signed_ N (Numerics.sat_s_ N z)
  | .u =>
      Numerics.ofNatWrap N
        (Numerics.sat_u_ N (Int.ediv ((x.val * y.val + 2 ^ 14 : Nat) : Int) (2 ^ 15)))

def irelaxedQ15mulr (N : Nat) (sx : Sx) (x y : IN N) : List (IN N) :=
  [iq15mulrSat N sx x y]

def irelaxedLaneselect (N : Nat) (x y mask : IN N) : List (IN N) :=
  [ibitselect N x y mask]

/-! ## Exact finite arithmetic helpers -/

def finiteDyadic? {N : Nat} (f : FloatFormat) (x : FN N) : Option Foundation.Dyadic :=
  let signed (n : Nat) : Int := if fnSign x then -(n : Int) else (n : Int)
  match fnMag x with
  | .norm m e => some ⟨signed (2 ^ f.mantBits + m), e - (f.mantBits : Int)⟩
  | .subnorm m => some ⟨signed m, subnormalExp f⟩
  | .inf | .nan _ => none

def compareDyadic (a b : Foundation.Dyadic) : Ordering :=
  let e := min a.exp b.exp
  compare (a.num * 2 ^ (a.exp - e).toNat) (b.num * 2 ^ (b.exp - e).toNat)

def compareFloat? {N : Nat} (f : FloatFormat) (x y : FN N) : Option Ordering :=
  if fnIsNaN x || fnIsNaN y then none
  else
    match fnMag x, fnMag y with
    | .inf, .inf => some (compare (fnSign x) (fnSign y)).swap
    | .inf, _ => some (if fnSign x then .lt else .gt)
    | _, .inf => some (if fnSign y then .gt else .lt)
    | _, _ =>
        match finiteDyadic? f x, finiteDyadic? f y with
        | some a, some b => some (compareDyadic a b)
        | _, _ => none

def canonicalPayload (f : FloatFormat) : Nat := f.quietBitMask

def canonicalNaNs {N : Nat} (f : FloatFormat) : List (FN N) :=
  [withSign false (.nan f.quietBitMask), withSign true (.nan f.quietBitMask)]

/-- All arithmetic NaNs, both signs.  This list is intentionally large for
binary64: the Core relation itself permits every quiet payload, and replacing
it by a chosen representative would make successor enumeration incomplete. -/
def arithmeticNaNs {N : Nat} (f : FloatFormat) : List (FN N) :=
  (List.range (2 ^ f.mantBits - f.quietBitMask)).flatMap (fun k =>
    let payload := f.quietBitMask + k
    [withSign false (.nan payload), withSign true (.nan payload)])

def allNaNInputsCanonical {N : Nat} (f : FloatFormat) (xs : List (FN N)) : Bool :=
  xs.all (fun x => match fnNaNPayload? x with
    | none => true
    | some m => m == f.quietBitMask)

def nanResults {N : Nat} (f : FloatFormat) (inputs : List (FN N)) : List (FN N) :=
  if allNaNInputsCanonical f inputs then canonicalNaNs f else arithmeticNaNs f

def roundDyadicFn {N : Nat} (f : FloatFormat) (d : Foundation.Dyadic) : FN N :=
  fnOfBitsWith f (roundDyadic f d)

/-- Compare `a / b * 2^exp` with `2^p`, without introducing a rational or a
noncomputable real. -/
def ratioLtPow (a b : Nat) (exp p : Int) : Bool :=
  if p ≤ exp then decide (a * 2 ^ (exp - p).toNat < b)
  else decide (a < b * 2 ^ (p - exp).toNat)

/-- Exact numerator/denominator at the requested binary quantum. -/
def ratioRNEInput (a b : Nat) (exp q : Int) : Nat × Nat :=
  if q ≤ exp then (a * 2 ^ (exp - q).toNat, b)
  else (a, b * 2 ^ (q - exp).toNat)

def ratioRNE (a b : Nat) (exp q : Int) : Nat :=
  let p := ratioRNEInput a b exp q
  rneNat p.1 p.2

/-- Load-bearing rational rounding certificate: `ratioRNE` is within one half
unit of the exact scaled quotient. -/
theorem ratioRNE_spec (a b : Nat) (exp q : Int) (hb : 0 < b) :
    let p := ratioRNEInput a b exp q
    2 * p.1 ≤ (2 * ratioRNE a b exp q + 1) * p.2 ∧
      2 * ratioRNE a b exp q * p.2 ≤ 2 * p.1 + p.2 := by
  by_cases h : q ≤ exp
  · simp only [ratioRNEInput, ratioRNE, h, ↓reduceIte]
    exact rneNat_spec (a * 2 ^ (exp - q).toNat) b hb
  · simp only [ratioRNEInput, ratioRNE, h, ↓reduceIte]
    exact rneNat_spec a (b * 2 ^ (q - exp).toNat)
      (Nat.mul_pos hb (Nat.two_pow_pos _))

/-- Exact rational half-way cases choose an even significand. -/
theorem ratioRNE_tie_even (a b : Nat) (exp q : Int)
    (htie : let p := ratioRNEInput a b exp q; 2 * (p.1 % p.2) = p.2) :
    ratioRNE a b exp q % 2 = 0 := by
  exact rneNat_tie_even (ratioRNEInput a b exp q).1
    (ratioRNEInput a b exp q).2 htie

/-- Exact RNE conversion of `(-1)^neg * a/b * 2^exp`; callers keep `a,b`
positive. -/
def roundRatio (f : FloatFormat) (neg : Bool) (a b : Nat) (exp : Int) : Nat :=
  if a = 0 then f.pack neg 0 0
  else
    let b' := if b = 0 then 1 else b
    let e0 : Int := (bitLen a : Int) - (bitLen b' : Int) + exp
    let e : Int := if ratioLtPow a b' exp e0 then e0 - 1 else e0
    let emin := subnormalExp f
    let q0 : Int := max emin (e - (f.mantBits : Int))
    let sig0 := ratioRNE a b' exp q0
    packRoundedSignificand f neg sig0 q0

@[simp] theorem roundRatio_zero (f : FloatFormat) (neg : Bool) (b : Nat)
    (exp : Int) : roundRatio f neg 0 b exp = f.pack neg 0 0 := by
  simp [roundRatio]

/-- A nonzero rational is rounded by `ratioRNE_spec` and then passed without a
second rounding through the shared subnormal/normal/overflow boundary packer. -/
theorem roundRatio_eq_packRoundedSignificand (f : FloatFormat) (neg : Bool)
    (a b : Nat) (exp : Int) (ha : a ≠ 0) :
    roundRatio f neg a b exp =
      let b' := if b = 0 then 1 else b
      let e0 : Int := (bitLen a : Int) - (bitLen b' : Int) + exp
      let e : Int := if ratioLtPow a b' exp e0 then e0 - 1 else e0
      let q0 : Int := max (subnormalExp f) (e - (f.mantBits : Int))
      packRoundedSignificand f neg (ratioRNE a b' exp q0) q0 := by
  simp [roundRatio, ha]

def isqrtLoop : (fuel n lo hi : Nat) → lo * lo ≤ n → n < hi * hi →
    hi - lo ≤ fuel → {r : Nat // r * r ≤ n ∧ n < (r + 1) * (r + 1)}
  | 0, n, lo, hi, hlo, hhi, hspan => by
      have hhilo : hi ≤ lo := by omega
      have hsquares : hi * hi ≤ lo * lo := Nat.mul_le_mul hhilo hhilo
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans hsquares hlo)) hhi)
  | fuel + 1, n, lo, hi, hlo, hhi, hspan =>
      if hdone : hi ≤ lo + 1 then
        ⟨lo, hlo, by
          have hlthi : lo < hi := by
            apply Nat.lt_of_not_ge
            intro hhilo
            have hsquares : hi * hi ≤ lo * lo := Nat.mul_le_mul hhilo hhilo
            exact (Nat.not_lt_of_ge (Nat.le_trans hsquares hlo)) hhi
          have heq : hi = lo + 1 := by omega
          simpa [heq] using hhi⟩
      else
        let mid := (lo + hi) / 2
        if hmid : mid * mid ≤ n then
          isqrtLoop fuel n mid hi hmid hhi (by omega)
        else
          isqrtLoop fuel n lo mid hlo (Nat.lt_of_not_ge hmid) (by omega)

/-- Certified floor square root.  The proof component is erased by execution,
while keeping the binary-search result tied to its defining inequalities. -/
def isqrtCertified (n : Nat) :
    {r : Nat // r * r ≤ n ∧ n < (r + 1) * (r + 1)} :=
  isqrtLoop (n + 1) n 0 (n + 1) (by simp) (by
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have hle : n + 1 ≤ (n + 1) * (n + 1) :=
      Nat.le_mul_of_pos_left (n + 1) (Nat.succ_pos n)
    exact Nat.lt_of_lt_of_le hlt hle) (by omega)

def isqrt (n : Nat) : Nat := (isqrtCertified n).val

theorem isqrt_spec (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
  (isqrtCertified n).property

/-- RNE of the square root of the nonnegative rational `A/B`.  Comparing
`4*A` against `B*(2*r+1)^2` compares the exact root against the midpoint
between the adjacent integer candidates `r` and `r+1`. -/
def sqrtRNE (A B : Nat) : Nat :=
  let r := isqrt (A / B)
  let lhs := 4 * A
  let rhs := B * (2 * r + 1) ^ 2
  if lhs < rhs then r
  else if rhs < lhs then r + 1
  else if r % 2 = 0 then r else r + 1

/-- Load-bearing square-root rounding certificate: the candidates bracket the
exact rational radicand, midpoint comparison chooses the nearer one, and an
exact midpoint chooses an even candidate. -/
theorem sqrtRNE_spec (A B : Nat) (hB : 0 < B) :
    let r := isqrt (A / B)
    r * r * B ≤ A ∧ A < (r + 1) * (r + 1) * B ∧
      ((4 * A < B * (2 * r + 1) ^ 2 ∧ sqrtRNE A B = r) ∨
       (B * (2 * r + 1) ^ 2 < 4 * A ∧ sqrtRNE A B = r + 1) ∨
       (4 * A = B * (2 * r + 1) ^ 2 ∧
         sqrtRNE A B % 2 = 0 ∧
         (sqrtRNE A B = r ∨ sqrtRNE A B = r + 1))) := by
  dsimp only
  have hs := isqrt_spec (A / B)
  have hlo : isqrt (A / B) * isqrt (A / B) * B ≤ A :=
    (Nat.le_div_iff_mul_le hB).mp hs.1
  have hhi : A < (isqrt (A / B) + 1) * (isqrt (A / B) + 1) * B :=
    (Nat.div_lt_iff_lt_mul hB).mp hs.2
  refine ⟨hlo, hhi, ?_⟩
  by_cases hlt : 4 * A < B * (2 * isqrt (A / B) + 1) ^ 2
  · exact Or.inl ⟨hlt, by simp [sqrtRNE, hlt]⟩
  · by_cases hgt : B * (2 * isqrt (A / B) + 1) ^ 2 < 4 * A
    · exact Or.inr (Or.inl ⟨hgt, by simp [sqrtRNE, hlt, hgt]⟩)
    · have heq : 4 * A = B * (2 * isqrt (A / B) + 1) ^ 2 := by omega
      refine Or.inr (Or.inr ⟨heq, ?_, ?_⟩)
      · by_cases hp : isqrt (A / B) % 2 = 0
        · simp [sqrtRNE, hlt, hgt, hp]
        · have hm : isqrt (A / B) % 2 = 1 := by
            have := Nat.mod_lt (isqrt (A / B)) (by decide : 0 < 2)
            omega
          simp [sqrtRNE, hlt, hgt, hp]
          omega
      · by_cases hp : isqrt (A / B) % 2 = 0 <;>
          simp [sqrtRNE, hlt, hgt, hp]

/-- Exact RNE square root of the positive dyadic `N * 2^exp`. -/
def roundSqrt (f : FloatFormat) (N : Nat) (exp : Int) : Nat :=
  if N = 0 then f.pack false 0 0
  else
    let inputE : Int := (bitLen N : Int) - 1 + exp
    let e : Int := Int.ediv inputE 2
    let emin := subnormalExp f
    let q0 : Int := max emin (e - (f.mantBits : Int))
    let twiceQ := 2 * q0
    let A := if twiceQ ≤ exp then N * 2 ^ (exp - twiceQ).toNat else N
    let B := if twiceQ ≤ exp then 1 else 2 ^ (twiceQ - exp).toNat
    let sig0 := sqrtRNE A B
    packRoundedSignificand f false sig0 q0

@[simp] theorem roundSqrt_zero (f : FloatFormat) (exp : Int) :
    roundSqrt f 0 exp = f.pack false 0 0 := by
  simp [roundSqrt]

/-- A positive dyadic square root uses `sqrtRNE_spec` at its exact scaling and
then the same boundary packer as dyadic and rational rounding. -/
theorem roundSqrt_eq_packRoundedSignificand (f : FloatFormat) (N : Nat)
    (exp : Int) (hN : N ≠ 0) :
    roundSqrt f N exp =
      let inputE : Int := (bitLen N : Int) - 1 + exp
      let e : Int := Int.ediv inputE 2
      let q0 : Int := max (subnormalExp f) (e - (f.mantBits : Int))
      let twiceQ := 2 * q0
      let A := if twiceQ ≤ exp then N * 2 ^ (exp - twiceQ).toNat else N
      let B := if twiceQ ≤ exp then 1 else 2 ^ (twiceQ - exp).toNat
      packRoundedSignificand f false (sqrtRNE A B) q0 := by
  simp [roundSqrt, hN]

def truncDyadic (d : Foundation.Dyadic) : Int :=
  if 0 ≤ d.exp then d.num * 2 ^ d.exp.toNat
  else Int.tdiv d.num (2 ^ (-d.exp).toNat : Nat)

def floorDyadic (d : Foundation.Dyadic) : Int :=
  if 0 ≤ d.exp then d.num * 2 ^ d.exp.toNat
  else Int.ediv d.num (2 ^ (-d.exp).toNat : Nat)

def ceilDyadic (d : Foundation.Dyadic) : Int := -(floorDyadic ⟨-d.num, d.exp⟩)

def nearestDyadic (d : Foundation.Dyadic) : Int :=
  if 0 ≤ d.exp then d.num * 2 ^ d.exp.toNat
  else
    let rounded := rneNat d.num.natAbs (2 ^ (-d.exp).toNat)
    if d.num < 0 then -(rounded : Int) else (rounded : Int)

inductive IntegralRounding where
  | ceil | floor | trunc | nearest

def integralResult (mode : IntegralRounding) (d : Foundation.Dyadic) : Int :=
  match mode with
  | .ceil => ceilDyadic d
  | .floor => floorDyadic d
  | .trunc => truncDyadic d
  | .nearest => nearestDyadic d

/-! ## Scalar float builtins -/

def validUnary {N : Nat} (x : FN N) : Bool := FN.wf x

def validBinary {N : Nat} (x y : FN N) : Bool := FN.wf x && FN.wf y

def validTernary {N : Nat} (x y z : FN N) : Bool := FN.wf x && FN.wf y && FN.wf z

def fabs (N : Nat) (x : FN N) : List (FN N) :=
  if validUnary x then [fnAbs x] else []

def fneg (N : Nat) (x : FN N) : List (FN N) :=
  if validUnary x then [fnNeg x] else []

def fsqrt (N : Nat) (x : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validUnary x then []
      else if fnIsNaN x then nanResults f [x]
      else match fnMag x with
        | .inf => if fnSign x then nanResults f [] else [x]
        | .subnorm 0 => [x]
        | _ =>
            if fnSign x then nanResults f []
            else match finiteDyadic? f x with
              | some d => [fnOfBitsWith f (roundSqrt f d.num.toNat d.exp)]
              | none => []

def fintegral (mode : IntegralRounding) (N : Nat) (x : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validUnary x then []
      else if fnIsNaN x then nanResults f [x]
      else match fnMag x with
        | .inf => [x]
        | .subnorm 0 => [x]
        | _ => match finiteDyadic? f x with
          | none => []
          | some d =>
              let z := integralResult mode d
              if z = 0 then [withSign (fnSign x) (.subnorm 0)]
              else [roundDyadicFn f ⟨z, 0⟩]

def fadd (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else if fnIsNaN x || fnIsNaN y then nanResults f [x, y]
      else match fnMag x, fnMag y with
        | .inf, .inf => if fnSign x = fnSign y then [x] else nanResults f []
        | .inf, _ => [x]
        | _, .inf => [y]
        | .subnorm 0, .subnorm 0 =>
            if fnSign x = fnSign y then [x] else [withSign false (.subnorm 0)]
        | .subnorm 0, _ => [y]
        | _, .subnorm 0 => [x]
        | _, _ => match finiteDyadic? f x, finiteDyadic? f y with
          | some a, some b => [roundDyadicFn f (a.add b)]
          | _, _ => []

def fsub (N : Nat) (x y : FN N) : List (FN N) := fadd N x (fnNeg y)

def fmul (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else if fnIsNaN x || fnIsNaN y then nanResults f [x, y]
      else if (fnIsInf x && fnIsZero y) || (fnIsZero x && fnIsInf y) then nanResults f []
      else
        let sign := xor (fnSign x) (fnSign y)
        if fnIsInf x || fnIsInf y then [withSign sign .inf]
        else if fnIsZero x || fnIsZero y then [withSign sign (.subnorm 0)]
        else match finiteDyadic? f x, finiteDyadic? f y with
          | some a, some b => [roundDyadicFn f (a.mul b)]
          | _, _ => []

def fdiv (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else if fnIsNaN x || fnIsNaN y then nanResults f [x, y]
      else if (fnIsInf x && fnIsInf y) || (fnIsZero x && fnIsZero y) then nanResults f []
      else
        let sign := xor (fnSign x) (fnSign y)
        if fnIsInf x || fnIsZero y then [withSign sign .inf]
        else if fnIsZero x || fnIsInf y then [withSign sign (.subnorm 0)]
        else match finiteDyadic? f x, finiteDyadic? f y with
          | some a, some b =>
              [fnOfBitsWith f (roundRatio f sign a.num.natAbs b.num.natAbs (a.exp - b.exp))]
          | _, _ => []

def fmin (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else if fnIsNaN x || fnIsNaN y then nanResults f [x, y]
      else if fnIsZero x && fnIsZero y && fnSign x != fnSign y then
        [withSign true (.subnorm 0)]
      else match compareFloat? f x y with
        | some .gt => [y]
        | some _ => [x]
        | none => []

def fmax (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else if fnIsNaN x || fnIsNaN y then nanResults f [x, y]
      else if fnIsZero x && fnIsZero y && fnSign x != fnSign y then
        [withSign false (.subnorm 0)]
      else match compareFloat? f x y with
        | some .lt => [y]
        | some _ => [x]
        | none => []

def fpmin (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else match compareFloat? f y x with
        | some .lt => [y]
        | _ => [x]

def fpmax (N : Nat) (x y : FN N) : List (FN N) :=
  match floatFormat? N with
  | none => []
  | some f =>
      if !validBinary x y then []
      else match compareFloat? f x y with
        | some .lt => [y]
        | _ => [x]

def fcopysign (N : Nat) (x y : FN N) : List (FN N) :=
  if validBinary x y then [fnCopySign x y] else []

def floatPredicate (pred : Ordering → Bool) (N : Nat) (x y : FN N) : U32 :=
  match floatFormat? N with
  | none => Numerics.bool_ false
  | some f =>
      if !validBinary x y then Numerics.bool_ false
      else match compareFloat? f x y with
        | none => Numerics.bool_ false
        | some o => Numerics.bool_ (pred o)

def feq (N : Nat) (x y : FN N) : U32 :=
  floatPredicate (fun o => o == .eq) N x y

def fne (N : Nat) (x y : FN N) : U32 :=
  if fnIsNaN x || fnIsNaN y then Numerics.bool_ true
  else floatPredicate (fun o => o != .eq) N x y

def flt (N : Nat) (x y : FN N) : U32 :=
  floatPredicate (fun o => o == .lt) N x y

def fgt (N : Nat) (x y : FN N) : U32 :=
  floatPredicate (fun o => o == .gt) N x y

def fle (N : Nat) (x y : FN N) : U32 :=
  floatPredicate (fun o => o != .gt) N x y

def fge (N : Nat) (x y : FN N) : U32 :=
  floatPredicate (fun o => o != .lt) N x y

/-! Alternative zero of each unreachable relaxed operation. -/

def frelaxedMadd (N : Nat) (x y z : FN N) : List (FN N) :=
  if !validTernary x y z then []
  else (fmul N x y).flatMap (fun product => fadd N product z)

def frelaxedNmadd (N : Nat) (x y z : FN N) : List (FN N) :=
  frelaxedMadd N (fnNeg x) y z

/-! ## Numeric conversions -/

def wrap (M N : Nat) (x : IN M) : IN N := Numerics.ofNatWrap N x.val

def extend (M N : Nat) (sx : Sx) (x : IN M) : IN N :=
  match sx with
  | .u => Numerics.ofNatWrap N x.val
  | .s => Numerics.inv_signed_ N (Numerics.signed_ M x)

def trunc (M N : Nat) (sx : Sx) (x : FN M) : Option (IN N) :=
  match floatFormat? M with
  | none => none
  | some f =>
      if !validUnary x then none
      else match finiteDyadic? f x with
        | none => none
        | some d =>
            let z := truncDyadic d
            match sx with
            | .u =>
                if 0 ≤ z && z < (2 ^ N : Nat)
                then some (Numerics.ofNatWrap N z.toNat)
                else none
            | .s =>
                if -((2 ^ (N - 1) : Nat) : Int) ≤ z &&
                    z < ((2 ^ (N - 1) : Nat) : Int)
                then some (Numerics.inv_signed_ N z)
                else none

def truncSat (M N : Nat) (sx : Sx) (x : FN M) : Option (IN N) :=
  match floatFormat? M with
  | none => none
  | some f =>
      if !validUnary x then none
      else if fnIsNaN x then some (inZero N)
      else match fnMag x with
        | .inf => match sx with
          | .u => some (Numerics.ofNatWrap N (if fnSign x then 0 else 2 ^ N - 1))
          | .s => some (Numerics.inv_signed_ N
              (if fnSign x then -((2 ^ (N - 1) : Nat) : Int)
               else ((2 ^ (N - 1) : Nat) : Int) - 1))
        | _ => match finiteDyadic? f x with
          | none => none
          | some d =>
              let z := truncDyadic d
              match sx with
              | .u => some (Numerics.ofNatWrap N (Numerics.sat_u_ N z))
              | .s => some (Numerics.inv_signed_ N (Numerics.sat_s_ N z))

def convert (M N : Nat) (sx : Sx) (x : IN M) : FN N :=
  match floatFormat? N with
  | none => .pos (.subnorm 0)
  | some f =>
      let z : Int := match sx with
        | .u => x.val
        | .s => Numerics.signed_ M x
      roundDyadicFn f ⟨z, 0⟩

def convertFloat (M N : Nat) (x : FN M) : List (FN N) :=
  match floatFormat? M, floatFormat? N with
  | some src, some dst =>
      if !validUnary x then []
      else if fnIsNaN x then
        if fnNaNPayload? x == some src.quietBitMask
        then canonicalNaNs dst
        else arithmeticNaNs dst
      else match fnMag x with
        | .inf => [withSign (fnSign x) .inf]
        | .subnorm 0 => [withSign (fnSign x) (.subnorm 0)]
        | _ => match finiteDyadic? src x with
          | some d => [roundDyadicFn dst d]
          | none => []
  | _, _ => []

def narrow (M N : Nat) (sx : Sx) (x : IN M) : IN N :=
  match sx with
  | .u => Numerics.ofNatWrap N (Numerics.sat_u_ N (x.val : Int))
  | .s => Numerics.inv_signed_ N (Numerics.sat_s_ N (Numerics.signed_ M x))

def numBits : (nt : NumType) → Num_ nt → Nat
  | .i32, x => x.val
  | .i64, x => x.val
  | .f32, x => fnBitsWith FloatFormat.binary32 x
  | .f64, x => fnBitsWith FloatFormat.binary64 x

def numOfBits : (nt : NumType) → Nat → Num_ nt
  | .i32, bits => Numerics.ofNatWrap 32 bits
  | .i64, bits => Numerics.ofNatWrap 64 bits
  | .f32, bits => fnOfBitsWith FloatFormat.binary32 bits
  | .f64, bits => fnOfBitsWith FloatFormat.binary64 bits

def reinterpret : (nt₁ nt₂ : NumType) → Num_ nt₁ → Num_ nt₂
  | nt₁, nt₂, x => numOfBits nt₂ (numBits nt₁ x)

/-! ## Lane bijection -/

def laneOfBits : (lt : LaneType) → Nat → Lane_ lt
  | .num .i32, bits => Numerics.ofNatWrap 32 bits
  | .num .i64, bits => Numerics.ofNatWrap 64 bits
  | .num .f32, bits => fnOfBitsWith FloatFormat.binary32 bits
  | .num .f64, bits => fnOfBitsWith FloatFormat.binary64 bits
  | .pack .i8, bits => Numerics.ofNatWrap 8 bits
  | .pack .i16, bits => Numerics.ofNatWrap 16 bits

def laneBits : (lt : LaneType) → Lane_ lt → Nat
  | .num .i32, x => x.val
  | .num .i64, x => x.val
  | .num .f32, x => fnBitsWith FloatFormat.binary32 x
  | .num .f64, x => fnBitsWith FloatFormat.binary64 x
  | .pack .i8, x => x.val
  | .pack .i16, x => x.val

def lanes (sh : Shape) (v : V128Lit) : List (Lane_ sh.lane) :=
  (List.range sh.dim.toNat).map (fun k =>
    laneOfBits sh.lane (v.val / 2 ^ (sh.lane.size * k) % 2 ^ sh.lane.size))

def invLanes (sh : Shape) (xs : List (Lane_ sh.lane)) : V128Lit :=
  Numerics.ofNatWrap 128
    ((xs.zipIdx.foldl (fun acc xi => acc + laneBits sh.lane xi.1 * 2 ^ (sh.lane.size * xi.2)) 0))

/-! ## The released provider -/

/-- The sole concrete numeric provider used by the released Core execution. -/
def released : Numerics where
  ibytes_ := ibytes
  nbytes_ := nbytes
  vbytes_ := vbytes
  zbytes_ := zbytes
  inv_ibits_ := invIbits
  iclz_ := iclz
  ictz_ := ictz
  ipopcnt_ := ipopcnt
  inot_ := inot
  irev_ := bitReverse
  iand_ := iand
  iandnot_ := iandnot
  ior_ := ior
  ixor_ := ixor
  ishl_ := ishl
  ishr_ := ishr
  irotl_ := irotl
  irotr_ := irotr
  ibitselect_ := ibitselect
  iavgr_ := iavgr
  iq15mulr_sat_ := iq15mulrSat
  irelaxed_q15mulr_ := irelaxedQ15mulr
  irelaxed_laneselect_ := irelaxedLaneselect
  fabs_ := fabs
  fneg_ := fneg
  fsqrt_ := fsqrt
  fceil_ := fintegral .ceil
  ffloor_ := fintegral .floor
  ftrunc_ := fintegral .trunc
  fnearest_ := fintegral .nearest
  fadd_ := fadd
  fsub_ := fsub
  fmul_ := fmul
  fdiv_ := fdiv
  fmin_ := fmin
  fmax_ := fmax
  fpmin_ := fpmin
  fpmax_ := fpmax
  frelaxed_min_ := fmin
  frelaxed_max_ := fmax
  fcopysign_ := fcopysign
  feq_ := feq
  fne_ := fne
  flt_ := flt
  fgt_ := fgt
  fle_ := fle
  fge_ := fge
  frelaxed_madd_ := frelaxedMadd
  frelaxed_nmadd_ := frelaxedNmadd
  wrap__ := wrap
  extend__ := extend
  trunc__ := trunc
  trunc_sat__ := truncSat
  relaxed_trunc__ := truncSat
  convert__ := convert
  promote__ := convertFloat
  demote__ := convertFloat
  narrow__ := narrow
  reinterpret__ := reinterpret
  lanes_ := lanes
  inv_lanes_ := invLanes
  nd := true
  r_swizzle := false
  r_idot := false

end ConcreteNumerics

/-- Public released Core numeric semantics. -/
abbrev releasedNumerics : Numerics := ConcreteNumerics.released

@[simp] theorem releasedNumerics_nd : releasedNumerics.nd = true := rfl
@[simp] theorem releasedNumerics_r_swizzle : releasedNumerics.r_swizzle = false := rfl
@[simp] theorem releasedNumerics_r_idot : releasedNumerics.r_idot = false := rfl

namespace ConcreteNumerics

/-! ## Pinned numeric result-set conformance

These statements expose the prose cases of Core 3.0's builtin numeric
operators as kernel-checked equations.  In particular, the NaN statements
characterize the whole finite result set rather than selecting one witness. -/

theorem mem_canonicalNaNs_iff {N : Nat} (f : FloatFormat) (z : FN N) :
    z ∈ canonicalNaNs f ↔
      z = .pos (.nan f.quietBitMask) ∨ z = .neg (.nan f.quietBitMask) := by
  simp [canonicalNaNs, withSign]

theorem mem_arithmeticNaNs_iff {N : Nat} (f : FloatFormat) (z : FN N) :
    z ∈ arithmeticNaNs f ↔
      ∃ k, k < 2 ^ f.mantBits - f.quietBitMask ∧
        (z = .pos (.nan (f.quietBitMask + k)) ∨
         z = .neg (.nan (f.quietBitMask + k))) := by
  simp [arithmeticNaNs, withSign]

theorem nanResults_of_canonical_inputs {N : Nat} (f : FloatFormat)
    (xs : List (FN N)) (h : allNaNInputsCanonical f xs = true) :
    nanResults f xs = canonicalNaNs f := by
  simp [nanResults, h]

theorem nanResults_of_arithmetic_input {N : Nat} (f : FloatFormat)
    (xs : List (FN N)) (h : allNaNInputsCanonical f xs = false) :
    nanResults f xs = arithmeticNaNs f := by
  simp [nanResults, h]

theorem fadd_nan_result_set {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hn : (fnIsNaN x || fnIsNaN y) = true) :
    fadd N x y = nanResults f [x, y] := by
  simp [fadd, hf, hv, hn]

theorem fmul_nan_result_set {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hn : (fnIsNaN x || fnIsNaN y) = true) :
    fmul N x y = nanResults f [x, y] := by
  simp [fmul, hf, hv, hn]

theorem fdiv_nan_result_set {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hn : (fnIsNaN x || fnIsNaN y) = true) :
    fdiv N x y = nanResults f [x, y] := by
  simp [fdiv, hf, hv, hn]

theorem fmin_nan_result_set {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hn : (fnIsNaN x || fnIsNaN y) = true) :
    fmin N x y = nanResults f [x, y] := by
  simp [fmin, hf, hv, hn]

theorem fmax_nan_result_set {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hn : (fnIsNaN x || fnIsNaN y) = true) :
    fmax N x y = nanResults f [x, y] := by
  simp [fmax, hf, hv, hn]

theorem fsqrt_nan_result_set {N : Nat} (f : FloatFormat) (x : FN N)
    (hf : floatFormat? N = some f) (hv : validUnary x = true)
    (hn : fnIsNaN x = true) :
    fsqrt N x = nanResults f [x] := by
  simp [fsqrt, hf, hv, hn]

theorem fintegral_nan_result_set {N : Nat} (f : FloatFormat) (x : FN N)
    (mode : IntegralRounding) (hf : floatFormat? N = some f)
    (hv : validUnary x = true) (hn : fnIsNaN x = true) :
    fintegral mode N x = nanResults f [x] := by
  simp [fintegral, hf, hv, hn]

/-! Pseudo-minimum and pseudo-maximum select operands exactly by the pinned
ordered comparison; unordered (NaN) comparisons take the first operand. -/

theorem fpmin_of_lt {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hc : compareFloat? f y x = some .lt) :
    fpmin N x y = [y] := by
  simp [fpmin, hf, hv, hc]

theorem fpmin_of_not_lt {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hc : compareFloat? f y x ≠ some .lt) :
    fpmin N x y = [x] := by
  simp [fpmin, hf, hv]

theorem fpmax_of_lt {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hc : compareFloat? f x y = some .lt) :
    fpmax N x y = [y] := by
  simp [fpmax, hf, hv, hc]

theorem fpmax_of_not_lt {N : Nat} (f : FloatFormat) (x y : FN N)
    (hf : floatFormat? N = some f) (hv : validBinary x y = true)
    (hc : compareFloat? f x y ≠ some .lt) :
    fpmax N x y = [x] := by
  simp [fpmax, hf, hv]

/-! Finite cases expose the exact dyadic, rational, and integral kernels used
before the final IEEE round-to-nearest-ties-to-even conversion. -/

theorem fsqrt_positive_norm {N : Nat} (f : FloatFormat) (m : Nat) (e : Int)
    (hf : floatFormat? N = some f)
    (hv : FNMag.wf (.norm m e : FNMag N) = true) :
    fsqrt N (.pos (.norm m e)) =
      [fnOfBitsWith f
        (roundSqrt f (2 ^ f.mantBits + (m : Int)).toNat (e - f.mantBits))] := by
  simp [fsqrt, hf, validUnary, FN.wf, hv, fnIsNaN, fnMag, fnSign,
    finiteDyadic?]

theorem fadd_norm {N : Nat} (f : FloatFormat) (sx sy : Bool)
    (mx my : Nat) (ex ey : Int) (hf : floatFormat? N = some f)
    (hvx : FNMag.wf (.norm mx ex : FNMag N) = true)
    (hvy : FNMag.wf (.norm my ey : FNMag N) = true) :
    fadd N (withSign sx (.norm mx ex)) (withSign sy (.norm my ey)) =
      let a : Foundation.Dyadic :=
        ⟨if sx then -((2 ^ f.mantBits + mx : Nat) : Int)
          else ((2 ^ f.mantBits + mx : Nat) : Int), ex - f.mantBits⟩
      let b : Foundation.Dyadic :=
        ⟨if sy then -((2 ^ f.mantBits + my : Nat) : Int)
          else ((2 ^ f.mantBits + my : Nat) : Int), ey - f.mantBits⟩
      [roundDyadicFn f (a.add b)] := by
  cases sx <;> cases sy <;>
    simp [fadd, hf, validBinary, FN.wf, hvx, hvy, withSign, fnIsNaN,
      fnMag, fnSign, finiteDyadic?]

theorem fmul_norm {N : Nat} (f : FloatFormat) (sx sy : Bool)
    (mx my : Nat) (ex ey : Int) (hf : floatFormat? N = some f)
    (hvx : FNMag.wf (.norm mx ex : FNMag N) = true)
    (hvy : FNMag.wf (.norm my ey : FNMag N) = true) :
    fmul N (withSign sx (.norm mx ex)) (withSign sy (.norm my ey)) =
      let a : Foundation.Dyadic :=
        ⟨if sx then -((2 ^ f.mantBits + mx : Nat) : Int)
          else ((2 ^ f.mantBits + mx : Nat) : Int), ex - f.mantBits⟩
      let b : Foundation.Dyadic :=
        ⟨if sy then -((2 ^ f.mantBits + my : Nat) : Int)
          else ((2 ^ f.mantBits + my : Nat) : Int), ey - f.mantBits⟩
      [roundDyadicFn f (a.mul b)] := by
  cases sx <;> cases sy <;>
    simp [fmul, hf, validBinary, FN.wf, hvx, hvy, withSign, fnIsNaN,
      fnIsInf, fnIsZero, fnMag, fnSign, finiteDyadic?]

theorem fdiv_norm {N : Nat} (f : FloatFormat) (sx sy : Bool)
    (mx my : Nat) (ex ey : Int) (hf : floatFormat? N = some f)
    (hvx : FNMag.wf (.norm mx ex : FNMag N) = true)
    (hvy : FNMag.wf (.norm my ey : FNMag N) = true) :
    fdiv N (withSign sx (.norm mx ex)) (withSign sy (.norm my ey)) =
      [fnOfBitsWith f
        (roundRatio f (xor sx sy) (2 ^ f.mantBits + (mx : Int)).natAbs
          (2 ^ f.mantBits + (my : Int)).natAbs
          ((ex - f.mantBits) - (ey - f.mantBits)))] := by
  cases sx <;> cases sy <;>
    simp [fdiv, hf, validBinary, FN.wf, hvx, hvy, withSign, fnIsNaN,
      fnIsInf, fnIsZero, fnMag, fnSign, finiteDyadic?]

theorem fintegral_norm {N : Nat} (f : FloatFormat) (s : Bool)
    (m : Nat) (e : Int) (mode : IntegralRounding) (hf : floatFormat? N = some f)
    (hv : FNMag.wf (.norm m e : FNMag N) = true) :
    fintegral mode N (withSign s (.norm m e)) =
      let d : Foundation.Dyadic :=
        ⟨if s then -((2 ^ f.mantBits + m : Nat) : Int)
          else ((2 ^ f.mantBits + m : Nat) : Int), e - f.mantBits⟩
      let z := integralResult mode d
      if z = 0 then [withSign s (.subnorm 0)]
      else [roundDyadicFn f ⟨z, 0⟩] := by
  cases s <;>
    simp [fintegral, hf, validUnary, FN.wf, hv, withSign, fnIsNaN, fnMag,
      fnSign, finiteDyadic?]

theorem trunc_finite {M N : Nat} (f : FloatFormat) (x : FN M)
    (d : Foundation.Dyadic) (sx : Sx) (hf : floatFormat? M = some f)
    (hv : validUnary x = true) (hd : finiteDyadic? f x = some d) :
    trunc M N sx x =
      let z := truncDyadic d
      match sx with
      | .u => if 0 ≤ z && z < (2 ^ N : Nat)
        then some (Numerics.ofNatWrap N z.toNat) else none
      | .s => if -((2 ^ (N - 1) : Nat) : Int) ≤ z &&
                    z < ((2 ^ (N - 1) : Nat) : Int)
        then some (Numerics.inv_signed_ N z) else none := by
  cases sx <;> simp [trunc, hf, hv, hd]

theorem convertFloat_canonical_nan {M N : Nat} (src dst : FloatFormat)
    (x : FN M) (hsrc : floatFormat? M = some src)
    (hdst : floatFormat? N = some dst) (hv : validUnary x = true)
    (hn : fnIsNaN x = true)
    (hp : (fnNaNPayload? x == some src.quietBitMask) = true) :
    convertFloat M N x = canonicalNaNs dst := by
  simp [convertFloat, hsrc, hdst, hv, hn, hp]

theorem convertFloat_arithmetic_nan {M N : Nat} (src dst : FloatFormat)
    (x : FN M) (hsrc : floatFormat? M = some src)
    (hdst : floatFormat? N = some dst) (hv : validUnary x = true)
    (hn : fnIsNaN x = true)
    (hp : (fnNaNPayload? x == some src.quietBitMask) = false) :
    convertFloat M N x = arithmeticNaNs dst := by
  simp [convertFloat, hsrc, hdst, hv, hn, hp]

/-! ## Released-field coverage

Every builtin field is fixed below to the executable equation proved about it
in this namespace.  These projection theorems prevent a downstream use of the
released relation from reopening a numeric-provider choice. -/

@[simp] theorem released_ibytes (N : Nat) (x : IN N) :
    releasedNumerics.ibytes_ N x = ibytes N x := rfl
@[simp] theorem released_nbytes (nt : NumType) (x : Num_ nt) :
    releasedNumerics.nbytes_ nt x = nbytes nt x := rfl
@[simp] theorem released_vbytes (vt : VecType) (x : VecLit vt.toVnn) :
    releasedNumerics.vbytes_ vt x = vbytes vt x := rfl
@[simp] theorem released_zbytes (zt : StorageType) (x : Lit_ zt) :
    releasedNumerics.zbytes_ zt x = zbytes zt x := rfl
@[simp] theorem released_inv_ibits (N : Nat) (xs : List Bit) :
    releasedNumerics.inv_ibits_ N xs = invIbits N xs := rfl

@[simp] theorem released_iclz (N : Nat) (x : IN N) :
    releasedNumerics.iclz_ N x = iclz N x := rfl
@[simp] theorem released_ictz (N : Nat) (x : IN N) :
    releasedNumerics.ictz_ N x = ictz N x := rfl
@[simp] theorem released_ipopcnt (N : Nat) (x : IN N) :
    releasedNumerics.ipopcnt_ N x = ipopcnt N x := rfl
@[simp] theorem released_inot (N : Nat) (x : IN N) :
    releasedNumerics.inot_ N x = inot N x := rfl
@[simp] theorem released_irev (N : Nat) (x : IN N) :
    releasedNumerics.irev_ N x = bitReverse N x := rfl
@[simp] theorem released_iand (N : Nat) (x y : IN N) :
    releasedNumerics.iand_ N x y = iand N x y := rfl
@[simp] theorem released_iandnot (N : Nat) (x y : IN N) :
    releasedNumerics.iandnot_ N x y = iandnot N x y := rfl
@[simp] theorem released_ior (N : Nat) (x y : IN N) :
    releasedNumerics.ior_ N x y = ior N x y := rfl
@[simp] theorem released_ixor (N : Nat) (x y : IN N) :
    releasedNumerics.ixor_ N x y = ixor N x y := rfl
@[simp] theorem released_ishl (N : Nat) (x : IN N) (k : U32) :
    releasedNumerics.ishl_ N x k = ishl N x k := rfl
@[simp] theorem released_ishr (N : Nat) (sx : Sx) (x : IN N) (k : U32) :
    releasedNumerics.ishr_ N sx x k = ishr N sx x k := rfl
@[simp] theorem released_irotl (N : Nat) (x k : IN N) :
    releasedNumerics.irotl_ N x k = irotl N x k := rfl
@[simp] theorem released_irotr (N : Nat) (x k : IN N) :
    releasedNumerics.irotr_ N x k = irotr N x k := rfl
@[simp] theorem released_ibitselect (N : Nat) (x y m : IN N) :
    releasedNumerics.ibitselect_ N x y m = ibitselect N x y m := rfl
@[simp] theorem released_iavgr (N : Nat) (sx : Sx) (x y : IN N) :
    releasedNumerics.iavgr_ N sx x y = iavgr N sx x y := rfl
@[simp] theorem released_iq15mulr_sat (N : Nat) (sx : Sx) (x y : IN N) :
    releasedNumerics.iq15mulr_sat_ N sx x y = iq15mulrSat N sx x y := rfl

@[simp] theorem released_fabs (N : Nat) (x : FN N) :
    releasedNumerics.fabs_ N x = fabs N x := rfl
@[simp] theorem released_fneg (N : Nat) (x : FN N) :
    releasedNumerics.fneg_ N x = fneg N x := rfl
@[simp] theorem released_fsqrt (N : Nat) (x : FN N) :
    releasedNumerics.fsqrt_ N x = fsqrt N x := rfl
@[simp] theorem released_fceil (N : Nat) (x : FN N) :
    releasedNumerics.fceil_ N x = fintegral .ceil N x := rfl
@[simp] theorem released_ffloor (N : Nat) (x : FN N) :
    releasedNumerics.ffloor_ N x = fintegral .floor N x := rfl
@[simp] theorem released_ftrunc (N : Nat) (x : FN N) :
    releasedNumerics.ftrunc_ N x = fintegral .trunc N x := rfl
@[simp] theorem released_fnearest (N : Nat) (x : FN N) :
    releasedNumerics.fnearest_ N x = fintegral .nearest N x := rfl
@[simp] theorem released_fadd (N : Nat) (x y : FN N) :
    releasedNumerics.fadd_ N x y = fadd N x y := rfl
@[simp] theorem released_fsub (N : Nat) (x y : FN N) :
    releasedNumerics.fsub_ N x y = fadd N x (fnNeg y) := rfl
@[simp] theorem released_fmul (N : Nat) (x y : FN N) :
    releasedNumerics.fmul_ N x y = fmul N x y := rfl
@[simp] theorem released_fdiv (N : Nat) (x y : FN N) :
    releasedNumerics.fdiv_ N x y = fdiv N x y := rfl
@[simp] theorem released_fmin (N : Nat) (x y : FN N) :
    releasedNumerics.fmin_ N x y = fmin N x y := rfl
@[simp] theorem released_fmax (N : Nat) (x y : FN N) :
    releasedNumerics.fmax_ N x y = fmax N x y := rfl
@[simp] theorem released_fpmin (N : Nat) (x y : FN N) :
    releasedNumerics.fpmin_ N x y = fpmin N x y := rfl
@[simp] theorem released_fpmax (N : Nat) (x y : FN N) :
    releasedNumerics.fpmax_ N x y = fpmax N x y := rfl
@[simp] theorem released_fcopysign (N : Nat) (x y : FN N) :
    releasedNumerics.fcopysign_ N x y = fcopysign N x y := rfl
@[simp] theorem released_feq (N : Nat) (x y : FN N) :
    releasedNumerics.feq_ N x y = feq N x y := rfl
@[simp] theorem released_fne (N : Nat) (x y : FN N) :
    releasedNumerics.fne_ N x y = fne N x y := rfl
@[simp] theorem released_flt (N : Nat) (x y : FN N) :
    releasedNumerics.flt_ N x y = flt N x y := rfl
@[simp] theorem released_fgt (N : Nat) (x y : FN N) :
    releasedNumerics.fgt_ N x y = fgt N x y := rfl
@[simp] theorem released_fle (N : Nat) (x y : FN N) :
    releasedNumerics.fle_ N x y = fle N x y := rfl
@[simp] theorem released_fge (N : Nat) (x y : FN N) :
    releasedNumerics.fge_ N x y = fge N x y := rfl

@[simp] theorem released_wrap (M N : Nat) (x : IN M) :
    releasedNumerics.wrap__ M N x = wrap M N x := rfl
@[simp] theorem released_extend (M N : Nat) (sx : Sx) (x : IN M) :
    releasedNumerics.extend__ M N sx x = extend M N sx x := rfl
@[simp] theorem released_trunc (M N : Nat) (sx : Sx) (x : FN M) :
    releasedNumerics.trunc__ M N sx x = trunc M N sx x := rfl
@[simp] theorem released_trunc_sat (M N : Nat) (sx : Sx) (x : FN M) :
    releasedNumerics.trunc_sat__ M N sx x = truncSat M N sx x := rfl
@[simp] theorem released_convert (M N : Nat) (sx : Sx) (x : IN M) :
    releasedNumerics.convert__ M N sx x = convert M N sx x := rfl
@[simp] theorem released_promote (M N : Nat) (x : FN M) :
    releasedNumerics.promote__ M N x = convertFloat M N x := rfl
@[simp] theorem released_demote (M N : Nat) (x : FN M) :
    releasedNumerics.demote__ M N x = convertFloat M N x := rfl
@[simp] theorem released_narrow (M N : Nat) (sx : Sx) (x : IN M) :
    releasedNumerics.narrow__ M N sx x = narrow M N sx x := rfl
@[simp] theorem released_reinterpret (nt₁ nt₂ : NumType) (x : Num_ nt₁) :
    releasedNumerics.reinterpret__ nt₁ nt₂ x = reinterpret nt₁ nt₂ x := rfl
@[simp] theorem released_lanes (sh : Shape) (x : V128Lit) :
    releasedNumerics.lanes_ sh x = lanes sh x := rfl
@[simp] theorem released_inv_lanes (sh : Shape) (xs : List (Lane_ sh.lane)) :
    releasedNumerics.inv_lanes_ sh xs = invLanes sh xs := rfl

/-! The unreachable relaxed families are fixed to alternative zero.  These
equations record every embedded selector in addition to the three public
profile bits above. -/

theorem released_relaxed_madd_is_unfused (N : Nat) (x y z : FN N) :
    releasedNumerics.frelaxed_madd_ N x y z = frelaxedMadd N x y z := rfl

theorem released_relaxed_nmadd_is_unfused (N : Nat) (x y z : FN N) :
    releasedNumerics.frelaxed_nmadd_ N x y z = frelaxedNmadd N x y z := rfl

theorem released_relaxed_min_is_standard (N : Nat) (x y : FN N) :
    releasedNumerics.frelaxed_min_ N x y = fmin N x y := rfl

theorem released_relaxed_max_is_standard (N : Nat) (x y : FN N) :
    releasedNumerics.frelaxed_max_ N x y = fmax N x y := rfl

theorem released_relaxed_trunc_is_saturating (M N : Nat) (sx : Sx) (x : FN M) :
    releasedNumerics.relaxed_trunc__ M N sx x = truncSat M N sx x := rfl

theorem released_relaxed_q15_is_saturating (N : Nat) (sx : Sx) (x y : IN N) :
    releasedNumerics.irelaxed_q15mulr_ N sx x y = [iq15mulrSat N sx x y] := rfl

theorem released_relaxed_laneselect_is_bitselect (N : Nat) (x y m : IN N) :
    releasedNumerics.irelaxed_laneselect_ N x y m = [ibitselect N x y m] := rfl

end ConcreteNumerics

/-! ## Kernel-reduced non-vacuity witnesses -/

theorem released_iclz32_zero :
    releasedNumerics.iclz_ 32 (inZero 32) = Numerics.ofNatWrap 32 32 := by
  decide

theorem released_iand32_nonzero :
    (releasedNumerics.iand_ 32 (Numerics.ofNatWrap 32 0xF0)
      (Numerics.ofNatWrap 32 0xCC)).val = 0xC0 := by
  decide

theorem released_fadd32_one_one :
    releasedNumerics.fadd_ 32 (.pos (.norm 0 0)) (.pos (.norm 0 0)) =
      [.pos (.norm 0 1)] := by
  decide

theorem released_fadd32_invalid_nan_has_both_canonical_signs :
    releasedNumerics.fadd_ 32 (.pos .inf) (.neg .inf) =
      [.pos (.nan (2 ^ 22)), .neg (.nan (2 ^ 22))] := by
  decide

theorem released_fsqrt32_two_rne :
    releasedNumerics.fsqrt_ 32 (.pos (.norm 0 1)) =
      [.pos (.norm 3474675 0)] := by
  decide

theorem released_fdiv32_one_third_rne :
    releasedNumerics.fdiv_ 32 (.pos (.norm 0 0)) (.pos (.norm (2 ^ 22) 1)) =
      [.pos (.norm 2796203 (-2))] := by
  decide

theorem released_integral_rounding_boundaries :
    releasedNumerics.fceil_ 32 (.neg (.norm 0 (-1))) = [.neg (.subnorm 0)] ∧
    releasedNumerics.ffloor_ 32 (.pos (.norm 0 (-1))) = [.pos (.subnorm 0)] ∧
    releasedNumerics.fnearest_ 32 (.pos (.norm (2 ^ 21) 1)) = [.pos (.norm 0 1)] ∧
    releasedNumerics.fnearest_ 32 (.neg (.norm 0 (-1))) = [.neg (.subnorm 0)] := by
  decide

theorem released_trunc_boundaries :
    releasedNumerics.trunc__ 32 32 .u (.neg (.norm 0 (-1))) = some (inZero 32) ∧
    releasedNumerics.trunc__ 32 32 .u (.neg (.norm 0 0)) = none ∧
    releasedNumerics.trunc__ 32 32 .s (.neg (.norm 0 31)) =
      some (Numerics.ofNatWrap 32 (2 ^ 31)) ∧
    releasedNumerics.trunc__ 32 32 .s (.pos (.norm 0 31)) = none := by
  decide

theorem released_trunc_sat_boundaries :
    releasedNumerics.trunc_sat__ 32 32 .u (.pos .inf) =
      some (Numerics.ofNatWrap 32 (2 ^ 32 - 1)) ∧
    releasedNumerics.trunc_sat__ 32 32 .s (.neg .inf) =
      some (Numerics.ofNatWrap 32 (2 ^ 31)) ∧
    releasedNumerics.trunc_sat__ 32 32 .u (.pos (.nan (2 ^ 22))) =
      some (inZero 32) := by
  decide

theorem released_promote_canonical_nan :
    releasedNumerics.promote__ 32 64 (.neg (.nan (2 ^ 22))) =
      ConcreteNumerics.canonicalNaNs FloatFormat.binary64 := by
  decide

theorem released_narrow_unsigned_high_source :
    (releasedNumerics.narrow__ 16 8 .u (Numerics.ofNatWrap 16 0xffff)).val = 0xff := by
  decide

theorem released_narrow_signed_high_source :
    (releasedNumerics.narrow__ 16 8 .s (Numerics.ofNatWrap 16 0xffff)).val = 0xff := by
  decide

theorem released_lane_roundtrip_i8x16 :
    releasedNumerics.inv_lanes_ { lane := .pack .i8, dim := .d16 }
      (releasedNumerics.lanes_ { lane := .pack .i8, dim := .d16 }
        (Numerics.ofNatWrap 128 0x00112233445566778899AABBCCDDEEFF)) =
      Numerics.ofNatWrap 128 0x00112233445566778899AABBCCDDEEFF := by
  decide

end WasmGemmGnaf.Wasm.Core.Exec
