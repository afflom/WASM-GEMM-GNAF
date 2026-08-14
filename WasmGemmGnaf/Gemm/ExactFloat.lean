import WasmGemmGnaf.Foundation.ExactFloat
import WasmGemmGnaf.Gemm.Arithmetic

set_option autoImplicit false
set_option exponentiation.threshold 400
set_option maxRecDepth 8000

/-! GEMM-specific classifications and format selection layered over the neutral
exact binary-float kernel in `Foundation/ExactFloat.lean`. -/

namespace WasmGemmGnaf.Gemm

open WasmGemmGnaf.Foundation

/-- The coarse class SPEC §8.2's tables react to. -/
def evalClass : EVal → SpecialClass
  | .nan => .nan
  | .inf s => .inf s
  | .num d => if d.num = 0 then .zero false else .finite (decide (d.num < 0))

/-- **`evalMul` is SPEC §8.2's product table.**  Whenever the table of
`Gemm/Arithmetic.lean` prescribes an outcome class, `evalMul` produces exactly
that class. -/
theorem classOf_evalMul {x y : EVal} {c : SpecialClass}
    (h : SpecialClass.mul (evalClass x) (evalClass y) = some c) :
    evalClass (evalMul x y) = c := by
  cases x with
  | nan => cases y <;> simp_all [evalClass, evalMul, SpecialClass.mul]
  | inf s =>
    cases y with
    | nan => simp_all [evalClass, evalMul, SpecialClass.mul]
    | inf t => simp_all [evalClass, evalMul, SpecialClass.mul]
    | num d =>
      by_cases hd : d.num = 0 <;>
        simp_all [evalClass, evalMul, SpecialClass.mul]
  | num a =>
    cases y with
    | nan =>
      by_cases ha : a.num = 0 <;> simp_all [evalClass, evalMul, SpecialClass.mul]
    | inf t =>
      by_cases ha : a.num = 0 <;>
        simp_all [evalClass, evalMul, SpecialClass.mul]
    | num b =>
      by_cases ha : a.num = 0 <;> by_cases hb : b.num = 0 <;>
        simp_all [evalClass, evalMul, SpecialClass.mul]

/-- **`evalAdd` is SPEC §8.2's sum table.** -/
theorem classOf_evalAdd {x y : EVal} {c : SpecialClass}
    (h : SpecialClass.add (evalClass x) (evalClass y) = some c) :
    evalClass (evalAdd x y) = c := by
  cases x with
  | nan => cases y <;> simp_all [evalClass, evalAdd, SpecialClass.add]
  | inf s =>
    cases y with
    | nan => simp_all [evalClass, evalAdd, SpecialClass.add]
    | inf t =>
      by_cases hst : s = t <;> simp_all [evalClass, evalAdd, SpecialClass.add]
    | num d =>
      by_cases hd : d.num = 0 <;> simp_all [evalClass, evalAdd, SpecialClass.add]
  | num a =>
    cases y with
    | nan =>
      by_cases ha : a.num = 0 <;> simp_all [evalClass, evalAdd, SpecialClass.add]
    | inf t =>
      by_cases ha : a.num = 0 <;> simp_all [evalClass, evalAdd, SpecialClass.add]
    | num b =>
      by_cases ha : a.num = 0 <;> by_cases hb : b.num = 0 <;>
        simp_all [evalClass, evalAdd, SpecialClass.add]


/-- The format of a floating stored kind.  Total by construction; it is only
ever applied to a floating kind, because a compatible descriptor in a floating
mode has floating stored kinds (`Gemm.compatible_*`). -/
def formatOf (k : ScalarKind) : FloatFormat :=
  (k.floatFormat?).getD FloatFormat.binary64

@[simp] theorem formatOf_binary16 : formatOf .binary16 = FloatFormat.binary16 := rfl
@[simp] theorem formatOf_bfloat16 : formatOf .bfloat16 = FloatFormat.bfloat16 := rfl
@[simp] theorem formatOf_binary32 : formatOf .binary32 = FloatFormat.binary32 := rfl
@[simp] theorem formatOf_binary64 : formatOf .binary64 = FloatFormat.binary64 := rfl

end WasmGemmGnaf.Gemm
