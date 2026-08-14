import WasmGemmGnaf.Foundation.FloatBits
import WasmGemmGnaf.Gemm.Scalar

set_option autoImplicit false

namespace WasmGemmGnaf.Gemm

open WasmGemmGnaf.Foundation

/-! ## Attaching formats to scalar kinds -/

namespace ScalarKind

/-- The interchange format of a floating stored kind. -/
def floatFormat? : ScalarKind → Option FloatFormat
  | binary16 => some FloatFormat.binary16
  | bfloat16 => some FloatFormat.bfloat16
  | binary32 => some FloatFormat.binary32
  | binary64 => some FloatFormat.binary64
  | _ => none

theorem floatFormat?_isSome_iff (k : ScalarKind) :
    (k.floatFormat?).isSome = true ↔ k.isFloat = true := by
  cases k <;> decide

/-- The format width agrees with the stored width of the kind. -/
theorem floatFormat?_totalBits (k : ScalarKind) (f : FloatFormat)
    (h : k.floatFormat? = some f) : f.totalBits = k.bitWidth := by
  cases k <;> simp only [floatFormat?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-- The canonical quiet NaN pattern of a floating stored kind (SPEC §8.2). -/
def canonicalQuietNaN? (k : ScalarKind) : Option Nat :=
  (k.floatFormat?).map FloatFormat.canonicalQuietNaN

theorem canonicalQuietNaN?_binary16 : binary16.canonicalQuietNaN? = some 0x7e00 := by decide
theorem canonicalQuietNaN?_bfloat16 : bfloat16.canonicalQuietNaN? = some 0x7fc0 := by decide
theorem canonicalQuietNaN?_binary32 :
    binary32.canonicalQuietNaN? = some 0x7fc00000 := by decide
theorem canonicalQuietNaN?_binary64 :
    binary64.canonicalQuietNaN? = some 0x7ff8000000000000 := by decide

/-- Signaling-NaN detection at the level of stored kinds: non-floating kinds
never signal. -/
def isSignalingNaNBits (k : ScalarKind) (bits : Nat) : Bool :=
  match k.floatFormat? with
  | some f => f.isSignalingNaN bits
  | none => false

theorem isSignalingNaNBits_of_integer (k : ScalarKind) (bits : Nat)
    (h : k.isInteger = true) : k.isSignalingNaNBits bits = false := by
  cases k <;> simp_all [isSignalingNaNBits, floatFormat?, isInteger]

theorem isSignalingNaNBits_canonicalQuietNaN (k : ScalarKind) (f : FloatFormat)
    (h : k.floatFormat? = some f) :
    k.isSignalingNaNBits f.canonicalQuietNaN = false := by
  cases k <;> simp only [floatFormat?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp only [isSignalingNaNBits, floatFormat?] <;> decide

end ScalarKind

end WasmGemmGnaf.Gemm
