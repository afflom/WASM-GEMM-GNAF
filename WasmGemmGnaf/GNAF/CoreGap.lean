/-
  GNAF/CoreGap.lean --- BI-009: no total map from the legacy release-path
  instruction syntax to the pinned Core 3.0 instructions preserves `i32`
  constants.

  ## The obstruction

  `Wasm.Instr.i32Const : Int -> Instr`: the legacy release path's `i32` literal
  is an UNBOUNDED integer.  The pinned syntax is not.  `2-syntax.values.spectec`
  fixes

      syntax uN(N) = 0 | ... | 2^N-1        syntax iN(N) = uN(N)

  and `3-syntax.instructions.spectec` fixes `CONST num_(numtype)`, so a Core 3.0
  `i32` literal is a `u32` and nothing else --- `no_core_i32_lit_two_pow_32`
  below.  `Wasm.Instr.i32Const (2 ^ 32)` is therefore outside the image of any
  constant-preserving map --- `no_i32const_preserving_map`.

  ## What became of the reachability witnesses

  Earlier revisions of this file also proved the gap REACHABLE from the legacy
  subset compiler: `GNAF.bodyCode` appended `i32.const e.statusAddr` to every
  compiled body with no clamp on the address, and the `nop` plan typed at an
  interface declaring `2 ^ 30` memory cells compiled to a body carrying
  `i32.const (2 ^ 32)` (`compile_body_mem_statusAddr`,
  `compile_gapChecked_emits_two_pow_32`).  The compiler change those witnesses
  priced has since been made: `GNAF/Compile.lean` now constructs
  `Wasm.Core.Instr` directly, and every conversion from a source `Nat` to a
  Core literal is reached only through `CheckedPlan.coreRepresentable` --- no
  address or page count is clamped.  The legacy subset compiler was removed in
  that migration, so the reachability witnesses retired with their subject.
  The type-level obstruction below is unchanged and remains the discharged
  content of BI-009; the public-Core compiler obligations continue under
  BI-010 and BI-002.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Syntax
import WasmGemmGnaf.Wasm.Core.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

/-! ## 1. The pinned bound on a Core 3.0 `i32` literal -/

/-- The `i32` constant a pinned Core 3.0 instruction carries, if it is one. -/
def coreI32Const? : Wasm.Core.Instr → Option Nat
  | .const .i32 c => some c.val
  | _ => none

/-- The `i32` constant a release-path instruction carries, if it is one. -/
def subsetI32Const? : Wasm.Instr → Option Int
  | .i32Const z => some z
  | _ => none

/-- **The pinned bound.**  Every `i32` literal of the Core 3.0 syntax is a
`u32`: `syntax num_(I32) = iN(32) = uN(32) = 0 | ... | 2^32-1`.  In particular
none of them is `2 ^ 32`. -/
theorem no_core_i32_lit_two_pow_32 (i : Wasm.Core.Instr) :
    coreI32Const? i ≠ some (2 ^ 32) := by
  cases i with
  | const nt c =>
      cases nt with
      | i32 =>
          intro h
          simp only [coreI32Const?, Option.some.injEq] at h
          exact absurd h (Nat.ne_of_lt c.property)
      | i64 => simp [coreI32Const?]
      | f32 => simp [coreI32Const?]
      | f64 => simp [coreI32Const?]
  | _ => simp [coreI32Const?]

/-! ## 2. BI-009 -/

/-- **BI-009.**  No total map from the release path's instructions to the pinned
Core 3.0 instructions preserves `i32` constants.

The witness is `Wasm.Instr.i32Const (2 ^ 32)`: the legacy syntax holds it, and
`no_core_i32_lit_two_pow_32` shows the pinned syntax has no image for it.
Emitting Core 3.0 therefore requires the compiler to carry a `< 2 ^ 32` bound
on its layout rather than translate legacy instructions --- the change
`GNAF/Compile.lean` has since made through `CheckedPlan.coreRepresentable`. -/
theorem no_i32const_preserving_map :
    ¬ ∃ f : Wasm.Instr → Wasm.Core.Instr,
        ∀ i : Wasm.Instr,
          (coreI32Const? (f i)).map Int.ofNat = subsetI32Const? i := by
  rintro ⟨f, hf⟩
  have h := hf (Wasm.Instr.i32Const (2 ^ 32))
  have hr : subsetI32Const? (Wasm.Instr.i32Const (2 ^ 32)) = some (2 ^ 32) := rfl
  rw [hr] at h
  cases hc : coreI32Const? (f (Wasm.Instr.i32Const (2 ^ 32))) with
  | none => rw [hc] at h; simp at h
  | some n =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hcast : (n : Int) = 2 ^ 32 := h
      have hn : n = 2 ^ 32 := by omega
      exact no_core_i32_lit_two_pow_32 _ (hn ▸ hc)

end WasmGemmGnaf.GNAF
