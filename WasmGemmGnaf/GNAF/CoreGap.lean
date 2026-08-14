/-
  GNAF/CoreGap.lean --- BI-009: `GNAF.compile` reaches an instruction the
  pinned Core 3.0 syntax cannot hold.

  ## Why this file exists

  The migration brief for the release path says: move `GNAF/Compile.lean` and
  everything downstream from `Wasm.Subset.Module` to `Wasm.Core.Module`; and it says
  that if `GNAF.compile` cannot emit Core modules without a real compiler
  change, report that rather than invent a bridge.  `Wasm/CoreGap.lean` already
  proves that no total map preserves all subset function type indices or export
  name bytes.  It does not deny arbitrary total functions between the carrier
  types.  This file settles the instruction-level preservation obstruction,
  which is where the compiler actually lives, and does so on the compiler's own
  output rather than an arbitrary syntax term.

  ## The obstruction

  `GNAF.constI n = Wasm.Instr.i32Const (Int.ofNat n)` and
  `Wasm.Instr.i32Const : Int -> Instr`: the release path's `i32` literal is an
  UNBOUNDED integer.  The pinned syntax is not.  `2-syntax.values.spectec` fixes

      syntax uN(N) = 0 | ... | 2^N-1        syntax iN(N) = uN(N)

  and `3-syntax.instructions.spectec` fixes `CONST num_(numtype)`, so a Core 3.0
  `i32` literal is a `u32` and nothing else --- `no_core_i32_lit_two_pow_32`
  below.

  ## The gap is REACHABLE from `GNAF.compile`, not merely present in the type

  `GNAF.bodyCode e scr p = code e 0 scr p ++ loadAt e.statusAddr`, so EVERY
  compiled module's function body ends with `i32.const e.statusAddr` followed by
  the `i32` load: the status word is the ABI result and the compiler always
  reads it.  `e.statusAddr` is `4 * memWords + 4 * scratchWords + 4 * (tableCount
  * tableStride)`, and nothing clamps it --- `CompileEnv.pages` is clamped to the
  hard page limit, the ADDRESSES are not.

  `gapChecked` is an ordinary `GNAF.CheckedPlan`: the plan is `nop`, and
  `HasType.nop` types it at every interface, so there is no side condition to
  argue about.  Its interface declares `2 ^ 30` memory cells, which is what
  `Sig.mem` is, and `compile_gapChecked_emits_two_pow_32` shows the compiled
  body carries `i32.const (2 ^ 32)`.

  ## What this file proves, exactly

  * `no_core_i32_lit_two_pow_32` --- no Core 3.0 `i32` literal is `2 ^ 32`.
  * `compile_gapChecked_emits_two_pow_32` --- `GNAF.compile` emits that literal
    on a checked plan.
  * `no_i32const_preserving_map` --- therefore no total map from the release
    path's instructions to the pinned Core 3.0 instructions preserves `i32`
    constants, and the release path's emitted instruction really is outside the
    image of any such map.

  ## What it does NOT claim

  It does not claim `GNAF.compile` is wrong, nor that the modules it emits for
  SMALL layouts are inexpressible --- they are not, and
  `Wasm/CoreArtifact.lean` exhibits a Core 3.0 module of exactly the released
  ABI shape, with bytes.  It claims one thing: emitting Core 3.0 requires the
  compiler to CARRY a `< 2 ^ 32` bound on its layout, which `GNAF.CompileEnv`
  does not have and which `GNAF.envOf` cannot manufacture from a `Sig`, because
  `Sig.mem`, `Sig.scratch` and `Sig.tables` are unbounded `Nat`s.  That is a
  change to the compiler and its address lemmas, not a translation of its
  output.  This is the discharged negative result `BI-009`; the direct bounded
  public-Core compiler remains open as `BI-010`, and full arithmetic-mode
  support remains separately open as `BI-002`.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.GNAF.Compile
import WasmGemmGnaf.Wasm.Core.Instructions

set_option autoImplicit false
set_option maxRecDepth 100000

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

/-! ## 2. The compiler reaches it

Every compiled body ends with `i32.const e.statusAddr`, because `bodyCode`
appends `loadAt e.statusAddr`. -/

/-- The status-word read that `GNAF.bodyCode` appends to every compiled body. -/
theorem bodyCode_suffix (e : CompileEnv) (scr : Nat) (p : Plan) :
    bodyCode e scr p = code e 0 scr p ++ [constI e.statusAddr, loadW] := rfl

/-- **Every** compiled module carries the `i32` constant `e.statusAddr` in its
function body. -/
theorem compile_body_mem_statusAddr {s t : Sig} (c : CheckedPlan s t) :
    Wasm.Instr.i32Const (Int.ofNat (envOf s c.plan).statusAddr) ∈
      ((compile c).funcs[0]!.body).toList := by
  have hfuncs : (compile c).funcs =
      [{ type := 0
         locals := List.replicate (envOf s c.plan).declaredLocals
           (Wasm.ValType.num .i32)
         body := Wasm.Expr.ofList
           (bodyCode (envOf s c.plan) s.scratch c.plan) }] := rfl
  rw [hfuncs]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero,
    Option.getD_some, Wasm.Expr.toList_ofList]
  rw [bodyCode_suffix]
  exact List.mem_append_right _ (by simp [constI])

/-! ## 3. The witness

`Sig.mem` is the observable memory extent in CELLS, and `CompileEnv.memAddr`
scales it by four, so `2 ^ 30` cells put the status word at exactly `2 ^ 32`. -/

/-- An interface declaring `2 ^ 30` memory cells.  Nothing else is unusual about
it, and `HasType.nop` types `nop` at every interface whatsoever. -/
def gapSig : Sig := { (default : Sig) with mem := 2 ^ 30 }

/-- An ordinary checked plan at that interface. -/
def gapChecked : CheckedPlan gapSig gapSig := ⟨.nop, HasType.nop _⟩

/-- Its layout puts the status word at `2 ^ 32`, one past the largest `u32`. -/
theorem gapChecked_statusAddr :
    (envOf gapSig gapChecked.plan).statusAddr = 2 ^ 32 := by
  rfl

/-- **The release path's compiler emits an inexpressible literal.**  This is not
a term somebody could write; it is what `GNAF.compile` returns on a checked
plan. -/
theorem compile_gapChecked_emits_two_pow_32 :
    Wasm.Instr.i32Const (2 ^ 32) ∈
      ((compile gapChecked).funcs[0]!.body).toList := by
  have h := compile_body_mem_statusAddr gapChecked
  rw [gapChecked_statusAddr] at h
  exact h

/-! ## 4. BI-009 -/

/-- **BI-009.**  No total map from the release path's instructions to the pinned
Core 3.0 instructions preserves `i32` constants.

The witness is not hypothetical: `compile_gapChecked_emits_two_pow_32` shows
`GNAF.compile` emits `Wasm.Instr.i32Const (2 ^ 32)` on an ordinary checked plan,
and `no_core_i32_lit_two_pow_32` shows the pinned syntax has no image for it.
Migrating `GNAF.compile` to `Wasm.Core.Module` therefore requires the compiler
to carry a `< 2 ^ 32` bound on its layout --- a change to `GNAF.CompileEnv`,
`GNAF.envOf` and every address lemma stated over them --- and not a translation
of the compiler's existing output. -/
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
