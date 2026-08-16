import WasmGemmGnaf.Wasm.Core.ValidateModuleSources

set_option autoImplicit false

/-!
# Closing source function types for runtime activation

Module validation types function bodies against rolled source types.  Runtime
allocation stores the corresponding closed types.  These lemmas expose the
exact computational transport for function expansions; they do not assert a
typing or progress conclusion.
-/

namespace WasmGemmGnaf.Wasm.Core

/-- Close every value type in a compact result-type sequence using the exact
type vector of a validation context. -/
def Context.closValTypes (context : Context) (types : ValTypes) : ValTypes :=
  substValTypes types (idxVars context.closTypes.length) context.closTypes

/-- Closing a source defined type commutes with function expansion, closing
both its domain and codomain pointwise. -/
theorem Expand.close_func {context : Context} {definedType : DefType}
    {domain codomain : ValTypes}
    (hexpand : Expand definedType (.func domain codomain)) :
    Expand (context.closDefType definedType)
      (.func (context.closValTypes domain) (context.closValTypes codomain)) := by
  cases hexpand with
  | mk hexpand =>
      apply Expand.mk
      have hclose := Validate.expandDt_close
        (closDefTypes context.types) definedType
      rw [hexpand] at hclose
      simpa [Context.closDefType, Context.closTypes, Context.closValTypes,
        substCompType] using hclose

/-- Function expansion is functional after closing: any runtime expansion of
the same closed source type has exactly the closed source domain and codomain. -/
theorem Expand.closed_func_eq {context : Context} {definedType : DefType}
    {sourceDomain sourceCodomain runtimeDomain runtimeCodomain : ValTypes}
    (hsource : Expand definedType (.func sourceDomain sourceCodomain))
    (hruntime : Expand (context.closDefType definedType)
      (.func runtimeDomain runtimeCodomain)) :
    runtimeDomain = context.closValTypes sourceDomain ∧
      runtimeCodomain = context.closValTypes sourceCodomain := by
  have hclosed := hsource.close_func (context := context)
  cases hclosed with
  | mk hclosed =>
      cases hruntime with
      | mk hruntime =>
          have heq :
              CompType.func runtimeDomain runtimeCodomain =
                .func (context.closValTypes sourceDomain)
                  (context.closValTypes sourceCodomain) :=
            Option.some.inj (hruntime.symm.trans hclosed)
          exact ⟨CompType.func.inj heq |>.1, CompType.func.inj heq |>.2⟩

/-- Numeric value types are unchanged by context closure. -/
@[simp] theorem Context.closValTypes_i32 (context : Context) :
    context.closValTypes (ValTypes.ofList [.num .i32]) =
      ValTypes.ofList [.num .i32] := by
  rfl

/-- The released two-argument numeric domain is unchanged by closure. -/
@[simp] theorem Context.closValTypes_i32_i32 (context : Context) :
    context.closValTypes
        (ValTypes.ofList [.num .i32, .num .i32]) =
      ValTypes.ofList [.num .i32, .num .i32] := by
  rfl

/-- Closure cannot turn a non-`i32` source result into the released scalar
result shape. -/
theorem Context.closValTypes_eq_i32 {context : Context} {types : ValTypes}
    (h : context.closValTypes types =
      ValTypes.ofList [.num .i32]) :
    types = ValTypes.ofList [.num .i32] := by
  cases types with
  | nil => simp [Context.closValTypes, substValTypes, ValTypes.ofList] at h
  | cons type rest =>
      cases type <;> cases rest <;>
        simp_all [Context.closValTypes, substValTypes, substValType,
          ValTypes.ofList]

/-- Closure cannot change the released two-`i32` argument shape. -/
theorem Context.closValTypes_eq_i32_i32 {context : Context}
    {types : ValTypes}
    (h : context.closValTypes types =
      ValTypes.ofList [.num .i32, .num .i32]) :
    types = ValTypes.ofList [.num .i32, .num .i32] := by
  cases types with
  | nil => simp [Context.closValTypes, substValTypes, ValTypes.ofList] at h
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;>
            simp_all [Context.closValTypes, substValTypes, substValType,
              ValTypes.ofList]
      | cons second tail =>
          cases first <;> cases second <;> cases tail <;>
            simp_all [Context.closValTypes, substValTypes, substValType,
              ValTypes.ofList]

end WasmGemmGnaf.Wasm.Core
