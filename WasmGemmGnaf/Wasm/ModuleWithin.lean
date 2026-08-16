import WasmGemmGnaf.Wasm.CoreValidation
import WasmGemmGnaf.Wasm.Core.Profile
import WasmGemmGnaf.Wasm.Core.Encode

set_option autoImplicit false

/-!
# Static public-module resource envelope

`ModuleWithin` is the static half of SPEC section 11.4's compiler resource
contract.  It deliberately states only facts determined by the module itself:
amended-Core validation, the profile's declaration/table/memory limits, and a
structural bound on every emitted function body.  Execution prefixes and their
dynamic resource vectors are governed by `Wasm.FiniteExecution` and the public
costed evaluator; they are not smuggled into this syntax predicate.
-/

namespace WasmGemmGnaf.Wasm

/-- Structural Core instruction count of all defined function bodies.  Nested
structured instructions contribute their complete bodies through
`Core.Binary.instrsSize`. -/
def moduleCodeSize (module : Module) : Nat :=
  (module.core.funcs.map fun func => Core.Binary.instrsSize func.body).sum

/-- A representable module is statically within a profile and a supplied code
budget exactly when it validates, its declaration spaces satisfy the profile's
stored limits, and its complete function bodies fit the budget. -/
def ModuleWithin (profile : Profile) (module : Module) (codeBound : Nat) : Prop :=
  validate module = true ∧
    Core.Module.withinLimitsOf profile module.core = true ∧
    moduleCodeSize module ≤ codeBound

instance instDecidableModuleWithin (profile : Profile) (module : Module)
    (codeBound : Nat) : Decidable (ModuleWithin profile module codeBound) := by
  unfold ModuleWithin
  exact inferInstance

end WasmGemmGnaf.Wasm
