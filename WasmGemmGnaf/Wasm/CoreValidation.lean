/-
  The public amended-Core validation facade.

  The legacy subset checker is retained only as `Wasm.Subset.validate`.  The
  definitions here expose the one public `Wasm.Module` carrier and the combined
  AMD-005/011/013 declarative hierarchy.  Soundness is unconditional.  The
  reverse implication is deliberately not asserted: the current executable
  checker has only the explicitly fragment-scoped completeness theorem in
  `Core/ValidateComplete.lean`.
-/
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Core.ValidateComplete
import WasmGemmGnaf.Wasm.Core.ProfileAmendment

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-- The executable amended-Core validator on the public representable carrier. -/
def validate (module : Module) : Bool := Core.validate module.core

/-- The independent combined amended Core 3.0 module judgment. -/
def DeclarativelyValid (module : Module) : Prop :=
  ∃ moduleType : Core.ModuleType, Core.Module_okA module.core moduleType

/-- Every module accepted by the executable checker has an amended declarative
derivation. -/
theorem validate_sound {module : Module} (h : validate module = true) :
    DeclarativelyValid module :=
  Core.validate_sound h

/-- Executable profile validation combines amended Core validation with the
profile's exact, stored admission matrix. -/
def validateUnder (profile : Profile) (module : Module) : Bool :=
  validate module && Core.Module.admittedBy profile module.core

/-- Public profile validation is sound for the independent declarative
validity-and-admission proposition. -/
theorem validateUnder_sound {profile : Profile} {module : Module}
    (h : validateUnder profile module = true) :
    Core.Module.ValidUnder profile module.core := by
  rw [validateUnder, Bool.and_eq_true] at h
  exact Core.Module.validUnder_of_validate h.1 h.2

/-- A public profile-valid module is admitted by the exact profile matrix. -/
theorem admittedBy_of_validateUnder {profile : Profile} {module : Module}
    (h : validateUnder profile module = true) :
    Core.Module.AdmittedBy profile module.core :=
  (validateUnder_sound h).2

end WasmGemmGnaf.Wasm
