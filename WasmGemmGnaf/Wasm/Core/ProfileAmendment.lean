/-
  Wasm/Core/ProfileAmendment.lean --- profile validity under the canonical
  Core 3.0 authority-amendment set.

  Amendment identity and exact source patches live only in
  `Wasm/AuthorityAmendments.lean`.  This file supplies the semantic consumer:
  the profile-validity predicate uses the combined `Module_okA` hierarchy,
  which composes the instruction-sequence, bottom-subtyping, and free-index
  repairs.  The earlier single-amendment module hierarchy is not on this path.

  The executable validator is used only through its proved soundness theorem to
  construct two concrete anti-vacuity witnesses.  `Module.ValidUnder` itself is
  entirely declarative: existence of a `Module_okA` derivation, conjoined with
  the profile-admission predicate.
-/
import WasmGemmGnaf.Wasm.Core.ValidateModule
import WasmGemmGnaf.Wasm.Core.Profile

set_option autoImplicit false
set_option maxRecDepth 100000

namespace WasmGemmGnaf.Wasm.Core

/-- A module is valid under a profile exactly when the combined amended Core
3.0 rules assign it a module type and the released profile admits it. -/
def Module.ValidUnder (P : Profile) (m : Module) : Prop :=
  (∃ mt : ModuleType, Module_okA m mt) ∧ Module.AdmittedBy P m

/-- Sound executable validation is one way to construct the declarative half;
profile admission remains an independent premise. -/
theorem Module.validUnder_of_validate {P : Profile} {m : Module}
    (hv : validate m = true) (ha : Module.AdmittedBy P m) :
    Module.ValidUnder P m :=
  ⟨validate_sound hv, ha⟩

theorem Module.admittedBy_of_validUnder {P : Profile} {m : Module}
    (h : Module.ValidUnder P m) : Module.AdmittedBy P m := h.2

theorem Module.module_okA_of_validUnder {P : Profile} {m : Module}
    (h : Module.ValidUnder P m) : ∃ mt : ModuleType, Module_okA m mt := h.1

/-- A rejected feature family prevents profile validity independently of the
module's declarative typing derivation. -/
theorem Module.not_validUnder_of_rejected (P : Profile) (m : Module)
    {f : FeatureFamily} (hmem : f ∈ Module.requiredFeatures m) (hf : Rejected f) :
    ¬ Module.ValidUnder P m :=
  fun h => Module.not_admittedBy_of_rejected P m hmem hf h.2

/-! ## Concrete anti-vacuity witnesses -/

/-- The released baseline has a derivation in the combined amended module
judgment.  The validator's already-proved soundness constructs that derivation;
no completeness or reflection equivalence is used. -/
theorem releaseBaselineModule_module_okA :
    ∃ mt : ModuleType, Module_okA releaseBaselineModule mt :=
  validate_sound (by decide)

/-- The released baseline is valid under every lawful released profile. -/
theorem releaseBaselineModule_validUnder (P : Profile) :
    Module.ValidUnder P releaseBaselineModule :=
  ⟨releaseBaselineModule_module_okA, releaseBaselineModule_admitted P⟩

/-- The memory64 variant is also declaratively Core-valid; its rejection below
is therefore a profile decision rather than a missing typing derivation. -/
theorem memory64Module_module_okA :
    ∃ mt : ModuleType, Module_okA memory64Module mt :=
  validate_sound (by decide)

theorem memory64Module_not_validUnder (P : Profile) :
    ¬ Module.ValidUnder P memory64Module :=
  Module.not_validUnder_of_rejected (f := FeatureFamily.memory64) P _
    memory64Module_uses_memory64 (by decide)

end WasmGemmGnaf.Wasm.Core
