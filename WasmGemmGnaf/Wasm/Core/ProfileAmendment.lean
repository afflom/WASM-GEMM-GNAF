/-
  Wasm/Core/ProfileAmendment.lean --- the IDENTITY BINDING of the grammar
  amendment, and the profile-level notion of validity it feeds.

  WHY THIS FILE EXISTS.  `Wasm/Core/Validation/InstructionsAmended.lean` states
  the amendment `AMD-005` / `DEV-006` requires, and proves it correct.  What it
  does not do --- what no Lean file can do by itself --- is make "this
  repository validates against an amendment, stated against THAT pinned source,
  answering THAT upstream defect, and not advancing the pin" a checkable fact
  rather than a paragraph.  `Wasm/Revision.lean` now carries
  `core3InstrSeqAmendment`, a first-order body with a canonical identity, in
  exactly the shape `core3VendoredTree` uses for the vendored tree.  This file
  is the other half of that binding: every property the record CLAIMS is
  discharged here by a theorem about the amended relation itself.

  THE FOUR BOUND FLAGS.  `GrammarAmendmentBody` stores no count of rules or
  premises --- "one modified premise and no new rule" is a statement about the
  SHAPE of a Lean inductive, which Lean cannot state about itself, and a field
  holding it would be prose wearing a field name.  What it stores are four
  properties that CAN be discharged, and here they are:

  * `pinAdvanced = false` --- `amendment_pin_not_advanced`, together with the
    vendored tree still standing at the pin and not at upstream's repair.
  * `noRegression = true` --- `amendment_noRegression`: every pinned derivation
    is an amended one, at sequence, expression, function and MODULE level.
  * `strictlyWider = true` --- `amendment_strictlyWider`: an explicit sequence
    the amended rules type and the pinned rules provably cannot, so the
    amendment is not a no-op wearing a flag.
  * `arityPreserved = true` --- `amendment_arityPreserved`: the pinned arity
    discipline, re-proved against the amended relation in every context at every
    instruction type.

  A record whose flags did not hold would fail to compile here, and a record
  that drifted would change `GrammarAmendmentBody.identity`.  That is the whole
  point of the exercise.

  WHAT IS STILL NOT PROVED, STATED PLAINLY.  Containment of the amended relation
  in the CORRECTED UPSTREAM rules (`bd4633ac`) is a different statement, and the
  pin is deliberately not advanced, so those rules are not transcribed in this
  repository and there is nothing here to state it against.  `validate_bool_iff`
  remains outstanding; nothing in this file discharges it.

  Every declaration in this file is proved.  Nothing is assumed, and no
  declaration here carries a Core 3.0 coverage marker.
-/
import WasmGemmGnaf.Wasm.Core.ValidateModule
import WasmGemmGnaf.Wasm.Core.Profile

set_option autoImplicit false
set_option maxRecDepth 100000

namespace WasmGemmGnaf.Wasm.Core

/-! ## The recorded amendment is the amendment this repository carries -/

/-- **The pin is not advanced.**  The recorded flag says so, the recorded
pinned commit is the pinned revision's, and the vendored tree still stands at
that same commit rather than at upstream's repair --- which is what "not
advanced" means operationally. -/
theorem amendment_pin_not_advanced :
    core3InstrSeqAmendment.pinAdvanced = false ∧
    core3InstrSeqAmendment.pinnedCommit = core3Revision.commit ∧
    core3VendoredTree.commit = core3InstrSeqAmendment.pinnedCommit ∧
    core3InstrSeqAmendment.upstreamRepairCommit ≠ core3VendoredTree.commit :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- **`noRegression = true` is a theorem.**  The amended judgments accept
everything the pinned judgments accept, at every level SPEC section 7.3 names:
instruction sequences, expressions, functions and whole modules. -/
theorem amendment_noRegression :
    core3InstrSeqAmendment.noRegression = true ∧
    (∀ (C : Context) (is : List Instr) (it : InstrType),
      Instrs_ok C is it → Instrs_ok' C is it) ∧
    (∀ (C : Context) (e : Expr) (ts : List ValType),
      Expr_ok C e ts → Expr_ok' C e ts) ∧
    (∀ (C : Context) (f : Func) (dt : DefType),
      Func_ok C f dt → Func_ok' C f dt) ∧
    (∀ (m : Module) (mt : ModuleType), Module_ok m mt → Module_ok' m mt) :=
  ⟨rfl,
   fun _ _ _ h => h.to_amended,
   fun _ _ _ h => h.to_amended,
   fun _ _ _ h => h.to_amended,
   fun _ _ h => h.to_amended⟩

/-- **`strictlyWider = true` is a theorem.**  `(I32.CONST 0) (BINOP I32 ADD)`
--- the smallest instance of the pinned defect, and the shape of every binary
arithmetic expression --- is typed by the amended rules in every context, and
`Validate.Instrs_ok.const_binop_untypable` proves the pinned rules give it no
type in any context at all.

Without this the amendment could be the pinned relation under a new name and
`noRegression` would still hold. -/
theorem amendment_strictlyWider :
    core3InstrSeqAmendment.strictlyWider = true ∧
    ∃ (C : Context) (is : List Instr) (it : InstrType),
      Instrs_ok' C is it ∧ ¬ Instrs_ok C is it := by
  refine ⟨rfl, Context.empty,
    [Instr.const .i32 (default : Num_ .i32), Instr.binop .i32 (.int .add)],
    ⟨[ValType.i32], [], [ValType.i32]⟩, ?_, ?_⟩
  · exact Instrs_ok'.const_binop rfl
  · intro h
    exact Validate.Instrs_ok.const_binop_untypable h rfl

/-- **`arityPreserved = true` is a theorem.**  The amendment supplies missing
operands from the frame; it must not invent them.  Under the AMENDED rules the
empty sequence is still balanced, `CONST` still pushes exactly one operand, and
`BINOP` still consumes two and nets minus one --- in every context, at every
instruction type.  `binop_dom_length` is the very lemma that drives the pinned
negative result, re-proved against the amended relation. -/
theorem amendment_arityPreserved :
    core3InstrSeqAmendment.arityPreserved = true ∧
    (∀ (C : Context) (it : InstrType),
      Instrs_ok' C [] it → it.dom.length = it.cod.length) ∧
    (∀ (C : Context) (nt : NumType) (c : Num_ nt) (it : InstrType),
      Instrs_ok' C [Instr.const nt c] it → it.cod.length = it.dom.length + 1) ∧
    (∀ (C : Context) (nt : NumType) (op : Binop) (it : InstrType),
      Instrs_ok' C [Instr.binop nt op] it → 2 ≤ it.dom.length) ∧
    (∀ (C : Context) (nt : NumType) (op : Binop) (it : InstrType),
      Instrs_ok' C [Instr.binop nt op] it → it.cod.length + 1 = it.dom.length) :=
  ⟨rfl,
   fun _ _ h => Instrs_ok'.nil_length h rfl,
   fun _ _ _ _ h => Instrs_ok'.const_length h rfl,
   fun _ _ _ _ h => Instrs_ok'.binop_dom_length h rfl,
   fun _ _ _ _ h => Instrs_ok'.binop_length h rfl⟩

/-- **The whole record, discharged.**  Each of the four stored flags is exactly
the property proved above, so `core3InstrSeqAmendment` describes the amendment
this repository actually carries and `GrammarAmendmentBody.identity` of it is a
binding rather than a label. -/
theorem amendment_flags_discharged :
    core3InstrSeqAmendment.pinAdvanced = false ∧
    core3InstrSeqAmendment.noRegression = true ∧
    core3InstrSeqAmendment.strictlyWider = true ∧
    core3InstrSeqAmendment.arityPreserved = true :=
  ⟨amendment_pin_not_advanced.1, amendment_noRegression.1,
   amendment_strictlyWider.1, amendment_arityPreserved.1⟩

/-- The recorded amendment names the relation the module validator is proved
sound against.  `Wasm.Core.validate_sound` concludes `Module_ok'`, and
`amendedRelation` records that name; the two are kept honest by the theorem
below, which USES the validator's conclusion. -/
theorem amendment_amendedRelation :
    core3InstrSeqAmendment.amendedRelation = "WasmGemmGnaf.Wasm.Core.Instrs_ok'" :=
  rfl

/-! ## `validateUnder Release.wasmProfile`

SPEC section 7.2 asks for one predicate, and it has two halves: is the module a
well-typed Core 3.0 module, and does it stay inside the released profile.  The
first half is `Module_ok'` --- the amended judgment, for the reason `DEV-006`
gives --- and the second is `Module.AdmittedBy` of `Wasm/Core/Profile.lean`.
`Module.ValidUnder` is their conjunction, and it is the notion the migration of
`Artifact/Release.lean` needs. -/

/-- **A module is valid under a profile** when it is a well-typed Core 3.0
module in the amended judgment AND the profile admits it. -/
def Module.ValidUnder (P : Profile) (m : Module) : Prop :=
  (∃ mt : ModuleType, Module_ok' m mt) ∧ Module.AdmittedBy P m

/-- The executable route in: whatever the module validator of
`Core/ValidateModule.lean` accepts and the profile admits is valid under the
profile.  Both halves are decidable, so this is a computation. -/
theorem Module.validUnder_of_validate {P : Profile} {m : Module}
    (hv : validate m = true) (ha : Module.AdmittedBy P m) :
    Module.ValidUnder P m :=
  ⟨validate_sound hv, ha⟩

/-- The declarative route in: a module the PINNED rules type is a fortiori
typed by the amended ones, so a pinned-valid admitted module is valid under the
profile.  This is where `noRegression` earns its keep. -/
theorem Module.validUnder_of_pinned {P : Profile} {m : Module} {mt : ModuleType}
    (hok : Module_ok m mt) (ha : Module.AdmittedBy P m) :
    Module.ValidUnder P m :=
  ⟨⟨mt, hok.to_amended⟩, ha⟩

theorem Module.admittedBy_of_validUnder {P : Profile} {m : Module}
    (h : Module.ValidUnder P m) : Module.AdmittedBy P m := h.2

theorem Module.module_ok'_of_validUnder {P : Profile} {m : Module}
    (h : Module.ValidUnder P m) : ∃ mt : ModuleType, Module_ok' m mt := h.1

/-- A module using a rejected family is not valid under any profile, however
well-typed it is. -/
theorem Module.not_validUnder_of_rejected (P : Profile) (m : Module)
    {f : FeatureFamily} (hmem : f ∈ Module.requiredFeatures m) (hf : Rejected f) :
    ¬ Module.ValidUnder P m :=
  fun h => Module.not_admittedBy_of_rejected P m hmem hf h.2

/-! ### Anti-vacuity, both halves at once

`Module.ValidUnder` would be satisfied by nothing if either half were too
strong.  The released baseline shape of `Wasm/Core/Profile.lean` passes the
module validator and is admitted by every profile. -/

/-- The released baseline shape is accepted by the Core 3.0 module validator. -/
theorem releaseBaselineModule_validates :
    validate releaseBaselineModule = true := by decide

/-- **The released baseline shape is valid under the released profile.**  Both
halves: core-valid in the amended judgment, and profile-admitted. -/
theorem releaseBaselineModule_validUnder (P : Profile) :
    Module.ValidUnder P releaseBaselineModule :=
  Module.validUnder_of_validate releaseBaselineModule_validates
    (releaseBaselineModule_admitted P)

/-- The memory64 module is core-valid too, and still not valid under any
profile: the rejection is the PROFILE's, not the type system's --- which is
what SPEC section 7.2's "decode when grammatically valid and then fail profile
validation" asserts. -/
theorem memory64Module_validates : validate memory64Module = true := by decide

theorem memory64Module_not_validUnder (P : Profile) :
    ¬ Module.ValidUnder P memory64Module :=
  Module.not_validUnder_of_rejected (f := FeatureFamily.memory64) P _
    memory64Module_uses_memory64 (by decide)

end WasmGemmGnaf.Wasm.Core
