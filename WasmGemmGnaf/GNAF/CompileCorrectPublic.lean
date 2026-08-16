import WasmGemmGnaf.GNAF.CompileValidate
import WasmGemmGnaf.GNAF.CompileScalar
import WasmGemmGnaf.GNAF.Accepts
import WasmGemmGnaf.Wasm.ModuleWithin

set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Public static compiler correctness

This module closes the two compiler obligations that are independent of an
execution simulation: amended-Core validation and the exact static
`Wasm.ModuleWithin` envelope.  Refinement and dynamic cost exactness live at
the public execution boundary and are intentionally not approximated here.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

/-! ## Exact public-profile admission -/

/-- Every feature family attributed to the complete compiled Core module is
exactly the base scalar Core family.  The type, memory and local declarations
have that family directly; the body fact is inherited from the independent
source-support check. -/
theorem compileCore_requiredFeatures_scalar {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    ∀ family ∈ (compileCore checked).requiredFeatures,
      family = Wasm.FeatureFamily.scalarCore := by
  intro family membership
  simp only [compileCore, moduleOf, Wasm.Core.Module.requiredFeatures,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_nil, List.length_singleton, Nat.reduceLT,
    ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with (h | h) | (h | h)
  · simp_all [Wasm.Core.TypeDef.requiredFeatures,
      Wasm.Core.RecType.subTypes, Wasm.Core.SubType.requiredFeatures,
      Wasm.Core.CompType.requiredFeatures, Wasm.Core.CompType.requiredFeature,
      Wasm.Core.ValType.requiredFeature, Wasm.Core.gemmTypeDef]
  · simp_all [Wasm.Core.AddrType.requiredFeature]
  · simp only [List.map_replicate, List.mem_replicate,
      Wasm.Core.ValType.requiredFeature] at h
    exact h.2
  · exact DirectScalar.listSafe_requiredFeatures_scalar _
      (DirectScalar.bodyCode_safe checked) family h

/-- The compiled module's complete feature footprint is admitted by the exact
profile stored on its checked source. -/
theorem compileCore_featuresAdmitted {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    Wasm.Core.Module.featuresAdmittedBy P (compileCore checked) = true := by
  unfold Wasm.Core.Module.featuresAdmittedBy Wasm.Core.Module.featuresAdmitted
  apply List.all_eq_true.mpr
  intro family membership
  have hfamily : family = Wasm.FeatureFamily.scalarCore :=
    compileCore_requiredFeatures_scalar checked family membership
  subst family
  rw [P.lawful.featureTable]
  rfl

/-- The direct compiler emits exactly the memory and `(i32,i32)→i32` GEMM
exports required by every lawful release profile. -/
theorem compileCore_exportsAdmitted {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    Wasm.Core.Module.exportsAdmittedBy P (compileCore checked) = true := by
  unfold Wasm.Core.Module.exportsAdmittedBy
  rw [P.lawful.requiredExports]
  simp only [Wasm.requiredReleaseExports, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  change
    Wasm.Core.Module.satisfiesExport (compileCore checked)
        { name := "memory", kind := .memory } = true ∧
      Wasm.Core.Module.satisfiesExport (compileCore checked)
        { name := "gemm", kind := .function Wasm.gemmFuncType } = true
  constructor
  · simp [Wasm.Core.Module.satisfiesExport, compileCore, moduleOf,
      Wasm.Core.memoryExportName_matches]
  · simp [Wasm.Core.Module.satisfiesExport, compileCore, moduleOf,
      Wasm.Core.gemmExportName_matches, Wasm.Core.Module.funcTypeAt?,
      Wasm.Core.Module.subTypes, Wasm.Core.RecType.subTypes,
      Wasm.Core.SubTypes.toList, Wasm.Core.SubTypes.ofList,
      Wasm.Core.ValTypes.toList, Wasm.Core.ValTypes.ofList,
      coreU32, Wasm.Core.gemmTypeDef, Wasm.gemmFuncType_toCore]

/-- The direct Core compiler's single memory and local declaration are inside
the exact limits stored by the profile.  All other declaration spaces are the
fixed empty/singleton spaces of `moduleOf`. -/
theorem compileCore_withinLimits {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.Module.withinLimitsOf P (compileCore checked) = true := by
  have represented := of_decide_eq_true checked.coreRepresentable
  have hlocals := represented.2.2.2.1
  rw [P.lawful.limits] at hlocals
  have hpages := represented.2.1
  rw [P.lawful.maxPages] at hpages
  rw [Wasm.Core.Module.withinLimitsOf, P.lawful.limits]
  simp only [compileCore, moduleOf]
  simp [Wasm.Core.Module.withinLimits, Wasm.canonicalResourceLimits,
    Wasm.wasm32Ceiling]
  constructor
  · change checked.inputSig.regs + checked.plan.depth + 2 ≤ 4294967295
    simpa [Wasm.canonicalResourceLimits, Wasm.wasm32Ceiling] using hlocals
  · have henvPages :
        (envOf checked.inputSig checked.plan).pages ≤ 65536 := by
      rw [DirectValidation.DirectTyping.envOf_pages_eq]
      exact hpages
    have hlt : (envOf checked.inputSig checked.plan).pages < 2 ^ 64 := by
      omega
    rw [show (coreU64 (envOf checked.inputSig checked.plan).pages).val =
      (envOf checked.inputSig checked.plan).pages by
        simp [coreU64, Nat.mod_eq_of_lt hlt]]
    rw [P.lawful.maxPages]
    exact ⟨henvPages, by simp [CompileEnv.maxPages, coreU64]⟩

/-- **SPEC section 11.4.** Every profile/problem-indexed checked plan compiles
to a module accepted by the executable amended-Core validator. -/
theorem compile_validates {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) : Wasm.validate (compile checked) = true := by
  unfold Wasm.validate
  rw [compile_core]
  exact DirectValidation.DirectTyping.compileCore_validates checked

/-- Every directly compiled module satisfies the profile's complete admission
matrix: intrinsic syntax, closed imports, enabled features, declaration limits
and the exact two-export ABI. -/
theorem compile_admitted {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.Module.AdmittedBy P (compile checked).core := by
  apply Wasm.Core.Module.admittedBy_of_conjuncts
  · exact (compile checked).core_wf
  · rw [P.lawful.importPolicy]
    rfl
  · rfl
  · simpa [compile_core] using compileCore_featuresAdmitted checked
  · simpa [compile_core] using compileCore_withinLimits checked
  · simpa [compile_core] using compileCore_exportsAdmitted checked

/-- The public executable profile validator accepts every compiled module.
This is the exact initializer precondition, not merely the profile-independent
Core typing bit proved by `compile_validates`. -/
theorem compile_validateUnder {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.validateUnder P (compile checked) = true := by
  rw [Wasm.validateUnder, Bool.and_eq_true]
  exact ⟨compile_validates checked, compile_admitted checked⟩

/-- The complete nested instruction tree of the sole emitted function fits
the source-side structural budget exactly selected by `resourceBound`. -/
theorem compile_codeSize {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.moduleCodeSize (compile checked) ≤ checked.resourceBound := by
  have hcode := DirectEncoding.code_size_le
    (envOf checked.inputSig checked.plan) checked.plan 0 checked.inputSig.scratch
  unfold Wasm.moduleCodeSize CheckedPlan.resourceBound
  simp only [compile_core, compileCore, moduleOf, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  change DirectEncoding.seqSize
      (bodyCode (envOf checked.inputSig checked.plan) checked.inputSig.scratch
        checked.plan) ≤ checked.plan.codeBudget + 4
  rw [bodyCode, DirectEncoding.seqSize_append]
  have hstatus : DirectEncoding.seqSize
      [localGet (envOf checked.inputSig checked.plan).statusLocal, wrapI64] = 4 := by
    simp
  rw [hstatus]
  omega

/-- **SPEC section 11.4, `compile_resources`.** The compiled public module is
validated, obeys the profile's static declaration limits, and fits the checked
source plan's complete structural code budget. -/
theorem compile_resources {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.ModuleWithin P (compile checked) checked.resourceBound := by
  exact ⟨compile_validates checked, compileCore_withinLimits checked,
    compile_codeSize checked⟩

end WasmGemmGnaf.GNAF
