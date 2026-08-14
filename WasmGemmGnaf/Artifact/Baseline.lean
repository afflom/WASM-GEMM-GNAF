/-
  Artifact/Baseline.lean --- module-level facts about the legacy GNAF baseline.

  `GNAF.compile` currently returns `Wasm.Subset.Module`, while the public
  `Artifact.emit` endpoint required by SPEC §11.4 accepts `Wasm.Module`.  No
  proved carrier bridge connects those types.  Consequently this file defines
  no emitted baseline bytes and makes no decode, profile-validity, evaluation,
  or admissibility claim about such bytes.

  The declarations retained here concern only the compiler output itself: its
  subset validation and declarative validity, closed import list, exact export
  list, and current profile-limit checks.  They are useful intermediate GNAF
  and resource facts; they do not discharge the public emitter or release
  artifact obligations.
-/
import WasmGemmGnaf.Artifact.Release
import WasmGemmGnaf.GNAF.CompileCorrect

set_option autoImplicit false

namespace WasmGemmGnaf.Artifact

open WasmGemmGnaf

/-! ## The legacy baseline module -/

/-- The legacy subset compiler output for the anti-vacuity GEMM witness plan in
`GNAF/CompileCorrect.lean`. -/
def baselineModule : Wasm.Subset.Module := GNAF.compile GNAF.gemmWitnessChecked

/-- The legacy subset module passes its executable validator. -/
theorem baseline_validate : Wasm.validate baselineModule = true :=
  GNAF.gemmWitness_compiles

/-- The legacy subset module satisfies its declarative validity predicate. -/
theorem baseline_declarativelyValid : Wasm.DeclarativelyValid baselineModule :=
  GNAF.compile_declarativelyValid GNAF.gemmWitnessChecked

/-- The legacy subset module declares no import. -/
theorem baseline_imports : baselineModule.imports = [] := rfl

/-- The legacy subset module's export list, in full. -/
theorem baseline_exports :
    baselineModule.exports =
      [{ name := Wasm.gemmExportName, desc := .func 0 },
       { name := Wasm.memoryExportName, desc := .mem 0 }] :=
  GNAF.compile_exports GNAF.gemmWitnessChecked

/--
  Every index-space population of the legacy subset module is inside the
  current profile's limit table.

  This is `decide`, and it is cheap because every count in `GNAF.moduleOf` is a
  literal `0`, `1` or `2` -- one recursive type group, one function, one memory,
  two exports and nothing else -- while every relevant limit in
  `Wasm.canonicalResourceLimits` is `Wasm.wasm32Ceiling = 2 ^ 32 - 1`.  The
  function body is never forced.
-/
theorem baseline_withinProfileLimits :
    Universal.WithinProfileLimits Release.wasmProfile baselineModule = true := by
  decide

/-- The legacy subset module passes the current `Universal.validateUnder`
helper: its subset validator together with the profile's limit table. -/
theorem baseline_validateUnder :
    Universal.validateUnder Release.wasmProfile baselineModule = true := by
  unfold Universal.validateUnder
  rw [baseline_validate, baseline_withinProfileLimits]
  rfl

/-! ## The required exports

`Wasm.validate` already carries the two export conjuncts, so they are read out
of `baseline_validate` rather than reproved.  `&&` associates to the left, so
the ten conjuncts of `Wasm.validate` are a left-nested tower and the two export
conjuncts -- the sixth and seventh of ten -- sit at `h.1.1.1.1.2` and
`h.1.1.1.2`. -/

/-- The memory export, extracted from subset validation itself. -/
theorem baseline_exportsMemory :
    Wasm.Subset.Module.exportsMemory baselineModule = true := by
  have h := baseline_validate
  unfold Wasm.validate at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

/-- The ABI-shaped `gemm` export, extracted from subset validation itself. -/
theorem baseline_checkGemmExport :
    Wasm.Subset.Module.checkGemmExport baselineModule = true := by
  have h := baseline_validate
  unfold Wasm.validate at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- The legacy subset module exports the `gemm` function and memory, and no
other export. -/
theorem baseline_hasExactGemmExports :
    Universal.HasExactGemmExports Release.wasmProfile baselineModule := by
  refine ⟨baseline_exportsMemory, baseline_checkGemmExport, ?_⟩
  intro e he
  rw [baseline_exports] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end WasmGemmGnaf.Artifact
