/-
  Artifact/Release.lean --- the public amended-Core release scope.

  This file fixes the exact profile, problem, public costed machine, canonical
  evaluator token, and objective used by the release proposition.  It contains
  no legacy `Wasm.Subset` seam and no caller-selected semantics callback.

  The 53-byte Core artifact retained below is diagnostic only: it proves that
  the amended decoder and profile admission path are inhabited, but its body is
  `local.get 0` and it is not a GEMM implementation.  In particular this file
  deliberately does not define `Release.artifactBytes`.  That name is reserved
  for the bytes emitted from a checked full-GEMM public-Core compilation.
-/
import WasmGemmGnaf.Artifact.ReleaseProfile
import WasmGemmGnaf.Cost.CanonicalObjective
import WasmGemmGnaf.Gemm.Problem
import WasmGemmGnaf.Universal.EnumerateInputs
import WasmGemmGnaf.Universal.Evaluate
import WasmGemmGnaf.Wasm.CoreArtifact

set_option autoImplicit false
set_option exponentiation.threshold 321

namespace WasmGemmGnaf.Release

open WasmGemmGnaf

/-! ## Public release profile -/

theorem wasmProfile_costTableBody :
    wasmProfile.costTableBody = wasmCostTableBody :=
  profile_cost_table_exact

theorem wasmProfile_ruleRows_nodup :
    (wasmProfile.costTableBody.ruleRows.map Wasm.CostRuleRow.ruleId).Nodup := by
  simpa [wasmProfile_costTableBody] using wasmCostTableBody_ruleRows_nodup

theorem wasmProfile_addressBits : wasmProfile.body.addressBits = 32 := rfl

theorem wasmProfile_maxPages : wasmProfile.body.maxPages = 65536 := rfl

theorem wasmProfile_decodeCost (bytes : ByteArray) :
    wasmProfile.costTableBody.decodeCost bytes = bytes.size + 1 :=
  wasmProfile.decodeCost_eq bytes

/-! ## Diagnostic amended-Core ABI-shape bytes

These declarations retain the exact WS-005 proof boundary.  The bytes are not
selected release bytes and the module is not a GEMM implementation.
-/

def coreArtifactBytes : ByteArray := Wasm.Core.releaseArtifactBytes

def coreArtifactModule : Wasm.Module := Wasm.Core.releaseArtifactModule

theorem coreArtifact_decode :
    Wasm.decode coreArtifactBytes = .ok coreArtifactModule :=
  Wasm.Core.decode_releaseArtifactBytes

theorem coreArtifact_declarative :
    Wasm.DeclarativeBinaryRelation coreArtifactBytes coreArtifactModule :=
  Wasm.Core.releaseArtifactBytes_declarative

theorem coreArtifact_admitted :
    Wasm.Core.Module.AdmittedBy wasmProfile coreArtifactModule.core :=
  Wasm.Core.releaseArtifactBytes_admitted wasmProfile

/-- WS-005: the diagnostic module is derivable in the amended Core judgment
and admitted by the exact public release profile. -/
theorem coreArtifact_validUnder :
    Wasm.Core.Module.ValidUnder wasmProfile coreArtifactModule.core :=
  Wasm.Core.releaseArtifactBytes_validUnder wasmProfile

theorem coreArtifact_imports : coreArtifactModule.core.imports = [] := rfl

theorem coreArtifact_exports :
    coreArtifactModule.core.exports =
      [ { name := Wasm.Core.memoryExportName, externidx := .mem Wasm.Core.idx0 }
      , { name := Wasm.Core.gemmExportName, externidx := .func Wasm.Core.idx0 } ] :=
  rfl

/-- A diagnostic public-Core profile-admission conjunction.  This is not
`Universal.ProfileValid`: it intentionally uses the semantic `ValidUnder`
proposition rather than asserting executable-validator completeness. -/
theorem coreArtifact_profileValid_spec_reading :
    ∃ module : Wasm.Module,
      Wasm.decode coreArtifactBytes = .ok module ∧
      Wasm.Core.Module.ValidUnder wasmProfile module.core ∧
      module.core.imports = [] ∧
      Wasm.Core.Module.exportsAdmittedBy wasmProfile module.core = true := by
  refine ⟨coreArtifactModule, coreArtifact_decode, coreArtifact_validUnder,
    coreArtifact_imports, ?_⟩
  have admitted := coreArtifact_admitted
  unfold Wasm.Core.Module.AdmittedBy Wasm.Core.Module.admittedBy at admitted
  simp only [Bool.and_eq_true] at admitted
  exact admitted.2

/-! ## Canonical release problem -/

def gemmProblemBody : Gemm.ProblemBody wasmProfile.body :=
  gemmProblemBodyFor wasmProfile

def gemmProblem : Gemm.Problem wasmProfile :=
  gemmProblemFor wasmProfile

theorem gemmProblem_body : gemmProblem.body = gemmProblemBody := rfl

theorem gemmProblem_canonical :
    gemmProblem.body =
      Gemm.canonicalWGNGv1ProblemBody wasmProfile.body
        (workloadRepetitions := 1) :=
  rfl

theorem gemmProblem_workloadRepetitions :
    gemmProblem.workloadRepetitions = 1 :=
  rfl

theorem gemmProblem_maxSteps : gemmProblem.maxSteps = 2 ^ 320 := rfl

/-! ## Canonical public evaluator scope -/

/-- The exact problem consumed by the public evaluator.  Its acceptance
relation is `Gemm.Reference.Accepts`; no artifact can replace it. -/
def problem : Universal.Problem wasmProfile where
  gemm := gemmProblem
  workloadRepetitionsPositive := Nat.le_refl 1

/-- Empty token selecting the sole public initializer/explorer. -/
def machine : Universal.CostedMachine wasmProfile := {}

/-- The release setting has only the canonical public machine and problem. -/
def setting : Universal.Setting wasmProfile where
  machine := machine
  problem := problem

/-- Empty token selecting `Universal.evaluate`; it stores no evaluator. -/
def decider : Universal.Decider setting := {}

@[simp] theorem setting_machine : setting.machine = machine := rfl

@[simp] theorem setting_problem : setting.problem = problem := rfl

theorem setting_maxSteps : setting.problem.maxSteps = 2 ^ 320 := rfl

theorem setting_limit : setting.problem.limit = gemmProblem.resources.limit := rfl

theorem setting_workloadRepetitions :
    setting.problem.workloadRepetitions = 1 :=
  rfl

theorem setting_rawInvocation :
    setting.problem.RawInvocation = Gemm.RawInvocation wasmProfile :=
  rfl

theorem setting_accepts (raw : Gemm.RawInvocation wasmProfile)
    (observation : Wasm.ExecutionObservation) :
    setting.problem.Accepts raw observation ↔
      Gemm.Reference.Accepts gemmProblem raw observation :=
  Iff.rfl

theorem decider_evaluate (bytes : ByteArray) :
    decider.evaluate bytes = Universal.evaluate setting bytes :=
  rfl

/-! ## Canonical objective -/

def costObjective : Cost.ProperObjective wasmProfile setting.problem :=
  Cost.canonicalObjective wasmProfile setting.problem

theorem costObjective_body :
    costObjective.body = Cost.canonicalObjectiveBody :=
  rfl

theorem costObjective_weights_one (coordinate : Cost.ArtifactCoordinate) :
    costObjective.body.weight coordinate = 1 :=
  Cost.canonicalObjectiveBody_weight coordinate

theorem costObjective_tieOrder :
    costObjective.body.tieOrder = .unsignedByteLexicographic :=
  rfl

theorem costObjective_score (cost : Cost.CompleteSystemCost) :
    costObjective.score cost = Cost.CanonicalObjective.score cost :=
  Cost.canonicalObjective_score wasmProfile setting.problem cost

/-!
No selected, committed, or globally optimal artifact is defined here.  Those
declarations require an emitted full-GEMM checked plan, its exact public system
evaluation, selection/lower-bound evidence, and byte-identical reproduction.
-/

end WasmGemmGnaf.Release
