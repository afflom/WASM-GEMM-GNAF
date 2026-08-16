/-
  Theorems/Release.lean --- public release-scope identity facts.

  This module contains no legacy-subset seam and states no selected-artifact or
  global-optimality conclusion.  It packages only the exact public profile,
  problem, machine/evaluator, and objective identities fixed in
  `Artifact/Release.lean`.
-/
import WasmGemmGnaf.Artifact.Release

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

open WasmGemmGnaf

theorem release_scope_identities :
    Release.wasmProfile.costTableBody = Release.wasmCostTableBody ∧
    Release.wasmProfile.body.addressBits = 32 ∧
    Release.wasmProfile.body.maxPages = 65536 ∧
    Release.gemmProblem.body =
      Gemm.canonicalWGNGv1ProblemBody Release.wasmProfile.body
        (workloadRepetitions := 1) ∧
    Release.gemmProblem.workloadRepetitions = 1 ∧
    Release.gemmProblem.maxSteps = 2 ^ 320 ∧
    Release.setting.problem = Release.problem ∧
    Release.setting.problem.RawInvocation =
      Gemm.RawInvocation Release.wasmProfile ∧
    (∀ raw observation,
      Release.setting.problem.Accepts raw observation ↔
        Gemm.Reference.Accepts Release.gemmProblem raw observation) ∧
    Release.costObjective.body = Cost.canonicalObjectiveBody ∧
    (∀ coordinate, Release.costObjective.body.weight coordinate = 1) ∧
    Release.costObjective.body.tieOrder = .unsignedByteLexicographic ∧
    (∀ cost, Release.costObjective.score cost =
      Cost.CanonicalObjective.score cost) := by
  exact ⟨Release.wasmProfile_costTableBody,
    Release.wasmProfile_addressBits,
    Release.wasmProfile_maxPages,
    Release.gemmProblem_canonical,
    Release.gemmProblem_workloadRepetitions,
    Release.gemmProblem_maxSteps,
    Release.setting_problem,
    Release.setting_rawInvocation,
    Release.setting_accepts,
    Release.costObjective_body,
    Release.costObjective_weights_one,
    Release.costObjective_tieOrder,
    Release.costObjective_score⟩

end WasmGemmGnaf.Theorems
