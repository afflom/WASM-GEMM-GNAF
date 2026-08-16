/-
  Exact executable successor enumeration for the proof-carrying public Core
  Harness machine.

  The finite raw enumerator is lifted through preservation to `Wasm.Config`;
  its relation remains exactly the authority Harness relation after erasure.
-/
import WasmGemmGnaf.Wasm.Step
import WasmGemmGnaf.Wasm.Core.HarnessSuccessors
import WasmGemmGnaf.Wasm.Core.HarnessFunctional

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-- Every executable successor of a public configuration, retaining its
validated-reachability proof. -/
def successors (config : Config) : List (Event × Config) :=
  Core.Harness.typedSuccessors config

/-- The public executable successor list is sound for the amended-Core Harness
relation. -/
theorem mem_successors_step {config : Config} {event : Event} {next : Config}
    (hmem : (event, next) ∈ successors config) : Step config event next :=
  Core.Harness.mem_typedSuccessors_stepA hmem

/-- **SPEC §7.1.**  The executable successor list is extensionally exact for
the complete proof-carrying amended-Core Harness relation. -/
theorem mem_successors_iff_step (config : Config) (event : Event)
    (next : Config) :
    (event, next) ∈ successors config ↔ Step config event next :=
  ⟨mem_successors_step, Core.Harness.stepA_mem_typedSuccessors⟩

/-- A fixed proof-carrying public source and complete event determine at most
one proof-carrying target. -/
theorem step_target_functional {source : Config} {event : Event}
    {left right : Config} (hleft : Step source event left)
    (hright : Step source event right) : left = right := by
  apply Subtype.ext
  exact Core.Harness.StepA.target_functional hleft hright

end WasmGemmGnaf.Wasm
