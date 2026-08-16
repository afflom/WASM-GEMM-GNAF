/-
  Fixed-event functionality of the released amended-Core Harness relation.
-/
import WasmGemmGnaf.Wasm.Core.EventFunctional
import WasmGemmGnaf.Wasm.Core.HarnessExecution

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Harness

/-- Invocation is an executable one-constructor configuration builder, so a
fixed store, address, and argument vector determine its Core target. -/
theorem Exec.InvokeA.target_functional {store : Exec.Store}
    {address : Exec.FuncAddr} {arguments : List Exec.Val}
    {left right : Exec.Config} (hleft : Exec.InvokeA store address arguments left)
    (hright : Exec.InvokeA store address arguments right) : left = right := by
  cases hleft
  cases hright
  simp_all

/-- The state component of a fixed labelled Core transition is functional. -/
theorem Exec.StepA.target_state_functional
    {source : Exec.Config} {event : Exec.Event} {left right : Exec.Config}
    (hleft : Exec.StepA source event left)
    (hright : Exec.StepA source event right) : left.1 = right.1 :=
  congrArg Prod.fst (Exec.StepA.target_functional hleft hright)

/-- Distinct instruction components cannot both be targets of one fixed
labelled Core transition. -/
theorem Exec.StepA.false_of_target_instrs_ne
    {source : Exec.Config} {event : Exec.Event} {left right : Exec.Config}
    (hleft : Exec.StepA source event left)
    (hright : Exec.StepA source event right)
    (hne : left.2 ≠ right.2) : False :=
  hne (congrArg Prod.snd (Exec.StepA.target_functional hleft hright))

/-- Specialization used by Harness terminal-trap constructors. -/
theorem Exec.StepA.trap_target_state_functional
    {source : Exec.Config} {event : Exec.Event} {left right : Exec.State}
    (hleft : Exec.StepA source event (left, [.trap]))
    (hright : Exec.StepA source event (right, [.trap])) : left = right := by
  exact congrArg Prod.fst (Exec.StepA.target_functional hleft hright)

/-- Re-index a Harness derivation through explicit equalities before inversion;
this keeps dependent value encodings out of constructor elimination motives. -/
theorem StepA.unindexSourceEventTarget
    {source : Config} {event : Event} {target : Config}
    (h : StepA source event target) :
    ∃ unindexedSource unindexedEvent unindexedTarget,
      unindexedSource = source ∧ unindexedEvent = event ∧
        unindexedTarget = target ∧
          StepA unindexedSource unindexedEvent unindexedTarget := by
  exact ⟨source, event, target, rfl, rfl, rfl, h⟩

/-- A fixed raw Harness source and complete event determine at most one raw
target.  Core-labelled transitions use the corresponding exact Core theorem;
fresh initialization uses the AMD-019 executable-target certificate. -/
theorem StepA.target_functional {source : Config} {event : Event}
    {left right : Config} (hleft : StepA source event left)
    (hright : StepA source event right) : left = right := by
  induction hleft generalizing right <;>
    obtain ⟨rightSource, rightEvent, rightTarget, hrightSource, hrightEvent,
      hrightTarget, rightProof⟩ := hright.unindexSourceEventTarget <;>
    rw [← hrightTarget] <;>
    clear hright hrightTarget right <;>
    cases rightProof <;>
    simp_all
  all_goals try solve_by_elim [Exec.StepA.target_functional,
    Exec.StepA.target_state_functional,
    Exec.StepA.trap_target_state_functional,
    Exec.StepA.false_of_target_instrs_ne,
    Exec.InvokeA.target_functional, InitializesA.target_functional]

end WasmGemmGnaf.Wasm.Core.Harness
