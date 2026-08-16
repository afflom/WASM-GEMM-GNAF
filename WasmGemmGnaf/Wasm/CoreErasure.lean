/-
  Cost-labelled execution and structural erasure for the public typed
  amended-Core harness.

  The legacy subset relation remains under `Wasm.Subset`.  This module defines
  the SPEC section 7.5 names at the public `Wasm` root over `Wasm.Module`,
  profile-indexed public invocations, typed public configurations, and exact
  Harness events.  A `CostedEvent` stores only the authority event; its charge
  is computed from the profile by `Wasm.eventCost`, so no caller can forge a
  separate numeric payload.
-/
import WasmGemmGnaf.Wasm.Evaluate

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-! ## Public plain and costed runs -/

/-- A plain public run starts from the canonical fresh public initializer and
derives one exact terminal Harness observation along `trace`. -/
def Run {P : Profile} (module : Module) (invocation : Invocation P)
    (trace : List Event) (observation : ExecutionObservation) : Prop :=
  ∃ initial : Config,
    initialGemmInvocation P module invocation = .ok initial ∧
      ExecutionObservation.trace observation = trace ∧
      FiniteExecution initial observation

/-- A public costed run uses the independent `CostedReduces` derivation.  The
profile determines every label's charge through `CostedEvent.cost`; it is not a
caller-supplied proof or payload. -/
def CostedRun (P : Profile) (module : Module) (invocation : Invocation P)
    (costedTrace : List CostedEvent) (observation : ExecutionObservation) : Prop :=
  ∃ (initial : Config) (final : RawConfig) (visited : List RawConfig),
    initialGemmInvocation P module invocation = .ok initial ∧
      CostedReduces initial.1 costedTrace visited final ∧
      Core.Harness.Observes (eraseCosts costedTrace) final observation

/-- The trace is a machine-produced labelling when its independent costed
reduction starts from the canonical fresh public initializer.  This predicate
mentions neither an observation nor a terminal result. -/
def CostedLabelling {P : Profile} (module : Module) (invocation : Invocation P)
    (costedTrace : List CostedEvent) : Prop :=
  ∃ (initial : Config) (final : RawConfig) (visited : List RawConfig),
    initialGemmInvocation P module invocation = .ok initial ∧
      CostedReduces initial.1 costedTrace visited final

/-- A Harness observation records exactly the trace that produced it. -/
theorem Core.Harness.Observes.trace_eq {trace : List Event}
    {final : Core.Harness.Config} {observation : ExecutionObservation}
    (observes : Core.Harness.Observes trace final observation) :
    ExecutionObservation.trace observation = trace := by
  cases observes <;> rfl

/-- Erasing the labels of a public costed run yields the same plain run. -/
theorem costedRun_erase {P : Profile} {module : Module}
    {invocation : Invocation P} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (run : CostedRun P module invocation costedTrace observation) :
    Run module invocation (eraseCosts costedTrace) observation := by
  obtain ⟨initial, final, _, hinitial, reduction, observes⟩ := run
  exact ⟨initial, hinitial, observes.trace_eq,
    Core.Harness.FiniteExecution.mk reduction.erase observes⟩

/-- Every public costed run exposes its machine-produced labelling. -/
theorem costedRun_labelling {P : Profile} {module : Module}
    {invocation : Invocation P} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation}
    (run : CostedRun P module invocation costedTrace observation) :
    CostedLabelling module invocation costedTrace := by
  obtain ⟨initial, final, visited, hinitial, reduction, _⟩ := run
  exact ⟨initial, final, visited, hinitial, reduction⟩

/-- **SPEC §7.5, `Wasm.costed_erase_iff_plain_run`.**  Cost labels over the
public typed amended-Core Harness erase exactly to the ordinary public run.
The amended right-hand side retains the labels-only machine-production
condition required by AMD-002. -/
theorem costed_erase_iff_plain_run {P : Profile} {module : Module}
    {invocation : Invocation P} {costedTrace : List CostedEvent}
    {observation : ExecutionObservation} :
    CostedRun P module invocation costedTrace observation ↔
      (Run module invocation (eraseCosts costedTrace) observation ∧
        CostedLabelling module invocation costedTrace) := by
  constructor
  · intro run
    exact ⟨costedRun_erase run, costedRun_labelling run⟩
  · rintro ⟨⟨initial, hinitial, traceEq, finite⟩, _⟩
    change Core.Harness.FiniteExecution initial.1 observation at finite
    cases finite with
    | @mk trace final _ reduction observes =>
      have observedTrace : ExecutionObservation.trace observation = trace :=
        observes.trace_eq
      have traceIsErasure : trace = eraseCosts costedTrace :=
        observedTrace.symm.trans traceEq
      rw [traceIsErasure] at reduction observes
      obtain ⟨visited, costedReduction⟩ :=
        CostedReduces.of_erase costedTrace reduction
      exact ⟨initial, final, visited, hinitial, costedReduction, observes⟩

/-- With the public costed trace existentially quantified, instrumentation is
transparent without a side condition. -/
theorem costed_run_iff_plain_run {P : Profile} {module : Module}
    {invocation : Invocation P} {observation : ExecutionObservation} :
    (∃ costedTrace : List CostedEvent,
      CostedRun P module invocation costedTrace observation) ↔
      Run module invocation observation.trace observation := by
  constructor
  · rintro ⟨costedTrace, run⟩
    obtain ⟨initial, hinitial, _, finite⟩ := costedRun_erase run
    exact ⟨initial, hinitial, rfl, finite⟩
  · rintro ⟨initial, hinitial, _, finite⟩
    change Core.Harness.FiniteExecution initial.1 observation at finite
    cases finite with
    | @mk trace final _ reduction observes =>
      have observedTrace : ExecutionObservation.trace observation = trace :=
        observes.trace_eq
      subst trace
      obtain ⟨visited, labelled⟩ := CostedReduces.label reduction
      exact ⟨labelCosts observation.trace, initial, final, visited, hinitial,
        labelled, by simpa using observes⟩

end WasmGemmGnaf.Wasm
