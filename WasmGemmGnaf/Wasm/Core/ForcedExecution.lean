import WasmGemmGnaf.Wasm.Core.HarnessExecution

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Harness

/-! ## Finite executions forced by a unique outgoing edge

This module packages a small relational eliminator used by compiler
refinement proofs.  It does not assume global determinism of Core: each
nonterminal node carries a proof that the one edge used by the exhibited path
is the only labelled edge from that particular source configuration.
-/

/-- A finite path whose final configuration is terminal and whose every
nonterminal source has exactly the displayed outgoing labelled edge. -/
inductive ForcedSteps : Config → List Event → Config → Prop where
  | terminal {config : Config} (terminal : IsTerminal config) :
      ForcedSteps config [] config
  | cons {config next final : Config} {event : Event} {trace : List Event}
      (step : StepA config event next)
      (unique : ∀ {otherEvent : Event} {otherNext : Config},
        StepA config otherEvent otherNext →
          otherEvent = event ∧ otherNext = next)
      (tail : ForcedSteps next trace final) :
      ForcedSteps config (event :: trace) final

/-- A terminal Harness configuration has no outgoing transition. -/
theorem IsTerminal.not_step {config : Config} (terminal : IsTerminal config)
    {event : Event} {next : Config} : ¬ StepA config event next := by
  intro step
  rcases terminal with ⟨_, halt⟩ | ⟨_, trapped⟩ | ⟨_, thrown⟩
  · cases halt
    cases step
  · cases trapped <;> cases step
  · cases thrown <;> cases step

/-- Every exact Harness observation is made at a terminal configuration. -/
theorem Observes.isTerminal {trace : List Event} {config : Config}
    {observation : ExecutionObservation}
    (observes : Observes trace config observation) : IsTerminal config := by
  cases observes
  · exact Or.inl ⟨_, .returned _ _ _ _⟩
  · exact Or.inr (Or.inl ⟨_, .beforeEntry _ _ _⟩)
  · exact Or.inr (Or.inl ⟨_, .afterEntry _ _ _ _⟩)
  · exact Or.inr (Or.inr ⟨_, .beforeEntry _ _ _ _⟩)
  · exact Or.inr (Or.inr ⟨_, .afterEntry _ _ _ _ _⟩)

/-- A fixed trace and fixed terminal configuration determine one public
observation. -/
theorem Observes.target_functional {trace : List Event} {config : Config}
    {left right : ExecutionObservation}
    (leftObserves : Observes trace config left)
    (rightObserves : Observes trace config right) : left = right := by
  cases leftObserves <;> cases rightObserves <;> simp_all

/-- A forced path is the only finite reduction from its source to any
terminal configuration. -/
theorem ForcedSteps.eq_steps_to_terminal
    {initial final : Config} {trace : List Event}
    (forced : ForcedSteps initial trace final)
    {otherFinal : Config} {otherTrace : List Event}
    (steps : StepsA initial otherTrace otherFinal)
    (terminal : IsTerminal otherFinal) :
    otherTrace = trace ∧ otherFinal = final := by
  induction forced generalizing otherFinal otherTrace with
  | terminal sourceTerminal =>
      cases steps with
      | refl => exact ⟨rfl, rfl⟩
      | cons step _ => exact (sourceTerminal.not_step step).elim
  | @cons config next final event trace step unique tail ih =>
      cases steps with
      | refl => exact (terminal.not_step step).elim
      | @cons _ otherNext otherFinal otherEvent otherTrace otherStep otherSteps =>
          obtain ⟨eventEq, nextEq⟩ := unique otherStep
          subst otherEvent
          subst otherNext
          obtain ⟨traceEq, finalEq⟩ := ih otherSteps terminal
          exact ⟨congrArg (List.cons event) traceEq, finalEq⟩

/-- An exhibited forced path and observation determine every relational finite
execution from the same initial configuration. -/
theorem ForcedSteps.finiteExecution_eq
    {initial final : Config} {trace : List Event}
    (forced : ForcedSteps initial trace final)
    {canonical arbitrary : ExecutionObservation}
    (canonicalObserves : Observes trace final canonical)
    (execution : FiniteExecution initial arbitrary) : arbitrary = canonical := by
  cases execution with
  | @mk otherTrace otherFinal _ steps otherObserves =>
      obtain ⟨traceEq, finalEq⟩ :=
        forced.eq_steps_to_terminal steps otherObserves.isTerminal
      subst otherTrace
      subst otherFinal
      exact otherObserves.target_functional canonicalObserves

/-! ## Target-forced paths

Core administrative contexts can label the same transition through more than
one nested context derivation.  The weaker carrier below therefore fixes only
the successor configuration at each source, while deliberately permitting
distinct event labels for that same edge.
-/

/-- A finite path whose final configuration is terminal and whose every
nonterminal source has exactly one possible successor configuration. -/
inductive ForcedTargets : Config → Config → Prop where
  | terminal {config : Config} (terminal : IsTerminal config) :
      ForcedTargets config config
  | cons {config next final : Config} {event : Event}
      (step : StepA config event next)
      (targetUnique : ∀ {otherEvent : Event} {otherNext : Config},
        StepA config otherEvent otherNext → otherNext = next)
      (tail : ForcedTargets next final) :
      ForcedTargets config final

/-- Target-forced paths compose without imposing any equality on the event
labels chosen by their two witnesses. -/
theorem ForcedTargets.trans {initial middle final : Config}
    (left : ForcedTargets initial middle)
    (right : ForcedTargets middle final) :
    ForcedTargets initial final := by
  induction left with
  | terminal _ => exact right
  | cons step targetUnique _ ih =>
      exact .cons step targetUnique (ih right)

/-- Every finite reduction from a target-forced source to a terminal
configuration reaches the displayed final configuration.  Event labels are
not compared. -/
theorem ForcedTargets.eq_final_of_steps
    {initial final : Config} (forced : ForcedTargets initial final)
    {otherFinal : Config} {otherTrace : List Event}
    (steps : StepsA initial otherTrace otherFinal)
    (terminal : IsTerminal otherFinal) : otherFinal = final := by
  induction forced generalizing otherFinal otherTrace with
  | terminal sourceTerminal =>
      cases steps with
      | refl => rfl
      | cons step _ => exact (sourceTerminal.not_step step).elim
  | @cons config next final event step targetUnique tail ih =>
      cases steps with
      | refl => exact (terminal.not_step step).elim
      | @cons _ otherNext otherFinal otherEvent otherTrace otherStep otherSteps =>
          have nextEq : otherNext = next := targetUnique otherStep
          subst otherNext
          exact ih otherSteps terminal

/-- A finite execution from a target-forced source observes the forced final
configuration, though its admissible administrative event trace may differ
from the exhibited trace. -/
theorem ForcedTargets.finiteExecution_observes_final
    {initial final : Config} (forced : ForcedTargets initial final)
    {observation : ExecutionObservation}
    (execution : FiniteExecution initial observation) :
    ∃ trace, Observes trace final observation := by
  cases execution with
  | @mk trace otherFinal _ steps observes =>
      have finalEq : otherFinal = final :=
        forced.eq_final_of_steps steps observes.isTerminal
      subst otherFinal
      exact ⟨trace, observes⟩

/-! ## Lifting target uniqueness through the released Harness

The Core relation may assign several administrative event labels to one
successor.  Compiler simulations therefore establish successor uniqueness at
the Core configuration level.  The lemma below transports exactly that fact
through the normal post-entry Harness phase.  The two source exclusions are
the genuine phase-boundary alternatives: a singleton value returns from the
entry function, while an exposed exception reference is thrown by the
Harness. -/

/-- A nontrapping, target-unique Core source has the same target after the
normal post-entry Harness lift.  No event uniqueness is assumed. -/
theorem afterEntry_target_unique_of_core
    {harness : Harness} {entry : Exec.Store}
    {source target : Exec.Config}
    (targetNotTrap : target.2 ≠ [.trap])
    (sourceNotReturn : ∀ (state : Exec.State) (value : Exec.Val),
      source ≠ (state, Exec.vals [value]))
    (sourceNotThrow : ∀ (state : Exec.State) (address : Exec.ExnAddr),
      source ≠ (state,
        [.addrref (.exnAddr address), .plain .throwRef]))
    (allCore : ∀ {event : Exec.Event} {next : Exec.Config},
      Exec.StepA source event next →
        next = target ∧ coreTrapCause? event = none)
    {event : Event} {next : Config}
    (step : StepA (.afterEntry harness entry source) event next) :
    next = .afterEntry harness entry target := by
  cases step with
  | coreAfter coreStep _ _ =>
      obtain ⟨rfl, _⟩ := allCore coreStep
      rfl
  | coreAfterTrap coreStep cause _ =>
      obtain ⟨_, noCause⟩ := allCore coreStep
      simp [noCause] at cause
  | coreAfterTrapFinal coreStep _ =>
      obtain ⟨targetEq, _⟩ := allCore coreStep
      exact (targetNotTrap (congrArg Prod.snd targetEq.symm)).elim
  | returnAfter =>
      exact (sourceNotReturn _ _ rfl).elim
  | throwAfter =>
      exact (sourceNotThrow _ _ rfl).elim

end WasmGemmGnaf.Wasm.Core.Harness
