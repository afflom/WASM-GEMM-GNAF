/-
  Executable terminal observations for the proof-carrying public Core Harness.

  The relational carrier remains `Core.Harness.Observes`; this file only makes
  its deterministic terminal projections available to the bounded explorer.
-/
import WasmGemmGnaf.Wasm.Run

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-- Compute the exact observation of a terminal public Harness configuration.
Nonterminal configurations, missing exported memory, and a trap trace whose
recorded cause disagrees with the terminal configuration return `none`. -/
def observationOfConfig (trace : List Event) (config : Config) :
    Option ExecutionObservation :=
  match config.1 with
  | .returned harness entry value finalState => do
      let entryObservation ← Core.Harness.observeStore harness entry
      let finalObservation ← Core.Harness.observeStore harness finalState.store
      pure (.returned trace entryObservation value finalObservation
        Core.Harness.ObservableEffects.none)
  | .trappedBeforeEntry harness trap finalState => do
      if Core.Harness.traceTrap? trace = some trap then
        let finalObservation ← Core.Harness.observeStore harness finalState.store
        pure (.trappedBeforeEntry trace trap finalObservation
          Core.Harness.ObservableEffects.none)
      else none
  | .trappedAfterEntry harness entry trap finalState => do
      if Core.Harness.traceTrap? trace = some trap then
        let entryObservation ← Core.Harness.observeStore harness entry
        let finalObservation ← Core.Harness.observeStore harness finalState.store
        pure (.trappedAfterEntry trace entryObservation trap finalObservation
          Core.Harness.ObservableEffects.none)
      else none
  | .thrownBeforeEntry harness _ exceptionValue finalState => do
      let finalObservation ← Core.Harness.observeStore harness finalState.store
      pure (.thrownBeforeEntry trace exceptionValue finalObservation
        Core.Harness.ObservableEffects.none)
  | .thrownAfterEntry harness entry _ exceptionValue finalState => do
      let entryObservation ← Core.Harness.observeStore harness entry
      let finalObservation ← Core.Harness.observeStore harness finalState.store
      pure (.thrownAfterEntry trace entryObservation exceptionValue
        finalObservation Core.Harness.ObservableEffects.none)
  | _ => none

/-- The executable terminal projection is sound for the independent
`Core.Harness.Observes` relation. -/
theorem observationOfConfig_sound {trace : List Event} {config : Config}
    {observation : ExecutionObservation}
    (h : observationOfConfig trace config = some observation) :
    Core.Harness.Observes trace config.1 observation := by
  rcases config with ⟨config, typed⟩
  cases config with
  | initializing request => simp [observationOfConfig] at h
  | beforeEntry harness core => simp [observationOfConfig] at h
  | trappingBeforeEntry harness trap core =>
      simp [observationOfConfig] at h
  | readyToEnter harness state => simp [observationOfConfig] at h
  | afterEntry harness entry core => simp [observationOfConfig] at h
  | trappingAfterEntry harness entry trap core =>
      simp [observationOfConfig] at h
  | returned harness entry value finalState =>
    change Core.Harness.Observes trace
      (.returned harness entry value finalState) observation
    cases hentry : Core.Harness.observeStore harness entry with
    | none => simp [observationOfConfig, hentry] at h
    | some entryObservation =>
        cases hfinal : Core.Harness.observeStore harness finalState.store with
        | none => simp [observationOfConfig, hentry, hfinal] at h
        | some finalObservation =>
            simp [observationOfConfig, hentry, hfinal] at h
            subst observation
            exact .returned hentry hfinal
  | trappedBeforeEntry harness trap finalState =>
    change Core.Harness.Observes trace
      (.trappedBeforeEntry harness trap finalState) observation
    by_cases htrap : Core.Harness.traceTrap? trace = some trap
    · cases hfinal : Core.Harness.observeStore harness finalState.store with
      | none => simp [observationOfConfig, htrap, hfinal] at h
      | some finalObservation =>
          simp [observationOfConfig, htrap, hfinal] at h
          subst observation
          exact .trappedBefore htrap hfinal
    · simp [observationOfConfig, htrap] at h
  | trappedAfterEntry harness entry trap finalState =>
    change Core.Harness.Observes trace
      (.trappedAfterEntry harness entry trap finalState) observation
    by_cases htrap : Core.Harness.traceTrap? trace = some trap
    · cases hentry : Core.Harness.observeStore harness entry with
      | none => simp [observationOfConfig, htrap, hentry] at h
      | some entryObservation =>
          cases hfinal : Core.Harness.observeStore harness finalState.store with
          | none =>
              simp [observationOfConfig, htrap, hentry, hfinal] at h
          | some finalObservation =>
              simp [observationOfConfig, htrap, hentry, hfinal] at h
              subst observation
              exact .trappedAfter htrap hentry hfinal
    · simp [observationOfConfig, htrap] at h
  | thrownBeforeEntry harness address exceptionValue finalState =>
    change Core.Harness.Observes trace
      (.thrownBeforeEntry harness address exceptionValue finalState) observation
    cases hfinal : Core.Harness.observeStore harness finalState.store with
    | none => simp [observationOfConfig, hfinal] at h
    | some finalObservation =>
        simp [observationOfConfig, hfinal] at h
        subst observation
        exact .thrownBefore hfinal
  | thrownAfterEntry harness entry address exceptionValue finalState =>
    change Core.Harness.Observes trace
      (.thrownAfterEntry harness entry address exceptionValue finalState)
        observation
    cases hentry : Core.Harness.observeStore harness entry with
    | none => simp [observationOfConfig, hentry] at h
    | some entryObservation =>
        cases hfinal : Core.Harness.observeStore harness finalState.store with
        | none => simp [observationOfConfig, hentry, hfinal] at h
        | some finalObservation =>
            simp [observationOfConfig, hentry, hfinal] at h
            subst observation
            exact .thrownAfter hentry hfinal

/-- Every relational terminal observation is returned by the executable
projection. -/
theorem observationOfConfig_complete {trace : List Event} {config : Config}
    {observation : ExecutionObservation}
    (h : Core.Harness.Observes trace config.1 observation) :
    observationOfConfig trace config = some observation := by
  rcases config with ⟨config, typed⟩
  change Core.Harness.Observes trace config observation at h
  cases h <;> simp [observationOfConfig, *]

theorem observationOfConfig_iff_observes {trace : List Event}
    {config : Config} {observation : ExecutionObservation} :
    observationOfConfig trace config = some observation ↔
      Core.Harness.Observes trace config.1 observation :=
  ⟨observationOfConfig_sound, observationOfConfig_complete⟩

/-- Every relational observation comes from a terminal raw Harness phase. -/
theorem isTerminal_of_observes {trace : List Event}
    {config : Core.Harness.Config} {observation : ExecutionObservation}
    (h : Core.Harness.Observes trace config observation) :
    Core.Harness.IsTerminal config := by
  cases h with
  | returned hentry hfinal =>
      exact Or.inl ⟨_, .returned _ _ _ _⟩
  | trappedBefore htrap hfinal =>
      exact Or.inr (Or.inl ⟨_, .beforeEntry _ _ _⟩)
  | trappedAfter htrap hentry hfinal =>
      exact Or.inr (Or.inl ⟨_, .afterEntry _ _ _ _⟩)
  | thrownBefore hfinal =>
      exact Or.inr (Or.inr ⟨_, .beforeEntry _ _ _ _⟩)
  | thrownAfter hentry hfinal =>
      exact Or.inr (Or.inr ⟨_, .afterEntry _ _ _ _ _⟩)

/-- A computed observation is terminal. -/
theorem isTerminal_of_observationOfConfig {trace : List Event}
    {config : Config} {observation : ExecutionObservation}
    (h : observationOfConfig trace config = some observation) :
    IsTerminal config := by
  exact isTerminal_of_observes (observationOfConfig_sound h)

end WasmGemmGnaf.Wasm
