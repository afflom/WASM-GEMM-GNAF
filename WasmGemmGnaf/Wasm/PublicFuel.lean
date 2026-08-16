/-
  Verified bounded all-branch exploration for the proof-carrying public
  amended-Core Harness machine.
-/
import WasmGemmGnaf.Wasm.PublicObservation
import WasmGemmGnaf.Wasm.PublicSuccessors
import WasmGemmGnaf.Foundation.Result

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

namespace Reduces

/-- Reflexivity for the public trace relation. -/
theorem refl (config : Config) : Reduces config [] config :=
  Core.Harness.StepsA.refl config.1

/-- Prefix one public transition to a public trace. -/
theorem cons {config next final : Config} {event : Event}
    {trace : List Event} (step : Step config event next)
    (tail : Reduces next trace final) :
    Reduces config (event :: trace) final :=
  Core.Harness.StepsA.cons step tail

/-- An empty public trace has the same proof-carrying endpoint. -/
theorem eq_of_nil {config final : Config}
    (reduction : Reduces config [] final) : config = final := by
  rcases config with ⟨config, configTyped⟩
  rcases final with ⟨final, finalTyped⟩
  change Core.Harness.StepsA config [] final at reduction
  cases reduction
  rfl

/-- Expose the first edge of a nonempty public reduction while reconstructing
the proof-carrying intermediate configuration by preservation. -/
theorem uncons {config final : Config} {event : Event} {trace : List Event}
    (reduction : Reduces config (event :: trace) final) :
    ∃ next : Config, Step config event next ∧ Reduces next trace final := by
  rcases config with ⟨config, configTyped⟩
  rcases final with ⟨final, finalTyped⟩
  change Core.Harness.StepsA config (event :: trace) final at reduction
  cases reduction with
  | cons step tail =>
      let next : Config := ⟨_, step.preserveWellTyped configTyped⟩
      exact ⟨next, step, tail⟩

end Reduces

/-- Membership in an optional singleton list is equality with `some`. -/
theorem mem_option_toList {α : Type} {option : Option α} {value : α} :
    value ∈ option.toList ↔ option = some value := by
  cases option <;> simp [Option.toList, eq_comm]

/-- The trace retained by a computed terminal observation is its input trace. -/
theorem trace_observationOfConfig {trace : List Event} {config : Config}
    {observation : ExecutionObservation}
    (h : observationOfConfig trace config = some observation) :
    observation.trace = trace := by
  rcases config with ⟨config, configTyped⟩
  have observes := observationOfConfig_sound h
  change Core.Harness.Observes trace config observation at observes
  cases observes <;> rfl

/-- Every terminal observation reachable within `fuel` steps.  The current
configuration is inspected at every depth, while every listed successor is
recursed into, so early terminal branches and all nondeterministic branches are
retained. -/
def exploreTree : Nat → List Event → Config → List ExecutionObservation
  | 0, trace, config => (observationOfConfig trace config).toList
  | fuel + 1, trace, config =>
      (observationOfConfig trace config).toList ++
        (successors config).flatMap fun successor =>
          exploreTree fuel (trace ++ [successor.1]) successor.2

@[simp] theorem exploreTree_zero (trace : List Event) (config : Config) :
    exploreTree 0 trace config = (observationOfConfig trace config).toList :=
  rfl

@[simp] theorem exploreTree_succ (fuel : Nat) (trace : List Event)
    (config : Config) :
    exploreTree (fuel + 1) trace config =
      (observationOfConfig trace config).toList ++
        (successors config).flatMap fun successor =>
          exploreTree fuel (trace ++ [successor.1]) successor.2 :=
  rfl

/-- Every observation emitted by the executable tree is a relational finite
execution from the explored configuration. -/
theorem exploreTree_sound :
    ∀ (fuel : Nat) (trace : List Event) (config : Config)
      (observation : ExecutionObservation),
      observation ∈ exploreTree fuel trace config →
      ∃ (suffix : List Event) (final : Config),
        observation.trace = trace ++ suffix ∧
          Reduces config suffix final ∧
          observationOfConfig observation.trace final = some observation := by
  intro fuel
  induction fuel with
  | zero =>
      intro trace config observation hmember
      have hobserve : observationOfConfig trace config = some observation :=
        mem_option_toList.mp hmember
      refine ⟨[], config, ?_, Reduces.refl config, ?_⟩
      · simpa using trace_observationOfConfig hobserve
      · simpa [trace_observationOfConfig hobserve] using hobserve
  | succ fuel ih =>
      intro trace config observation hmember
      rw [exploreTree_succ, List.mem_append] at hmember
      cases hmember with
      | inl hcurrent =>
          have hobserve : observationOfConfig trace config = some observation :=
            mem_option_toList.mp hcurrent
          refine ⟨[], config, ?_, Reduces.refl config, ?_⟩
          · simpa using trace_observationOfConfig hobserve
          · simpa [trace_observationOfConfig hobserve] using hobserve
      | inr hsuccessor =>
          rw [List.mem_flatMap] at hsuccessor
          obtain ⟨successor, hsuccessor, hmember⟩ := hsuccessor
          obtain ⟨suffix, final, htrace, hreduces, hobserve⟩ :=
            ih (trace ++ [successor.1]) successor.2 observation hmember
          refine ⟨successor.1 :: suffix, final, ?_, ?_, hobserve⟩
          · rw [htrace]
            simp
          · apply Reduces.cons
            · exact (mem_successors_iff_step config successor.1 successor.2).mp
                (by simpa using hsuccessor)
            · exact hreduces

/-- Every relational terminal branch no longer than `fuel` occurs in the
executable tree. -/
theorem exploreTree_complete :
    ∀ (fuel : Nat) (trace suffix : List Event) (config final : Config)
      (observation : ExecutionObservation),
      Reduces config suffix final →
      observationOfConfig (trace ++ suffix) final = some observation →
      suffix.length ≤ fuel →
      observation ∈ exploreTree fuel trace config := by
  intro fuel
  induction fuel with
  | zero =>
      intro trace suffix config final observation hreduces hobserve hlength
      have hsuffix : suffix = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hlength)
      subst suffix
      have hfinal := Reduces.eq_of_nil hreduces
      subst final
      rw [exploreTree_zero, mem_option_toList]
      simpa using hobserve
  | succ fuel ih =>
      intro trace suffix config final observation hreduces hobserve hlength
      cases suffix with
      | nil =>
          have hfinal := Reduces.eq_of_nil hreduces
          subst final
          rw [exploreTree_succ, List.mem_append]
          exact Or.inl (mem_option_toList.mpr (by simpa using hobserve))
      | cons event rest =>
          obtain ⟨next, publicStep, publicTail⟩ := Reduces.uncons hreduces
          rw [exploreTree_succ, List.mem_append]
          apply Or.inr
          rw [List.mem_flatMap]
          refine ⟨(event, next),
            (mem_successors_iff_step config event next).mpr publicStep, ?_⟩
          apply ih (trace ++ [event]) rest next final observation publicTail
          · simpa using hobserve
          · simp only [List.length_cons] at hlength
            omega

/-- Traces of exactly `fuel` further relational steps, whether the endpoint is
terminal or not.  A trace of length `bound + 1` is precisely the executable
witness that the advertised bound was exceeded. -/
def prefixes : Nat → List Event → Config → List (List Event)
  | 0, trace, _ => [trace]
  | fuel + 1, trace, config =>
      (successors config).flatMap fun successor =>
        prefixes fuel (trace ++ [successor.1]) successor.2

/-- Every emitted prefix has the requested total length. -/
theorem prefixes_length :
    ∀ (fuel : Nat) (trace : List Event) (config : Config)
      (path : List Event),
      path ∈ prefixes fuel trace config →
      path.length = trace.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro trace config path hmember
      simp [prefixes] at hmember
      subst path
      simp
  | succ fuel ih =>
      intro trace config path hmember
      rw [prefixes, List.mem_flatMap] at hmember
      obtain ⟨successor, _, hmember⟩ := hmember
      have hlength := ih (trace ++ [successor.1]) successor.2 path hmember
      simp at hlength ⊢
      omega

/-- Every emitted prefix is a real public reduction sequence. -/
theorem prefixes_sound :
    ∀ (fuel : Nat) (trace : List Event) (config : Config)
      (path : List Event),
      path ∈ prefixes fuel trace config →
      ∃ (suffix : List Event) (final : Config),
        path = trace ++ suffix ∧ Reduces config suffix final ∧
          suffix.length = fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro trace config path hmember
      simp [prefixes] at hmember
      subst path
      exact ⟨[], config, by simp, Reduces.refl config, rfl⟩
  | succ fuel ih =>
      intro trace config path hmember
      rw [prefixes, List.mem_flatMap] at hmember
      obtain ⟨successor, hsuccessor, hmember⟩ := hmember
      obtain ⟨suffix, final, hprefix, hreduces, hlength⟩ :=
        ih (trace ++ [successor.1]) successor.2 path hmember
      refine ⟨successor.1 :: suffix, final, ?_, ?_, ?_⟩
      · rw [hprefix]
        simp
      · apply Reduces.cons
        · exact (mem_successors_iff_step config successor.1 successor.2).mp
            (by simpa using hsuccessor)
        · exact hreduces
      · simp [hlength]

/-- Every relational branch with at least `fuel` steps contributes an
executable prefix of exactly that length. -/
theorem prefixes_nonempty_of_reduces :
    ∀ (fuel : Nat) (trace suffix : List Event) (config final : Config),
      Reduces config suffix final → fuel ≤ suffix.length →
      ∃ path, path ∈ prefixes fuel trace config := by
  intro fuel
  induction fuel with
  | zero =>
      intro trace suffix config final hreduces hlength
      exact ⟨trace, by simp [prefixes]⟩
  | succ fuel ih =>
      intro trace suffix config final hreduces hlength
      cases suffix with
      | nil => simp at hlength
      | cons event rest =>
          obtain ⟨next, publicStep, publicTail⟩ := Reduces.uncons hreduces
          have htailLength : fuel ≤ rest.length := by
            simp only [List.length_cons] at hlength
            omega
          obtain ⟨path, hpath⟩ :=
            ih (trace ++ [event]) rest next final publicTail htailLength
          refine ⟨path, ?_⟩
          rw [prefixes, List.mem_flatMap]
          exact ⟨(event, next),
            (mem_successors_iff_step config event next).mpr publicStep, hpath⟩

/-- A trace of exactly `length` public events. -/
structure TraceOfLength (length : Nat) where
  events : List Event
  length_eq : events.length = length

/-- Soundness plus bounded completeness for the observations retained by one
tree. -/
def CoversEveryMaximalFiniteBranch (bound : Nat) (initial : Config)
    (observations : List ExecutionObservation) : Prop :=
  (∀ observation ∈ observations, FiniteExecution initial observation) ∧
    (∀ observation : ExecutionObservation,
      FiniteExecution initial observation →
      observation.trace.length ≤ bound → observation ∈ observations)

/-- Result of the public bounded all-branch explorer. -/
inductive ExecutionTreeResult (bound : Nat) (initial : Config)
  | complete (observations : List ExecutionObservation)
      (coverage : CoversEveryMaximalFiniteBranch bound initial observations)
  | nonterminalPrefix (observations : List ExecutionObservation)
      (coverage : CoversEveryMaximalFiniteBranch bound initial observations)
      (trace : TraceOfLength (bound + 1))
  | initializationFailure (report : FailureReport)

/-- Observations retained by either executable tree branch. -/
def ExecutionTreeResult.observations {bound : Nat} {initial : Config} :
    ExecutionTreeResult bound initial → List ExecutionObservation
  | .complete observations _ => observations
  | .nonterminalPrefix observations _ _ => observations
  | .initializationFailure _ => []

/-- Observation membership in an executable tree result. -/
def TreeContains {bound : Nat} {initial : Config}
    (result : ExecutionTreeResult bound initial)
    (observation : ExecutionObservation) : Prop :=
  observation ∈ result.observations

/-- The raw public tree is sound and complete for every finite execution
inside its explicit bound. -/
theorem covers_exploreTree (bound : Nat) (initial : Config) :
    CoversEveryMaximalFiniteBranch bound initial
      (exploreTree bound [] initial) := by
  constructor
  · intro observation hmember
    obtain ⟨suffix, final, htrace, hreduces, hobserve⟩ :=
      exploreTree_sound bound [] initial observation hmember
    unfold FiniteExecution
    apply Core.Harness.FiniteExecution.mk hreduces
    rw [htrace] at hobserve
    exact observationOfConfig_sound hobserve
  · intro observation hrun hlength
    unfold FiniteExecution at hrun
    cases hrun with
    | @mk trace rawFinal _ rawReduction observes =>
        let final : Config :=
          ⟨rawFinal, rawReduction.preserveWellTyped initial.2⟩
        have hobserve : observationOfConfig trace final = some observation :=
          observationOfConfig_complete observes
        have htrace : observation.trace = trace := by
          cases observes <;> rfl
        apply exploreTree_complete bound [] trace initial final observation
        · exact rawReduction
        · simpa using hobserve
        · simpa [htrace] using hlength

/-- The public bounded all-branch explorer. -/
def exploreAll (bound : Nat) (initial : Config) :
    ExecutionTreeResult bound initial :=
  match hprefixes : prefixes (bound + 1) [] initial with
  | trace :: rest =>
      .nonterminalPrefix (exploreTree bound [] initial)
        (covers_exploreTree bound initial)
        ⟨trace, by
          have hmember : trace ∈ prefixes (bound + 1) [] initial := by
            simp [hprefixes]
          simpa using prefixes_length (bound + 1) [] initial trace hmember⟩
  | [] =>
      .complete (exploreTree bound [] initial)
        (covers_exploreTree bound initial)

/-- Both successful result constructors expose the same explored tree. -/
theorem observations_exploreAll (bound : Nat) (initial : Config) :
    (exploreAll bound initial).observations = exploreTree bound [] initial := by
  unfold exploreAll
  split <;> rfl

/-- **SPEC §7.4.** Every returned tree observation is a relational finite
execution. -/
theorem runFuel_sound {bound : Nat} {initial : Config}
    {observation : ExecutionObservation}
    (hmember : TreeContains (exploreAll bound initial) observation) :
    FiniteExecution initial observation := by
  unfold TreeContains at hmember
  rw [observations_exploreAll] at hmember
  exact (covers_exploreTree bound initial).1 observation hmember

/-- **SPEC §7.4.** Every relational finite branch inside the explicit bound
occurs in the executable tree. -/
theorem runFuel_complete_with_bound {bound : Nat} {initial : Config}
    {observation : ExecutionObservation}
    (hrun : FiniteExecution initial observation)
    (hlen : observation.trace.length ≤ bound) :
    TreeContains (exploreAll bound initial) observation := by
  unfold TreeContains
  rw [observations_exploreAll]
  exact (covers_exploreTree bound initial).2 observation hrun hlen

/-- A completed bounded tree contains every finite maximal branch, without a
remaining length hypothesis: completion proves that no trace of length
`bound + 1` exists. -/
theorem bounded_tree_covers_every_branch {bound : Nat} {initial : Config}
    {observations : List ExecutionObservation}
    {coverage : CoversEveryMaximalFiniteBranch bound initial observations}
    (hcomplete : exploreAll bound initial = .complete observations coverage)
    {observation : ExecutionObservation}
    (hrun : FiniteExecution initial observation) :
    observation ∈ observations := by
  have hprefixes : prefixes (bound + 1) [] initial = [] := by
    have htag := congrArg
      (fun result : ExecutionTreeResult bound initial =>
        match result with
        | .complete _ _ => true
        | .nonterminalPrefix _ _ _ => false
        | .initializationFailure _ => false)
      hcomplete
    unfold exploreAll at htag
    split at htag
    · simp at htag
    · rename_i hprefixes
      exact hprefixes
  have hlength : observation.trace.length ≤ bound := by
    by_cases hle : observation.trace.length ≤ bound
    · exact hle
    · exfalso
      have hover : bound + 1 ≤ observation.trace.length := by omega
      have hrunCopy := hrun
      unfold FiniteExecution at hrunCopy
      cases hrunCopy with
      | @mk trace rawFinal _ rawReduction observes =>
          have htrace : observation.trace = trace := by
            cases observes <;> rfl
          have hoverTrace : bound + 1 ≤ trace.length := by
            simpa [htrace] using hover
          let final : Config :=
            ⟨rawFinal, rawReduction.preserveWellTyped initial.2⟩
          have hnonempty := prefixes_nonempty_of_reduces (bound + 1) [] trace
            initial final rawReduction hoverTrace
          obtain ⟨path, hpath⟩ := hnonempty
          rw [hprefixes] at hpath
          simp at hpath
  exact coverage.2 observation hrun hlength

end WasmGemmGnaf.Wasm
