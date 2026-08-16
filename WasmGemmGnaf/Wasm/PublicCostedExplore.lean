/-
  Canonical costed exploration for the proof-carrying public amended-Core
  Harness machine.
-/
import WasmGemmGnaf.Wasm.Evaluate
import WasmGemmGnaf.Wasm.PublicFuel
import WasmGemmGnaf.Wasm.Core.HarnessFunctional
import WasmGemmGnaf.Foundation.Bytes

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Canonical branch codes

An authority event is intentionally rich: it retains the complete Core rule
and all cost-relevant operands.  The explorer does not duplicate a second
serialization of that authority syntax.  Instead, a valid trace is encoded by
its characteristic choice vector at each finite public successor list.  For a
fixed initial configuration these vectors determine the event trace exactly.
-/

/-- The Boolean characteristic vector of an event in one successor list. -/
def eventChoiceBits (config : Config) (event : Event) : List Bool :=
  (successors config).map fun edge => decide (edge.1 = event)

/-- Follow the first successor carrying the requested exact event. -/
def followEvent? (config : Config) (event : Event) : Option Config :=
  ((successors config).find? fun edge => decide (edge.1 = event)).map (·.2)

/-- A valid labelled step is found by the executable successor search, and
fixed-event target functionality pins the found target. -/
theorem followEvent?_eq_some_of_step {config next : Config} {event : Event}
    (step : Step config event next) : followEvent? config event = some next := by
  have hmember : (event, next) ∈ successors config :=
    (mem_successors_iff_step config event next).mpr step
  unfold followEvent?
  cases hfind : (successors config).find?
      (fun edge => decide (edge.1 = event)) with
  | none =>
      rw [List.find?_eq_none] at hfind
      exact False.elim (absurd (hfind (event, next) hmember) (by simp))
  | some edge =>
      have hedgeMember : edge ∈ successors config :=
        List.mem_of_find?_eq_some hfind
      have hedgeTest := List.find?_some hfind
      rcases edge with ⟨foundEvent, foundNext⟩
      have hedgeEvent : foundEvent = event := by
        exact of_decide_eq_true (by simpa using hedgeTest)
      subst foundEvent
      have hedgeStep : Step config event foundNext :=
        (mem_successors_iff_step config event foundNext).mp hedgeMember
      have hedgeTarget : foundNext = next := step_target_functional hedgeStep step
      simp [hfind, hedgeTarget]

/-- Equality of maps over one fixed list is pointwise at every member. -/
theorem map_eq_at_member {α β : Type} {values : List α} {left right : α → β}
    (hmaps : values.map left = values.map right) {value : α}
    (hvalue : value ∈ values) : left value = right value := by
  induction values with
  | nil => simp at hvalue
  | cons head rest ih =>
      simp only [List.map_cons, List.cons.injEq] at hmaps
      rcases hmaps with ⟨hhead, htail⟩
      simp only [List.mem_cons] at hvalue
      cases hvalue with
      | inl heq => simpa [heq] using hhead
      | inr hmem => exact ih htail hmem

/-- On admitted steps, the characteristic vector determines the exact event. -/
theorem event_eq_of_choiceBits_eq {config leftNext rightNext : Config}
    {leftEvent rightEvent : Event}
    (leftStep : Step config leftEvent leftNext)
    (rightStep : Step config rightEvent rightNext)
    (hbits : eventChoiceBits config leftEvent =
      eventChoiceBits config rightEvent) :
    leftEvent = rightEvent := by
  have hmember : (leftEvent, leftNext) ∈ successors config :=
    (mem_successors_iff_step config leftEvent leftNext).mpr leftStep
  have hpoint := map_eq_at_member hbits hmember
  simp only [decide_true] at hpoint
  exact of_decide_eq_true hpoint.symm

/-- Canonical branch-choice vectors for an event trace.  Invalid traces stop
at the first missing event; relational traces never take that branch. -/
def branchChoices : Config → List Event → List (List Bool)
  | _, [] => []
  | config, event :: rest =>
      eventChoiceBits config event ::
        match followEvent? config event with
        | none => []
        | some next => branchChoices next rest

/-- For a fixed public initial configuration, valid relational traces have
injective canonical branch-choice vectors. -/
theorem branchChoices_injective_of_reduces {initial : Config} :
    ∀ {leftTrace rightTrace : List Event} {leftFinal rightFinal : Config},
      Reduces initial leftTrace leftFinal →
      Reduces initial rightTrace rightFinal →
      branchChoices initial leftTrace = branchChoices initial rightTrace →
      leftTrace = rightTrace := by
  intro leftTrace
  induction leftTrace generalizing initial with
  | nil =>
      intro rightTrace leftFinal rightFinal leftReduction rightReduction hchoices
      cases rightTrace with
      | nil => rfl
      | cons rightEvent rightRest =>
          obtain ⟨rightNext, rightStep, rightTail⟩ :=
            Reduces.uncons rightReduction
          simp [branchChoices, followEvent?_eq_some_of_step rightStep] at hchoices
  | cons leftEvent leftRest ih =>
      intro rightTrace leftFinal rightFinal leftReduction rightReduction hchoices
      obtain ⟨leftNext, leftStep, leftTail⟩ := Reduces.uncons leftReduction
      cases rightTrace with
      | nil =>
          simp [branchChoices, followEvent?_eq_some_of_step leftStep] at hchoices
      | cons rightEvent rightRest =>
          obtain ⟨rightNext, rightStep, rightTail⟩ :=
            Reduces.uncons rightReduction
          simp only [branchChoices,
            followEvent?_eq_some_of_step leftStep,
            followEvent?_eq_some_of_step rightStep,
            List.cons.injEq] at hchoices
          have hevent : leftEvent = rightEvent :=
            event_eq_of_choiceBits_eq leftStep rightStep hchoices.1
          subst rightEvent
          have hnext : leftNext = rightNext :=
            step_target_functional leftStep rightStep
          subst rightNext
          have hrest : leftRest = rightRest :=
            ih leftTail rightTail hchoices.2
          subst rightRest
          rfl

/-! ## Costed-observation identity -/

/-- A public costed observation is determined by its exact public observation.
The fixed-event target theorem pins every visited configuration and therefore
every retained resource snapshot. -/
theorem CostedExecutionObservation.eq_of_observation_eq
    {profile : Profile} {initial : Config}
    (left right : CostedExecutionObservation profile initial)
    (hobservation : left.observation = right.observation) : left = right := by
  obtain ⟨htrace, hconfigs, hcost⟩ :=
    left.functional_of_observation Core.Harness.StepA.target_functional
      right hobservation
  cases left
  cases right
  simp only at hobservation htrace hconfigs hcost
  subst hobservation
  subst htrace
  subst hconfigs
  subst hcost
  rfl

/-- Branch-choice vectors are injective on proof-carrying costed observations. -/
theorem costedBranchChoices_injective (profile : Profile) (initial : Config) :
    Function.Injective
      (fun costed : CostedExecutionObservation profile initial =>
        branchChoices initial (eraseCosts costed.costedTrace)) := by
  intro left right hchoices
  obtain ⟨leftVisited, leftRawFinal, leftReduction, _, leftObserves⟩ := left.run
  obtain ⟨rightVisited, rightRawFinal, rightReduction, _, rightObserves⟩ :=
    right.run
  let leftFinal : Config :=
    ⟨leftRawFinal, leftReduction.erase.preserveWellTyped initial.2⟩
  let rightFinal : Config :=
    ⟨rightRawFinal, rightReduction.erase.preserveWellTyped initial.2⟩
  have leftPublic : Reduces initial (eraseCosts left.costedTrace) leftFinal :=
    leftReduction.erase
  have rightPublic : Reduces initial (eraseCosts right.costedTrace) rightFinal :=
    rightReduction.erase
  have herased : eraseCosts left.costedTrace = eraseCosts right.costedTrace :=
    branchChoices_injective_of_reduces leftPublic rightPublic hchoices
  have htrace : left.costedTrace = right.costedTrace :=
    eraseCosts_injective herased
  obtain ⟨_, _, hrawFinal⟩ :=
    CostedReduces.unique_of_step_functional
      Core.Harness.StepA.target_functional leftReduction rightReduction herased
  have hobservation : left.observation = right.observation := by
    have hleft : observationOfConfig (eraseCosts left.costedTrace) leftFinal =
        some left.observation := observationOfConfig_complete leftObserves
    have hright : observationOfConfig (eraseCosts right.costedTrace) rightFinal =
        some right.observation := observationOfConfig_complete rightObserves
    have hfinal : leftFinal = rightFinal := by
      apply Subtype.ext
      exact hrawFinal
    rw [herased, hfinal] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  exact left.eq_of_observation_eq right hobservation

/-- Prefix-free bytes for one costed observation, relative to its fixed public
initial configuration. -/
def costedObservationBytes {profile : Profile} (initial : Config)
    (costed : CostedExecutionObservation profile initial) : List UInt8 :=
  Bytes.listBytes (Bytes.listBytes Bytes.boolBytes)
    (branchChoices initial (eraseCosts costed.costedTrace))

theorem costedObservationBytes_prefixFree {profile : Profile}
    (initial : Config) :
    Bytes.PrefixFree (costedObservationBytes (profile := profile) initial) :=
  (Bytes.listBytes_prefixFree
    (Bytes.listBytes_prefixFree Bytes.boolBytes_prefixFree)).comp
      (costedBranchChoices_injective profile initial)

/-- Frozen canonical schema for public costed observations. -/
def costedObservationSchema (profile : Profile) (initial : Config) :
    CanonicalSchema (CostedExecutionObservation profile initial) :=
  CanonicalSchema.ofPrefixFree 1 .generic
    (TypeTag.leaf [80, 117, 98, 108, 105, 99, 67, 111, 115, 116])
    (TypeTag.leaf_size_pos _) (costedObservationBytes initial)
    (costedObservationBytes_prefixFree initial)

/-! ## Executable replay and exact cost lifting -/

/-- Replay a trace through the exact successor enumeration while retaining
every visited proof-carrying configuration.  The result is nonempty even for
an invalid trace; relational traces never use the missing-event branch. -/
def replayConfigs : Config → List Event → NonemptyCanonicalList Config
  | config, [] => .singleton config
  | config, event :: rest =>
      match followEvent? config event with
      | none => .singleton config
      | some next =>
          let tail := replayConfigs next rest
          { head := config, rest := tail.elements }

/-- Replay snapshots in semantic visit order. -/
def replaySnapshots (profile : Profile) (initial : Config)
    (trace : List Event) : NonemptyCanonicalList ConfigResourceSnapshot :=
  let configs := replayConfigs initial trace
  { head := snapshotOf profile.costTableBody.layout configs.head
    rest := configs.rest.map (snapshotOf profile.costTableBody.layout) }

@[simp] theorem replaySnapshots_elements (profile : Profile) (initial : Config)
    (trace : List Event) :
    (replaySnapshots profile initial trace).elements =
      (replayConfigs initial trace).elements.map
        (snapshotOf profile.costTableBody.layout) := by
  rfl

/-- A valid replay has exactly the visited raw configurations retained by the
independent cost-labelled reduction relation. -/
theorem replayConfigs_costedReduces {initial : Config} :
    ∀ {trace : List Event} {final : Config},
      Reduces initial trace final →
      ∃ visited : List RawConfig,
        CostedReduces initial.1 (labelCosts trace) visited final.1 ∧
          (replayConfigs initial trace).elements.map (·.1) = visited := by
  intro trace
  induction trace generalizing initial with
  | nil =>
      intro final reduction
      have hfinal := Reduces.eq_of_nil reduction
      subst final
      exact ⟨[initial.1], .refl initial.1, by simp [replayConfigs]⟩
  | cons event rest ih =>
      intro final reduction
      obtain ⟨next, step, tail⟩ := Reduces.uncons reduction
      obtain ⟨visited, costedTail, hvisited⟩ := ih tail
      refine ⟨initial.1 :: visited,
        .cons (.ofEvent event) step costedTail, ?_⟩
      simp only [replayConfigs, followEvent?_eq_some_of_step step,
        NonemptyCanonicalList.elements, List.map_cons, List.cons.injEq,
        true_and]
      exact hvisited

/-- Snapshot replay agrees exactly with the raw visited list of a relational
trace. -/
theorem replaySnapshots_eq_visited {profile : Profile} {initial final : Config}
    {trace : List Event} (reduction : Reduces initial trace final) :
    ∃ visited : List RawConfig,
      CostedReduces initial.1 (labelCosts trace) visited final.1 ∧
        (replaySnapshots profile initial trace).elements =
          visited.map (snapshotRaw profile.costTableBody.layout) := by
  obtain ⟨visited, costed, hconfigs⟩ :=
    replayConfigs_costedReduces reduction
  refine ⟨visited, costed, ?_⟩
  rw [replaySnapshots_elements]
  have hmapped := congrArg
    (List.map (snapshotRaw profile.costTableBody.layout)) hconfigs
  simpa [List.map_map, Function.comp_def, snapshotOf] using hmapped

/-- Construct the unique independently cost-labelled observation of one
relational finite execution.  All data fields are executable functions of the
initial configuration and exact observation trace. -/
def costedOfObservation (profile : Profile) (initial : Config)
    (observation : ExecutionObservation)
    (run : FiniteExecution initial observation) :
    CostedExecutionObservation profile initial where
  observation := observation
  costedTrace := labelCosts observation.trace
  configs := replaySnapshots profile initial observation.trace
  run := by
    unfold FiniteExecution at run
    cases run with
    | @mk trace rawFinal _ rawReduction observes =>
        have htrace : observation.trace = trace := by
          cases observes <;> rfl
        let final : Config :=
          ⟨rawFinal, rawReduction.preserveWellTyped initial.2⟩
        have publicReduction : Reduces initial trace final := rawReduction
        obtain ⟨visited, costedReduction, hconfigs⟩ :=
          replaySnapshots_eq_visited (profile := profile) publicReduction
        refine ⟨visited, rawFinal, ?_, ?_, ?_⟩
        · simpa [htrace] using costedReduction
        · simpa [htrace] using hconfigs
        · simpa [htrace] using observes
  maximal := run.isTerminalObservation
  cost := Cost.foldTrace profile.costTableBody
    (replaySnapshots profile initial observation.trace)
    (labelCosts observation.trace)
  costExact := rfl

@[simp] theorem costedOfObservation_observation (profile : Profile)
    (initial : Config) (observation : ExecutionObservation)
    (run : FiniteExecution initial observation) :
    (costedOfObservation profile initial observation run).observation =
      observation := rfl

/-- Lift every observation in a list with its exact relational derivation. -/
def costedList (profile : Profile) (initial : Config) :
    (observations : List ExecutionObservation) →
    (∀ observation ∈ observations, FiniteExecution initial observation) →
    List (CostedExecutionObservation profile initial)
  | [], _ => []
  | observation :: rest, sound =>
      costedOfObservation profile initial observation
          (sound observation List.mem_cons_self) ::
        costedList profile initial rest
          (fun other hmember => sound other (List.mem_cons_of_mem observation hmember))

@[simp] theorem costedList_map_observation (profile : Profile)
    (initial : Config) :
    ∀ (observations : List ExecutionObservation)
      (sound : ∀ observation ∈ observations,
        FiniteExecution initial observation),
      (costedList profile initial observations sound).map (·.observation) =
        observations
  | [], _ => rfl
  | observation :: rest, sound => by
      simp only [costedList, List.map_cons, costedOfObservation_observation,
        List.cons.injEq, true_and]
      exact costedList_map_observation profile initial rest _

/-! ## Canonical frontier ordering -/

section Sorting

variable {α : Type}

/-- Insert one value into a canonically ordered list. -/
def canonicalInsert (schema : CanonicalSchema α) (value : α) :
    List α → List α
  | [] => [value]
  | head :: rest =>
      if CanonicalBytesLE (schema.encode value) (schema.encode head) then
        value :: head :: rest
      else head :: canonicalInsert schema value rest

/-- Executable insertion sort under the frozen canonical byte order. -/
def canonicalSort (schema : CanonicalSchema α) : List α → List α
  | [] => []
  | head :: rest => canonicalInsert schema head (canonicalSort schema rest)

theorem canonicalSorted_map_tail {schema : CanonicalSchema α} {head : α}
    {rest : List α}
    (sorted : CanonicalSorted ((head :: rest).map schema.encode)) :
    CanonicalSorted (rest.map schema.encode) := by
  cases rest with
  | nil => simp
  | cons next tail =>
      simp only [List.map_cons] at sorted ⊢
      exact (canonicalSorted_cons_cons.mp sorted).2

theorem canonicalSorted_map_cons {schema : CanonicalSchema α} (head : α) :
    ∀ values : List α,
      CanonicalSorted (values.map schema.encode) →
      (∀ (next : α) (tail : List α), values = next :: tail →
        CanonicalBytesLE (schema.encode head) (schema.encode next)) →
      CanonicalSorted ((head :: values).map schema.encode)
  | [], _, _ => by simp
  | next :: tail, sorted, headLe => by
      simp only [List.map_cons] at sorted ⊢
      exact canonicalSorted_cons_cons.mpr ⟨headLe next tail rfl, sorted⟩

theorem canonicalInsert_head (schema : CanonicalSchema α) (value : α) :
    ∀ (values : List α) (head : α) (tail : List α),
      canonicalInsert schema value values = head :: tail →
      head = value ∨ ∃ rest, values = head :: rest
  | [], head, tail, equality => by
      unfold canonicalInsert at equality
      simp only [List.cons.injEq] at equality
      exact Or.inl equality.1.symm
  | current :: rest, head, tail, equality => by
      unfold canonicalInsert at equality
      split at equality
      · simp only [List.cons.injEq] at equality
        exact Or.inl equality.1.symm
      · simp only [List.cons.injEq] at equality
        exact Or.inr ⟨rest, by rw [equality.1]⟩

theorem canonicalInsert_sorted (schema : CanonicalSchema α) (value : α) :
    ∀ values : List α,
      CanonicalSorted (values.map schema.encode) →
      CanonicalSorted ((canonicalInsert schema value values).map schema.encode)
  | [], _ => by simp [canonicalInsert]
  | head :: rest, sorted => by
      unfold canonicalInsert
      split
      · rename_i hle
        simp only [List.map_cons] at sorted ⊢
        exact canonicalSorted_cons_cons.mpr ⟨hle, sorted⟩
      · rename_i hnotle
        have hreverse :
            CanonicalBytesLE (schema.encode head) (schema.encode value) :=
          (CanonicalBytesLE.total (schema.encode value)
            (schema.encode head)).resolve_left hnotle
        refine canonicalSorted_map_cons head _
          (canonicalInsert_sorted schema value rest
            (canonicalSorted_map_tail sorted)) ?_
        intro next tail equality
        rcases canonicalInsert_head schema value rest next tail equality with
          hvalue | ⟨remaining, hremaining⟩
        · rw [hvalue]
          exact hreverse
        · rw [hremaining] at sorted
          simp only [List.map_cons] at sorted
          exact (canonicalSorted_cons_cons.mp sorted).1

theorem canonicalInsert_perm (schema : CanonicalSchema α) (value : α) :
    ∀ values : List α,
      (canonicalInsert schema value values).Perm (value :: values)
  | [] => List.Perm.refl _
  | head :: rest => by
      unfold canonicalInsert
      split
      · exact List.Perm.refl _
      · exact List.Perm.trans
          (List.Perm.cons head (canonicalInsert_perm schema value rest))
          (List.Perm.swap value head rest)

theorem canonicalSort_sorted (schema : CanonicalSchema α) :
    ∀ values : List α,
      CanonicalSorted ((canonicalSort schema values).map schema.encode)
  | [] => by simp [canonicalSort]
  | head :: rest => by
      unfold canonicalSort
      exact canonicalInsert_sorted schema head _
        (canonicalSort_sorted schema rest)

theorem canonicalSort_perm (schema : CanonicalSchema α) :
    ∀ values : List α, (canonicalSort schema values).Perm values
  | [] => List.Perm.refl _
  | head :: rest => by
      unfold canonicalSort
      exact List.Perm.trans
        (canonicalInsert_perm schema head (canonicalSort schema rest))
        (List.Perm.cons head (canonicalSort_perm schema rest))

end Sorting

/-- Canonically sort the exact costed lifts of a plain observation list. -/
def costedObservations (profile : Profile) (initial : Config)
    (observations : List ExecutionObservation)
    (sound : ∀ observation ∈ observations,
      FiniteExecution initial observation) :
    List (CostedExecutionObservation profile initial) :=
  canonicalSort (costedObservationSchema profile initial)
    (costedList profile initial observations sound)

theorem costedObservations_sorted (profile : Profile) (initial : Config)
    (observations : List ExecutionObservation)
    (sound : ∀ observation ∈ observations,
      FiniteExecution initial observation) :
    CanonicalSorted
      ((costedObservations profile initial observations sound).map
        (costedObservationSchema profile initial).encode) :=
  canonicalSort_sorted _ _

theorem costedObservations_map_observation_perm (profile : Profile)
    (initial : Config) (observations : List ExecutionObservation)
    (sound : ∀ observation ∈ observations,
      FiniteExecution initial observation) :
    ((costedObservations profile initial observations sound).map
      (·.observation)).Perm observations := by
  have permutation := List.Perm.map
    (fun costed : CostedExecutionObservation profile initial =>
      costed.observation)
    (canonicalSort_perm (costedObservationSchema profile initial)
      (costedList profile initial observations sound))
  rwa [costedList_map_observation] at permutation

theorem costedObservations_ne_nil (profile : Profile) (initial : Config)
    (observations : List ExecutionObservation)
    (sound : ∀ observation ∈ observations,
      FiniteExecution initial observation)
    (nonempty : observations ≠ []) :
    costedObservations profile initial observations sound ≠ [] := by
  intro empty
  have permutation :=
    costedObservations_map_observation_perm profile initial observations sound
  rw [empty] at permutation
  apply nonempty
  apply List.eq_nil_of_length_eq_zero
  exact permutation.length_eq.symm

/-! ## Relational bound consequences -/

/-- The endpoint obtained by replaying an event trace through the exact public
successor enumeration. -/
def replayFinal : Config → List Event → Config
  | config, [] => config
  | config, event :: rest =>
      match followEvent? config event with
      | none => config
      | some next => replayFinal next rest

/-- Relational traces replay to their own endpoint. -/
theorem replayFinal_eq_of_reduces {initial final : Config}
    {trace : List Event} (reduction : Reduces initial trace final) :
    replayFinal initial trace = final := by
  induction trace generalizing initial with
  | nil =>
      simpa [replayFinal] using Reduces.eq_of_nil reduction
  | cons event rest ih =>
      obtain ⟨next, step, tail⟩ := Reduces.uncons reduction
      simp [replayFinal, followEvent?_eq_some_of_step step, ih tail]

/-- Turn an executable exact-length prefix into the public relational overrun
witness retained by `CostedTreeResult`. -/
def nonterminalPrefixOfMember (initial : Config) (length : Nat)
    (events : List Event) (member : events ∈ prefixes length [] initial) :
    NonterminalPrefix initial length :=
  { witness :=
      { events := events
        final := replayFinal initial events
        lengthEq := by simpa using prefixes_length length [] initial events member }
    valid := by
      obtain ⟨suffix, final, hevents, reduction, _⟩ :=
        prefixes_sound length [] initial events member
      have heq : events = suffix := by simpa using hevents
      subst events
      unfold RelationalPrefix.Valid
      simpa [replayFinal_eq_of_reduces reduction] using reduction }

/-- An empty exact-prefix enumeration is the semantic no-overrun statement. -/
theorem noOverrun_of_prefixes_eq_nil {bound : Nat} {initial : Config}
    (empty : prefixes (bound + 1) [] initial = []) :
    ¬ ∃ branchPrefix : RelationalPrefix initial (bound + 1),
      branchPrefix.Valid := by
  rintro ⟨branchPrefix, valid⟩
  have nonempty := prefixes_nonempty_of_reduces (bound + 1) []
    branchPrefix.events initial branchPrefix.final valid
    (Nat.le_of_eq branchPrefix.lengthEq.symm)
  obtain ⟨events, member⟩ := nonempty
  rw [empty] at member
  simp at member

/-- Conversely, semantic no-overrun forces the exact-prefix enumeration to be
empty. -/
theorem prefixes_eq_nil_of_noOverrun {bound : Nat} {initial : Config}
    (noOverrun : ¬ ∃ branchPrefix : RelationalPrefix initial (bound + 1),
      branchPrefix.Valid) :
    prefixes (bound + 1) [] initial = [] := by
  cases hprefixes : prefixes (bound + 1) [] initial with
  | nil => rfl
  | cons events rest =>
      exfalso
      apply noOverrun
      exact ⟨nonterminalPrefixOfMember initial (bound + 1) events
        (by simp [hprefixes]) |>.witness,
        nonterminalPrefixOfMember initial (bound + 1) events
          (by simp [hprefixes]) |>.valid⟩

/-- No exact prefix at `bound + 1` bounds every finite observation trace. -/
theorem finite_trace_length_le_of_prefixes_eq_nil {bound : Nat}
    {initial : Config} {observation : ExecutionObservation}
    (empty : prefixes (bound + 1) [] initial = [])
    (run : FiniteExecution initial observation) :
    observation.trace.length ≤ bound := by
  by_cases bounded : observation.trace.length ≤ bound
  · exact bounded
  · exfalso
    have over : bound + 1 ≤ observation.trace.length := by omega
    have runCopy := run
    unfold FiniteExecution at runCopy
    cases runCopy with
    | @mk trace rawFinal _ rawReduction observes =>
        have htrace : observation.trace = trace := by
          cases observes <;> rfl
        have overTrace : bound + 1 ≤ trace.length := by
          simpa [htrace] using over
        let final : Config :=
          ⟨rawFinal, rawReduction.preserveWellTyped initial.2⟩
        obtain ⟨events, member⟩ :=
          prefixes_nonempty_of_reduces (bound + 1) [] trace initial final
            rawReduction overTrace
        rw [empty] at member
        simp at member

/-- The first `length` events of an infinite public execution. -/
def streamPrefix (events : Nat → Event) : Nat → List Event
  | 0 => []
  | length + 1 => streamPrefix events length ++ [events length]

@[simp] theorem streamPrefix_length (events : Nat → Event) :
    ∀ length, (streamPrefix events length).length = length
  | 0 => rfl
  | length + 1 => by simp [streamPrefix, streamPrefix_length events length]

/-- Every finite prefix of a divergent public execution is a relational
reduction. -/
theorem streamPrefix_reduces {initial : Config} {events : Nat → Event}
    {configs : Nat → Config} (starts : configs 0 = initial)
    (step : ∀ index,
      Step (configs index) (events index) (configs (index + 1))) :
    ∀ length, Reduces initial (streamPrefix events length) (configs length)
  | 0 => by
      rw [starts]
      exact Reduces.refl initial
  | length + 1 => by
      change Core.Harness.StepsA initial.1
        (streamPrefix events (length + 1)) (configs (length + 1)).1
      rw [streamPrefix]
      exact Core.Harness.StepsA.snoc
        (streamPrefix_reduces starts step length) (step length)

/-- Semantic no-overrun excludes the divergent constructor of a maximal
execution. -/
theorem false_of_diverges_noOverrun {bound : Nat} {initial : Config}
    {events : Nat → Event} {configs : Nat → Config}
    (starts : configs 0 = initial)
    (step : ∀ index,
      Step (configs index) (events index) (configs (index + 1)))
    (noOverrun : ¬ ∃ branchPrefix : RelationalPrefix initial (bound + 1),
      branchPrefix.Valid) : False := by
  apply noOverrun
  exact ⟨
    { events := streamPrefix events (bound + 1)
      final := configs (bound + 1)
      lengthEq := streamPrefix_length events (bound + 1) },
    streamPrefix_reduces starts step (bound + 1)⟩

/-! ## Completed canonical frontiers -/

/-- Build the proof-carrying canonical frontier from an already sorted
nonempty list. -/
def frontierOfSortedCons {profile : Profile} {initial : Config}
    (head : CostedExecutionObservation profile initial)
    (rest : List (CostedExecutionObservation profile initial))
    (sorted : CanonicalSorted
      ((head :: rest).map (costedObservationSchema profile initial).encode)) :
    NonemptyCanonicalFrontier (CostedExecutionObservation profile initial) :=
  { schema := costedObservationSchema profile initial
    head := head
    rest := rest
    ordered := sorted }

@[simp] theorem frontierOfSortedCons_elements {profile : Profile}
    {initial : Config} (head : CostedExecutionObservation profile initial)
    (rest : List (CostedExecutionObservation profile initial))
    (sorted : CanonicalSorted
      ((head :: rest).map (costedObservationSchema profile initial).encode)) :
    (frontierOfSortedCons head rest sorted).elements = head :: rest := rfl

/-- Transport public finite-tree coverage through the canonical permutation,
and strengthen completion to unrestricted maximal coverage using the proved
absence of a `bound + 1` prefix. -/
theorem costedCoverage_of_perm {profile : Profile} {bound : Nat}
    {initial : Config}
    (frontier : NonemptyCanonicalFrontier
      (CostedExecutionObservation profile initial))
    (permutation :
      (frontier.elements.map (·.observation)).Perm
        (exploreTree bound [] initial))
    (empty : prefixes (bound + 1) [] initial = []) :
    CostedCoverage profile bound initial frontier := by
  have noOverrun := noOverrun_of_prefixes_eq_nil empty
  refine
    { elementsSound := ?_
      finiteWithinBound := ?_
      maximal := ?_
      noOverrun := noOverrun }
  · intro costed member
    exact costed.execution
  · intro observation run traceBound
    have plainMember : observation ∈ exploreTree bound [] initial :=
      (covers_exploreTree bound initial).2 observation run traceBound
    have mappedMember : observation ∈
        frontier.elements.map (·.observation) :=
      permutation.mem_iff.mpr plainMember
    obtain ⟨costed, member, equality⟩ := List.mem_map.mp mappedMember
    exact ⟨costed, member, equality⟩
  · intro execution
    cases execution with
    | finite observation run maximal =>
        have traceBound := finite_trace_length_le_of_prefixes_eq_nil empty run
        have plainMember : observation ∈ exploreTree bound [] initial :=
          (covers_exploreTree bound initial).2 observation run traceBound
        have mappedMember : observation ∈
            frontier.elements.map (·.observation) :=
          permutation.mem_iff.mpr plainMember
        obtain ⟨costed, member, equality⟩ := List.mem_map.mp mappedMember
        exact ⟨costed, member, equality.symm⟩
    | diverges events configs starts steps =>
        exact False.elim (false_of_diverges_noOverrun starts steps noOverrun)

/-- Canonical report used only when a completed plain tree contains no
terminal observation and therefore cannot populate the mandated nonempty
frontier. -/
def emptyCostedTreeReport : FailureReport where
  site :=
    { schemaVersion := 1
      domain := .generic
      typeTag := TypeTag.leaf [67, 111, 115, 116, 101, 100, 84, 114, 101, 101]
      canonicalBodyBytes := ByteArray.empty }
  code := 1
  context := []

/-- Canonically sorted exact costed observations of the public plain tree. -/
def exploredCostedObservations (profile : Profile) (bound : Nat)
    (initial : Config) :
    List (CostedExecutionObservation profile initial) :=
  costedObservations profile initial (exploreTree bound [] initial)
    (covers_exploreTree bound initial).1

theorem exploredCostedObservations_sorted (profile : Profile) (bound : Nat)
    (initial : Config) :
    CanonicalSorted
      ((exploredCostedObservations profile bound initial).map
        (costedObservationSchema profile initial).encode) :=
  costedObservations_sorted profile initial _ _

theorem exploredCostedObservations_perm (profile : Profile) (bound : Nat)
    (initial : Config) :
    ((exploredCostedObservations profile bound initial).map
      (·.observation)).Perm (exploreTree bound [] initial) :=
  costedObservations_map_observation_perm profile initial _ _

theorem exploredCostedObservations_ne_nil_of_tree_ne_nil
    (profile : Profile) (bound : Nat) (initial : Config)
    (nonempty : exploreTree bound [] initial ≠ []) :
    exploredCostedObservations profile bound initial ≠ [] :=
  costedObservations_ne_nil profile initial _ _ nonempty

/-- Build the completed costed frontier once exact-prefix absence is known.
The empty-tree branch remains an explicit located failure because the result
algebra deliberately requires a nonempty frontier. -/
def completedCostedResult (profile : Profile) (bound : Nat) (initial : Config)
    (empty : prefixes (bound + 1) [] initial = []) :
    CostedTreeResult profile bound initial :=
  match hcosted : exploredCostedObservations profile bound initial with
  | [] => .initializationFailure emptyCostedTreeReport
  | head :: rest =>
      let frontier := frontierOfSortedCons head rest (by
        simpa [hcosted] using
          exploredCostedObservations_sorted profile bound initial)
      .complete frontier (costedCoverage_of_perm frontier (by
        simpa [frontier, hcosted] using
          exploredCostedObservations_perm profile bound initial) empty)

/-- A nonempty plain terminal tree forces the completed costed constructor. -/
theorem completedCostedResult_complete_of_tree_ne_nil
    {profile : Profile} {bound : Nat} {initial : Config}
    (empty : prefixes (bound + 1) [] initial = [])
    (nonempty : exploreTree bound [] initial ≠ []) :
    ∃ frontier coverage,
      completedCostedResult profile bound initial empty =
        CostedTreeResult.complete frontier coverage := by
  have costedNonempty :=
    exploredCostedObservations_ne_nil_of_tree_ne_nil profile bound initial
      nonempty
  unfold completedCostedResult
  split
  · rename_i hcosted
    exact False.elim (costedNonempty hcosted)
  · rename_i head rest hcosted
    let sorted : CanonicalSorted
        ((head :: rest).map
          (costedObservationSchema profile initial).encode) := by
      simpa [hcosted] using
        exploredCostedObservations_sorted profile bound initial
    let frontier := frontierOfSortedCons head rest sorted
    let permutation :
        (frontier.elements.map (·.observation)).Perm
          (exploreTree bound [] initial) := by
      simpa [frontier, hcosted] using
        exploredCostedObservations_perm profile bound initial
    let coverage : CostedCoverage profile bound initial frontier :=
      costedCoverage_of_perm frontier permutation empty
    exact ⟨frontier, coverage, rfl⟩

/-- The sole canonical public costed explorer.  It reports a real relational
prefix when the bound is exceeded, otherwise it builds the sorted exact costed
frontier (or the explicit empty-tree failure). -/
def exploreAllCosted (profile : Profile) (bound : Nat) (initial : Config) :
    CostedTreeResult profile bound initial :=
  match hprefixes : prefixes (bound + 1) [] initial with
  | events :: rest =>
      .nonterminalPrefix
        (nonterminalPrefixOfMember initial (bound + 1) events (by
          simp [hprefixes]))
  | [] => completedCostedResult profile bound initial hprefixes

/-- Exact-prefix absence selects the completed-tree path of the canonical
explorer. -/
theorem exploreAllCosted_eq_completed {profile : Profile} {bound : Nat}
    {initial : Config} (empty : prefixes (bound + 1) [] initial = []) :
    exploreAllCosted profile bound initial =
      completedCostedResult profile bound initial empty := by
  unfold exploreAllCosted
  split
  · rename_i events rest hprefixes
    rw [empty] at hprefixes
    contradiction
  · rfl

/-- The canonical explorer completes whenever at least one finite observation
exists and no relational branch reaches `bound + 1`.  Completion itself carries
soundness, bounded completeness, every-maximal-execution coverage, and the
no-overrun certificate in `CostedCoverage`. -/
theorem exploreAllCosted_complete_of_finite_noOverrun
    {profile : Profile} {bound : Nat} {initial : Config}
    (finite : ∃ observation : ExecutionObservation,
      FiniteExecution initial observation)
    (noOverrun : ¬ ∃ branchPrefix : RelationalPrefix initial (bound + 1),
      branchPrefix.Valid) :
    ∃ frontier coverage,
      exploreAllCosted profile bound initial =
        CostedTreeResult.complete frontier coverage := by
  have empty : prefixes (bound + 1) [] initial = [] :=
    prefixes_eq_nil_of_noOverrun noOverrun
  obtain ⟨observation, run⟩ := finite
  have traceBound := finite_trace_length_le_of_prefixes_eq_nil empty run
  have member : observation ∈ exploreTree bound [] initial :=
    (covers_exploreTree bound initial).2 observation run traceBound
  have treeNonempty : exploreTree bound [] initial ≠ [] := by
    intro treeEmpty
    rw [treeEmpty] at member
    simp at member
  obtain ⟨frontier, coverage, completed⟩ :=
    completedCostedResult_complete_of_tree_ne_nil empty treeNonempty
  exact ⟨frontier, coverage,
    (exploreAllCosted_eq_completed empty).trans completed⟩

/-- Every element of a returned completed frontier is an exact relational
finite execution. -/
theorem exploreAllCosted_sound {profile : Profile} {bound : Nat}
    {initial : Config}
    {frontier : NonemptyCanonicalFrontier
      (CostedExecutionObservation profile initial)}
    {coverage : CostedCoverage profile bound initial frontier}
    (completed : exploreAllCosted profile bound initial =
      CostedTreeResult.complete frontier coverage)
    {costed : CostedExecutionObservation profile initial}
    (member : costed ∈ frontier.elements) :
    FiniteExecution initial costed.observation :=
  coverage.elementsSound costed member

end WasmGemmGnaf.Wasm
