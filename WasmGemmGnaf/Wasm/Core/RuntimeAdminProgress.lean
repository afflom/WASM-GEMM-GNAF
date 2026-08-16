import WasmGemmGnaf.Wasm.Core.RuntimeSequenceTyping

set_option autoImplicit false

/-!
# Administrative-context progress combinators

These lemmas isolate the structural part of Core progress.  They do not add a
runtime typing invariant and do not assume global determinism: a caller still
has to prove progress for the first non-value source instruction.  Once that
leaf step is available, the lemmas below lift it through the remaining source
instruction suffix and through the released label/frame evaluation contexts.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- If the canonical value split has no residual instructions, the original
administrative sequence consists exactly of those values. -/
theorem eq_vals_of_splitVals_tail_nil {body : List AdminInstr}
    (tailEmpty : (splitVals body).2 = []) :
    body = vals (splitVals body).1 := by
  have reassemble := splitVals_append body
  rw [tailEmpty] at reassemble
  simpa using reassemble.symm

/-- An indexed `ref.null` is syntactically value-shaped but still performs
the authority's type-index closure step.  This helper exposes that step at an
arbitrary maximal value prefix/suffix, including the singleton case where an
instruction context would not be admissible. -/
theorem refNullIdx_step_of_decomposition
    (state : State) (body : List AdminInstr) (prefixValues : List Val)
    (suffix : List AdminInstr) (index : TypeIdx) (definedType : DefType)
    (hlookup : state.typeOf index = some definedType)
    (hbody : body = vals prefixValues ++
      [.plain (.refNull (.use (.idx index)))] ++ suffix) :
    ∃ event target, StepA (state, body) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  let innerEvent : Event :=
    .read .refNullIdx [.refNull (.use (.idx index))]
  have inner : StepA
      (state, [.plain (.refNull (.use (.idx index)))]) innerEvent
      (state, [Ref.toAdmin (.null (.use (.defd definedType)))]) := by
    exact .read (.refNullIdx hlookup)
  by_cases hprefix : prefixValues = []
  · subst prefixValues
    by_cases hsuffix : suffix = []
    · subst suffix
      exact ⟨innerEvent, _, by simpa [hbody] using inner⟩
    · let event : Event := .ctxtInstrs 0 suffix.length innerEvent
      refine ⟨event,
        (state, [Ref.toAdmin (.null (.use (.defd definedType)))] ++ suffix), ?_⟩
      rw [hbody]
      simpa [event, List.append_assoc] using
        (StepA.ctxtInstrs (vs := []) (is₁ := suffix) inner (Or.inr hsuffix))
  · let event : Event :=
      .ctxtInstrs prefixValues.length suffix.length innerEvent
    refine ⟨event,
      (state, vals prefixValues ++
        [Ref.toAdmin (.null (.use (.defd definedType)))] ++ suffix), ?_⟩
    rw [hbody]
    simpa [event, List.append_assoc] using
      (StepA.ctxtInstrs (vs := prefixValues) (is₁ := suffix) inner
        (Or.inl hprefix))

/-- Lift progress of the first non-value plain instruction across the source
instruction suffix following it.  The maximal value prefix remains inside the
redex, so this lemma does not assume that an instruction is nullary. -/
theorem step_of_splitVals_plain_head
    {state : State} {body : List AdminInstr} {head : Instr}
    {suffix : List AdminInstr}
    (tailHead : (splitVals body).2 = .plain head :: suffix)
    (headStep : ∃ event target,
      StepA (state, vals (splitVals body).1 ++ [.plain head]) event target) :
    ∃ event target, StepA (state, body) event target := by
  obtain ⟨event, target, step⟩ := headStep
  rcases target with ⟨nextState, nextBody⟩
  have reassemble := splitVals_append body
  rw [tailHead] at reassemble
  cases suffix with
  | nil =>
      refine ⟨event, (nextState, nextBody), ?_⟩
      rw [← reassemble]
      simpa using step
  | cons first rest =>
      have lifted : StepA
          (state,
            vals ([] : List Val) ++
              (vals (splitVals body).1 ++ [.plain head]) ++ first :: rest)
          (.ctxtInstrs 0 (first :: rest).length event)
          (nextState,
            vals ([] : List Val) ++ nextBody ++ first :: rest) :=
        StepA.ctxtInstrs step (Or.inr (by simp))
      refine ⟨.ctxtInstrs 0 (first :: rest).length event,
        (nextState, nextBody ++ first :: rest), ?_⟩
      rw [← reassemble]
      simpa [List.append_assoc] using lifted

/-- Generic administrative-body decomposition.  A caller supplies only the
two facts specific to its runtime invariant: every nonempty residual begins
with a source instruction, and that instruction has a redex at the canonical
value prefix. -/
theorem values_or_step_of_splitVals
    {state : State} {body : List AdminInstr}
    (residualPlain : ∀ {first : AdminInstr} {suffix : List AdminInstr},
      (splitVals body).2 = first :: suffix →
        ∃ head : Instr, first = .plain head)
    (headProgress : ∀ {head : Instr} {suffix : List AdminInstr},
      (splitVals body).2 = .plain head :: suffix →
        ∃ event target,
          StepA (state, vals (splitVals body).1 ++ [.plain head])
            event target) :
    (∃ values, body = vals values) ∨
      ∃ event target, StepA (state, body) event target := by
  cases tailEq : (splitVals body).2 with
  | nil =>
      exact Or.inl ⟨(splitVals body).1,
        eq_vals_of_splitVals_tail_nil tailEq⟩
  | cons first suffix =>
      obtain ⟨head, rfl⟩ := residualPlain tailEq
      exact Or.inr (step_of_splitVals_plain_head tailEq
        (headProgress tailEq))

/-- A body which is already values, or which can step internally, makes its
enclosing label step.  The value case is the released `label-vals` rule. -/
theorem label_step_of_values_or_step
    {state : State} {arity : Nat} {continuation body : List AdminInstr}
    (bodyProgress :
      (∃ values, body = vals values) ∨
        ∃ event target, StepA (state, body) event target) :
    ∃ event target,
      StepA (state, [.label arity continuation body]) event target := by
  rcases bodyProgress with ⟨values, rfl⟩ | ⟨event, target, step⟩
  · have pure : Step_pure releasedNumerics
        [.label arity continuation (vals values)] (vals values) :=
      .labelVals
    obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
    exact ⟨.pure pureEvent
        (sourcePlains [.label arity continuation (vals values)]),
      (state, vals values), .pure member⟩
  · rcases target with ⟨nextState, nextBody⟩
    exact ⟨.ctxtLabel arity event,
      (nextState, [.label arity continuation nextBody]), .ctxtLabel step⟩

/-- A frame whose body has exactly its result values exits by `frame-vals`; an
internally stepping body instead steps through the released frame context. -/
theorem frame_step_of_values_or_step
    {store : Store} {outerFrame innerFrame : Frame} {arity : Nat}
    {body : List AdminInstr}
    (bodyProgress :
      (∃ values, body = vals values ∧ values.length = arity) ∨
        ∃ event target,
          StepA (⟨store, innerFrame⟩, body) event target) :
    ∃ event target,
      StepA (⟨store, outerFrame⟩, [.frame arity innerFrame body])
        event target := by
  rcases bodyProgress with
    ⟨values, rfl, valueCount⟩ | ⟨event, target, step⟩
  · have pure : Step_pure releasedNumerics
        [.frame arity innerFrame (vals values)] (vals values) :=
      .frameVals valueCount
    obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
    exact ⟨.pure pureEvent
        (sourcePlains [.frame arity innerFrame (vals values)]),
      (⟨store, outerFrame⟩, vals values), .pure member⟩
  · rcases target with ⟨⟨nextStore, nextInnerFrame⟩, nextBody⟩
    exact ⟨.ctxtFrame arity event,
      (⟨nextStore, outerFrame⟩,
        [.frame arity nextInnerFrame nextBody]), .ctxtFrame step⟩

/-- The common function-body shape: first obtain either label exit or an
internal label step, then lift that exact step through the activation frame. -/
theorem frame_label_step_of_values_or_step
    {store : Store} {outerFrame innerFrame : Frame} {arity : Nat}
    {continuation body : List AdminInstr}
    (bodyProgress :
      (∃ values, body = vals values) ∨
        ∃ event target,
          StepA (⟨store, innerFrame⟩, body) event target) :
    ∃ event target,
      StepA (⟨store, outerFrame⟩,
        [.frame arity innerFrame [.label arity continuation body]])
        event target := by
  obtain ⟨event, target, step⟩ :=
    label_step_of_values_or_step bodyProgress
  rcases target with ⟨⟨nextStore, nextInnerFrame⟩, nextBody⟩
  exact ⟨.ctxtFrame arity event,
    (⟨nextStore, outerFrame⟩,
      [.frame arity nextInnerFrame nextBody]), .ctxtFrame step⟩

/-! ## Escaping heads

Branch and return instructions are deliberately not standalone redexes.  They
reduce only when their enclosing label or frame is visible.  The following
constructors expose those genuine authority steps without pretending that a
bare `br` or `return` can make progress.
-/

/-- A depth-zero branch exits the current label with exactly its result
values and the label continuation. -/
theorem label_br_zero_step (state : State) (arity : Nat)
    (continuation : List AdminInstr) (prefixValues results : List Val)
    (suffix : List AdminInstr) (label : LabelIdx)
    (hresults : results.length = arity)
    (hlabel : label.val = 0) :
    ∃ event target, StepA
      (state, [.label arity continuation
        (vals prefixValues ++ vals results ++ [.plain (.br label)] ++ suffix)])
      event target := by
  have pure : Step_pure releasedNumerics
      [.label arity continuation
        (vals prefixValues ++ vals results ++
          [.plain (.br label)] ++ suffix)]
      (vals results ++ continuation) :=
    .brLabelZero hresults hlabel
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A nonzero branch crosses one label and retains the decremented branch. -/
theorem label_br_succ_step (state : State) (arity : Nat)
    (continuation : List AdminInstr) (values : List Val)
    (suffix : List AdminInstr) (label outerLabel : LabelIdx)
    (hlabel : label.val = outerLabel.val + 1) :
    ∃ event target, StepA
      (state, [.label arity continuation
        (vals values ++ [.plain (.br label)] ++ suffix)]) event target := by
  have pure : Step_pure releasedNumerics
      [.label arity continuation
        (vals values ++ [.plain (.br label)] ++ suffix)]
      (vals values ++ [.plain (.br outerLabel)]) :=
    .brLabelSucc hlabel
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A return crosses the current label while retaining its value prefix. -/
theorem label_return_step (state : State) (arity : Nat)
    (continuation : List AdminInstr) (values : List Val)
    (suffix : List AdminInstr) :
    ∃ event target, StepA
      (state, [.label arity continuation
        (vals values ++ [.plain .ret] ++ suffix)]) event target := by
  have pure : Step_pure releasedNumerics
      [.label arity continuation
        (vals values ++ [.plain .ret] ++ suffix)]
      (vals values ++ [.plain .ret]) := .returnLabel
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A branch propagates unchanged through an exception handler until it
reaches the surrounding label that owns its depth. -/
theorem handler_br_step (state : State) (arity : Nat)
    (catches : List Catch) (values : List Val)
    (suffix : List AdminInstr) (label : LabelIdx) :
    ∃ event target, StepA
      (state, [.handler arity catches
        (vals values ++ [.plain (.br label)] ++ suffix)]) event target := by
  have pure : Step_pure releasedNumerics
      [.handler arity catches
        (vals values ++ [.plain (.br label)] ++ suffix)]
      (vals values ++ [.plain (.br label)]) := .brHandler
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A return propagates unchanged through an exception handler. -/
theorem handler_return_step (state : State) (arity : Nat)
    (catches : List Catch) (values : List Val)
    (suffix : List AdminInstr) :
    ∃ event target, StepA
      (state, [.handler arity catches
        (vals values ++ [.plain .ret] ++ suffix)]) event target := by
  have pure : Step_pure releasedNumerics
      [.handler arity catches
        (vals values ++ [.plain .ret] ++ suffix)]
      (vals values ++ [.plain .ret]) := .returnHandler
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A return exits its activation frame with exactly the frame result arity. -/
theorem frame_return_step (store : Store) (outerFrame innerFrame : Frame)
    (arity : Nat) (prefixValues results : List Val)
    (suffix : List AdminInstr) (hresults : results.length = arity) :
    ∃ event target, StepA
      (⟨store, outerFrame⟩,
        [.frame arity innerFrame
          (vals prefixValues ++ vals results ++ [.plain .ret] ++ suffix)])
      event target := by
  have pure : Step_pure releasedNumerics
      [.frame arity innerFrame
        (vals prefixValues ++ vals results ++ [.plain .ret] ++ suffix)]
      (vals results) := .returnFrame hresults
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩

/-- A handler whose body has become values exits like the corresponding
label, retaining the exact value list. -/
theorem handler_values_step (state : State) (arity : Nat)
    (catches : List Catch) (values : List Val) :
    ∃ event target,
      StepA (state, [.handler arity catches (vals values)]) event target := by
  have pure : Step_pure releasedNumerics
      [.handler arity catches (vals values)] (vals values) := .handlerVals
  obtain ⟨pureEvent, member⟩ := step_pure_mem_pureSuccessors pure
  exact ⟨.pure pureEvent (sourcePlains _), _, .pure member⟩


end WasmGemmGnaf.Wasm.Core.Exec
