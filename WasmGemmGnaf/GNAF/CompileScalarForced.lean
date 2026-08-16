import WasmGemmGnaf.GNAF.CompileScalarUnique
import WasmGemmGnaf.Wasm.Core.ForcedExecution

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.GNAF.DirectScalarRuntime

open WasmGemmGnaf

@[simp] theorem frame_admin_ne_value (arity : Nat)
    (frame : Wasm.Core.Exec.Frame)
    (body : List Wasm.Core.Exec.AdminInstr)
    (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.frame arity frame body ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  simp at mapped

@[simp] theorem label_admin_ne_value (arity : Nat)
    (continuation body : List Wasm.Core.Exec.AdminInstr)
    (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.label arity continuation body ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  simp at mapped

theorem singleton_nonvalue_ctxt_false
    (state : Wasm.Core.Exec.State)
    (admin : Wasm.Core.Exec.AdminInstr)
    (hnonvalue : Wasm.Core.Exec.adminToVal admin = none)
    (values : List Wasm.Core.Exec.Val)
    (inner post : List Wasm.Core.Exec.AdminInstr)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (step : Wasm.Core.Exec.StepA (state, inner) event next)
    (nonempty : values ≠ [] ∨ post ≠ [])
    (source : [admin] = Wasm.Core.Exec.vals values ++ inner ++ post) : False := by
  cases values with
  | nil =>
      simp only [Wasm.Core.Exec.vals, List.map_nil, List.nil_append] at source
      cases inner with
      | nil => exact (probe_nil_no_step state step).elim
      | cons first rest =>
          cases post with
          | nil => exact nonempty.elim (fun h => h rfl) (fun h => h rfl)
          | cons next post => simp at source
  | cons first rest =>
      change [admin] = first.toAdmin ::
        (Wasm.Core.Exec.vals rest ++ inner ++ post) at source
      have head := (List.cons.inj source).1
      have mapped := congrArg Wasm.Core.Exec.adminToVal head
      rw [hnonvalue, Wasm.Core.Exec.adminToVal_toAdmin] at mapped
      simp at mapped

theorem singleton_label_ne_vals_plain
    (arity : Nat) (continuation body : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr) :
    [Wasm.Core.Exec.AdminInstr.label arity continuation body] ≠
      Wasm.Core.Exec.vals values ++ [.plain instruction] := by
  intro equality
  cases values with
  | nil => simp at equality
  | cons first rest =>
      have head : Wasm.Core.Exec.AdminInstr.label arity continuation body =
          first.toAdmin := by
        simpa only [Wasm.Core.Exec.vals, List.map_cons, List.cons_append,
          List.cons.injEq] using (List.cons.inj equality).1
      exact label_admin_ne_value arity continuation body first head

theorem singleton_label_ne_vals_plain_post
    (arity : Nat) (continuation body : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr) :
    [Wasm.Core.Exec.AdminInstr.label arity continuation body] ≠
      Wasm.Core.Exec.vals values ++ .plain instruction :: post := by
  intro equality
  cases values with
  | nil => simp at equality
  | cons first rest =>
      have head : Wasm.Core.Exec.AdminInstr.label arity continuation body =
          first.toAdmin := by
        simpa only [Wasm.Core.Exec.vals, List.map_cons, List.cons_append,
          List.cons.injEq] using (List.cons.inj equality).1
      exact label_admin_ne_value arity continuation body first head

theorem singleton_label_ne_vals_addrref_plain
    (arity : Nat) (continuation body : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr) :
    [Wasm.Core.Exec.AdminInstr.label arity continuation body] ≠
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post := by
  intro equality
  cases values with
  | nil => simp at equality
  | cons first rest =>
      have head : Wasm.Core.Exec.AdminInstr.label arity continuation body =
          first.toAdmin := by
        simpa only [Wasm.Core.Exec.vals, List.map_cons, List.cons_append,
          List.cons.injEq] using (List.cons.inj equality).1
      exact label_admin_ne_value arity continuation body first head

theorem singleton_frame_ne_vals_plain
    (arity : Nat) (frame : Wasm.Core.Exec.Frame)
    (body : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr) :
    [Wasm.Core.Exec.AdminInstr.frame arity frame body] ≠
      Wasm.Core.Exec.vals values ++ [.plain instruction] := by
  intro equality
  cases values with
  | nil => simp at equality
  | cons first rest =>
      have head : Wasm.Core.Exec.AdminInstr.frame arity frame body =
          first.toAdmin := by
        simpa only [Wasm.Core.Exec.vals, List.map_cons, List.cons_append,
          List.cons.injEq] using (List.cons.inj equality).1
      exact frame_admin_ne_value arity frame body first head

theorem singleton_frame_ne_vals_addrref_plain
    (arity : Nat) (frame : Wasm.Core.Exec.Frame)
    (body : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr) :
    [Wasm.Core.Exec.AdminInstr.frame arity frame body] ≠
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post := by
  intro equality
  cases values with
  | nil => simp at equality
  | cons first rest =>
      have head : Wasm.Core.Exec.AdminInstr.frame arity frame body =
          first.toAdmin := by
        simpa only [Wasm.Core.Exec.vals, List.map_cons, List.cons_append,
          List.cons.injEq] using (List.cons.inj equality).1
      exact frame_admin_ne_value arity frame body first head

theorem status_ne_vals_plain_post (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localSet index) :
    (statusValue value).toAdmin :: .plain (localSet index) :: tail ≠
      Wasm.Core.Exec.vals values ++ .plain instruction :: post := by
  intro equality
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain (localSet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain (localSet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue post]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem statusPair_label_step_unique
    (state : Wasm.Core.Exec.State) (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [Wasm.Core.Exec.AdminInstr.label 1 []
        ((statusValue value).toAdmin ::
          .plain (localSet index) :: tail)]) event next) :
    next = (writeLocal state index (statusValue value),
      [Wasm.Core.Exec.AdminInstr.label 1 [] tail]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, [Wasm.Core.Exec.AdminInstr.label 1 []
      ((statusValue value).toAdmin ::
        .plain (localSet index) :: tail)]) = source at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_label] at membership
    simp [Wasm.Core.Exec.pureOfLabel, Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.adminToVal, Wasm.Core.Exec.Val.toAdmin,
      Wasm.Core.Exec.Ref.toAdmin, statusValue, localSet]
      at membership
  case read readStep =>
    cases readStep <;> simp_all [statusValue,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin]
    case block =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case loop =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case callRefFunc =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case returnCallRefLabel =>
      exact (status_ne_vals_plain_post index value tail _ _ _ rfl
        (by intro equality; cases equality) hsource.2.2.2).elim
    case throwRefInstrs =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (Wasm.Core.Exec.AdminInstr.label 1 []
        ((statusValue value).toAdmin ::
          .plain (localSet index) :: tail)) rfl values inner post bodyStep
      nonempty (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtLabel bodyStep =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    have target := statusPair_step_unique _ index value tail
      hindex hexact bodyStep
    simp_all [Wasm.Core.Harness.coreTrapCause?]

theorem statusPair_frame_label_step_unique
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      ({ store := state.store, frame := outerFrame },
        [Wasm.Core.Exec.AdminInstr.frame 1 state.frame
          [Wasm.Core.Exec.AdminInstr.label 1 []
          ((statusValue value).toAdmin ::
            .plain (localSet index) :: tail)]]) event next) :
    next =
      ({ store := state.store, frame := outerFrame },
        [Wasm.Core.Exec.AdminInstr.frame 1
          (writeLocal state index (statusValue value)).frame
          [Wasm.Core.Exec.AdminInstr.label 1 [] tail]]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (({ store := state.store, frame := outerFrame } : Wasm.Core.Exec.State),
      [Wasm.Core.Exec.AdminInstr.frame 1 state.frame
        [Wasm.Core.Exec.AdminInstr.label 1 []
        ((statusValue value).toAdmin ::
          .plain (localSet index) :: tail)]]) = source at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_frame] at membership
    simp [Wasm.Core.Exec.pureOfFrame, Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.adminToVal] at membership
  case read readStep =>
    cases readStep <;> simp_all
    case block =>
      exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
        hsource.2).elim
    case loop =>
      exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
        hsource.2).elim
    case callRefFunc =>
      exact (singleton_frame_ne_vals_addrref_plain 1 state.frame _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case throwRefInstrs =>
      exact (singleton_frame_ne_vals_addrref_plain 1 state.frame _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
        hsource.2).elim
    case returnCallRefFrameNull =>
      exact (singleton_label_ne_vals_plain_post 1 [] _
        (_ ++ [.ref (.null _)]) _ _
        (by simpa [Wasm.Core.Exec.vals, List.map_append,
          List.append_assoc, Wasm.Core.Exec.Val.toAdmin,
          Wasm.Core.Exec.Ref.toAdmin] using hsource.2.2.2)).elim
    case returnCallRefFrameAddr =>
      exact (singleton_label_ne_vals_plain_post 1 [] _
        (_ ++ _ ++ [.ref (.addr (.funcAddr _))]) _ _
        (by simpa [Wasm.Core.Exec.vals, List.map_append,
          List.append_assoc, Wasm.Core.Exec.Val.toAdmin,
          Wasm.Core.Exec.Ref.toAdmin] using hsource.2.2.2)).elim
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (Wasm.Core.Exec.AdminInstr.frame 1 state.frame
        [Wasm.Core.Exec.AdminInstr.label 1 []
          ((statusValue value).toAdmin ::
            .plain (localSet index) :: tail)]) rfl values inner post bodyStep
      nonempty (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
      hsource.2).elim
  case structNew =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
      hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _
      hsource.2).elim
  case ctxtFrame bodyStep =>
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := hsource
    have target := statusPair_label_step_unique _ index value tail
      hindex hexact bodyStep
    have stateTarget := congrArg Prod.fst target.1
    have storeTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.store) stateTarget
    have frameTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.frame) stateTarget
    simp_all

theorem statusPair_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (Wasm.Core.Harness.Config.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            ((statusValue value).toAdmin ::
              .plain (localSet index) :: tail)]])) event next) :
    next = Wasm.Core.Harness.Config.afterEntry harness entry
      (⟨state.store, outerFrame⟩,
        [.frame 1 (writeLocal state index (statusValue value)).frame
          [.label 1 [] tail]]) := by
  apply Wasm.Core.Harness.afterEntry_target_unique_of_core
    (targetNotTrap := by simp)
    (sourceNotReturn := by
      intro sourceState sourceValue equality
      have instructions := congrArg Prod.snd equality
      exact frame_admin_ne_value 1 state.frame _ sourceValue
        (List.cons.inj instructions).1)
    (sourceNotThrow := by intro sourceState address equality; simp at equality)
    (allCore := fun coreStep =>
      statusPair_frame_label_step_unique outerFrame state index value tail
        hindex hexact coreStep)
    other

/-- Prepending the emitted status assignments to a target-forced suffix
preserves target-forcing.  Each assignment is the concrete `i64.const ;
local.set` pair emitted by `statusCode`; the proof uses the exact local-store
transition rather than a determinism assumption about all of Core. -/
theorem statusAssignments_afterEntry_forcedTargets
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index : Nat)
    (assignments : List Nat) (suffix : List Wasm.Core.Instr)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    (hsuffix : suffix ≠ [])
    {final : Wasm.Core.Harness.Config}
    (tailForced : Wasm.Core.Harness.ForcedTargets
      (.afterEntry harness entry
        (⟨(applyStatusWrites state index assignments).store, outerFrame⟩,
          [.frame 1 (applyStatusWrites state index assignments).frame
            [.label 1 [] (Wasm.Core.Exec.plains suffix)]])) final) :
    Wasm.Core.Harness.ForcedTargets
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            (Wasm.Core.Exec.plains
              (assignments.flatMap (fun value =>
                [constL value, localSet index]) ++ suffix))]])) final := by
  induction assignments generalizing state with
  | nil => simpa using tailForced
  | cons value rest ih =>
      let remaining : List Wasm.Core.Instr :=
        rest.flatMap (fun next => [constL next, localSet index]) ++ suffix
      have hremaining : remaining ≠ [] := by
        intro equality
        have dropped := congrArg
          (List.drop
            (rest.flatMap (fun next => [constL next, localSet index])).length)
          equality
        exact hsuffix (by simpa [remaining] using dropped)
      obtain ⟨event, coreStep, eventSafe⟩ :=
        statusAssignment_step state index value remaining hindex hexact
          hremaining
      have framedStep : Wasm.Core.Exec.StepA
          (⟨state.store, outerFrame⟩,
            [.frame 1 state.frame [.label 1 []
              (Wasm.Core.Exec.plains
                ([constL value, localSet index] ++ remaining))]])
          (.ctxtFrame 1 (.ctxtLabel 1 event))
          (⟨(writeLocal state index (statusValue value)).store, outerFrame⟩,
            [.frame 1 (writeLocal state index (statusValue value)).frame
              [.label 1 [] (Wasm.Core.Exec.plains remaining)]]) := by
        exact .ctxtFrame (.ctxtLabel coreStep)
      have harnessStep : Wasm.Core.Harness.StepA
          (.afterEntry harness entry
            (⟨state.store, outerFrame⟩,
              [.frame 1 state.frame [.label 1 []
                (Wasm.Core.Exec.plains
                  ([constL value, localSet index] ++ remaining))]]))
          (.coreAfterEntry (.ctxtFrame 1 (.ctxtLabel 1 event)))
          (.afterEntry harness entry
            (⟨(writeLocal state index (statusValue value)).store, outerFrame⟩,
              [.frame 1 (writeLocal state index (statusValue value)).frame
                [.label 1 [] (Wasm.Core.Exec.plains remaining)]])) := by
        apply Wasm.Core.Harness.StepA.coreAfter framedStep
        · simpa [Wasm.Core.Harness.coreTrapCause?] using eventSafe
        · intro equality
          simp at equality
      have restForced : Wasm.Core.Harness.ForcedTargets
          (.afterEntry harness entry
            (⟨(writeLocal state index (statusValue value)).store, outerFrame⟩,
              [.frame 1 (writeLocal state index (statusValue value)).frame
                [.label 1 [] (Wasm.Core.Exec.plains remaining)]])) final := by
        apply ih (state := writeLocal state index (statusValue value))
            (by simpa using hindex)
        simpa [applyStatusWrites] using tailForced
      apply Wasm.Core.Harness.ForcedTargets.cons
        (step := by
          simpa [remaining, List.flatMap_cons, List.append_assoc] using
            harnessStep)
        (targetUnique := ?_) restForced
      intro otherEvent otherNext otherStep
      apply statusPair_afterEntry_target_unique harness entry outerFrame state
        index value (Wasm.Core.Exec.plains remaining) hindex hexact
      simpa [remaining, List.flatMap_cons, List.append_assoc] using otherStep

end WasmGemmGnaf.GNAF.DirectScalarRuntime
