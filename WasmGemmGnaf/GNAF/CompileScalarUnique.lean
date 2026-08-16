import WasmGemmGnaf.GNAF.CompileScalarRuntime

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.GNAF.DirectScalarRuntime

open WasmGemmGnaf

@[simp] theorem probe_instrLocalSet_admin_ne_value
    (index : Wasm.Core.LocalIdx) (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain (.localSet index) ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  change none = some value at mapped
  simp at mapped

@[simp] theorem probe_instrLocalSet_ne_constAddr
    (index : Wasm.Core.LocalIdx) (addressType : Wasm.Core.AddrType)
    (literal : Wasm.Core.Exec.AddrLit addressType) :
    Wasm.Core.Exec.AdminInstr.plain (.localSet index) ≠
      Wasm.Core.Exec.constAddr addressType literal := by
  cases addressType with
  | i32 => exact probe_instrLocalSet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact probe_instrLocalSet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem probe_instrLocalSet_ne_constInn
    (index : Wasm.Core.LocalIdx) (inn : Wasm.Core.Inn)
    (literal : Wasm.Core.Exec.InnLit inn) :
    Wasm.Core.Exec.AdminInstr.plain (.localSet index) ≠
      Wasm.Core.Exec.constInn inn literal := by
  cases inn with
  | i32 => exact probe_instrLocalSet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact probe_instrLocalSet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem probe_instrLocalSet_ne_constI32
    (index : Wasm.Core.LocalIdx) (literal : Wasm.Core.U32) :
    Wasm.Core.Exec.AdminInstr.plain (.localSet index) ≠
      Wasm.Core.Exec.constI32 literal :=
  probe_instrLocalSet_admin_ne_value index (.num ⟨.i32, literal⟩)

@[simp] theorem probe_instrLocalSet_ne_refAdmin
    (index : Wasm.Core.LocalIdx) (reference : Wasm.Core.Exec.Ref) :
    Wasm.Core.Exec.AdminInstr.plain (.localSet index) ≠ reference.toAdmin := by
  cases reference with
  | null heapType =>
      exact probe_instrLocalSet_admin_ne_value index (.ref (.null heapType))
  | addr address =>
      exact probe_instrLocalSet_admin_ne_value index (.ref (.addr address))

theorem probe_status_ne_vals_plain (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localSet index) :
    (statusValue value).toAdmin :: .plain (localSet index) :: tail ≠
      Wasm.Core.Exec.vals values ++ [.plain instruction] := by
  intro equality
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain (localSet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain (localSet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  change (.plain (localSet index) :: tail) = [.plain instruction] at tails
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem probe_status_ne_vals_addrref_plain (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localSet index) :
    (statusValue value).toAdmin :: .plain (localSet index) :: tail ≠
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post := by
  intro equality
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain (localSet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain (localSet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have tails := congrArg Prod.snd splitEquality
  change (.plain (localSet index) :: tail) = .plain instruction :: post at tails
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem probe_status_vals_addrref_plain_false (index value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality :
      (statusValue value).toAdmin :: .plain (localSet index) :: tail =
        Wasm.Core.Exec.vals values ++
          [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localSet index) : False :=
  (probe_status_ne_vals_addrref_plain index value tail values reference
    instruction post hnonvalue hdifferent) equality

theorem probe_nil_no_step (state : Wasm.Core.Exec.State)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA (state, []) event next := by
  intro step
  generalize hsource : (state, []) = source at step
  induction step
  case pure is is' pe membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    simp [Wasm.Core.Exec.pureSuccessors, Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.pureOfSplit] at membership
  case read readStep =>
    induction readStep <;> simp_all
  all_goals simp_all

theorem probe_localSet_vals_plain_false (index : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localSet index) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain (localSet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain (localSet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem probe_localSet_vals_addrref_plain_false (index : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain (localSet index) :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain (localSet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain (localSet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  simpa using valuesEquality

theorem probe_single_status_vals_plain_false (value : Nat)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : [(statusValue value).toAdmin] =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show [(statusValue value).toAdmin] =
      Wasm.Core.Exec.vals [statusValue value] by rfl,
    Wasm.Core.Exec.splitVals_vals,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  simp at tails

theorem probe_single_status_vals_addrref_plain_false (value : Nat)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : [(statusValue value).toAdmin] =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show [(statusValue value).toAdmin] =
      Wasm.Core.Exec.vals [statusValue value] by rfl,
    Wasm.Core.Exec.splitVals_vals,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have tails := congrArg Prod.snd splitEquality
  simp at tails

theorem probe_single_status_no_step (state : Wasm.Core.Exec.State)
    (value : Nat) {event : Wasm.Core.Exec.Event}
    {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state, [(statusValue value).toAdmin]) event next := by
  intro step
  generalize hsource :
    (state, [(statusValue value).toAdmin]) = source at step
  induction step
  case ctxtInstrs z z' values inner inner' post ev hinner hnonempty ih =>
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change [(statusValue value).toAdmin] = inner ++ post at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z hinner
        | cons instruction rest =>
            cases rest with
            | nil =>
                have hpost : post = [] := by
                  simpa only [List.singleton_append, List.cons.injEq] using
                    (List.cons.inj hinstructions).2.symm
                exact hnonempty.elim (fun h => h rfl) (fun h => h hpost)
            | cons nextInstruction rest =>
                simp at hinstructions
    | cons firstValue restValues =>
        cases restValues with
        | nil =>
            have hrest : inner ++ post = [] := by
              simpa only [Wasm.Core.Exec.vals, List.cons_append,
                List.cons.injEq] using (List.cons.inj hinstructions).2.symm
            have hempty : inner = [] := (List.append_eq_nil_iff.mp hrest).1
            subst inner
            exact probe_nil_no_step z hinner
        | cons secondValue restValues =>
            simp [Wasm.Core.Exec.vals] at hinstructions
  case pure is is' pe membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals [(statusValue value).toAdmin] =
        ([statusValue value], []) := by
      simpa [Wasm.Core.Exec.vals] using
        Wasm.Core.Exec.splitVals_vals [statusValue value]
    rw [hsplit] at membership
    simp [Wasm.Core.Exec.pureOfSplit] at membership
  case read readStep =>
    induction readStep <;>
      simp_all [statusValue, Wasm.Core.Exec.Val.toAdmin,
        Wasm.Core.Exec.Ref.toAdmin,
        Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case block =>
      exact probe_single_status_vals_plain_false value _ _ hsource.2 rfl
    case loop =>
      exact probe_single_status_vals_plain_false value _ _ hsource.2 rfl
    case callRefFunc =>
      exact probe_single_status_vals_addrref_plain_false value _ _ _ _
        (by simpa [statusValue, List.append_assoc] using hsource.2) rfl
    case throwRefInstrs =>
      exact probe_single_status_vals_addrref_plain_false value _ _ _ _
        (by simpa [statusValue, List.append_assoc] using hsource.2) rfl
    case tryTable =>
      exact probe_single_status_vals_plain_false value _ _ hsource.2 rfl
  case throw =>
    exact probe_single_status_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  case structNew =>
    exact probe_single_status_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  case arrayNewFixed =>
    exact probe_single_status_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  all_goals
    simp_all [statusValue, Wasm.Core.Exec.Val.toAdmin,
      Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff]

theorem probe_localSet_head_no_step (state : Wasm.Core.Exec.State)
    (index : Nat) (tail : List Wasm.Core.Exec.AdminInstr)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state, .plain (localSet index) :: tail) event next := by
  intro step
  generalize hsource :
    (state, .plain (localSet index) :: tail) = source at step
  induction step generalizing state tail
  case ctxtInstrs z z' values inner inner' post ev hinner hnonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change .plain (localSet index) :: tail = inner ++ post at hinstructions
        cases inner with
        | nil =>
            exact probe_nil_no_step z hinner
        | cons instruction rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hhead : .plain (localSet index) = instruction :=
              hinstructions.1
            subst instruction
            exact ih state rest (Prod.ext hstate rfl)
    | cons firstValue restValues =>
        change .plain (localSet index) :: tail =
          firstValue.toAdmin ::
            (Wasm.Core.Exec.vals restValues ++ inner ++ post) at hinstructions
        have hhead : .plain (localSet index) = firstValue.toAdmin :=
          (List.cons.inj hinstructions).1
        exact (probe_instrLocalSet_admin_ne_value
          (coreU32 index) firstValue hhead).elim
  case pure is is' pe membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals
        (.plain (localSet index) :: tail) =
        ([], .plain (localSet index) :: tail) := by
      rfl
    rw [hsplit] at membership
    cases tail <;>
      simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr,
        localSet] at membership
  case read readStep =>
    induction readStep <;>
      simp_all [localSet, Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case block =>
      exact probe_localSet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
    case loop =>
      exact probe_localSet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
    case callRefFunc =>
      exact probe_localSet_vals_addrref_plain_false index tail _ _ _ _
        (by simpa [localSet, List.append_assoc] using hsource.2) rfl
    case throwRefInstrs =>
      exact probe_localSet_vals_addrref_plain_false index tail _ _ _ _
        (by simpa [localSet, List.append_assoc] using hsource.2) rfl
    case tryTable =>
      exact probe_localSet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
  case throw =>
    exact probe_localSet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  case structNew =>
    exact probe_localSet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  case arrayNewFixed =>
    exact probe_localSet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  all_goals
    simp_all [localSet, Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff]

/-- Any amended-Core step from an emitted status-assignment redex reaches the
same state and suffix as the direct `local.set` step and is nontrapping.  The
proof covers every administrative split allowed by `ctxtInstrs`; it does not
assume global Core determinism. -/
theorem statusPair_step_unique (state : Wasm.Core.Exec.State)
    (index value : Nat) (tail : List Wasm.Core.Exec.AdminInstr)
    (hindex : index < state.frame.locals.length)
    (hexact : (coreU32 index).val = index)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, (statusValue value).toAdmin ::
        .plain (localSet index) :: tail) event next) :
    next = (writeLocal state index (statusValue value), tail) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, (statusValue value).toAdmin ::
      .plain (localSet index) :: tail) = source at other
  induction other generalizing state tail <;>
    simp_all [localSet, Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff,
      Wasm.Core.Exec.splitVals_vals_append_nonval,
      Wasm.Core.Exec.splitVals_cons_val,
      withLocal_eq_writeLocal, Wasm.Core.Harness.coreTrapCause?]
  case ctxtInstrs z z' values inner inner' post ev hinner hnonempty ih =>
    have hstate := hsource.1
    have hinstructions := hsource.2
    cases values with
    | nil =>
        change (statusValue value).toAdmin ::
          .plain (.localSet (coreU32 index)) :: tail =
            inner ++ post at hinstructions
        cases inner with
        | nil =>
            exact (probe_nil_no_step z hinner).elim
        | cons first rest =>
            cases rest with
            | nil =>
                have hfirst : (statusValue value).toAdmin = first :=
                  (List.cons.inj hinstructions).1
                subst first
                exact (probe_single_status_no_step z value hinner).elim
            | cons second innerTail =>
                simp only [List.cons_append, List.cons.injEq] at hinstructions
                obtain ⟨rfl, rfl, htail⟩ := hinstructions
                have hindexState : index < state.frame.locals.length := by
                  rw [hstate]
                  exact hindex
                obtain ⟨⟨hnextState, hnextInstructions⟩, hcause⟩ :=
                  ih state innerTail hindexState hstate rfl
                constructor
                · constructor
                  · exact hnextState
                  · simpa [hnextInstructions] using htail.symm
                · simpa [Wasm.Core.Harness.coreTrapCause?] using hcause
    | cons firstValue restValues =>
        cases restValues with
        | nil =>
            change (statusValue value).toAdmin ::
              .plain (.localSet (coreU32 index)) :: tail =
                firstValue.toAdmin :: (inner ++ post) at hinstructions
            have hfirst : statusValue value = firstValue :=
              Wasm.Core.Exec.Val.toAdmin_injective
                (List.cons.inj hinstructions).1
            subst firstValue
            have hrest : .plain (localSet index) :: tail =
                inner ++ post := (List.cons.inj hinstructions).2
            cases inner with
            | nil =>
                exact (probe_nil_no_step z hinner).elim
            | cons instruction innerTail =>
                have hinstruction : .plain (localSet index) = instruction :=
                  (List.cons.inj hrest).1
                subst instruction
                exact (probe_localSet_head_no_step z index innerTail hinner).elim
        | cons secondValue restValues =>
            simp only [Wasm.Core.Exec.vals, List.map_cons,
              List.cons_append] at hinstructions
            have hsecond : .plain (.localSet (coreU32 index)) =
                secondValue.toAdmin :=
              (List.cons.inj (List.cons.inj hinstructions).2).1
            exact (probe_instrLocalSet_admin_ne_value
              (coreU32 index) secondValue hsecond).elim
  case pure is is' pe membership =>
    rw [← hsource.2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals
        ((statusValue value).toAdmin ::
          .plain (.localSet (coreU32 index)) :: tail) =
        ([statusValue value],
          .plain (.localSet (coreU32 index)) :: tail) := by
      simpa [localSet] using
        (Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
          (a := .plain (localSet index)) rfl tail)
    rw [hsplit] at membership
    cases tail <;>
      simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr,
        localSet] at membership
  case read readStep =>
    cases readStep <;> simp_all [localSet, statusValue]
    case block =>
      exact (probe_status_ne_vals_plain index value tail _ _ rfl
        (by intro equality; cases equality) hsource.2).elim
    case loop =>
      exact (probe_status_ne_vals_plain index value tail _ _ rfl
        (by intro equality; cases equality) hsource.2).elim
    case callRefFunc =>
      exact (probe_status_vals_addrref_plain_false index value tail _ _ _ _
        (by simpa [statusValue, localSet] using hsource.2) rfl
        (by intro equality; cases equality)).elim
    case throwRefInstrs =>
      exact (probe_status_vals_addrref_plain_false index value tail _ _ _ _
        (by simpa [statusValue, localSet, List.append_assoc] using hsource.2) rfl
        (by intro equality; cases equality)).elim
    case tryTable =>
      exact (probe_status_ne_vals_plain index value tail _ _ rfl
        (by intro equality; cases equality) hsource.2).elim
  case throw =>
    exact (probe_status_ne_vals_plain index value tail _ _ rfl
      (by intro equality; cases equality) hsource.2).elim
  case localSet hwith =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    exact Option.some.inj (hwith.symm.trans
      (withLocal_eq_writeLocal state index
        (statusValue value) hindex hexact))
  case structNew =>
    exact (probe_status_ne_vals_plain index value tail _ _ rfl
      (by intro equality; cases equality) hsource.2).elim
  case arrayNewFixed =>
    exact (probe_status_ne_vals_plain index value tail _ _ rfl
      (by intro equality; cases equality) hsource.2).elim

end WasmGemmGnaf.GNAF.DirectScalarRuntime
