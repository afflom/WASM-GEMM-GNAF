import WasmGemmGnaf.GNAF.CompileScalarForced

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.GNAF.DirectScalarRuntime

open WasmGemmGnaf

/-! ## Forced execution of the fixed result epilogue -/

@[simp] theorem wrap_admin_ne_value (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain wrapI64 ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  change none = some value at mapped
  simp at mapped

@[simp] theorem instrWrap_admin_ne_value (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain
        (.cvtop .i32 .i64 (.ii .wrap)) ≠ value.toAdmin :=
  wrap_admin_ne_value value

@[simp] theorem localGet_admin_ne_value (index : Nat)
    (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain (localGet index) ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  change none = some value at mapped
  simp at mapped

@[simp] theorem instrLocalGet_admin_ne_value
    (index : Wasm.Core.LocalIdx) (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain (.localGet index) ≠ value.toAdmin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin] at mapped
  change none = some value at mapped
  simp at mapped

@[simp] theorem localGet_ne_constAddr (index : Nat)
    (addressType : Wasm.Core.AddrType)
    (literal : Wasm.Core.Exec.AddrLit addressType) :
    Wasm.Core.Exec.AdminInstr.plain (localGet index) ≠
      Wasm.Core.Exec.constAddr addressType literal := by
  cases addressType with
  | i32 => exact localGet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact localGet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem instrLocalGet_ne_constAddr (index : Wasm.Core.LocalIdx)
    (addressType : Wasm.Core.AddrType)
    (literal : Wasm.Core.Exec.AddrLit addressType) :
    Wasm.Core.Exec.AdminInstr.plain (.localGet index) ≠
      Wasm.Core.Exec.constAddr addressType literal := by
  cases addressType with
  | i32 => exact instrLocalGet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact instrLocalGet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem localGet_ne_constInn (index : Nat) (inn : Wasm.Core.Inn)
    (literal : Wasm.Core.Exec.InnLit inn) :
    Wasm.Core.Exec.AdminInstr.plain (localGet index) ≠
      Wasm.Core.Exec.constInn inn literal := by
  cases inn with
  | i32 => exact localGet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact localGet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem instrLocalGet_ne_constInn (index : Wasm.Core.LocalIdx)
    (inn : Wasm.Core.Inn) (literal : Wasm.Core.Exec.InnLit inn) :
    Wasm.Core.Exec.AdminInstr.plain (.localGet index) ≠
      Wasm.Core.Exec.constInn inn literal := by
  cases inn with
  | i32 => exact instrLocalGet_admin_ne_value index (.num ⟨.i32, literal⟩)
  | i64 => exact instrLocalGet_admin_ne_value index (.num ⟨.i64, literal⟩)

@[simp] theorem localGet_ne_constI32 (index : Nat)
    (literal : Wasm.Core.U32) :
    Wasm.Core.Exec.AdminInstr.plain (localGet index) ≠
      Wasm.Core.Exec.constI32 literal :=
  localGet_admin_ne_value index (.num ⟨.i32, literal⟩)

@[simp] theorem instrLocalGet_ne_constI32 (index : Wasm.Core.LocalIdx)
    (literal : Wasm.Core.U32) :
    Wasm.Core.Exec.AdminInstr.plain (.localGet index) ≠
      Wasm.Core.Exec.constI32 literal :=
  instrLocalGet_admin_ne_value index (.num ⟨.i32, literal⟩)

@[simp] theorem localGet_ne_refAdmin (index : Nat)
    (reference : Wasm.Core.Exec.Ref) :
    Wasm.Core.Exec.AdminInstr.plain (localGet index) ≠ reference.toAdmin := by
  cases reference with
  | null heapType => exact localGet_admin_ne_value index (.ref (.null heapType))
  | addr address => exact localGet_admin_ne_value index (.ref (.addr address))

@[simp] theorem wrap_ne_constAddr (addressType : Wasm.Core.AddrType)
    (literal : Wasm.Core.Exec.AddrLit addressType) :
    Wasm.Core.Exec.AdminInstr.plain wrapI64 ≠
      Wasm.Core.Exec.constAddr addressType literal := by
  cases addressType with
  | i32 => exact wrap_admin_ne_value (.num ⟨.i32, literal⟩)
  | i64 => exact wrap_admin_ne_value (.num ⟨.i64, literal⟩)

@[simp] theorem instrWrap_ne_constAddr (addressType : Wasm.Core.AddrType)
    (literal : Wasm.Core.Exec.AddrLit addressType) :
    Wasm.Core.Exec.AdminInstr.plain
        (.cvtop .i32 .i64 (.ii .wrap)) ≠
      Wasm.Core.Exec.constAddr addressType literal := by
  cases addressType with
  | i32 => exact instrWrap_admin_ne_value (.num ⟨.i32, literal⟩)
  | i64 => exact instrWrap_admin_ne_value (.num ⟨.i64, literal⟩)

@[simp] theorem wrap_ne_constInn (inn : Wasm.Core.Inn)
    (literal : Wasm.Core.Exec.InnLit inn) :
    Wasm.Core.Exec.AdminInstr.plain wrapI64 ≠
      Wasm.Core.Exec.constInn inn literal := by
  cases inn with
  | i32 => exact wrap_admin_ne_value (.num ⟨.i32, literal⟩)
  | i64 => exact wrap_admin_ne_value (.num ⟨.i64, literal⟩)

@[simp] theorem instrWrap_ne_constInn (inn : Wasm.Core.Inn)
    (literal : Wasm.Core.Exec.InnLit inn) :
    Wasm.Core.Exec.AdminInstr.plain
        (.cvtop .i32 .i64 (.ii .wrap)) ≠
      Wasm.Core.Exec.constInn inn literal := by
  cases inn with
  | i32 => exact instrWrap_admin_ne_value (.num ⟨.i32, literal⟩)
  | i64 => exact instrWrap_admin_ne_value (.num ⟨.i64, literal⟩)

@[simp] theorem wrap_ne_constI32 (literal : Wasm.Core.U32) :
    Wasm.Core.Exec.AdminInstr.plain wrapI64 ≠
      Wasm.Core.Exec.constI32 literal :=
  wrap_admin_ne_value (.num ⟨.i32, literal⟩)

@[simp] theorem instrWrap_ne_constI32 (literal : Wasm.Core.U32) :
    Wasm.Core.Exec.AdminInstr.plain
        (.cvtop .i32 .i64 (.ii .wrap)) ≠
      Wasm.Core.Exec.constI32 literal :=
  instrWrap_admin_ne_value (.num ⟨.i32, literal⟩)

@[simp] theorem wrap_ne_refAdmin (reference : Wasm.Core.Exec.Ref) :
    Wasm.Core.Exec.AdminInstr.plain wrapI64 ≠ reference.toAdmin := by
  cases reference with
  | null heapType => exact wrap_admin_ne_value (.ref (.null heapType))
  | addr address => exact wrap_admin_ne_value (.ref (.addr address))

theorem singletonLocalGet_vals_plain_parts (index : Nat)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (source : [Wasm.Core.Exec.AdminInstr.plain (localGet index)] =
      Wasm.Core.Exec.vals values ++ [.plain instruction]) :
    values = [] ∧ instruction = localGet index := by
  have split := congrArg Wasm.Core.Exec.splitVals source
  rw [show Wasm.Core.Exec.splitVals
      [Wasm.Core.Exec.AdminInstr.plain (localGet index)] =
        ([], [Wasm.Core.Exec.AdminInstr.plain (localGet index)]) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at split
  have valuesEq := congrArg Prod.fst split
  have instructionsEq := congrArg Prod.snd split
  constructor
  · exact valuesEq.symm
  · have head := (List.cons.inj instructionsEq).1
    injection head with instructionEq
    exact instructionEq.symm

theorem singletonLocalGet_ne_vals_addrref_plain (index : Nat)
    (values : List Wasm.Core.Exec.Val)
    (reference : Wasm.Core.Exec.AddrRef) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    [Wasm.Core.Exec.AdminInstr.plain (localGet index)] ≠
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post := by
  intro source
  have split := congrArg Wasm.Core.Exec.splitVals source
  rw [show Wasm.Core.Exec.splitVals
      [Wasm.Core.Exec.AdminInstr.plain (localGet index)] =
        ([], [Wasm.Core.Exec.AdminInstr.plain (localGet index)]) by rfl,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at split
  have valuesEq := congrArg Prod.fst split
  simp at valuesEq

theorem localGet_vals_plain_false (index : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localGet index) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain (localGet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain (localGet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem localGet_vals_plain_post_false (index : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality : .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals values ++ .plain instruction :: post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ localGet index) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain (localGet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain (localGet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue post]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem localGet_vals_addrref_plain_false (index : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain (localGet index) :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain (localGet index) :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain (localGet index)) rfl tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  simpa using valuesEquality

theorem localGet_head_step_target
    (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hlocal : state.localOf (coreU32 index) = some (some value))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, .plain (localGet index) :: tail) event next) :
    next = (state, value.toAdmin :: tail) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, .plain (localGet index) :: tail) = source at other
  induction other generalizing state tail
  case ctxtInstrs z z' values inner inner' post ev innerStep nonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change .plain (localGet index) :: tail = inner ++ post at hinstructions
        cases inner with
        | nil => exact (probe_nil_no_step z innerStep).elim
        | cons instruction rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hhead : .plain (localGet index) = instruction :=
              hinstructions.1
            subst instruction
            obtain ⟨nextEq, causeEq⟩ :=
              ih state rest hlocal (Prod.ext hstate rfl)
            have nextStateEq : z' = state := congrArg Prod.fst nextEq
            have nextInstructionsEq : inner' = value.toAdmin :: rest :=
              congrArg Prod.snd nextEq
            constructor
            · apply Prod.ext
              · exact nextStateEq
              · simp only [Wasm.Core.Exec.vals, List.map_nil,
                  List.nil_append, List.cons_append]
                rw [nextInstructionsEq]
                exact congrArg
                  (fun xs : List Wasm.Core.Exec.AdminInstr => value.toAdmin :: xs)
                  hinstructions.2.symm
            · simpa [Wasm.Core.Harness.coreTrapCause?] using causeEq
    | cons firstValue restValues =>
        change .plain (localGet index) :: tail = firstValue.toAdmin ::
          (Wasm.Core.Exec.vals restValues ++ inner ++ post) at hinstructions
        have hhead : .plain (localGet index) = firstValue.toAdmin :=
          (List.cons.inj hinstructions).1
        exact (localGet_admin_ne_value index firstValue hhead).elim
  case pure is is' pureEvent membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals
        (.plain (localGet index) :: tail) =
        ([], .plain (localGet index) :: tail) := by rfl
    rw [hsplit] at membership
    cases tail <;>
      simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr,
        localGet] at membership
  case read readStep =>
    induction readStep <;>
      simp_all [Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case localGet z x v hlookup =>
      have indexEq : coreU32 index = x := by
        injection hsource.2.1
      subst x
      have valueEq : value = v :=
        Option.some.inj (Option.some.inj (hlocal.symm.trans hlookup))
      exact ⟨valueEq.symm, rfl⟩
    case block =>
      exact (localGet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    case loop =>
      exact (localGet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    case callRefFunc =>
      exact (localGet_vals_addrref_plain_false index tail _ _ _ _
        (by simpa [localGet, List.append_assoc] using hsource.2) rfl).elim
    case throwRefInstrs =>
      exact (localGet_vals_addrref_plain_false index tail _ _ _ _
        (by simpa [localGet, List.append_assoc] using hsource.2) rfl).elim
    case tryTable =>
      exact (localGet_vals_plain_false index tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    all_goals try
      simp_all [Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    all_goals simp_all [localGet]
  case throw =>
    exact (localGet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  case structNew =>
    exact (localGet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  case arrayNewFixed =>
    exact (localGet_vals_plain_false index tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  all_goals try simp_all
  all_goals
    simp_all [localGet, Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff,
      Wasm.Core.Harness.coreTrapCause?]
  all_goals try simp_all

theorem localGet_single_step_target
    (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val)
    (hlocal : state.localOf (coreU32 index) = some (some value))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [Wasm.Core.Exec.AdminInstr.plain (localGet index)]) event next) :
    next = (state, [value.toAdmin]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  simpa using localGet_head_step_target state index value [] hlocal other

theorem localGet_label_step_target
    (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hlocal : state.localOf (coreU32 index) = some (some value))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [.label 1 [] (.plain (localGet index) :: tail)]) event next) :
    next = (state, [.label 1 [] (value.toAdmin :: tail)]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, [Wasm.Core.Exec.AdminInstr.label 1 []
      (.plain (localGet index) :: tail)]) = source at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_label] at membership
    simp [Wasm.Core.Exec.pureOfLabel, Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.adminToVal, localGet] at membership
  case read readStep =>
    cases readStep <;> simp_all [localGet,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin]
    case block =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case loop =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case callRefFunc =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case returnCallRefLabel =>
      exact (localGet_vals_plain_post_false index tail _ _ _ hsource.2.2.2
        rfl (by intro equality; cases equality)).elim
    case throwRefInstrs =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (.label 1 [] (.plain (localGet index) :: tail)) rfl values inner post
      bodyStep nonempty (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtLabel bodyStep =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    simpa only [Prod.mk.injEq] using
      localGet_head_step_target state index value tail hlocal bodyStep

theorem localGet_frame_label_step_target
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hlocal : state.localOf (coreU32 index) = some (some value))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame
          [.label 1 [] (.plain (localGet index) :: tail)]]) event next) :
    next =
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame
          [.label 1 [] (value.toAdmin :: tail)]]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    ((⟨state.store, outerFrame⟩ : Wasm.Core.Exec.State),
      [Wasm.Core.Exec.AdminInstr.frame 1 state.frame
        [Wasm.Core.Exec.AdminInstr.label 1 []
          (.plain (localGet index) :: tail)]]) = source at other
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
      (.frame 1 state.frame
        [.label 1 [] (.plain (localGet index) :: tail)]) rfl
      values inner post bodyStep nonempty
      (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_frame_ne_vals_plain 1 state.frame _ _ _ hsource.2).elim
  case ctxtFrame bodyStep =>
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := hsource
    have target := localGet_label_step_target state index value tail hlocal
      bodyStep
    have stateTarget := congrArg Prod.fst target.1
    have storeTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.store) stateTarget
    have frameTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.frame) stateTarget
    simp_all

theorem localGet_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index : Nat)
    (value : Wasm.Core.Exec.Val)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hlocal : state.localOf (coreU32 index) = some (some value))
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame
            [.label 1 [] (.plain (localGet index) :: tail)]])) event next) :
    next = .afterEntry harness entry
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame
          [.label 1 [] (value.toAdmin :: tail)]]) := by
  apply Wasm.Core.Harness.afterEntry_target_unique_of_core
    (targetNotTrap := by simp)
    (sourceNotReturn := by
      intro sourceState sourceValue equality
      have instructions := congrArg Prod.snd equality
      exact frame_admin_ne_value 1 state.frame _ sourceValue
        (List.cons.inj instructions).1)
    (sourceNotThrow := by intro sourceState address equality; simp at equality)
    (allCore := fun coreStep =>
      localGet_frame_label_step_target outerFrame state index value tail hlocal
        coreStep)
    other

theorem wrap_vals_plain_false
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ wrapI64) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain wrapI64 :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain wrapI64) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem wrap_vals_addrref_plain_false
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain wrapI64 :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval []
      (a := .plain wrapI64) rfl tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  simpa using valuesEquality

theorem wrap_head_no_step (state : Wasm.Core.Exec.State)
    (tail : List Wasm.Core.Exec.AdminInstr)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA (state, .plain wrapI64 :: tail) event next := by
  intro step
  generalize hsource :
    (state, .plain wrapI64 :: tail) = source at step
  induction step generalizing state tail
  case ctxtInstrs z z' values inner inner' post ev innerStep nonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change .plain wrapI64 :: tail = inner ++ post at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z innerStep
        | cons instruction rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hhead : .plain wrapI64 = instruction := hinstructions.1
            subst instruction
            exact ih state rest (Prod.ext hstate rfl)
    | cons firstValue restValues =>
        change .plain wrapI64 :: tail = firstValue.toAdmin ::
          (Wasm.Core.Exec.vals restValues ++ inner ++ post) at hinstructions
        have hhead : .plain wrapI64 = firstValue.toAdmin :=
          (List.cons.inj hinstructions).1
        exact (wrap_admin_ne_value firstValue hhead).elim
  case pure is is' pureEvent membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals (.plain wrapI64 :: tail) =
        ([], .plain wrapI64 :: tail) := by rfl
    rw [hsplit] at membership
    cases tail <;>
      simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr,
        Wasm.Core.Exec.arg1num, wrapI64] at membership
  case read readStep =>
    induction readStep <;>
      simp_all [Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case block =>
      exact wrap_vals_plain_false tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
    case loop =>
      exact wrap_vals_plain_false tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
    case callRefFunc =>
      exact wrap_vals_addrref_plain_false tail _ _ _ _
        (by simpa [wrapI64, List.append_assoc] using hsource.2) rfl
    case throwRefInstrs =>
      exact wrap_vals_addrref_plain_false tail _ _ _ _
        (by simpa [wrapI64, List.append_assoc] using hsource.2) rfl
    case tryTable =>
      exact wrap_vals_plain_false tail _ _ hsource.2 rfl
        (by intro equality; cases equality)
    all_goals try
      simp_all [Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    all_goals simp_all [wrapI64]
  case throw =>
    exact wrap_vals_plain_false tail _ _ (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  case structNew =>
    exact wrap_vals_plain_false tail _ _ (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  case arrayNewFixed =>
    exact wrap_vals_plain_false tail _ _ (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)
  all_goals try simp_all
  all_goals
    simp_all [wrapI64, Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff]
  all_goals try simp_all

theorem statusWrap_ne_vals_plain (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ wrapI64) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain wrapI64 :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain wrapI64) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem statusWrap_vals_plain_post_false (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality : (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals values ++ .plain instruction :: post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ wrapI64) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain wrapI64 :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain wrapI64) rfl tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue post]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem statusWrap_vals_addrref_plain_false (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ wrapI64) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show (statusValue value).toAdmin :: .plain wrapI64 :: tail =
      Wasm.Core.Exec.vals [statusValue value] ++
        (.plain wrapI64 :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [statusValue value]
      (a := .plain wrapI64) rfl tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem statusWrap_step_target
    (state : Wasm.Core.Exec.State) (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hvalue : value < 2 ^ 32)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, (statusValue value).toAdmin :: .plain wrapI64 :: tail)
      event next) :
    next = (state,
      (Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin :: tail) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  have hcvtop :
      Wasm.Core.Exec.releasedNumerics.cvtop__ .i64 .i32 (.ii .wrap)
        (coreU64 value) = [coreU32 value] := by
    change [Wasm.Core.Exec.ConcreteNumerics.wrap 64 32 (coreU64 value)] =
      [coreU32 value]
    congr 2
    apply Subtype.ext
    simp [Wasm.Core.Exec.ConcreteNumerics.wrap,
      Wasm.Core.Exec.Numerics.ofNatWrap, coreU32, coreU64,
      Nat.mod_eq_of_lt hvalue,
      Nat.mod_eq_of_lt (Nat.lt_trans hvalue
        (by decide : 2 ^ 32 < 2 ^ 64))]
  generalize hsource :
    (state, (statusValue value).toAdmin :: .plain wrapI64 :: tail) =
      source at other
  induction other generalizing state tail
  case ctxtInstrs z z' values inner inner' post ev innerStep nonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change (statusValue value).toAdmin :: .plain wrapI64 :: tail =
          inner ++ post at hinstructions
        cases inner with
        | nil => exact (probe_nil_no_step z innerStep).elim
        | cons first rest =>
            cases rest with
            | nil =>
                have hfirst : (statusValue value).toAdmin = first :=
                  (List.cons.inj hinstructions).1
                subst first
                exact (probe_single_status_no_step z value innerStep).elim
            | cons second innerTail =>
                simp only [List.cons_append, List.cons.injEq] at hinstructions
                obtain ⟨rfl, rfl, htail⟩ := hinstructions
                obtain ⟨nextEq, hcause⟩ :=
                  ih state innerTail (Prod.ext hstate rfl)
                have hnextState : z' = state := congrArg Prod.fst nextEq
                constructor
                · apply Prod.ext
                  · exact hnextState
                  · have actualInstructions : inner' =
                        (Wasm.Core.Exec.Val.num
                          ⟨.i32, coreU32 value⟩).toAdmin :: innerTail :=
                      congrArg Prod.snd nextEq
                    simp only [Prod.snd] at actualInstructions
                    simp only [Prod.snd, Wasm.Core.Exec.vals, List.map_nil,
                      List.nil_append, List.cons_append]
                    rw [actualInstructions]
                    simpa using congrArg
                      (List.cons
                        (Wasm.Core.Exec.Val.num
                          ⟨.i32, coreU32 value⟩).toAdmin)
                      htail.symm
                · simpa [Wasm.Core.Harness.coreTrapCause?] using hcause
    | cons firstValue restValues =>
        cases restValues with
        | nil =>
            change (statusValue value).toAdmin :: .plain wrapI64 :: tail =
              firstValue.toAdmin :: (inner ++ post) at hinstructions
            have hfirst : statusValue value = firstValue :=
              Wasm.Core.Exec.Val.toAdmin_injective
                (List.cons.inj hinstructions).1
            subst firstValue
            have hrest : .plain wrapI64 :: tail = inner ++ post :=
              (List.cons.inj hinstructions).2
            cases inner with
            | nil => exact (probe_nil_no_step z innerStep).elim
            | cons instruction innerTail =>
                have hinstruction : .plain wrapI64 = instruction :=
                  (List.cons.inj hrest).1
                subst instruction
                exact (wrap_head_no_step z innerTail innerStep).elim
        | cons secondValue restValues =>
            simp only [Wasm.Core.Exec.vals, List.map_cons,
              List.cons_append] at hinstructions
            have hsecond : .plain wrapI64 = secondValue.toAdmin :=
              (List.cons.inj (List.cons.inj hinstructions).2).1
            exact (wrap_admin_ne_value secondValue hsecond).elim
  case pure is is' pureEvent membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    cases tail with
    | nil =>
        rw [show [(statusValue value).toAdmin, .plain wrapI64] =
          Wasm.Core.Exec.vals [statusValue value] ++ [.plain wrapI64] by rfl,
          Wasm.Core.Exec.pureSuccessors_ofInstr
            [statusValue value] wrapI64 rfl] at membership
        simp [Wasm.Core.Exec.pureOfInstr, statusValue, wrapI64, hcvtop,
          Wasm.Core.Exec.choices, Wasm.Core.Exec.withIndex,
          Wasm.Core.Harness.coreTrapCause?] at membership
        constructor
        · apply Prod.ext
          · exact (Prod.mk.inj hsource).1.symm
          · simpa using membership.2
        · rw [membership.1]
          rfl
    | cons nextInstruction rest =>
        rw [show (statusValue value).toAdmin :: .plain wrapI64 ::
            nextInstruction :: rest =
          Wasm.Core.Exec.vals [statusValue value] ++
            .plain wrapI64 :: nextInstruction :: rest by rfl] at membership
        unfold Wasm.Core.Exec.pureSuccessors at membership
        rw [Wasm.Core.Exec.splitVals_vals_append_nonval
          [statusValue value] (a := .plain wrapI64) rfl
          (nextInstruction :: rest)] at membership
        simp [Wasm.Core.Exec.pureOfSplit] at membership
  case read readStep =>
    cases readStep <;> simp_all [statusValue]
    case block =>
      exact (statusWrap_ne_vals_plain value tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    case loop =>
      exact (statusWrap_ne_vals_plain value tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    case callRefFunc =>
      exact (statusWrap_vals_addrref_plain_false value tail _ _ _ _
        (by simpa [statusValue, wrapI64, List.append_assoc] using hsource.2)
        rfl (by intro equality; cases equality)).elim
    case throwRefInstrs =>
      exact (statusWrap_vals_addrref_plain_false value tail _ _ _ _
        (by simpa [statusValue, wrapI64, List.append_assoc] using hsource.2)
        rfl (by intro equality; cases equality)).elim
    case tryTable =>
      exact (statusWrap_ne_vals_plain value tail _ _ hsource.2 rfl
        (by intro equality; cases equality)).elim
    all_goals try
      simp_all [statusValue,
        Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    all_goals simp_all [statusValue, wrapI64,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin]
  case throw =>
    exact (statusWrap_ne_vals_plain value tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  case structNew =>
    exact (statusWrap_ne_vals_plain value tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  case arrayNewFixed =>
    exact (statusWrap_ne_vals_plain value tail _ _
      (Prod.mk.inj hsource).2 rfl
      (by intro equality; cases equality)).elim
  all_goals try simp_all
  all_goals
    simp_all [statusValue, wrapI64,
      Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff,
      Wasm.Core.Harness.coreTrapCause?]
  all_goals try simp_all [statusValue]

theorem statusWrap_label_step_target
    (state : Wasm.Core.Exec.State) (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hvalue : value < 2 ^ 32)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [.label 1 []
        ((statusValue value).toAdmin :: .plain wrapI64 :: tail)])
      event next) :
    next = (state, [.label 1 []
      ((Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin :: tail)]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, [Wasm.Core.Exec.AdminInstr.label 1 []
      ((statusValue value).toAdmin :: .plain wrapI64 :: tail)]) = source
      at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_label] at membership
    simp [Wasm.Core.Exec.pureOfLabel, Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.adminToVal, statusValue, wrapI64,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin] at membership
  case read readStep =>
    cases readStep <;> simp_all [statusValue, wrapI64,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin]
    case block =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case loop =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case callRefFunc =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case returnCallRefLabel =>
      exact (statusWrap_vals_plain_post_false value tail _ _ _
        hsource.2.2.2 rfl (by intro equality; cases equality)).elim
    case throwRefInstrs =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (.label 1 []
        ((statusValue value).toAdmin :: .plain wrapI64 :: tail)) rfl
      values inner post bodyStep nonempty
      (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtLabel bodyStep =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    simpa only [Prod.mk.injEq] using
      statusWrap_step_target state value tail hvalue bodyStep

theorem statusWrap_frame_label_step_target
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hvalue : value < 2 ^ 32)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          ((statusValue value).toAdmin :: .plain wrapI64 :: tail)]])
      event next) :
    next =
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          ((Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin ::
            tail)]]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    ((⟨state.store, outerFrame⟩ : Wasm.Core.Exec.State),
      [Wasm.Core.Exec.AdminInstr.frame 1 state.frame
        [Wasm.Core.Exec.AdminInstr.label 1 []
          ((statusValue value).toAdmin :: .plain wrapI64 :: tail)]]) =
      source at other
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
      (.frame 1 state.frame [.label 1 []
        ((statusValue value).toAdmin :: .plain wrapI64 :: tail)]) rfl
      values inner post bodyStep nonempty
      (by simpa [List.append_assoc] using hsource.2)).elim
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
    have target := statusWrap_label_step_target state value tail hvalue
      bodyStep
    have stateTarget := congrArg Prod.fst target.1
    have storeTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.store) stateTarget
    have frameTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.frame) stateTarget
    simp_all

theorem statusWrap_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (value : Nat)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (hvalue : value < 2 ^ 32)
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            ((statusValue value).toAdmin :: .plain wrapI64 :: tail)]]))
      event next) :
    next = .afterEntry harness entry
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          ((Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin ::
            tail)]]) := by
  apply Wasm.Core.Harness.afterEntry_target_unique_of_core
    (targetNotTrap := by simp)
    (sourceNotReturn := by
      intro sourceState sourceValue equality
      have instructions := congrArg Prod.snd equality
      exact frame_admin_ne_value 1 state.frame _ sourceValue
        (List.cons.inj instructions).1)
    (sourceNotThrow := by intro sourceState address equality; simp at equality)
    (allCore := fun coreStep =>
      statusWrap_frame_label_step_target outerFrame state value tail hvalue
        coreStep)
    other

/-! ## Forced discharge of the result label, frame, and Harness return -/

theorem singletonValue_vals_plain_false
    (value : Wasm.Core.Exec.Val)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : [value.toAdmin] =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show [value.toAdmin] = Wasm.Core.Exec.vals [value] by rfl,
    Wasm.Core.Exec.splitVals_vals,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  simp at tails

theorem singletonValue_vals_addrref_plain_false
    (value : Wasm.Core.Exec.Val)
    (values : List Wasm.Core.Exec.Val) (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr) (post : List Wasm.Core.Exec.AdminInstr)
    (equality : [value.toAdmin] = Wasm.Core.Exec.vals values ++
      [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show [value.toAdmin] = Wasm.Core.Exec.vals [value] by rfl,
    Wasm.Core.Exec.splitVals_vals,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have tails := congrArg Prod.snd splitEquality
  simp at tails

theorem valueAdmin_ne_nonvalue (value : Wasm.Core.Exec.Val)
    (admin : Wasm.Core.Exec.AdminInstr)
    (hnonvalue : Wasm.Core.Exec.adminToVal admin = none) :
    value.toAdmin ≠ admin := by
  intro equality
  have mapped := congrArg Wasm.Core.Exec.adminToVal equality
  rw [Wasm.Core.Exec.adminToVal_toAdmin, hnonvalue] at mapped
  simp at mapped

theorem singletonValue_ne_vals_two
    (value : Wasm.Core.Exec.Val) (values : List Wasm.Core.Exec.Val)
    (first second : Wasm.Core.Exec.AdminInstr)
    (post : List Wasm.Core.Exec.AdminInstr) :
    [value.toAdmin] ≠ Wasm.Core.Exec.vals values ++
      first :: second :: post := by
  intro equality
  have lengths := congrArg List.length equality
  simp [Wasm.Core.Exec.vals] at lengths
  omega

theorem singletonValue_vals_plain_post_false
    (value : Wasm.Core.Exec.Val) (values : List Wasm.Core.Exec.Val)
    (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality : [value.toAdmin] =
      Wasm.Core.Exec.vals values ++ .plain instruction :: post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show [value.toAdmin] = Wasm.Core.Exec.vals [value] by rfl,
    Wasm.Core.Exec.splitVals_vals,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue post]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  simp at tails

theorem singletonValue_no_step (state : Wasm.Core.Exec.State)
    (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Exec.Event}
    {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA (state, [value.toAdmin]) event next := by
  intro step
  generalize hsource : (state, [value.toAdmin]) = source at step
  induction step
  case ctxtInstrs z z' values inner inner' post ev hinner hnonempty ih =>
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change [value.toAdmin] = inner ++ post at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z hinner
        | cons instruction rest =>
            cases rest with
            | nil =>
                have hpost : post = [] := by
                  simpa only [List.singleton_append, List.cons.injEq] using
                    (List.cons.inj hinstructions).2.symm
                exact hnonempty.elim (fun h => h rfl) (fun h => h hpost)
            | cons nextInstruction rest => simp at hinstructions
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
  case pure is is' pureEvent membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals [value.toAdmin] = ([value], []) := by
      simpa [Wasm.Core.Exec.vals] using
        Wasm.Core.Exec.splitVals_vals [value]
    rw [hsplit] at membership
    simp [Wasm.Core.Exec.pureOfSplit] at membership
  case read readStep =>
    induction readStep <;>
      simp_all [Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case block =>
      exact singletonValue_vals_plain_false value _ _ hsource.2 rfl
    case loop =>
      exact singletonValue_vals_plain_false value _ _ hsource.2 rfl
    case callRefFunc =>
      exact singletonValue_vals_addrref_plain_false value _ _ _ _
        (by simpa [List.append_assoc] using hsource.2) rfl
    case throwRefInstrs =>
      exact singletonValue_vals_addrref_plain_false value _ _ _ _
        (by simpa [List.append_assoc] using hsource.2) rfl
    case tryTable =>
      exact singletonValue_vals_plain_false value _ _ hsource.2 rfl
    all_goals try
      exact (valueAdmin_ne_nonvalue value _ rfl hsource.2).elim
    all_goals
      rcases hnum with ⟨number, rfl⟩
      simp_all [Wasm.Core.Exec.Val.toAdmin]
  case throw =>
    exact singletonValue_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  case structNew =>
    exact singletonValue_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  case arrayNewFixed =>
    exact singletonValue_vals_plain_false value _ _
      (Prod.mk.inj hsource).2 rfl
  all_goals try
    exact (valueAdmin_ne_nonvalue value _ rfl hsource.2).elim
  all_goals
    rcases hnum with ⟨number, rfl⟩
    simp_all [Wasm.Core.Exec.Val.toAdmin]
  all_goals
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff]

theorem labelValue_step_target (state : Wasm.Core.Exec.State)
    (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [.label 1 [] [value.toAdmin]]) event next) :
    next = (state, [value.toAdmin]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, [Wasm.Core.Exec.AdminInstr.label 1 [] [value.toAdmin]]) =
      source at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure is is' pureEvent membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_label] at membership
    change (pureEvent, is') ∈
      Wasm.Core.Exec.pureOfLabel 1 [] (Wasm.Core.Exec.vals [value])
      at membership
    rw [Wasm.Core.Exec.pureOfLabel_vals] at membership
    simp [Wasm.Core.Exec.single] at membership
    exact ⟨membership.2, by rw [membership.1]; rfl⟩
  case read readStep =>
    cases readStep <;> simp_all
    case block =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case loop =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
    case callRefFunc =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case returnCallRefLabel =>
      exact (singletonValue_vals_plain_post_false value _ _ _
        hsource.2.2.2 rfl).elim
    case throwRefInstrs =>
      exact (singleton_label_ne_vals_addrref_plain 1 [] _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (.label 1 [] [value.toAdmin]) rfl values inner post bodyStep nonempty
      (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_label_ne_vals_plain 1 [] _ _ _ hsource.2).elim
  case ctxtLabel bodyStep =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    exact (singletonValue_no_step state value hnum bodyStep).elim

theorem labelValue_frame_step_target
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 [] [value.toAdmin]]]) event next) :
    next = (⟨state.store, outerFrame⟩,
      [.frame 1 state.frame [value.toAdmin]]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    ((⟨state.store, outerFrame⟩ : Wasm.Core.Exec.State),
      [Wasm.Core.Exec.AdminInstr.frame 1 state.frame
        [Wasm.Core.Exec.AdminInstr.label 1 [] [value.toAdmin]]]) =
      source at other
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
      (.frame 1 state.frame [.label 1 [] [value.toAdmin]]) rfl
      values inner post bodyStep nonempty
      (by simpa [List.append_assoc] using hsource.2)).elim
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
    have target := labelValue_step_target state value hnum bodyStep
    have stateTarget := congrArg Prod.fst target.1
    have storeTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.store) stateTarget
    have frameTarget := congrArg
      (fun nextState : Wasm.Core.Exec.State => nextState.frame) stateTarget
    simp_all

theorem labelValue_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 [] [value.toAdmin]]]))
      event next) :
    next = .afterEntry harness entry
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [value.toAdmin]]) := by
  apply Wasm.Core.Harness.afterEntry_target_unique_of_core
    (targetNotTrap := by simp)
    (sourceNotReturn := by
      intro sourceState sourceValue equality
      have instructions := congrArg Prod.snd equality
      exact frame_admin_ne_value 1 state.frame _ sourceValue
        (List.cons.inj instructions).1)
    (sourceNotThrow := by intro sourceState address equality; simp at equality)
    (allCore := fun coreStep =>
      labelValue_frame_step_target outerFrame state value hnum coreStep)
    other

theorem frameValue_step_target (state : Wasm.Core.Exec.State)
    (frame : Wasm.Core.Exec.Frame) (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state, [.frame 1 frame [value.toAdmin]]) event next) :
    next = (state, [value.toAdmin]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state, [Wasm.Core.Exec.AdminInstr.frame 1 frame [value.toAdmin]]) =
      source at other
  induction other <;> simp_all [Wasm.Core.Harness.coreTrapCause?]
  case pure is is' pureEvent membership =>
    rw [← hsource.2, Wasm.Core.Exec.pureSuccessors_frame] at membership
    change (pureEvent, is') ∈
      Wasm.Core.Exec.pureOfFrame 1 (Wasm.Core.Exec.vals [value])
      at membership
    rw [Wasm.Core.Exec.pureOfFrame_vals, if_pos (by simp)] at membership
    simp [Wasm.Core.Exec.single] at membership
    exact ⟨membership.2, by rw [membership.1]; rfl⟩
  case read readStep =>
    cases readStep <;> simp_all
    case block =>
      exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
    case loop =>
      exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
    case callRefFunc =>
      exact (singleton_frame_ne_vals_addrref_plain 1 frame _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case throwRefInstrs =>
      exact (singleton_frame_ne_vals_addrref_plain 1 frame _ _ _ _ _
        (by simpa [List.append_assoc] using hsource.2)).elim
    case tryTable =>
      exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
    case returnCallRefFrameNull =>
      have lengths := congrArg List.length hsource.2.2.2
      simp [Wasm.Core.Exec.vals] at lengths
      omega
    case returnCallRefFrameAddr =>
      have lengths := congrArg List.length hsource.2.2.2
      simp [Wasm.Core.Exec.vals] at lengths
      omega
  case ctxtInstrs z z' values inner inner' post ev bodyStep nonempty =>
    exact (singleton_nonvalue_ctxt_false z
      (.frame 1 frame [value.toAdmin]) rfl values inner post bodyStep
      nonempty (by simpa [List.append_assoc] using hsource.2)).elim
  case throw =>
    exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
  case structNew =>
    exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
  case arrayNewFixed =>
    exact (singleton_frame_ne_vals_plain 1 frame _ _ _ hsource.2).elim
  case ctxtFrame bodyStep =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsource
    exact (singletonValue_no_step _ value hnum bodyStep).elim

theorem frameValue_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (state : Wasm.Core.Exec.State) (frame : Wasm.Core.Exec.Frame)
    (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (state, [.frame 1 frame [value.toAdmin]])) event next) :
    next = .afterEntry harness entry (state, [value.toAdmin]) := by
  apply Wasm.Core.Harness.afterEntry_target_unique_of_core
    (targetNotTrap := by
      intro equality
      exact (valueAdmin_ne_nonvalue value .trap rfl
        (List.cons.inj equality).1).elim)
    (sourceNotReturn := by
      intro sourceState sourceValue equality
      have instructions := congrArg Prod.snd equality
      exact frame_admin_ne_value 1 frame _ sourceValue
        (List.cons.inj instructions).1)
    (sourceNotThrow := by intro sourceState address equality; simp at equality)
    (allCore := fun coreStep =>
      frameValue_step_target state frame value hnum coreStep)
    other

theorem return_afterEntry_target_unique
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store) (state : Wasm.Core.Exec.State)
    (value : Wasm.Core.Exec.Val)
    (hnum : ∃ number : Wasm.Core.Exec.NumVal, value = .num number)
    {event : Wasm.Core.Harness.Event} {next : Wasm.Core.Harness.Config}
    (other : Wasm.Core.Harness.StepA
      (.afterEntry harness entry (state, [value.toAdmin])) event next) :
    next = .returned harness entry value state := by
  rcases hnum with ⟨number, rfl⟩
  generalize hsource : Wasm.Core.Harness.Config.afterEntry harness entry
    (state, [(Wasm.Core.Exec.Val.num number).toAdmin]) = source at other
  induction other <;> simp_all [Wasm.Core.Exec.Val.toAdmin,
    Wasm.Core.Exec.Ref.toAdmin]
  case returnAfter h' entry' state' returnedValue =>
    rcases hsource with ⟨rfl, rfl, rfl, hadmin⟩
    change (Wasm.Core.Exec.Val.num number).toAdmin =
      returnedValue.toAdmin at hadmin
    have valueEq : (Wasm.Core.Exec.Val.num number) = returnedValue :=
      Wasm.Core.Exec.Val.toAdmin_injective hadmin
    subst returnedValue
    rfl
  all_goals
    exfalso
    apply singletonValue_no_step state (.num number) ⟨number, rfl⟩
    change Wasm.Core.Exec.StepA
      (state, [.plain (.const number.nt number.c)]) _ _
    rw [hsource.2.2]
    assumption

theorem statusEpilogue_first_two_steps
    (state : Wasm.Core.Exec.State) (index value : Nat)
    (hlocal : state.localOf (coreU32 index) =
      some (some (statusValue value))) (hvalue : value < 2 ^ 32) :
    ∃ readEvent wrapEvent,
      Wasm.Core.Exec.StepA
        (state, [.plain (localGet index), .plain wrapI64]) readEvent
        (state, [(statusValue value).toAdmin, .plain wrapI64]) ∧
      Wasm.Core.Exec.StepA
        (state, [(statusValue value).toAdmin, .plain wrapI64]) wrapEvent
        (state,
          [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin]) := by
  obtain ⟨trace, steps, _⟩ :=
    statusEpilogue_steps state index value hlocal hvalue
  change Wasm.Core.Exec.StepsA
      (state, [.plain (localGet index), .plain wrapI64]) trace
      (state, [(Wasm.Core.Exec.Val.num ⟨.i32, coreU32 value⟩).toAdmin])
    at steps
  cases steps with
  | @cons _ middle _ readEvent restTrace readStep restSteps =>
      have readTarget := localGet_head_step_target state index
        (statusValue value) [.plain wrapI64] hlocal readStep
      have exactRead : Wasm.Core.Exec.StepA
          (state, [.plain (localGet index), .plain wrapI64]) readEvent
          (state, [(statusValue value).toAdmin, .plain wrapI64]) := by
        simpa [readTarget.1] using readStep
      rw [readTarget.1] at restSteps
      cases restSteps with
      | @cons _ middleAfterWrap _ wrapEvent remaining wrapStep rest =>
          have wrapTarget := statusWrap_step_target state value [] hvalue
            wrapStep
          have exactWrap : Wasm.Core.Exec.StepA
              (state, [(statusValue value).toAdmin, .plain wrapI64])
              wrapEvent
              (state, [(Wasm.Core.Exec.Val.num
                ⟨.i32, coreU32 value⟩).toAdmin]) := by
            simpa [wrapTarget.1] using wrapStep
          exact ⟨readEvent, wrapEvent, exactRead, exactWrap⟩

theorem statusEpilogue_afterEntry_forcedTargets
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store)
    (outerFrame : Wasm.Core.Exec.Frame)
    (state : Wasm.Core.Exec.State) (index value : Nat)
    (hlocal : state.localOf (coreU32 index) =
      some (some (statusValue value)))
    (hvalue : value < 2 ^ 32) :
    Wasm.Core.Harness.ForcedTargets
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            [.plain (localGet index), .plain wrapI64]]]))
      (.returned harness entry
        (.num ⟨.i32, coreU32 value⟩)
        ⟨state.store, outerFrame⟩) := by
  let resultValue : Wasm.Core.Exec.Val :=
    .num ⟨.i32, coreU32 value⟩
  obtain ⟨readEvent, wrapEvent, readStep, wrapStep⟩ :=
    statusEpilogue_first_two_steps state index value hlocal hvalue
  have readFramed : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          [.plain (localGet index), .plain wrapI64]]])
      (.ctxtFrame 1 (.ctxtLabel 1 readEvent))
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          [(statusValue value).toAdmin, .plain wrapI64]]]) :=
    .ctxtFrame (.ctxtLabel readStep)
  have readSafe := (localGet_head_step_target state index
    (statusValue value) [.plain wrapI64] hlocal readStep).2
  have readHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            [.plain (localGet index), .plain wrapI64]]]))
      (.coreAfterEntry (.ctxtFrame 1 (.ctxtLabel 1 readEvent)))
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            [(statusValue value).toAdmin, .plain wrapI64]]])) := by
    apply Wasm.Core.Harness.StepA.coreAfter readFramed
    · simpa [Wasm.Core.Harness.coreTrapCause?] using readSafe
    · simp
  have wrapFramed : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 []
          [(statusValue value).toAdmin, .plain wrapI64]]])
      (.ctxtFrame 1 (.ctxtLabel 1 wrapEvent))
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 [] [resultValue.toAdmin]]]) := by
    simpa [resultValue] using
      (Wasm.Core.Exec.StepA.ctxtFrame
        (Wasm.Core.Exec.StepA.ctxtLabel wrapStep))
  have wrapSafe := (statusWrap_step_target state value [] hvalue wrapStep).2
  have wrapHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            [(statusValue value).toAdmin, .plain wrapI64]]]))
      (.coreAfterEntry (.ctxtFrame 1 (.ctxtLabel 1 wrapEvent)))
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 [] [resultValue.toAdmin]]])) := by
    apply Wasm.Core.Harness.StepA.coreAfter wrapFramed
    · simpa [Wasm.Core.Harness.coreTrapCause?] using wrapSafe
    · simp
  let labelEvent : Wasm.Core.Exec.Event :=
    .pure ⟨.labelVals, 0⟩
      (Wasm.Core.Exec.sourcePlains
        [.label 1 [] [resultValue.toAdmin]])
  have labelInner : Wasm.Core.Exec.StepA
      (state, [.label 1 [] [resultValue.toAdmin]]) labelEvent
      (state, [resultValue.toAdmin]) := by
    simpa [labelEvent, resultValue] using
      labelVals_step state 1 [] [resultValue]
  have labelFramed : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [.label 1 [] [resultValue.toAdmin]]])
      (.ctxtFrame 1 labelEvent)
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [resultValue.toAdmin]]) :=
    .ctxtFrame labelInner
  have labelHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 [] [resultValue.toAdmin]]]))
      (.coreAfterEntry (.ctxtFrame 1 labelEvent))
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [resultValue.toAdmin]])) := by
    apply Wasm.Core.Harness.StepA.coreAfter labelFramed
    · rfl
    · simp
  let frameEvent : Wasm.Core.Exec.Event :=
    .pure ⟨.frameVals, 0⟩
      (Wasm.Core.Exec.sourcePlains
        [.frame 1 state.frame [resultValue.toAdmin]])
  have frameCore : Wasm.Core.Exec.StepA
      (⟨state.store, outerFrame⟩,
        [.frame 1 state.frame [resultValue.toAdmin]]) frameEvent
      (⟨state.store, outerFrame⟩, [resultValue.toAdmin]) := by
    simpa [frameEvent, resultValue] using
      frameVals_step ⟨state.store, outerFrame⟩ 1 state.frame
        [resultValue] (by simp)
  have frameHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [resultValue.toAdmin]]))
      (.coreAfterEntry frameEvent)
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩, [resultValue.toAdmin])) := by
    apply Wasm.Core.Harness.StepA.coreAfter frameCore
    · rfl
    · simp [resultValue, Wasm.Core.Exec.Val.toAdmin]
  have returnHarness : Wasm.Core.Harness.StepA
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩, [resultValue.toAdmin]))
      .returnAfterEntry
      (.returned harness entry resultValue ⟨state.store, outerFrame⟩) :=
    .returnAfter
  apply Wasm.Core.Harness.ForcedTargets.cons
    (step := readHarness)
    (targetUnique := fun other =>
      localGet_afterEntry_target_unique harness entry outerFrame state index
        (statusValue value) [.plain wrapI64] hlocal other)
  apply Wasm.Core.Harness.ForcedTargets.cons
    (step := wrapHarness)
    (targetUnique := fun other =>
      statusWrap_afterEntry_target_unique harness entry outerFrame state value
        [] hvalue other)
  apply Wasm.Core.Harness.ForcedTargets.cons
    (step := labelHarness)
    (targetUnique := fun other =>
      labelValue_afterEntry_target_unique harness entry outerFrame state
        resultValue ⟨⟨.i32, coreU32 value⟩, rfl⟩ other)
  apply Wasm.Core.Harness.ForcedTargets.cons
    (step := frameHarness)
    (targetUnique := fun other =>
      frameValue_afterEntry_target_unique harness entry
        ⟨state.store, outerFrame⟩ state.frame resultValue
        ⟨⟨.i32, coreU32 value⟩, rfl⟩ other)
  apply Wasm.Core.Harness.ForcedTargets.cons
    (step := returnHarness)
    (targetUnique := fun other =>
      return_afterEntry_target_unique harness entry
        ⟨state.store, outerFrame⟩ resultValue
        ⟨⟨.i32, coreU32 value⟩, rfl⟩ other)
  exact .terminal (Or.inl ⟨_, .returned _ _ _ _⟩)

theorem emittedFunction_afterEntry_forcedTargets
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (state : Wasm.Core.Exec.State)
    (harness : Wasm.Core.Harness.Harness)
    (entry : Wasm.Core.Exec.Store) (outerFrame : Wasm.Core.Exec.Frame)
    (hindex : (envOf checked.inputSig checked.plan).statusLocal <
      state.frame.locals.length)
    (hexact : (coreU32
      (envOf checked.inputSig checked.plan).statusLocal).val =
        (envOf checked.inputSig checked.plan).statusLocal)
    (hzero : state.localOf
      (coreU32 (envOf checked.inputSig checked.plan).statusLocal) =
        some (some (statusValue 0))) :
    Wasm.Core.Harness.ForcedTargets
      (.afterEntry harness entry
        (⟨state.store, outerFrame⟩,
          [.frame 1 state.frame [.label 1 []
            (Wasm.Core.Exec.plains
              (bodyCode (envOf checked.inputSig checked.plan)
                checked.inputSig.scratch checked.plan))]]))
      (.returned harness entry
        (.num ⟨.i32, coreU32 checked.returnedStatus⟩)
        ⟨state.store, outerFrame⟩) := by
  let environment := envOf checked.inputSig checked.plan
  let assignments := DirectScalar.statusAssignments checked.plan
  let suffix := [localGet environment.statusLocal, wrapI64]
  let afterStatus := applyStatusWrites state environment.statusLocal assignments
  have hstatusLocal : afterStatus.localOf (coreU32 environment.statusLocal) =
      some (some (statusValue checked.returnedStatus)) := by
    have hlocal := applyStatusWrites_local state environment.statusLocal 0
      assignments (by simpa [environment] using hindex)
      (by simpa [environment] using hexact)
      (by simpa [environment] using hzero)
    simpa [afterStatus, assignments, CheckedPlan.returnedStatus,
      DirectScalar.apply_statusAssignments] using hlocal
  have epilogueForced := statusEpilogue_afterEntry_forcedTargets harness entry
    outerFrame afterStatus environment.statusLocal checked.returnedStatus
    hstatusLocal checked.returnedStatus_lt_two_pow_32
  have bodyForced := statusAssignments_afterEntry_forcedTargets harness entry
    outerFrame state environment.statusLocal assignments suffix
    (by simpa [environment] using hindex)
    (by simpa [environment] using hexact)
    (by simp [suffix]) epilogueForced
  have bodyEq := DirectScalar.bodyCode_eq_statusCode checked
  rw [DirectScalar.statusCode_eq_flatMap] at bodyEq
  simpa [environment, assignments, suffix, afterStatus, bodyEq] using
    bodyForced

/-! ## Forced compiler invocation prefix -/

/-- The only administrative values that occur before the emitted `call_ref`.
Unlike an indexed `ref.null`, neither numeric constants nor concrete function
addresses carry a latent read reduction. -/
def callPrefixInert : Wasm.Core.Exec.AdminInstr → Bool
  | .plain (.const _ _) => true
  | .addrref (.funcAddr _) => true
  | _ => false

theorem callPrefixInert_no_step (state : Wasm.Core.Exec.State)
    (instructions : List Wasm.Core.Exec.AdminInstr)
    (hinert : ∀ instruction, instruction ∈ instructions →
      callPrefixInert instruction)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA (state, instructions) event next := by
  intro step
  have hall : instructions.all callPrefixInert = true :=
    List.all_eq_true.mpr hinert
  generalize hsource : (state, instructions) = source at step
  induction step generalizing state instructions
  case ctxtInstrs z z' values inner inner' post ev innerStep nonempty ih =>
    have hstate := congrArg Prod.fst hsource
    have hinstructions := congrArg Prod.snd hsource
    simp only [Prod.fst] at hstate
    simp only [Prod.snd] at hinstructions
    apply ih z inner
    · intro instruction membership
      apply hinert instruction
      rw [hinstructions]
      simp only [List.mem_append]
      exact Or.inl (Or.inr membership)
    · apply List.all_eq_true.mpr
      intro instruction membership
      apply hinert instruction
      rw [hinstructions]
      simp only [List.mem_append]
      exact Or.inl (Or.inr membership)
    · rfl
  case pure membership =>
    have pureStep := Wasm.Core.Exec.mem_pureSuccessors_step_pure membership
    induction pureStep <;>
      have hinstructions := congrArg Prod.snd hsource <;>
      simp only [Prod.snd] at hinstructions <;>
      rw [hinstructions] at hall <;>
      simp [callPrefixInert, List.all_append,
        Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
        Wasm.Core.Exec.vals] at hall
  case read readStep =>
    induction readStep <;>
      have hinstructions := congrArg Prod.snd hsource <;>
      simp only [Prod.snd] at hinstructions <;>
      rw [hinstructions] at hall <;>
      simp [callPrefixInert, List.all_append,
        Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
        Wasm.Core.Exec.vals] at hall
  all_goals
    have hinstructions := congrArg Prod.snd hsource
    simp only [Prod.snd] at hinstructions
    rw [hinstructions] at hall
    simp [callPrefixInert, List.all_append,
      Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals] at hall

theorem callRefPair_vals_plain_parts
    (first second : Wasm.Core.U32) (address : Wasm.Core.Exec.FuncAddr)
    (type : Wasm.Core.DefType) (values : List Wasm.Core.Exec.Val)
    (instruction : Wasm.Core.Instr)
    (equality :
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    values =
        [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
          .ref (.addr (.funcAddr address))] ∧
      instruction = .callRef (.defd type) := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  have leftShape :
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
            .ref (.addr (.funcAddr address))] ++
        [.plain (.callRef (.defd type))] := by
    rfl
  rw [leftShape,
    Wasm.Core.Exec.splitVals_vals_append_nonval
      [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
        .ref (.addr (.funcAddr address))] rfl [],
    Wasm.Core.Exec.splitVals_vals_append_nonval values hnonvalue []]
      at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  have instructionsEquality := congrArg Prod.snd splitEquality
  constructor
  · simpa using valuesEquality.symm
  · have head := (List.cons.inj instructionsEquality).1
    injection head with instructionEquality
    exact instructionEquality.symm

theorem callRefPair_vals_addrref_plain_instruction
    (first second : Wasm.Core.U32) (address : Wasm.Core.Exec.FuncAddr)
    (type : Wasm.Core.DefType) (values : List Wasm.Core.Exec.Val)
    (reference : Wasm.Core.Exec.AddrRef) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality :
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    instruction = .callRef (.defd type) := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  have leftShape :
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
            .ref (.addr (.funcAddr address))] ++
        [.plain (.callRef (.defd type))] := by
    rfl
  rw [leftShape,
    Wasm.Core.Exec.splitVals_vals_append_nonval
      [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
        .ref (.addr (.funcAddr address))] rfl [],
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have instructionsEquality := congrArg Prod.snd splitEquality
  have head := (List.cons.inj instructionsEquality).1
  injection head with instructionEquality
  exact instructionEquality.symm

theorem callRefPair_read_rule
    (state : Wasm.Core.Exec.State) (first second : Wasm.Core.U32)
    (address : Wasm.Core.Exec.FuncAddr) (type : Wasm.Core.DefType)
    {rule : Wasm.Core.Exec.ReadRule}
    {target : List Wasm.Core.Exec.AdminInstr}
    (step : Wasm.Core.Exec.Step_readA state rule
      (Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))])
      target) :
    rule = .callRefFunc := by
  generalize hsource :
    (Wasm.Core.Exec.vals
        [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
      [.addrref (.funcAddr address), .plain (.callRef (.defd type))]) =
      source at step
  induction step <;>
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals]
  case block =>
    have parts := callRefPair_vals_plain_parts first second address type _ _
      hsource rfl
    cases parts.2
  case loop =>
    have parts := callRefPair_vals_plain_parts first second address type _ _
      hsource rfl
    cases parts.2
  case throwRefInstrs =>
    have instruction := callRefPair_vals_addrref_plain_instruction
      first second address type _ _ _ _
        (by simpa [List.append_assoc] using hsource) rfl
    cases instruction
  case tryTable =>
    have parts := callRefPair_vals_plain_parts first second address type _ _
      hsource rfl
    cases parts.2

theorem callRef_vals_plain_parts
    (prefixValues : List Wasm.Core.Exec.Val)
    (address : Wasm.Core.Exec.FuncAddr) (type : Wasm.Core.DefType)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality :
      Wasm.Core.Exec.vals prefixValues ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    values = prefixValues ++ [.ref (.addr (.funcAddr address))] ∧
      instruction = .callRef (.defd type) := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  have leftShape :
      Wasm.Core.Exec.vals prefixValues ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals
          (prefixValues ++ [.ref (.addr (.funcAddr address))]) ++
        [.plain (.callRef (.defd type))] := by
    simp [Wasm.Core.Exec.vals, Wasm.Core.Exec.Val.toAdmin,
      Wasm.Core.Exec.Ref.toAdmin]
  rw [leftShape,
    Wasm.Core.Exec.splitVals_vals_append_nonval
      (vs := prefixValues ++
        [Wasm.Core.Exec.Val.ref
          (Wasm.Core.Exec.Ref.addr (.funcAddr address))])
        (a := .plain (.callRef (.defd type))) rfl [],
    Wasm.Core.Exec.splitVals_vals_append_nonval (vs := values)
      (a := .plain instruction) hnonvalue []]
      at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  have instructionsEquality := congrArg Prod.snd splitEquality
  constructor
  · simpa using valuesEquality.symm
  · have head := (List.cons.inj instructionsEquality).1
    injection head with instructionEquality
    exact instructionEquality.symm

theorem callRef_vals_addrref_plain_instruction
    (prefixValues : List Wasm.Core.Exec.Val)
    (address : Wasm.Core.Exec.FuncAddr) (type : Wasm.Core.DefType)
    (values : List Wasm.Core.Exec.Val)
    (reference : Wasm.Core.Exec.AddrRef) (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality :
      Wasm.Core.Exec.vals prefixValues ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hnonvalue : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    instruction = .callRef (.defd type) := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  have leftShape :
      Wasm.Core.Exec.vals prefixValues ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
      Wasm.Core.Exec.vals
          (prefixValues ++ [.ref (.addr (.funcAddr address))]) ++
        [.plain (.callRef (.defd type))] := by
    simp [Wasm.Core.Exec.vals, Wasm.Core.Exec.Val.toAdmin,
      Wasm.Core.Exec.Ref.toAdmin]
  rw [leftShape,
    Wasm.Core.Exec.splitVals_vals_append_nonval
      (vs := prefixValues ++
        [Wasm.Core.Exec.Val.ref
          (Wasm.Core.Exec.Ref.addr (.funcAddr address))])
        (a := .plain (.callRef (.defd type))) rfl [],
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hnonvalue] at splitEquality
  have instructionsEquality := congrArg Prod.snd splitEquality
  have head := (List.cons.inj instructionsEquality).1
  injection head with instructionEquality
  exact instructionEquality.symm

theorem addr_callRef_read_rule
    (state : Wasm.Core.Exec.State)
    (address : Wasm.Core.Exec.FuncAddr) (type : Wasm.Core.DefType)
    {rule : Wasm.Core.Exec.ReadRule}
    {target : List Wasm.Core.Exec.AdminInstr}
    (step : Wasm.Core.Exec.Step_readA state rule
      [.addrref (.funcAddr address), .plain (.callRef (.defd type))]
      target) :
    rule = .callRefFunc := by
  obtain ⟨unindexedSource, unindexedTarget, hsource', htarget',
      unindexedStep⟩ := step.unindexSourceTarget
  have hsource :
      [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
        unindexedSource := hsource'.symm
  clear step hsource' htarget'
  induction unindexedStep <;>
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals]
  case block =>
    have parts := callRef_vals_plain_parts [] address type _ _
      (by simpa using hsource) rfl
    cases parts.2
  case loop =>
    have parts := callRef_vals_plain_parts [] address type _ _
      (by simpa using hsource) rfl
    cases parts.2
  case throwRefInstrs =>
    have instruction := callRef_vals_addrref_plain_instruction
      [] address type _ _ _ _
        (by simpa [List.append_assoc] using hsource) rfl
    cases instruction
  case tryTable =>
    have parts := callRef_vals_plain_parts [] address type _ _
      (by simpa using hsource) rfl
    cases parts.2

theorem plainHead_vals_plain_false (head : Wasm.Core.Instr)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val) (instruction : Wasm.Core.Instr)
    (equality : .plain head :: tail =
      Wasm.Core.Exec.vals values ++ [.plain instruction])
    (hhead : Wasm.Core.Exec.adminToVal (.plain head) = none)
    (hinstruction : Wasm.Core.Exec.adminToVal (.plain instruction) = none)
    (hdifferent : instruction ≠ head) : False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain head :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain head :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [] hhead tail,
    Wasm.Core.Exec.splitVals_vals_append_nonval values hinstruction []]
      at splitEquality
  have tails := congrArg Prod.snd splitEquality
  have heads := (List.cons.inj tails).1
  cases heads
  exact hdifferent rfl

theorem plainHead_vals_addrref_plain_false (head : Wasm.Core.Instr)
    (tail : List Wasm.Core.Exec.AdminInstr)
    (values : List Wasm.Core.Exec.Val)
    (reference : Wasm.Core.Exec.AddrRef)
    (instruction : Wasm.Core.Instr)
    (post : List Wasm.Core.Exec.AdminInstr)
    (equality : .plain head :: tail =
      Wasm.Core.Exec.vals values ++
        [.addrref reference, .plain instruction] ++ post)
    (hhead : Wasm.Core.Exec.adminToVal (.plain head) = none)
    (hinstruction : Wasm.Core.Exec.adminToVal (.plain instruction) = none) :
    False := by
  have splitEquality := congrArg Wasm.Core.Exec.splitVals equality
  rw [show .plain head :: tail =
      Wasm.Core.Exec.vals [] ++ (.plain head :: tail) by rfl,
    Wasm.Core.Exec.splitVals_vals_append_nonval [] hhead tail,
    Wasm.Core.Exec.splitVals_vals_addrref_plain values reference instruction
      post hinstruction] at splitEquality
  have valuesEquality := congrArg Prod.fst splitEquality
  simp at valuesEquality

theorem callRef_ne_valueAdmin (type : Wasm.Core.DefType)
    (value : Wasm.Core.Exec.Val) :
    Wasm.Core.Exec.AdminInstr.plain (.callRef (.defd type)) ≠
      value.toAdmin := by
  intro equality
  exact (valueAdmin_ne_nonvalue value
    (.plain (.callRef (.defd type))) rfl equality.symm)

theorem callRef_ne_refAdmin (type : Wasm.Core.DefType)
    (reference : Wasm.Core.Exec.Ref) :
    Wasm.Core.Exec.AdminInstr.plain (.callRef (.defd type)) ≠
      reference.toAdmin :=
  callRef_ne_valueAdmin type (.ref reference)

theorem callRef_head_no_step (state : Wasm.Core.Exec.State)
    (type : Wasm.Core.DefType) (tail : List Wasm.Core.Exec.AdminInstr)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state, .plain (.callRef (.defd type)) :: tail) event next := by
  intro step
  generalize hsource :
    (state, .plain (.callRef (.defd type)) :: tail) = source at step
  induction step generalizing state tail
  case ctxtInstrs z z' values inner inner' post ev innerStep
      contextNonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change .plain (.callRef (.defd type)) :: tail = inner ++ post
          at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z innerStep
        | cons instruction rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hhead : .plain (.callRef (.defd type)) = instruction :=
              hinstructions.1
            subst instruction
            exact ih state rest (Prod.ext hstate rfl)
    | cons firstValue restValues =>
        change .plain (.callRef (.defd type)) :: tail =
          firstValue.toAdmin ::
            (Wasm.Core.Exec.vals restValues ++ inner ++ post)
              at hinstructions
        exact (valueAdmin_ne_nonvalue firstValue
          (.plain (.callRef (.defd type))) rfl
          (List.cons.inj hinstructions).1.symm).elim
  case pure membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    have hsplit : Wasm.Core.Exec.splitVals
        (.plain (.callRef (.defd type)) :: tail) =
        ([], .plain (.callRef (.defd type)) :: tail) := by
      rfl
    rw [hsplit] at membership
    cases tail <;>
      simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr]
        at membership
  case read readStep =>
    induction readStep <;>
      simp_all [Wasm.Core.Exec.adminToVal,
        Wasm.Core.Exec.constI32_eq_iff,
        Wasm.Core.Exec.constAddr_eq_iff,
        Wasm.Core.Exec.Val.toAdmin_eq_iff]
    case block =>
      exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
        hsource.2 rfl rfl (by intro equality; cases equality)
    case loop =>
      exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
        hsource.2 rfl rfl (by intro equality; cases equality)
    case callRefFunc =>
      exact plainHead_vals_addrref_plain_false (.callRef (.defd type)) tail
        _ _ _ _ (by simpa [List.append_assoc] using hsource.2) rfl rfl
    case throwRefInstrs =>
      exact plainHead_vals_addrref_plain_false (.callRef (.defd type)) tail
        _ _ _ _ (by simpa [List.append_assoc] using hsource.2) rfl rfl
    case tryTable =>
      exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
        hsource.2 rfl rfl (by intro equality; cases equality)
    all_goals try
      exact (valueAdmin_ne_nonvalue _ (.plain (.callRef (.defd type)))
        rfl hsource.2.1.symm).elim
    all_goals try
      simp_all [callRef_ne_valueAdmin, callRef_ne_refAdmin,
        Wasm.Core.Exec.constAddr, Wasm.Core.Exec.constI32]
  case throw =>
    exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
      (Prod.mk.inj hsource).2 rfl rfl (by intro equality; cases equality)
  case structNew =>
    exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
      (Prod.mk.inj hsource).2 rfl rfl (by intro equality; cases equality)
  case arrayNewFixed =>
    exact plainHead_vals_plain_false (.callRef (.defd type)) tail _ _
      (Prod.mk.inj hsource).2 rfl rfl (by intro equality; cases equality)
  all_goals try
    exact (valueAdmin_ne_nonvalue _ (.plain (.callRef (.defd type)))
      rfl hsource.2.1.symm).elim
  all_goals
    have hsplit := congrArg
      (fun config : Wasm.Core.Exec.Config =>
        Wasm.Core.Exec.splitVals config.2) hsource
    simp_all [callRef_ne_valueAdmin,
      callRef_ne_refAdmin,
      Wasm.Core.Exec.splitVals,
      Wasm.Core.Exec.adminToVal,
      Wasm.Core.Exec.constAddr,
      Wasm.Core.Exec.constI32,
      Wasm.Core.Exec.constI32_eq_iff,
      Wasm.Core.Exec.constAddr_eq_iff,
      Wasm.Core.Exec.Val.toAdmin_eq_iff]

theorem callRef_only_no_step (state : Wasm.Core.Exec.State)
    (type : Wasm.Core.DefType)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state, [.plain (.callRef (.defd type))]) event next :=
  callRef_head_no_step state type []

theorem addr_callRef_no_step
    (state : Wasm.Core.Exec.State) (address : Wasm.Core.Exec.FuncAddr)
    (function : Wasm.Core.Exec.FuncInst)
    (hfunction : state.funcinst[address]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32])))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state,
        [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))]) event next := by
  intro step
  obtain ⟨unindexedSource, unindexedEvent, unindexedTarget,
      hsource', hevent', htarget', unindexedStep⟩ :=
    step.unindexSourceEventTarget
  have hsource :
      (state,
        [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))]) = unindexedSource :=
    hsource'.symm
  clear step hsource' hevent' htarget'
  induction unindexedStep generalizing state
  case ctxtInstrs z z' values inner inner' post ev innerStep
      contextNonempty ih =>
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] = inner ++ post
            at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z innerStep
        | cons first rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hfirst : first = .addrref (.funcAddr address) :=
              hinstructions.1.symm
            subst first
            cases rest with
            | nil =>
                apply callPrefixInert_no_step z
                  [.addrref (.funcAddr address)]
                · intro instruction membership
                  simp_all [callPrefixInert]
                · exact innerStep
            | cons second rest =>
                simp only [List.cons_append, List.cons.injEq] at hinstructions
                have hempty :=
                  List.append_eq_nil_iff.mp hinstructions.2.2.symm
                exact contextNonempty.elim (fun h => h rfl)
                  (fun h => h hempty.2)
    | cons first restValues =>
        change [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] =
            first.toAdmin ::
              (Wasm.Core.Exec.vals restValues ++ inner ++ post)
                at hinstructions
        have htail := (List.cons.inj hinstructions).2
        cases restValues with
        | nil =>
            change [.plain (.callRef (.defd function.type))] =
              inner ++ post at htail
            cases inner with
            | nil => exact probe_nil_no_step z innerStep
            | cons instruction rest =>
                simp only [List.cons_append, List.cons.injEq] at htail
                have hinstruction : instruction =
                    .plain (.callRef (.defd function.type)) := htail.1.symm
                subst instruction
                have hempty := List.append_eq_nil_iff.mp htail.2.symm
                have hrest : rest = [] := hempty.1
                have hpost : post = [] := hempty.2
                subst rest
                subst post
                exact callRef_only_no_step z function.type innerStep
        | cons second restValues =>
            change [.plain (.callRef (.defd function.type))] =
              second.toAdmin ::
                (Wasm.Core.Exec.vals restValues ++ inner ++ post) at htail
            exact (valueAdmin_ne_nonvalue second
              (.plain (.callRef (.defd function.type))) rfl
              (List.cons.inj htail).1.symm).elim
  case pure membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    rw [show
      [.addrref (.funcAddr address),
        .plain (.callRef (.defd function.type))] =
      Wasm.Core.Exec.vals [.ref (.addr (.funcAddr address))] ++
        [.plain (.callRef (.defd function.type))] by rfl,
      Wasm.Core.Exec.splitVals_vals_append_nonval
        [.ref (.addr (.funcAddr address))] rfl []] at membership
    simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr]
      at membership
  case read readStep =>
    rw [← (Prod.mk.inj hsource).1,
      ← (Prod.mk.inj hsource).2] at readStep
    have ruleEquality := addr_callRef_read_rule state address function.type
      readStep
    obtain ⟨unindexedReadSource, unindexedReadTarget,
        hreadSource', hreadTarget', unindexedReadStep⟩ :=
      readStep.unindexSourceTarget
    have hreadSource :
        [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] =
          unindexedReadSource := hreadSource'.symm
    clear readStep hreadSource' hreadTarget'
    induction unindexedReadStep <;>
      simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
        Wasm.Core.Exec.vals, Wasm.Core.ValTypes.ofList]
    case callRefFunc =>
      rename_i _ _ _ _ values targetAddress typeUse targetFunction fn
        inputs outputs argumentCount resultCount targetFrame hlookup hexpand
        hinputs houtputs hvalues hcode hframe
      have sourceEquality := hreadSource.trans hsource.2.symm
      have lengths := congrArg List.length sourceEquality
      have hvaluesLength : values.length = 0 := by
        simp [Wasm.Core.Exec.vals] at lengths
        simpa [lengths]
      have hvaluesNil : values = [] :=
        List.eq_nil_of_length_eq_zero hvaluesLength
      subst values
      simp [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin]
        at sourceEquality
      have htargetAddress : targetAddress = address := sourceEquality.1.symm
      subst targetAddress
      have htargetFunction : targetFunction = function := by
        exact Option.some.inj (hlookup.symm.trans hfunction)
      subst targetFunction
      have hinputTypes : inputs =
          Wasm.Core.ValTypes.ofList [.num .i32, .num .i32] := by
        have hcomp := Option.some.inj (hexpand.symm.trans htype)
        injection hcomp
      rw [hinputTypes] at hinputs
      simp [Wasm.Core.ValTypes.ofList, Wasm.Core.ValTypes.length] at hinputs
      omega
  case throw =>
    have parts := callRef_vals_plain_parts [] address function.type _ _
      (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  case structNew =>
    have parts := callRef_vals_plain_parts [] address function.type _ _
      (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  case arrayNewFixed =>
    have parts := callRef_vals_plain_parts [] address function.type _ _
      (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  all_goals
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals, Wasm.Core.ValTypes.ofList]

theorem oneArg_addr_callRef_read_rule
    (state : Wasm.Core.Exec.State) (argument : Wasm.Core.U32)
    (address : Wasm.Core.Exec.FuncAddr) (type : Wasm.Core.DefType)
    {rule : Wasm.Core.Exec.ReadRule}
    {target : List Wasm.Core.Exec.AdminInstr}
    (step : Wasm.Core.Exec.Step_readA state rule
      (Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
        [.addrref (.funcAddr address), .plain (.callRef (.defd type))])
      target) :
    rule = .callRefFunc := by
  obtain ⟨unindexedSource, unindexedTarget, hsource', htarget',
      unindexedStep⟩ := step.unindexSourceTarget
  have hsource :
      Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
          [.addrref (.funcAddr address), .plain (.callRef (.defd type))] =
        unindexedSource := hsource'.symm
  clear step hsource' htarget'
  induction unindexedStep <;>
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals]
  case block =>
    have parts := callRef_vals_plain_parts
      [.num ⟨.i32, argument⟩] address type _ _ hsource rfl
    cases parts.2
  case loop =>
    have parts := callRef_vals_plain_parts
      [.num ⟨.i32, argument⟩] address type _ _ hsource rfl
    cases parts.2
  case throwRefInstrs =>
    have instruction := callRef_vals_addrref_plain_instruction
      [.num ⟨.i32, argument⟩] address type _ _ _ _
        (by simpa [List.append_assoc] using hsource) rfl
    cases instruction
  case tryTable =>
    have parts := callRef_vals_plain_parts
      [.num ⟨.i32, argument⟩] address type _ _ hsource rfl
    cases parts.2

theorem oneArg_addr_callRef_no_step
    (state : Wasm.Core.Exec.State) (argument : Wasm.Core.U32)
    (address : Wasm.Core.Exec.FuncAddr)
    (function : Wasm.Core.Exec.FuncInst)
    (hfunction : state.funcinst[address]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32])))
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config} :
    ¬ Wasm.Core.Exec.StepA
      (state,
        Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
          [.addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))]) event next := by
  intro step
  obtain ⟨unindexedSource, unindexedEvent, unindexedTarget,
      hsource', hevent', htarget', unindexedStep⟩ :=
    step.unindexSourceEventTarget
  have hsource :
      (state,
        Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
          [.addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))]) = unindexedSource :=
    hsource'.symm
  clear step hsource' hevent' htarget'
  induction unindexedStep generalizing state
  case ctxtInstrs z z' values inner inner' post ev innerStep
      contextNonempty ih =>
    have hstate := (Prod.mk.inj hsource).1
    subst state
    have hinstructions := (Prod.mk.inj hsource).2
    cases values with
    | nil =>
        change [.plain (.const .i32 argument),
          .addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] = inner ++ post
            at hinstructions
        cases inner with
        | nil => exact probe_nil_no_step z innerStep
        | cons first rest =>
            simp only [List.cons_append, List.cons.injEq] at hinstructions
            have hfirst : first = .plain (.const .i32 argument) :=
              hinstructions.1.symm
            subst first
            cases rest with
            | nil =>
                apply callPrefixInert_no_step z [.plain (.const .i32 argument)]
                · intro instruction membership
                  simp_all [callPrefixInert]
                · exact innerStep
            | cons second rest =>
                simp only [List.cons_append, List.cons.injEq] at hinstructions
                have hsecond : second = .addrref (.funcAddr address) :=
                  hinstructions.2.1.symm
                subst second
                cases rest with
                | nil =>
                    apply callPrefixInert_no_step z
                      [.plain (.const .i32 argument),
                        .addrref (.funcAddr address)]
                    · intro instruction membership
                      rcases List.mem_cons.mp membership with h | h
                      · subst instruction
                        rfl
                      · have h := List.mem_singleton.mp h
                        subst instruction
                        rfl
                    · exact innerStep
                | cons third rest =>
                    simp only [List.cons_append, List.cons.injEq]
                      at hinstructions
                    have hempty :=
                      List.append_eq_nil_iff.mp hinstructions.2.2.2.symm
                    exact contextNonempty.elim (fun h => h rfl)
                      (fun h => h hempty.2)
    | cons first restValues =>
        change [.plain (.const .i32 argument),
          .addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] =
            first.toAdmin ::
              (Wasm.Core.Exec.vals restValues ++ inner ++ post)
                at hinstructions
        have htail := (List.cons.inj hinstructions).2
        cases restValues with
        | nil =>
            change [.addrref (.funcAddr address),
              .plain (.callRef (.defd function.type))] = inner ++ post
                at htail
            cases inner with
            | nil => exact probe_nil_no_step z innerStep
            | cons instruction rest =>
                simp only [List.cons_append, List.cons.injEq] at htail
                have hinstruction : instruction =
                    .addrref (.funcAddr address) := htail.1.symm
                subst instruction
                cases rest with
                | nil =>
                    apply callPrefixInert_no_step z
                      [.addrref (.funcAddr address)]
                    · intro instruction membership
                      simp_all [callPrefixInert]
                    · exact innerStep
                | cons instruction rest =>
                    simp only [List.cons_append, List.cons.injEq] at htail
                    have hinstruction : instruction =
                        .plain (.callRef (.defd function.type)) :=
                      htail.2.1.symm
                    subst instruction
                    have hempty := List.append_eq_nil_iff.mp htail.2.2.symm
                    rcases hempty with ⟨rfl, rfl⟩
                    exact addr_callRef_no_step z address function
                      hfunction htype innerStep
        | cons second restValues =>
            change [.addrref (.funcAddr address),
              .plain (.callRef (.defd function.type))] =
                second.toAdmin ::
                  (Wasm.Core.Exec.vals restValues ++ inner ++ post) at htail
            have htail' := (List.cons.inj htail).2
            cases restValues with
            | nil =>
                change [.plain (.callRef (.defd function.type))] =
                    inner ++ post at htail'
                cases inner with
                | nil => exact probe_nil_no_step z innerStep
                | cons instruction rest =>
                    simp only [List.cons_append, List.cons.injEq] at htail'
                    have hinstruction : instruction =
                        .plain (.callRef (.defd function.type)) :=
                      htail'.1.symm
                    subst instruction
                    have hempty := List.append_eq_nil_iff.mp htail'.2.symm
                    rcases hempty with ⟨rfl, rfl⟩
                    exact callRef_only_no_step z function.type innerStep
            | cons third restValues =>
                change [.plain (.callRef (.defd function.type))] =
                  third.toAdmin ::
                    (Wasm.Core.Exec.vals restValues ++ inner ++ post) at htail'
                exact (valueAdmin_ne_nonvalue third
                  (.plain (.callRef (.defd function.type))) rfl
                  (List.cons.inj htail').1.symm).elim
  case pure membership =>
    rw [← (Prod.mk.inj hsource).2] at membership
    unfold Wasm.Core.Exec.pureSuccessors at membership
    rw [show
      Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
          [.addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))] =
        Wasm.Core.Exec.vals
          [.num ⟨.i32, argument⟩, .ref (.addr (.funcAddr address))] ++
          [.plain (.callRef (.defd function.type))] by rfl,
      Wasm.Core.Exec.splitVals_vals_append_nonval
        [.num ⟨.i32, argument⟩, .ref (.addr (.funcAddr address))]
        rfl []] at membership
    simp [Wasm.Core.Exec.pureOfSplit, Wasm.Core.Exec.pureOfInstr]
      at membership
  case read readStep =>
    rw [← (Prod.mk.inj hsource).1,
      ← (Prod.mk.inj hsource).2] at readStep
    have ruleEquality := oneArg_addr_callRef_read_rule state argument address
      function.type readStep
    obtain ⟨unindexedReadSource, unindexedReadTarget,
        hreadSource', hreadTarget', unindexedReadStep⟩ :=
      readStep.unindexSourceTarget
    have hreadSource :
        Wasm.Core.Exec.vals [.num ⟨.i32, argument⟩] ++
            [.addrref (.funcAddr address),
              .plain (.callRef (.defd function.type))] =
          unindexedReadSource := hreadSource'.symm
    clear readStep hreadSource' hreadTarget'
    induction unindexedReadStep
    case callRefFunc =>
      rename_i _ _ _ _ values targetAddress typeUse targetFunction fn
        inputs outputs argumentCount resultCount targetFrame hlookup hexpand
        hinputs houtputs hvalues hcode hframe
      have hstate := (Prod.mk.inj hsource).1
      subst state
      have sourceEquality := hreadSource
      have lengths := congrArg List.length sourceEquality
      have hvaluesLength : values.length = 1 := by
        simp [Wasm.Core.Exec.vals] at lengths
        omega
      cases values with
      | nil => simp at hvaluesLength
      | cons value rest =>
          cases rest with
          | cons value' rest => simp at hvaluesLength
          | nil =>
              simp [Wasm.Core.Exec.vals, Wasm.Core.Exec.Val.toAdmin,
                Wasm.Core.Exec.Ref.toAdmin,
                Wasm.Core.Exec.Val.toAdmin_eq_iff] at sourceEquality
              have htargetAddress : targetAddress = address :=
                sourceEquality.2.1.symm
              subst targetAddress
              have htargetFunction : targetFunction = function := by
                exact Option.some.inj (hlookup.symm.trans hfunction)
              subst targetFunction
              cases hexpand with
              | mk hexpand =>
              have hinputTypes : inputs =
                  Wasm.Core.ValTypes.ofList [.num .i32, .num .i32] := by
                have hcomp := Option.some.inj (hexpand.symm.trans htype)
                injection hcomp
              rw [hinputTypes] at hinputs
              simp [Wasm.Core.ValTypes.ofList, Wasm.Core.ValTypes.length]
                at hinputs
              omega
    all_goals
      simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
        Wasm.Core.Exec.vals, Wasm.Core.ValTypes.ofList]
  case throw =>
    have parts := callRef_vals_plain_parts [.num ⟨.i32, argument⟩]
      address function.type _ _ (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  case structNew =>
    have parts := callRef_vals_plain_parts [.num ⟨.i32, argument⟩]
      address function.type _ _ (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  case arrayNewFixed =>
    have parts := callRef_vals_plain_parts [.num ⟨.i32, argument⟩]
      address function.type _ _ (by simpa using (Prod.mk.inj hsource).2) rfl
    cases parts.2
  all_goals
    simp_all [Wasm.Core.Exec.Val.toAdmin, Wasm.Core.Exec.Ref.toAdmin,
      Wasm.Core.Exec.vals, Wasm.Core.ValTypes.ofList]

/-- A Core instruction context cannot select a proper subterm of the emitted
two-argument `call_ref`.  Any such selected subterm either contains only the
inert value prefix or reaches the call with fewer than its two required
arguments. -/
theorem callRefPair_no_proper_substep
    (state : Wasm.Core.Exec.State) (first second : Wasm.Core.U32)
    (address : Wasm.Core.Exec.FuncAddr)
    (function : Wasm.Core.Exec.FuncInst)
    (hfunction : state.funcinst[address]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32])))
    (preValues : List Wasm.Core.Exec.Val)
    (inner post : List Wasm.Core.Exec.AdminInstr)
    (hsource :
      Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address),
          .plain (.callRef (.defd function.type))] =
        Wasm.Core.Exec.vals preValues ++ inner ++ post)
    (hnonempty : preValues ≠ [] ∨ post ≠ [])
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (step : Wasm.Core.Exec.StepA (state, inner) event next) : False := by
  change [.plain (.const .i32 first), .plain (.const .i32 second),
      .addrref (.funcAddr address),
      .plain (.callRef (.defd function.type))] =
    Wasm.Core.Exec.vals preValues ++ inner ++ post at hsource
  cases preValues with
  | nil =>
      change [.plain (.const .i32 first), .plain (.const .i32 second),
        .addrref (.funcAddr address),
        .plain (.callRef (.defd function.type))] = inner ++ post at hsource
      cases inner with
      | nil => exact probe_nil_no_step state step
      | cons instruction rest =>
          simp only [List.cons_append, List.cons.injEq] at hsource
          have hinstruction : instruction = .plain (.const .i32 first) :=
            hsource.1.symm
          subst instruction
          cases rest with
          | nil =>
              apply callPrefixInert_no_step state [.plain (.const .i32 first)]
              · intro instruction membership
                have h := List.mem_singleton.mp membership
                subst instruction
                rfl
              · exact step
          | cons instruction rest =>
              simp only [List.cons_append, List.cons.injEq] at hsource
              have hinstruction : instruction = .plain (.const .i32 second) :=
                hsource.2.1.symm
              subst instruction
              cases rest with
              | nil =>
                  apply callPrefixInert_no_step state
                    [.plain (.const .i32 first), .plain (.const .i32 second)]
                  · intro instruction membership
                    rcases List.mem_cons.mp membership with h | h
                    · subst instruction
                      rfl
                    · have h := List.mem_singleton.mp h
                      subst instruction
                      rfl
                  · exact step
              | cons instruction rest =>
                  simp only [List.cons_append, List.cons.injEq] at hsource
                  have hinstruction : instruction = .addrref (.funcAddr address) :=
                    hsource.2.2.1.symm
                  subst instruction
                  cases rest with
                  | nil =>
                      apply callPrefixInert_no_step state
                        [.plain (.const .i32 first), .plain (.const .i32 second),
                          .addrref (.funcAddr address)]
                      · intro instruction membership
                        rcases List.mem_cons.mp membership with h | h
                        · subst instruction
                          rfl
                        · rcases List.mem_cons.mp h with h | h
                          · subst instruction
                            rfl
                          · have h := List.mem_singleton.mp h
                            subst instruction
                            rfl
                      · exact step
                  | cons instruction rest =>
                      simp only [List.cons_append, List.cons.injEq] at hsource
                      have hempty :=
                        List.append_eq_nil_iff.mp hsource.2.2.2.2.symm
                      exact hnonempty.elim (fun h => h rfl)
                        (fun h => h hempty.2)
  | cons firstValue restValues =>
      change [.plain (.const .i32 first), .plain (.const .i32 second),
        .addrref (.funcAddr address),
        .plain (.callRef (.defd function.type))] =
          firstValue.toAdmin ::
            (Wasm.Core.Exec.vals restValues ++ inner ++ post) at hsource
      have htail := (List.cons.inj hsource).2
      cases restValues with
      | nil =>
          change [.plain (.const .i32 second), .addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))] = inner ++ post at htail
          cases inner with
          | nil => exact probe_nil_no_step state step
          | cons instruction rest =>
              simp only [List.cons_append, List.cons.injEq] at htail
              have hinstruction : instruction = .plain (.const .i32 second) :=
                htail.1.symm
              subst instruction
              cases rest with
              | nil =>
                  apply callPrefixInert_no_step state [.plain (.const .i32 second)]
                  · intro instruction membership
                    have h := List.mem_singleton.mp membership
                    subst instruction
                    rfl
                  · exact step
              | cons instruction rest =>
                  simp only [List.cons_append, List.cons.injEq] at htail
                  have hinstruction : instruction = .addrref (.funcAddr address) :=
                    htail.2.1.symm
                  subst instruction
                  cases rest with
                  | nil =>
                      apply callPrefixInert_no_step state
                        [.plain (.const .i32 second), .addrref (.funcAddr address)]
                      · intro instruction membership
                        rcases List.mem_cons.mp membership with h | h
                        · subst instruction
                          rfl
                        · have h := List.mem_singleton.mp h
                          subst instruction
                          rfl
                      · exact step
                  | cons instruction rest =>
                      simp only [List.cons_append, List.cons.injEq] at htail
                      have hinstruction : instruction =
                          .plain (.callRef (.defd function.type)) :=
                        htail.2.2.1.symm
                      subst instruction
                      have hempty := List.append_eq_nil_iff.mp htail.2.2.2.symm
                      rcases hempty with ⟨rfl, rfl⟩
                      exact oneArg_addr_callRef_no_step state second address
                        function hfunction htype step
      | cons secondValue restValues =>
          change [.plain (.const .i32 second), .addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))] =
              secondValue.toAdmin ::
                (Wasm.Core.Exec.vals restValues ++ inner ++ post) at htail
          have htail' := (List.cons.inj htail).2
          cases restValues with
          | nil =>
              change [.addrref (.funcAddr address),
                .plain (.callRef (.defd function.type))] = inner ++ post
                  at htail'
              cases inner with
              | nil => exact probe_nil_no_step state step
              | cons instruction rest =>
                  simp only [List.cons_append, List.cons.injEq] at htail'
                  have hinstruction : instruction = .addrref (.funcAddr address) :=
                    htail'.1.symm
                  subst instruction
                  cases rest with
                  | nil =>
                      apply callPrefixInert_no_step state
                        [.addrref (.funcAddr address)]
                      · intro instruction membership
                        have h := List.mem_singleton.mp membership
                        subst instruction
                        rfl
                      · exact step
                  | cons instruction rest =>
                      simp only [List.cons_append, List.cons.injEq] at htail'
                      have hinstruction : instruction =
                          .plain (.callRef (.defd function.type)) :=
                        htail'.2.1.symm
                      subst instruction
                      have hempty := List.append_eq_nil_iff.mp htail'.2.2.symm
                      rcases hempty with ⟨rfl, rfl⟩
                      exact addr_callRef_no_step state address function
                        hfunction htype step
          | cons thirdValue restValues =>
              change [.addrref (.funcAddr address),
                .plain (.callRef (.defd function.type))] =
                  thirdValue.toAdmin ::
                    (Wasm.Core.Exec.vals restValues ++ inner ++ post) at htail'
              have htail'' := (List.cons.inj htail').2
              cases restValues with
              | nil =>
                  change [.plain (.callRef (.defd function.type))] =
                      inner ++ post at htail''
                  cases inner with
                  | nil => exact probe_nil_no_step state step
                  | cons instruction rest =>
                      simp only [List.cons_append, List.cons.injEq] at htail''
                      have hinstruction : instruction =
                          .plain (.callRef (.defd function.type)) :=
                        htail''.1.symm
                      subst instruction
                      have hempty := List.append_eq_nil_iff.mp htail''.2.symm
                      rcases hempty with ⟨rfl, rfl⟩
                      exact callRef_only_no_step state function.type step
              | cons fourthValue restValues =>
                  change [.plain (.callRef (.defd function.type))] =
                    fourthValue.toAdmin ::
                      (Wasm.Core.Exec.vals restValues ++ inner ++ post)
                        at htail''
                  exact (valueAdmin_ne_nonvalue fourthValue
                    (.plain (.callRef (.defd function.type))) rfl
                    (List.cons.inj htail'').1.symm).elim

theorem callRefFunc_pair_step_target
    (state : Wasm.Core.Exec.State) (first second : Wasm.Core.U32)
    (address : Wasm.Core.Exec.FuncAddr)
    (function : Wasm.Core.Exec.FuncInst) (fn : Wasm.Core.Func)
    (hfunction : state.funcinst[address]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32])))
    (hcode : function.code = .func fn)
    {event : Wasm.Core.Exec.Event} {next : Wasm.Core.Exec.Config}
    (other : Wasm.Core.Exec.StepA
      (state,
        Wasm.Core.Exec.vals
          [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
          [.addrref (.funcAddr address),
           .plain (.callRef (.defd function.type))]) event next) :
    next =
      (state,
        [.frame 1
          { locals :=
              [some (Wasm.Core.Exec.Val.num ⟨.i32, first⟩),
               some (Wasm.Core.Exec.Val.num ⟨.i32, second⟩)] ++
                fn.locals.map
                  (fun declaration =>
                    Wasm.Core.Exec.default_ declaration.valtype)
            mod := function.mod }
          [.label 1 [] (Wasm.Core.Exec.plains fn.body.toList)]]) ∧
      Wasm.Core.Harness.coreTrapCause? event = none := by
  generalize hsource :
    (state,
      Wasm.Core.Exec.vals
        [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
        [.addrref (.funcAddr address),
         .plain (.callRef (.defd function.type))]) = source at other
  induction other <;>
    simp_all [Wasm.Core.Harness.coreTrapCause?, Wasm.Core.Exec.Val.toAdmin,
      Wasm.Core.Exec.Ref.toAdmin, Wasm.Core.Exec.vals,
      Wasm.Core.ValTypes.ofList]
  case ctxtInstrs z z' values inner inner' post ev innerStep nonempty =>
    exact (callRefPair_no_proper_substep z first second address function
      hfunction htype values inner post
      (by simpa [List.append_assoc] using hsource.2)
      nonempty innerStep).elim
  case pure membership =>
    rw [← hsource.2] at membership
    have sourceShape :
        Wasm.Core.Exec.vals
            [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
          [.addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))] =
        Wasm.Core.Exec.vals
            [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
              .ref (.addr (.funcAddr address))] ++
          [.plain (.callRef (.defd function.type))] := by
      rfl
    rw [show
      [Wasm.Core.Exec.AdminInstr.plain (.const .i32 first),
       Wasm.Core.Exec.AdminInstr.plain (.const .i32 second),
       .addrref (.funcAddr address),
       .plain (.callRef (.defd function.type))] =
        Wasm.Core.Exec.vals
            [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
              .ref (.addr (.funcAddr address))] ++
          [.plain (.callRef (.defd function.type))] by rfl,
      Wasm.Core.Exec.pureSuccessors_ofInstr
        [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩,
          .ref (.addr (.funcAddr address))]
        (.callRef (.defd function.type)) rfl] at membership
    simp [Wasm.Core.Exec.pureOfInstr] at membership
  case read readStep =>
    rw [← hsource.1, ← hsource.2] at readStep
    rw [← hsource.1] at hfunction
    have ruleEquality := callRefPair_read_rule state first second address
      function.type readStep
    rw [ruleEquality] at readStep ⊢
    have canonical : Wasm.Core.Exec.Step_readA state .callRefFunc
        (Wasm.Core.Exec.vals
            [.num ⟨.i32, first⟩, .num ⟨.i32, second⟩] ++
          [.addrref (.funcAddr address),
            .plain (.callRef (.defd function.type))])
        [.frame 1
          { locals :=
              [some (Wasm.Core.Exec.Val.num ⟨.i32, first⟩),
               some (Wasm.Core.Exec.Val.num ⟨.i32, second⟩)] ++
                fn.locals.map
                  (fun declaration =>
                    Wasm.Core.Exec.default_ declaration.valtype)
            mod := function.mod }
          [.label 1 [] (Wasm.Core.Exec.plains fn.body.toList)]] := by
      letI : Wasm.Core.Exec.ExecutionAuthority :=
        Wasm.Core.Exec.amendedExecutionAuthority
      apply Wasm.Core.Exec.Step_read.callRefFunc
        (Nm := Wasm.Core.Exec.releasedNumerics) (n := 2) (m := 1)
      · exact hfunction
      · exact .mk htype
      · rfl
      · rfl
      · rfl
      · exact hcode
      · rfl
    have targetEquality :=
      Wasm.Core.Exec.Step_readA.target_functional readStep canonical
    exact ⟨by simpa [hsource.2] using targetEquality, rfl⟩
  case throw =>
    have parts := callRefPair_vals_plain_parts first second address
      function.type _ _ hsource.2 rfl
    cases parts.2
  case structNew =>
    have parts := callRefPair_vals_plain_parts first second address
      function.type _ _ hsource.2 rfl
    cases parts.2
  case arrayNewFixed =>
    have parts := callRefPair_vals_plain_parts first second address
      function.type _ _ hsource.2 rfl
    cases parts.2

end WasmGemmGnaf.GNAF.DirectScalarRuntime
