/-
  Wasm/Soundness.lean --- progress and preservation for the modelled machine.

  Normative source: SPEC.md section 7.1, which fixes

      Halt    : Config → Outcome → Prop
      Trapped : Config → Trap → Prop
      Thrown  : Config → ExceptionValue → Prop

  together with `IsTerminal config ↔ halted ∨ trapped ∨ thrown`, and section
  7.3, which requires

      theorem validation_progress
          (hvalid : Wasm.DeclarativelyValid module)
          (hconfig : Wasm.ConfigInstantiates module config)
          (hwelltyped : Wasm.ConfigWellTyped config) :
        (∃ outcome, Wasm.Halt config outcome) ∨
        (∃ trap, Wasm.Trapped config trap) ∨
        (∃ exceptionValue, Wasm.Thrown config exceptionValue) ∨
        (Wasm.successors config).Nonempty

  ## What the invariant is

  `ConfigWellTyped` is the ordinary syntactic typing invariant of the machine of
  `Wasm/Step.lean`, stated in the *declarative* judgment of `Wasm/Validate.lean`
  (`InstrTyping` / `ExprTyping`), not in any new judgment invented here:

  * there is a validation context whose `numLocals` is the length of the frame's
    locals and whose `globals` has the length of the store's globals;
  * the control stack is well formed: each `CtrlEntry` records an operand height
    at or above the height of the entry outside it, its `cont` types at the
    relative height it was suspended at, and a `loop` entry's `body` types at
    `0 → 0` one label deeper;
  * the operand stack is the innermost entry's recorded height plus the current
    relative height, and the remaining `code` types at that relative height in a
    context whose label stack has exactly one entry per control-stack entry, all
    of result arity `0` --- which is what `checkInstr` gives a `block`, `loop` or
    `if` body of empty block type;
  * a frame that has an enclosing label must return to relative height `0`.

  Nothing in it mentions `Step`, `successors`, `Halt`, `Trapped`, `Thrown` or
  the status field, so it cannot smuggle the conclusion of `validation_progress`
  in as a hypothesis.  Three results pin that down rather than leaving it to be
  read off the definition:

  * it is preserved by every reduction rule (`validation_preservation`), and
    `ConfigInstantiates` is preserved too (`ConfigInstantiates.step`), so the
    pair is an invariant of whole runs and not of a single step;
  * it is established by the configuration the machine starts in
    (`initialConfig_configWellTyped`, and unconditionally when the module has no
    start function), so it is reachable rather than empty;
  * it is *not* the trivially true predicate: `not_configWellTyped_drop_empty`
    and `not_configWellTyped_call` exhibit configurations it rejects, the second
    being an instruction outside the modelled subset --- which is the reason
    `validation_progress` needs `hwelltyped` at all.

  ## Scope, stated exactly

  This is a soundness theorem about the **modelled** machine: the released
  executable subset listed in the header of `Wasm/Validate.lean` (scalar `i32`
  arithmetic, locals, globals, full-width `i32` memory access on memory 0,
  `memory.size`/`memory.grow`, `block`/`loop`/`if` of empty block type,
  `br`/`br_if`, `throw`, and the harness frame).  It is not a soundness theorem
  for Core 3.0: GC, SIMD, tables, calls, `i64` and floating point are outside
  the modelled machine entirely --- they have no typing rule, so the invariant
  excludes them, which is exactly why `hwelltyped` is load-bearing.

  One further restriction is forced by `Wasm/Step.lean` rather than chosen here,
  and is disclosed rather than hidden.  `Module.funcCtx` seeds a function body's
  label stack with the function's own result arity --- Core's "implicit
  outermost label" --- so `Wasm.validate` accepts a body that branches to it, a
  branch which *returns* from the function.  `Wasm/Step.lean` models no such
  rule: `br`/`br_if` reduce only through `Config.ctrl`, and the outermost
  function label has no `CtrlEntry`.  A configuration whose code branches to it
  is therefore genuinely stuck, and no invariant can prove progress for it.  The
  invariant below consequently gives the current frame exactly one label per
  entry of `Config.ctrl` and no more, which is precisely the statement that
  every branch targets a label the code opened itself.  `GemmFrameLocal` and
  `StartFrameLocal` name that condition at module level; the released compiler
  of `GNAF/Compile.lean` emits only `block`/`loop`-local branches, so the
  condition holds of the artifact this repository releases.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Step

set_option autoImplicit false

universe u

/-- A list is nonempty when it exhibits a member.

SPEC section 7.3 writes the fourth disjunct of `validation_progress` as
`(Wasm.successors config).Nonempty`.  Neither Lean core nor `Std` defines
`List.Nonempty`, so it is defined here in the sense SPEC intends: the successor
enumeration exhibits at least one successor.  Combined with
`Wasm.mem_successors_iff_step` that member *is* a reduction, which is what makes
the disjunct say "the configuration can still take a step". -/
protected def List.Nonempty {α : Type u} (l : List α) : Prop := ∃ x, x ∈ l

theorem List.nonempty_of_mem {α : Type u} {l : List α} {x : α} (h : x ∈ l) :
    l.Nonempty := ⟨x, h⟩

theorem List.nonempty_cons {α : Type u} (x : α) (l : List α) : (x :: l).Nonempty :=
  ⟨x, List.mem_cons_self⟩

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Small list facts used below -/

theorem lt_of_getElem?_eq_some {α : Type u} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hlt, _⟩
  exact hlt

theorem exists_getElem?_of_lt {α : Type u} {l : List α} {i : Nat}
    (h : i < l.length) : ∃ x, l[i]? = some x := by
  cases hv : l[i]? with
  | none => rw [List.getElem?_eq_none_iff] at hv; omega
  | some x => exact ⟨x, rfl⟩

theorem stack_cons {st : List UInt32} (h : 0 < st.length) :
    ∃ x ys, st = x :: ys := by
  match st with
  | [] => exact absurd h (by simp)
  | x :: ys => exact ⟨x, ys, rfl⟩

theorem stack_cons2 {st : List UInt32} (h : 1 < st.length) :
    ∃ x y ys, st = x :: y :: ys := by
  match st with
  | [] => exact absurd h (by simp)
  | [_] => exact absurd h (by simp)
  | x :: y :: ys => exact ⟨x, y, ys, rfl⟩

/-! ## The three terminal predicates of SPEC section 7.1

`Config.status` already distinguishes the three terminal outcomes; these are the
SPEC-named projections of it.  Every value of the released subset is an `i32`,
so the machine's `Outcome` type is `UInt32`. -/

/-- **SPEC section 7.1.**  The configuration has returned `outcome`. -/
def Halt (c : Config) (outcome : UInt32) : Prop := c.status = .returned outcome

/-- **SPEC section 7.1.**  The configuration has trapped. -/
def Trapped (c : Config) (trap : Trap) : Prop := c.status = .trapped trap

/-- **SPEC section 7.1.**  The configuration terminated with an uncaught
exception. -/
def Thrown (c : Config) (exceptionValue : ExceptionValue) : Prop :=
  c.status = .thrown exceptionValue

/-- **SPEC section 7.1.**  A configuration is terminal exactly when it has
halted, trapped, or thrown. -/
theorem isTerminal_iff_halt_trapped_thrown (c : Config) :
    c.IsTerminal ↔
      ((∃ outcome, Halt c outcome) ∨ (∃ trap, Trapped c trap) ∨
        (∃ exceptionValue, Thrown c exceptionValue)) :=
  c.isTerminal_iff

theorem Halt.isTerminal {c : Config} {outcome : UInt32} (h : Halt c outcome) :
    c.IsTerminal := by
  unfold Config.IsTerminal; rw [h]; simp

theorem Trapped.isTerminal {c : Config} {trap : Trap} (h : Trapped c trap) :
    c.IsTerminal := by
  unfold Config.IsTerminal; rw [h]; simp

theorem Thrown.isTerminal {c : Config} {exceptionValue : ExceptionValue}
    (h : Thrown c exceptionValue) : c.IsTerminal := by
  unfold Config.IsTerminal; rw [h]; simp

/-! ## The typing context of a running frame

`Wasm.Ctx.labels` records label *result arities*.  Every structured control form
of the released subset has empty block type, so every label a running frame can
have open has arity `0`; a frame `depth` labels deep therefore types its code in
a context whose label stack is `List.replicate depth 0`. -/

/-- The validation context of a frame with `numLocals` locals, `globals` global
types, `numTags` tags, and `depth` enclosing labels. -/
def frameCtx (numLocals : Nat) (globals : List GlobalType) (numTags depth : Nat) :
    Ctx :=
  { numLocals := numLocals, globals := globals, numTags := numTags
    labels := List.replicate depth 0 }

@[simp] theorem frameCtx_numLocals (nl : Nat) (G : List GlobalType) (nt d : Nat) :
    (frameCtx nl G nt d).numLocals = nl := rfl

@[simp] theorem frameCtx_globals (nl : Nat) (G : List GlobalType) (nt d : Nat) :
    (frameCtx nl G nt d).globals = G := rfl

@[simp] theorem frameCtx_numTags (nl : Nat) (G : List GlobalType) (nt d : Nat) :
    (frameCtx nl G nt d).numTags = nt := rfl

@[simp] theorem frameCtx_labels (nl : Nat) (G : List GlobalType) (nt d : Nat) :
    (frameCtx nl G nt d).labels = List.replicate d 0 := rfl

/-- Opening one more label is exactly stepping the depth: this is the context in
which `InstrTyping.block`, `.loop` and `.ifThenElse` type their bodies. -/
theorem frameCtx_succ (nl : Nat) (G : List GlobalType) (nt d : Nat) :
    ({ frameCtx nl G nt d with
        labels := 0 :: (frameCtx nl G nt d).labels } : Ctx) = frameCtx nl G nt (d + 1) := by
  simp [frameCtx, List.replicate_succ]

/-- A branch target of a running frame names one of the frame's own labels, and
every such label has result arity `0`. -/
theorem frameCtx_label {nl : Nat} {G : List GlobalType} {nt d n x : Nat}
    (h : (frameCtx nl G nt d).labels[n]? = some x) : n < d ∧ x = 0 := by
  rw [frameCtx_labels, List.getElem?_replicate] at h
  by_cases hn : n < d
  · rw [if_pos hn] at h
    exact ⟨hn, by injection h with h; exact h.symm⟩
  · rw [if_neg hn] at h; exact absurd h (by simp)

/-! ## The well-typedness invariant -/

/-- The control stack is well formed.  The second index is the absolute operand
height of the innermost frame: `0` for the function frame, and the recorded
`height` of the innermost label otherwise.

`hcont` types the suspended continuation at the relative height it was suspended
at, one label shallower; `hexit` records that a frame with an enclosing label
must return to relative height `0`, which is Core's `pop_ctrl` check for an
empty block type; `hbody` types a `loop`'s body, which a branch to that label
re-enters. -/
inductive CtrlOk (nl : Nat) (G : List GlobalType) (nt : Nat) :
    List CtrlEntry → Nat → Prop
  | nil : CtrlOk nl G nt [] 0
  | cons {k : CtrlEntry} {ks : List CtrlEntry} {base final : Nat}
      (htail : CtrlOk nl G nt ks base)
      (hbase : base ≤ k.height)
      (hcont : ExprTyping (frameCtx nl G nt ks.length) (k.height - base)
        (Expr.ofList k.cont) final)
      (hexit : ks ≠ [] → final = 0)
      (hbody : k.isLoop = true →
        ExprTyping (frameCtx nl G nt (ks.length + 1)) 0 (Expr.ofList k.body) 0) :
      CtrlOk nl G nt (k :: ks) k.height

/-- The well-typedness invariant, relative to a choice of global types `G` and
tag count `nt`. -/
def ConfigWellTypedIn (c : Config) (G : List GlobalType) (nt : Nat) : Prop :=
  G.length = c.store.globals.length ∧
  ∃ base rel final : Nat,
    CtrlOk c.locals.length G nt c.ctrl base ∧
    c.stack.length = base + rel ∧
    ExprTyping (frameCtx c.locals.length G nt c.ctrl.length) rel
      (Expr.ofList c.code) final ∧
    (c.ctrl ≠ [] → final = 0)

/-- **SPEC section 7.3.**  The configuration is well typed. -/
def ConfigWellTyped (c : Config) : Prop := ∃ G nt, ConfigWellTypedIn c G nt

/-- The invariant does not see the status field, so a rule that only terminates
the configuration preserves it. -/
theorem ConfigWellTypedIn.status {c : Config} {G : List GlobalType} {nt : Nat}
    (h : ConfigWellTypedIn c G nt) (s : Status) :
    ConfigWellTypedIn { c with status := s } G nt := h

/-! ## Instantiation -/

/-- The context in which the exported `gemm` body is typed once the harness has
entered it: the two ABI parameters plus the function's declared locals, the
module's globals and tags, and no enclosing label. -/
def gemmEntryCtx (m : Module) (numGemmLocals : Nat) : Ctx :=
  frameCtx (2 + numGemmLocals) (m.globals.map (·.type)) m.tags.length 0

/-- **SPEC section 7.3.**  The configuration arises from `m`: its store carries
the module's globals, and its harness is the module's exported `gemm` --- its
body, its local count, and its two ABI arguments --- typed in the context the
harness enters it in. -/
def ConfigInstantiates (m : Module) (c : Config) : Prop :=
  c.store.globals.length = m.globals.length ∧
  c.harness.args.length = 2 ∧
  (∃ gi f, Module.gemmIndex? m = some gi ∧ m.funcs[gi]? = some f ∧
    c.harness.gemmBody = Func.code f ∧ c.harness.gemmNumLocals = f.locals.length) ∧
  (∃ final, ExprTyping (gemmEntryCtx m c.harness.gemmNumLocals) 0
    (Expr.ofList c.harness.gemmBody) final)

/-- The exported `gemm` body branches only to labels it opens itself: it types
with an empty enclosing label stack.  See the header for why the modelled
machine needs this and `Wasm.validate` alone does not give it. -/
def GemmFrameLocal (m : Module) : Prop :=
  ∃ gi f final, Module.gemmIndex? m = some gi ∧ m.funcs[gi]? = some f ∧
    ExprTyping (gemmEntryCtx m f.locals.length) 0 f.body final

/-- The module's start function, if it has one, branches only to labels it opens
itself. -/
def StartFrameLocal (m : Module) : Prop :=
  ∀ si f, m.start = some si → m.funcs[si]? = some f →
    ∃ final, ExprTyping
      (frameCtx f.locals.length (m.globals.map (·.type)) m.tags.length 0) 0 f.body final

/-- A module with no start function satisfies the start-frame condition
vacuously. -/
theorem startFrameLocal_of_start_none {m : Module} (h : m.start = none) :
    StartFrameLocal m := by
  intro si f hsi _
  rw [h] at hsi
  exact absurd hsi (by simp)

/-! ## Store facts -/

theorem Store.storeBytes_globals {s s' : Store} {a : Nat} {vs : List UInt8}
    (h : s.storeBytes a vs = some s') : s'.globals = s.globals := by
  unfold Store.storeBytes at h
  cases hm : s.memory.storeBytes a vs with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some mm =>
    rw [hm] at h
    simp only [Option.map_some] at h
    injection h with h
    subst h
    rfl

theorem Store.allocGlobals_length : ∀ {gs : List Global} {is : List GlobalInst},
    Store.allocGlobals gs = some is → is.length = gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro is h
    unfold Store.allocGlobals at h
    injection h with h
    subst h
    rfl
  | cons g gs ih =>
    intro is h
    unfold Store.allocGlobals at h
    cases hv : Store.constValue? g.init with
    | none => rw [hv] at h; exact absurd h (by simp)
    | some v =>
      cases hr : Store.allocGlobals gs with
      | none => rw [hv, hr] at h; exact absurd h (by simp)
      | some rest =>
        rw [hv, hr] at h
        injection h with h
        subst h
        simp [ih hr]

theorem Store.alloc_globals_length {m : Module} {s : Store}
    (h : Store.alloc m = some s) : s.globals.length = m.globals.length := by
  unfold Store.alloc at h
  split at h
  · cases hg : Store.allocGlobals m.globals with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some gs =>
      rw [hg] at h
      simp only [Option.map_some] at h
      injection h with h
      subst h
      exact Store.allocGlobals_length hg
  · exact absurd h (by simp)

/-! ## Reduction leaves the harness and the global count alone -/

theorem Step.harness_eq {c : Config} {e : Event} {c' : Config} (h : Step c e c') :
    c'.harness = c.harness := by
  cases h <;> rfl

theorem Step.globals_length {c : Config} {e : Event} {c' : Config} (h : Step c e c') :
    c'.store.globals.length = c.store.globals.length := by
  cases h with
  | globalSet _ _ _ _ => exact List.length_set
  | store _ _ _ hb => rw [Store.storeBytes_globals hb]
  | enterGemm _ _ _ _ hi => rw [Store.storeBytes_globals hi]
  | _ => rfl

/-- `ConfigInstantiates` is itself preserved by reduction, so the pair
`(ConfigInstantiates, ConfigWellTyped)` is an invariant of whole runs rather
than of a single step. -/
theorem ConfigInstantiates.step {m : Module} {c : Config} {e : Event} {c' : Config}
    (hstep : Step c e c') (h : ConfigInstantiates m c) : ConfigInstantiates m c' := by
  obtain ⟨hg, ha, hgi, ht⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep.globals_length]; exact hg
  · rw [hstep.harness_eq]; exact ha
  · rw [hstep.harness_eq]; exact hgi
  · rw [hstep.harness_eq]; exact ht

/-! ## Reading a branch target out of the control stack -/

/-- A branch to label `n` lands on a well-formed suspended frame: the labels
outside it are still well formed, its recorded height is between theirs and the
current one, its continuation is typed, and if it is a `loop` its body is. -/
theorem CtrlOk.get {nl : Nat} {G : List GlobalType} {nt : Nat}
    {ks : List CtrlEntry} {base : Nat} (h : CtrlOk nl G nt ks base) :
    ∀ {n : Nat} {k : CtrlEntry}, ks[n]? = some k →
      ∃ base' final,
        CtrlOk nl G nt (ks.drop (n + 1)) base' ∧
        base' ≤ k.height ∧ k.height ≤ base ∧
        ExprTyping (frameCtx nl G nt (ks.drop (n + 1)).length) (k.height - base')
          (Expr.ofList k.cont) final ∧
        (ks.drop (n + 1) ≠ [] → final = 0) ∧
        (k.isLoop = true →
          ExprTyping (frameCtx nl G nt ((ks.drop (n + 1)).length + 1)) 0
            (Expr.ofList k.body) 0) := by
  induction h with
  | nil => intro n k hk; simp at hk
  | @cons k' ks' base' final' htail hbase hcont hexit hbody ih =>
    intro n k hk
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨base', final', ?_, hbase, Nat.le_refl _, ?_, ?_, ?_⟩
      · simpa using htail
      · simpa using hcont
      · simpa using hexit
      · simpa using hbody
    | succ mm =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨b2, f2, hd, hle1, hle2, hct, hex, hbd⟩ := ih hk
      exact ⟨b2, f2, by simpa using hd, hle1, Nat.le_trans hle2 hbase,
        by simpa using hct, by simpa using hex, by simpa using hbd⟩

/-! ## Progress

Every case below is discharged by exhibiting a `Step` constructor.  The cases
that need no hypothesis at all --- an exhausted instruction sequence, a trap ---
are exactly the ones the machine can always take; the cases that need one take
it from the typing derivation, which is the load-bearing use of validation. -/

/-- **Progress, in the form the reduction relation states it.**  A running,
well-typed configuration reduces. -/
theorem exists_step_of_wellTyped {c : Config} (hrun : c.status = Status.running)
    (hwt : ConfigWellTyped c) : ∃ (e : Event) (c' : Config), Step c e c' := by
  obtain ⟨G, nt, hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
  cases hcode : c.code with
  | nil =>
    cases hk : c.ctrl with
    | cons k ks => exact ⟨_, _, Step.exitLabel hrun hcode hk⟩
    | nil =>
      cases hp : c.phase with
      | afterEntry => exact ⟨_, _, Step.returnGemm hrun hcode hk hp⟩
      | beforeEntry =>
        cases hi : c.store.storeBytes c.harness.rawPtr c.harness.rawBytes with
        | some s' => exact ⟨_, _, Step.enterGemm hrun hcode hk hp hi⟩
        | none => exact ⟨_, _, Step.installTrap hrun hcode hk hp hi⟩
  | cons i rest =>
    rw [hcode] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ h₂ _ _ _ hi _ =>
      cases hi with
      | unreachable => exact ⟨_, _, Step.unreachable hrun hcode⟩
      | nop => exact ⟨_, _, Step.nop hrun hcode⟩
      | i32Const => exact ⟨_, _, Step.i32Const hrun hcode⟩
      | @drop _ hh =>
        obtain ⟨x, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.drop hrun hcode hst⟩
      | @iBinOp _ hh op hop =>
        obtain ⟨b0, a0, st, hst⟩ := stack_cons2 (st := c.stack) (by omega)
        cases hv : evalIBinOp op a0 b0 with
        | none =>
          have := (evalIBinOp_isSome_iff op a0 b0).mpr hop
          rw [hv] at this
          exact absurd this (by simp)
        | some r =>
          cases r with
          | none => exact ⟨_, _, Step.iBinOpTrap hrun hcode hst hv⟩
          | some v => exact ⟨_, _, Step.iBinOp hrun hcode hst hv⟩
      | @iTestOp _ hh =>
        obtain ⟨x, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.iTestOp hrun hcode hst⟩
      | @iRelOp _ hh _ =>
        obtain ⟨b0, a0, st, hst⟩ := stack_cons2 (st := c.stack) (by omega)
        exact ⟨_, _, Step.iRelOp hrun hcode hst⟩
      | @localGet _ _ idx hidx =>
        rw [frameCtx_numLocals] at hidx
        obtain ⟨v, hv⟩ := exists_getElem?_of_lt hidx
        exact ⟨_, _, Step.localGet hrun hcode hv⟩
      | @localSet _ hh idx hidx =>
        rw [frameCtx_numLocals] at hidx
        obtain ⟨v, hv⟩ := exists_getElem?_of_lt hidx
        obtain ⟨x, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.localSet hrun hcode hst hv⟩
      | @localTee _ hh idx hidx =>
        rw [frameCtx_numLocals] at hidx
        obtain ⟨v, hv⟩ := exists_getElem?_of_lt hidx
        obtain ⟨x, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.localTee hrun hcode hst hv⟩
      | @globalGet _ _ idx g hg _ =>
        rw [frameCtx_globals] at hg
        have hlt : idx < c.store.globals.length := by
          rw [← hglen]; exact lt_of_getElem?_eq_some hg
        obtain ⟨g', hg'⟩ := exists_getElem?_of_lt hlt
        exact ⟨_, _, Step.globalGet hrun hcode hg'⟩
      | @globalSet _ hh idx g hg _ _ =>
        rw [frameCtx_globals] at hg
        have hlt : idx < c.store.globals.length := by
          rw [← hglen]; exact lt_of_getElem?_eq_some hg
        obtain ⟨g', hg'⟩ := exists_getElem?_of_lt hlt
        obtain ⟨x, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.globalSet hrun hcode hst hg'⟩
      | @load _ hh arg _ _ =>
        obtain ⟨a0, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        cases hb : c.store.loadBytes (a0.toNat + arg.offset) 4 with
        | some bs => exact ⟨_, _, Step.load hrun hcode hst hb⟩
        | none => exact ⟨_, _, Step.loadTrap hrun hcode hst hb⟩
      | @store _ hh arg _ _ =>
        obtain ⟨v, a0, st, hst⟩ := stack_cons2 (st := c.stack) (by omega)
        cases hb : c.store.storeBytes (a0.toNat + arg.offset) (u32ToBytes v) with
        | some s' => exact ⟨_, _, Step.store hrun hcode hst hb⟩
        | none => exact ⟨_, _, Step.storeTrap hrun hcode hst hb⟩
      | memorySize => exact ⟨_, _, Step.memorySize hrun hcode⟩
      | @memoryGrow _ hh =>
        obtain ⟨d, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.memoryGrowRefuse hrun hcode hst⟩
      | block => exact ⟨_, _, Step.block hrun hcode⟩
      | loop => exact ⟨_, _, Step.loop hrun hcode⟩
      | @ifThenElse _ hh _ _ _ _ =>
        obtain ⟨cnd, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        by_cases hcnd : cnd = 0
        · exact ⟨_, _, Step.ifFalse hrun hcode hst hcnd⟩
        · exact ⟨_, _, Step.ifTrue hrun hcode hst hcnd⟩
      | @br _ _ n hl =>
        obtain ⟨hn, _⟩ := frameCtx_label hl
        obtain ⟨k, hk⟩ := exists_getElem?_of_lt hn
        by_cases hloop : k.isLoop = true
        · exact ⟨_, _, Step.brLoop hrun hcode hk hloop⟩
        · exact ⟨_, _, Step.brBlock hrun hcode hk hloop⟩
      | @brIf _ hh n hl =>
        obtain ⟨hn, _⟩ := frameCtx_label hl
        obtain ⟨cnd, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        by_cases hcnd : cnd = 0
        · exact ⟨_, _, Step.brIfFalse hrun hcode hst hcnd⟩
        · obtain ⟨k, hk⟩ := exists_getElem?_of_lt hn
          by_cases hloop : k.isLoop = true
          · exact ⟨_, _, Step.brIfLoop hrun hcode hst hcnd hk hloop⟩
          · exact ⟨_, _, Step.brIfBlock hrun hcode hst hcnd hk hloop⟩
      | @throwTag _ hh tag _ =>
        obtain ⟨v, st, hst⟩ := stack_cons (st := c.stack) (by omega)
        exact ⟨_, _, Step.throwTag hrun hcode hst⟩

/-- A running, well-typed configuration has a successor in the enumeration. -/
theorem successors_nonempty_of_wellTyped {c : Config}
    (hrun : c.status = Status.running) (hwt : ConfigWellTyped c) :
    (successors c).Nonempty := by
  obtain ⟨e, c', hstep⟩ := exists_step_of_wellTyped hrun hwt
  exact List.nonempty_of_mem ((mem_successors_iff_step c e c').mpr hstep)

/-- **SPEC section 7.3, `Wasm.validation_progress`.**  A well-typed
configuration of a valid module has halted, trapped, thrown, or can still take a
step. -/
theorem validation_progress {module : Module} {config : Config}
    (hvalid : DeclarativelyValid module)
    (hconfig : ConfigInstantiates module config)
    (hwelltyped : ConfigWellTyped config) :
    (∃ outcome, Halt config outcome) ∨
    (∃ trap, Trapped config trap) ∨
    (∃ exceptionValue, Thrown config exceptionValue) ∨
    (successors config).Nonempty := by
  by_cases hrun : config.status = Status.running
  · exact Or.inr (Or.inr (Or.inr (successors_nonempty_of_wellTyped hrun hwelltyped)))
  · have hterm : config.IsTerminal := hrun
    rcases (isTerminal_iff_halt_trapped_thrown config).mp hterm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

/-! ## Preservation -/

/-- The invariant is preserved by any rule that keeps the control stack and the
frame, replaces the code by its tail, and moves the operand height by exactly
what the typing derivation of the head instruction says. -/
theorem wellTypedIn_tail {c c' : Config} {G : List GlobalType} {nt : Nat}
    {i : Instr} {rest : List Instr}
    (hwt : ConfigWellTypedIn c G nt)
    (hcode : c.code = i :: rest)
    (hcode' : c'.code = rest)
    (hctrl' : c'.ctrl = c.ctrl)
    (hloc' : c'.locals.length = c.locals.length)
    (hglob' : c'.store.globals.length = c.store.globals.length)
    (hdelta : ∀ bse r hnext : Nat, c.stack.length = bse + r →
      InstrTyping (frameCtx c.locals.length G nt c.ctrl.length) r i hnext →
      c'.stack.length = bse + hnext) :
    ConfigWellTypedIn c' G nt := by
  obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
  rw [hcode] at hchk
  simp only [Expr.ofList] at hchk
  cases hchk with
  | @cons _ _ h₂ _ _ _ hi he =>
    refine ⟨by rw [hglob']; exact hglen, base, h₂, final, ?_, ?_, ?_, ?_⟩
    · rw [hctrl', hloc']; exact hctrl
    · exact hdelta base rel h₂ hstack hi
    · rw [hcode', hctrl', hloc']; exact he
    · rw [hctrl']; exact hexit

/-- **Preservation.**  Every reduction of an instantiated, well-typed
configuration lands in a well-typed configuration. -/
theorem step_configWellTyped {m : Module} {c : Config} {e : Event} {c' : Config}
    (hstep : Step c e c') (hconfig : ConfigInstantiates m c)
    (hwt : ConfigWellTyped c) : ConfigWellTyped c' := by
  obtain ⟨G, nt, hwt⟩ := hwt
  cases hstep with
  | unreachable hs hc => exact ⟨G, nt, hwt.status _⟩
  | iBinOpTrap hs hc hst hv => exact ⟨G, nt, hwt.status _⟩
  | loadTrap hs hc hst hb => exact ⟨G, nt, hwt.status _⟩
  | storeTrap hs hc hst hb => exact ⟨G, nt, hwt.status _⟩
  | throwTag hs hc hst => exact ⟨G, nt, hwt.status _⟩
  | returnGemm hs hc hk hp => exact ⟨G, nt, hwt.status _⟩
  | installTrap hs hc hk hp hi => exact ⟨G, nt, hwt.status _⟩
  | nop hs hc =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    exact hsl
  | i32Const hs hc =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [List.length_cons]
    omega
  | drop hs hc hst =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | iBinOp hs hc hst hv =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | iTestOp hs hc hst =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | iRelOp hs hc hst =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | localGet hs hc hv =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [List.length_cons]
    omega
  | localSet hs hc hst hw =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl List.length_set rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | localTee hs hc hst hw =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl List.length_set rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    exact hsl
  | globalGet hs hc hg =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [List.length_cons]
    omega
  | globalSet hs hc hst hg =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl List.length_set ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | load hs hc hst hb =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | store hs hc hst hb =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl
      (by rw [Store.storeBytes_globals hb]) ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | memorySize hs hc =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [List.length_cons]
    omega
  | memoryGrowSucceed hs hc hst hg =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | memoryGrowRefuse hs hc hst =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | brIfFalse hs hc hst hcnd =>
    refine ⟨G, nt, wellTypedIn_tail hwt hc rfl rfl rfl rfl ?_⟩
    intro bse r hnext hsl hi
    cases hi
    simp only [hst, List.length_cons] at hsl ⊢
    omega
  | @block rest body hs hc =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ _ _ _ _ hi he =>
      cases hi with
      | @block _ _ _ hb =>
        rw [frameCtx_succ] at hb
        refine ⟨G, nt, hglen, c.stack.length, 0, 0, ?_, ?_, ?_, fun _ => rfl⟩
        · refine CtrlOk.cons hctrl (by show base ≤ c.stack.length; omega) ?_ hexit (by simp)
          show ExprTyping (frameCtx c.locals.length G nt c.ctrl.length)
            (c.stack.length - base) (Expr.ofList rest) final
          rw [show c.stack.length - base = rel by omega]
          exact he
        · simp
        · simpa using hb
  | @loop rest body hs hc =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ _ _ _ _ hi he =>
      cases hi with
      | @loop _ _ _ hb =>
        rw [frameCtx_succ] at hb
        refine ⟨G, nt, hglen, c.stack.length, 0, 0, ?_, ?_, ?_, fun _ => rfl⟩
        · refine CtrlOk.cons hctrl (by show base ≤ c.stack.length; omega) ?_ hexit
            (fun _ => ?_)
          · show ExprTyping (frameCtx c.locals.length G nt c.ctrl.length)
              (c.stack.length - base) (Expr.ofList rest) final
            rw [show c.stack.length - base = rel by omega]
            exact he
          · simpa using hb
        · simp
        · simpa using hb
  | @ifFalse rest thenBody elseBody cnd st hs hc hst hcnd =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ h₂ _ _ _ hi he =>
      cases hi with
      | @ifThenElse _ _ _ _ ht hel =>
        rw [frameCtx_succ] at ht hel
        have hstl : st.length = base + h₂ := by
          rw [hst] at hstack; simp only [List.length_cons] at hstack; omega
        refine ⟨G, nt, hglen, st.length, 0, 0, ?_, ?_, ?_, fun _ => rfl⟩
        · refine CtrlOk.cons hctrl (by show base ≤ st.length; omega) ?_ hexit (by simp)
          show ExprTyping (frameCtx c.locals.length G nt c.ctrl.length)
            (st.length - base) (Expr.ofList rest) final
          rw [show st.length - base = h₂ by omega]
          exact he
        · simp
        · simpa using hel
  | @ifTrue rest thenBody elseBody cnd st hs hc hst hcnd =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ h₂ _ _ _ hi he =>
      cases hi with
      | @ifThenElse _ _ _ _ ht hel =>
        rw [frameCtx_succ] at ht hel
        have hstl : st.length = base + h₂ := by
          rw [hst] at hstack; simp only [List.length_cons] at hstack; omega
        refine ⟨G, nt, hglen, st.length, 0, 0, ?_, ?_, ?_, fun _ => rfl⟩
        · refine CtrlOk.cons hctrl (by show base ≤ st.length; omega) ?_ hexit (by simp)
          show ExprTyping (frameCtx c.locals.length G nt c.ctrl.length)
            (st.length - base) (Expr.ofList rest) final
          rw [show st.length - base = h₂ by omega]
          exact he
        · simp
        · simpa using ht
  | @brLoop rest n k hs hc hk hl =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ _ _ _ _ hi he =>
      cases hi with
      | @br _ _ _ hlab =>
        obtain ⟨hn, hz⟩ := frameCtx_label hlab
        obtain ⟨base', final', htail, hb1, hb2, hcont, hex, hbody⟩ := hctrl.get hk
        refine ⟨G, nt, hglen, k.height, 0, 0,
          CtrlOk.cons htail hb1 hcont hex hbody, ?_, ?_, fun _ => rfl⟩
        · show (truncStack c.stack k.height).length = k.height + 0
          rw [truncStack_length (by omega)]
          omega
        · simpa using hbody hl
  | @brBlock rest n k hs hc hk hl =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ _ _ _ _ hi he =>
      cases hi with
      | @br _ _ _ hlab =>
        obtain ⟨hn, hz⟩ := frameCtx_label hlab
        obtain ⟨base', final', htail, hb1, hb2, hcont, hex, hbody⟩ := hctrl.get hk
        refine ⟨G, nt, hglen, base', k.height - base', final', htail, ?_, hcont, hex⟩
        show (truncStack c.stack k.height).length = base' + (k.height - base')
        rw [truncStack_length (by omega)]
        omega
  | @brIfLoop rest n cnd st k hs hc hst hcnd hk hl =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ h₂ _ _ _ hi he =>
      cases hi with
      | @brIf _ _ _ hlab =>
        obtain ⟨hn, hz⟩ := frameCtx_label hlab
        obtain ⟨base', final', htail, hb1, hb2, hcont, hex, hbody⟩ := hctrl.get hk
        have hstl : st.length = base + h₂ := by
          rw [hst] at hstack; simp only [List.length_cons] at hstack; omega
        refine ⟨G, nt, hglen, k.height, 0, 0,
          CtrlOk.cons htail hb1 hcont hex hbody, ?_, ?_, fun _ => rfl⟩
        · show (truncStack st k.height).length = k.height + 0
          rw [truncStack_length (by omega)]
          omega
        · simpa using hbody hl
  | @brIfBlock rest n cnd st k hs hc hst hcnd hk hl =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | @cons _ _ h₂ _ _ _ hi he =>
      cases hi with
      | @brIf _ _ _ hlab =>
        obtain ⟨hn, hz⟩ := frameCtx_label hlab
        obtain ⟨base', final', htail, hb1, hb2, hcont, hex, hbody⟩ := hctrl.get hk
        have hstl : st.length = base + h₂ := by
          rw [hst] at hstack; simp only [List.length_cons] at hstack; omega
        refine ⟨G, nt, hglen, base', k.height - base', final', htail, ?_, hcont, hex⟩
        show (truncStack st k.height).length = base' + (k.height - base')
        rw [truncStack_length (by omega)]
        omega
  | @exitLabel k ks hs hc hk =>
    obtain ⟨hglen, base, rel, final, hctrl, hstack, hchk, hexit⟩ := hwt
    rw [hc] at hchk
    simp only [Expr.ofList] at hchk
    cases hchk with
    | nil =>
      have hrel : rel = 0 := hexit (by rw [hk]; simp)
      rw [hk] at hctrl
      cases hctrl with
      | @cons _ _ base' final' htail hbase hcont hex hbody =>
        refine ⟨G, nt, hglen, base', k.height - base', final', htail, ?_, hcont, hex⟩
        show c.stack.length = base' + (k.height - base')
        omega
  | @enterGemm s' hs hc hk hp hi =>
    obtain ⟨hcg, hca, hcgi, fin, hcty⟩ := hconfig
    refine ⟨m.globals.map (·.type), m.tags.length, ?_, 0, 0, fin, CtrlOk.nil, rfl,
      ?_, fun hne => absurd rfl hne⟩
    · show (m.globals.map (·.type)).length = s'.globals.length
      rw [Store.storeBytes_globals hi, List.length_map, hcg]
    · show ExprTyping
        (frameCtx (c.harness.args ++ List.replicate c.harness.gemmNumLocals 0).length
          (m.globals.map (·.type)) m.tags.length 0) 0
        (Expr.ofList c.harness.gemmBody) fin
      have hlen : (c.harness.args ++ List.replicate c.harness.gemmNumLocals 0).length
          = 2 + c.harness.gemmNumLocals := by simp [hca]
      rw [hlen]
      exact hcty

/-- **SPEC section 7.3, `Wasm.validation_preservation`.**

SPEC section 7.3 writes this signature without `hwelltyped`.  That literal
statement is false --- with no invariant on `config`, `next` need not satisfy
one either: `code = [i32.const 0, drop, drop]` on an empty stack reduces to
`code = [drop, drop]` on a one-element stack, and neither configuration is well
typed.  The invariant hypothesis is therefore present here, which is what makes
this a preservation theorem rather than a claim that every reachable
configuration is well typed regardless of where it came from.  This declaration
is not on the SPEC section 15 required list. -/
theorem validation_preservation {module : Module} {config : Config} {event : Event}
    {next : Config}
    (hvalid : DeclarativelyValid module)
    (hstep : Step config event next)
    (hconfig : ConfigInstantiates module config)
    (hwelltyped : ConfigWellTyped config) :
    ConfigWellTyped next :=
  step_configWellTyped hstep hconfig hwelltyped

/-! ## The invariant is not the trivially true predicate

Progress would be worthless if `ConfigWellTyped` held of everything, so two
configurations the machine really does get stuck on are shown to fail it: one
that underflows the operand stack, and one whose head instruction is outside the
modelled subset.  The second is the load-bearing use of validation --- it is why
`validation_progress` needs `hwelltyped` at all. -/

/-- A configuration about to `drop` from an empty operand stack is not well
typed. -/
theorem not_configWellTyped_drop_empty {c : Config}
    (hcode : c.code = [Instr.drop]) (hstack : c.stack = []) (hctrl : c.ctrl = []) :
    ¬ ConfigWellTyped c := by
  rintro ⟨G, nt, hglen, base, rel, final, hctrlok, hstk, hchk, hexit⟩
  rw [hctrl] at hctrlok
  cases hctrlok
  rw [hstack] at hstk
  simp only [List.length_nil] at hstk
  have hrel : rel = 0 := by omega
  subst hrel
  rw [hcode] at hchk
  simp only [Expr.ofList] at hchk
  cases hchk with
  | @cons _ _ _ _ _ _ hi _ => cases hi

/-- A configuration whose next instruction is outside the modelled subset --- a
`call`, here --- is not well typed, whatever the rest of the machine state is.
`Wasm.Step` gives such a configuration no successor, so this exclusion is
exactly what makes progress provable. -/
theorem not_configWellTyped_call {c : Config} {idx : Nat} {rest : List Instr}
    (hcode : c.code = Instr.call idx :: rest) : ¬ ConfigWellTyped c := by
  rintro ⟨G, nt, hglen, base, rel, final, hctrlok, hstk, hchk, hexit⟩
  rw [hcode] at hchk
  simp only [Expr.ofList] at hchk
  cases hchk with
  | @cons _ _ _ _ _ _ hi _ => cases hi

/-! ## Reachability: the invariant holds of the configuration the machine starts
in, so it is not an empty predicate. -/

/-- Everything `initialConfig` fixes about the configuration it returns. -/
theorem initialConfig_full {m : Module} {raw : RawInvocation} {c : Config}
    (h : initialConfig m raw = .ok c) :
    ∃ store gi gemmFunc,
      Store.alloc m = some store ∧ Module.gemmIndex? m = some gi ∧
      m.funcs[gi]? = some gemmFunc ∧
      c.store = store ∧
      c.harness.gemmBody = Func.code gemmFunc ∧
      c.harness.gemmNumLocals = gemmFunc.locals.length ∧
      c.harness.args = [UInt32.ofNat raw.ptr, UInt32.ofNat raw.bytes.length] ∧
      c.ctrl = [] ∧ c.stack = [] ∧
      ((c.code = [] ∧ c.locals = []) ∨
        (∃ si startFunc, m.start = some si ∧ m.funcs[si]? = some startFunc ∧
          c.code = Func.code startFunc ∧
          c.locals = List.replicate startFunc.locals.length 0)) := by
  unfold initialConfig at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · next store halloc =>
      split at h
      · exact absurd h (by simp)
      · next gi hgi =>
        split at h
        · exact absurd h (by simp)
        · next gemmFunc hgf =>
          split at h
          · injection h with h
            subst h
            exact ⟨store, gi, gemmFunc, halloc, hgi, hgf, rfl, rfl, rfl, rfl, rfl,
              rfl, Or.inl ⟨rfl, rfl⟩⟩
          · next si hsi =>
            split at h
            · exact absurd h (by simp)
            · next startFunc hsf =>
              injection h with h
              subst h
              exact ⟨store, gi, gemmFunc, halloc, hgi, hgf, rfl, rfl, rfl, rfl, rfl,
                rfl, Or.inr ⟨si, startFunc, hsi, hsf, rfl, rfl⟩⟩

/-- The configuration `initialConfig` builds instantiates the module it was
built from. -/
theorem initialConfig_instantiates {m : Module} {raw : RawInvocation} {c : Config}
    (h : initialConfig m raw = .ok c) (hlocal : GemmFrameLocal m) :
    ConfigInstantiates m c := by
  obtain ⟨store, gi, gemmFunc, halloc, hgi, hgf, hstore, hbody, hnl, hargs, _, _, _⟩ :=
    initialConfig_full h
  obtain ⟨gi', f', fin, hgi', hgf', hty⟩ := hlocal
  rw [hgi] at hgi'
  injection hgi' with hgi'
  subst hgi'
  rw [hgf] at hgf'
  injection hgf' with hgf'
  subst hgf'
  refine ⟨?_, ?_, ⟨gi, gemmFunc, hgi, hgf, hbody, hnl⟩, fin, ?_⟩
  · rw [hstore, Store.alloc_globals_length halloc]
  · rw [hargs]; rfl
  · rw [hnl, hbody]
    simpa [Func.code] using hty

/-- **The invariant is reachable.**  The configuration the machine starts in is
well typed.  Note the hypothesis is `StartFrameLocal`, not validity of the whole
module: `initialConfig` only returns `.ok` for a module `Wasm.validate` accepts,
and the start-frame condition is the disclosed restriction of the header. -/
theorem initialConfig_configWellTyped {m : Module} {raw : RawInvocation} {c : Config}
    (h : initialConfig m raw = .ok c) (hstart : StartFrameLocal m) :
    ConfigWellTyped c := by
  obtain ⟨store, gi, gemmFunc, halloc, hgi, hgf, hstore, hbody, hnl, hargs, hctrl,
    hstk, hcase⟩ := initialConfig_full h
  have hglen : (m.globals.map (fun g => g.type)).length = c.store.globals.length := by
    rw [hstore, List.length_map, Store.alloc_globals_length halloc]
  rcases hcase with ⟨hcode, hloc⟩ | ⟨si, sf, hsi, hsf, hcode, hloc⟩
  · exact ⟨m.globals.map (fun g => g.type), m.tags.length, hglen, 0, 0, 0,
      by rw [hctrl]; exact CtrlOk.nil,
      by rw [hstk]; rfl,
      by rw [hcode, hctrl]; exact ExprTyping.nil,
      by rw [hctrl]; exact fun hne => absurd rfl hne⟩
  · obtain ⟨fin, hty⟩ := hstart si sf hsi hsf
    exact ⟨m.globals.map (fun g => g.type), m.tags.length, hglen, 0, 0, fin,
      by rw [hctrl]; exact CtrlOk.nil,
      by rw [hstk]; rfl,
      by rw [hcode, hctrl, hloc]; simpa [Func.code] using hty,
      by rw [hctrl]; exact fun hne => absurd rfl hne⟩

/-- A module with no start function starts in a well-typed configuration with no
side condition at all. -/
theorem initialConfig_configWellTyped_of_start_none {m : Module} {raw : RawInvocation}
    {c : Config} (h : initialConfig m raw = .ok c) (hs : m.start = none) :
    ConfigWellTyped c :=
  initialConfig_configWellTyped h (startFrameLocal_of_start_none hs)

end WasmGemmGnaf.Wasm
