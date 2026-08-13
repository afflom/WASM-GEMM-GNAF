/-
  Wasm/Core/Validation/InstructionsAmended.lean --- the AMENDED instruction
  sequence judgment, and the proofs that (a) it admits the compositions the
  pinned judgment cannot express, and (b) it does not widen the pinned
  judgment's arity discipline.

  WHY THIS FILE EXISTS.  `Core/Validation/Instructions.lean` transcribes the
  pinned Core 3.0 rules faithfully, and `Core/ValidateInstr.lean` proves,
  kernel-checked, that those rules give `(I32.CONST c) (BINOP I32 ADD)` NO
  instruction type in ANY context (`Instrs_ok.const_binop_untypable`, and the
  general schema `Instrs_ok.cons_untypable_of_arity` it is an instance of).
  That is a defect in the pinned SpecTec source, not in the transcription; it is
  recorded as DEV-006 in `model/spec-deviations.json`, and upstream filed and
  fixed the same defect after the pin (WebAssembly/spec issue #2194, PR #2197,
  merge commit `bd4633aced30b720ff62b44cf00c03ece792f008`, 2026-06-23; the pin
  `9d36019...` is dated 2025-09-26 and predates it).

  THE AMENDMENT, AND WHY IT IS THE SMALLEST ONE.  The pinned `Instrs_ok/seq`
  requires the tail's domain to be EXACTLY the head instruction's `Instr_ok`
  codomain.  `Instrs_ok/frame` could supply the missing operands, but it applies
  to a SEQUENCE and `seq`'s head premise is `Instr_ok`, which has no `sub` and
  no `frame` rule of its own.  The amendment carries the frame INSIDE the
  composition rule --- one modified premise, no new rule:

      C |- instr_1 instr_2* : (t_0* t_1*) ->_(x_1* x_2*) t_3*
      -- Instr_ok:      C |- instr_1  : t_1* ->_(x_1*) t_2*
      -- Resulttype_ok: C |- t_0* : OK
      -- (if C.LOCALS[x_1] = init t)*
      -- Instrs_ok: $with_locals(...) |- instr_2* : (t_0* t_2*) ->_(x_2*) t_3*

  `t_0* = eps` is exactly the pinned rule, so the amendment CONTAINS the pinned
  judgment (`Instrs_ok.to_amended` below); every other rule is unchanged.  This
  is the frame the classic prose rule for instruction sequences already carries
  ("there is a sequence of value types t_0* such that t_2* = t_0* t*"), and it
  is the second of the two repairs issue #2194 proposes.  Upstream took the
  first (lift the head to `Instrs_ok`, adding an `Instrs_ok/instr` rule and
  making `seq` concatenate two sequences); that shape adds a rule and makes the
  subject of `seq` an append, which no longer determines the split.  The two
  admit the same derivations in every case proved here; only this one is a
  single-premise edit, so it is the one the repository states.

  THE AMENDMENT MUST PROPAGATE THROUGH BLOCK BODIES.  `Instr_ok/block`,
  `Instr_ok/loop` and `Instr_ok/if` type their bodies with `Instrs_ok`, so
  amending `Instrs_ok` alone would leave every block whose body composes two
  instructions untypable and the vacuity would survive one nesting level down.
  `Instr_ok'` is therefore mutual with `Instrs_ok'`: it LIFTS every pinned
  `Instr_ok` rule unchanged (`Instr_ok'.lift`) and re-states exactly the three
  structured rules whose premises mention the sequence judgment.  No other
  instruction rule is touched, and no rule is weakened.

  NON-WIDENING.  The amendment supplies missing operands from the frame; it must
  not invent them.  `Instrs_ok'.nil_length`, `Instrs_ok'.const_length`,
  `Instrs_ok'.binop_dom_length` and `Instrs_ok'.binop_length` prove that under
  the AMENDED rules the empty sequence is still balanced, `CONST` still pushes
  exactly one operand, and `BINOP` still consumes two and nets minus one --- in
  every context, at every type.  `Instrs_ok'.binop_dom_length` is the very lemma
  that drives the pinned negative result, re-proved for the amended relation: the
  amendment did NOT buy composability by letting domains shrink.

  WHAT THE NON-WIDENING PROOF DOES NOT COVER, STATED PLAINLY.  `Instrs_ok'` IS
  strictly wider than `Instrs_ok` --- that is the point, and `Instrs_ok` cannot
  type ordinary WebAssembly, so a "the amendment rejects everything the pin
  rejects" theorem is not merely unproved, it is FALSE by construction.  What is
  proved is the two-sided bound that can be proved: containment of the pinned
  relation (no regression) and preservation of arity discipline in every context
  at every instruction type (no runaway).  The arity theorems are exactly the
  properties an over-wide repair would break.

  THE UPPER BOUND IS NOW A THEOREM, IN A LATER FILE.  `Core/ValidateSeq.lean`
  proves `checkSeq_complete`: over the decided fragment (`Context.frag`,
  `Instr.frag`) every instruction type `Instrs_ok'` gives a sequence is one the
  appendix ALGORITHM computes.  So the amendment is contained in what the
  algorithm accepts, on that fragment, and `checkSeq_sound` there is the
  converse in every context with no fragment hypothesis at all.  Containment in
  the CORRECTED UPSTREAM rules (`bd4633ac`) is a different statement and is
  still not proved: the pin is not advanced, so those rules are not transcribed
  in this repository and there is nothing here to state it against.

  NO COVERAGE MARKERS.  Nothing here is a transcription of a pinned rule, so no
  declaration in this file carries a coverage marker of any kind.  The Core 3.0
  inventory is unchanged by this file: it stays at 1288 of 1288, with validation
  rules 256 of 256.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## The amended judgment -/

mutual

/-- The pinned `Instr_ok`, with the three rules whose premises mention the
sequence judgment re-stated over `Instrs_ok'`.  Every other pinned rule is
carried over verbatim by `lift`. -/
inductive Instr_ok' : Context → Instr → InstrType → Prop where
  /-- Every pinned instruction rule still types what it typed. -/
  | lift {C : Context} {i : Instr} {it : InstrType} : Instr_ok C i it → Instr_ok' C i it
  /-- `Instr_ok/block`, with the body typed by the amended sequence judgment. -/
  | block {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_ok' C (.block bt body) ⟨ts₁, [], ts₂⟩
  /-- `Instr_ok/loop`, with the body typed by the amended sequence judgment. -/
  | loop {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok' (Context.pushLabel ts₁ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_ok' C (.loop bt body) ⟨ts₁, [], ts₂⟩
  /-- `Instr_ok/if`, with both arms typed by the amended sequence judgment. -/
  | if_ {C : Context} {bt : BlockType} {thn els : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList thn) ⟨ts₁, xs₁, ts₂⟩ →
      Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList els) ⟨ts₁, xs₂, ts₂⟩ →
      Instr_ok' C (.ifElse bt thn els) ⟨ts₁ ++ [ValType.i32], [], ts₂⟩

/-- The amended `Instrs_ok`.  `empty`, `sub` and `frame` are the pinned rules
verbatim; `seq` carries the frame `ts₀` inside the composition. -/
inductive Instrs_ok' : Context → List Instr → InstrType → Prop where
  /-- `rule Instrs_ok/empty`, unchanged. -/
  | empty {C : Context} : Instrs_ok' C [] ⟨[], [], []⟩
  /-- `rule Instrs_ok/seq`, AMENDED: the frame `ts₀` is available to the
  composition, so a head that produces fewer operands than the tail consumes can
  still be composed with the operands already on the stack. -/
  | seq {C : Context} {i₁ : Instr} {is : List Instr}
      {ts₀ ts₁ ts₂ ts₃ ts : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Instr_ok' C i₁ ⟨ts₁, xs₁, ts₂⟩ →
      SeqLen₂ xs₁ ts →
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs₁ ts →
      Resulttype_ok C ts₀ →
      Instrs_ok' (Context.withLocals C xs₁ (ts.map (fun t => ⟨.set, t⟩))) is
        ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ →
      Instrs_ok' C (i₁ :: is) ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, ts₃⟩
  /-- `rule Instrs_ok/sub`, unchanged. -/
  | sub {C : Context} {is : List Instr} {it it' : InstrType} :
      Instrs_ok' C is it → Instrtype_sub C it it' → Instrtype_ok C it' →
      Instrs_ok' C is it'
  /-- `rule Instrs_ok/frame`, unchanged. -/
  | frame {C : Context} {is : List Instr} {ts ts₁ ts₂ : List ValType}
      {xs : List LocalIdx} :
      Instrs_ok' C is ⟨ts₁, xs, ts₂⟩ → Resulttype_ok C ts →
      Instrs_ok' C is ⟨ts ++ ts₁, xs, ts ++ ts₂⟩

end

/-- `relation Expr_ok`, over the amended sequence judgment. -/
inductive Expr_ok' : Context → Expr → List ValType → Prop where
  | mk {C : Context} {e : Expr} {ts : List ValType} :
      Instrs_ok' C (InstrSeq.toList e) ⟨[], [], ts⟩ → Expr_ok' C e ts

/-! ## Well-formedness helpers -/

private theorem rt_ok_nil' {C : Context} : Resulttype_ok C [] := .mk (fun _ h => nomatch h)

private theorem rt_ok_cons' {C : Context} {t : ValType} {ts : List ValType}
    (ht : Valtype_ok C t) (hts : Resulttype_ok C ts) : Resulttype_ok C (t :: ts) := by
  cases hts with
  | mk hall => exact .mk (fun a ha => by cases ha with
      | head => exact ht
      | tail _ ha => exact hall a ha)

private theorem seq_all_nil' {α : Type} {P : α → Prop} : SeqAll P [] := fun _ h => nomatch h

private theorem seq_all₂_nil' {α β : Type} {R : α → β → Prop} : SeqAll₂ R [] [] :=
  fun _ _ _ h _ => nomatch h

/-! ## The amendment contains the pinned judgment

Nothing the pinned rules accept is rejected by the amended rules: `ts₀ = []`
recovers the pinned `seq`, and every other rule is unchanged.  The head premise
needs no induction --- the pinned `Instr_ok` derivation is carried across by
`Instr_ok'.lift` exactly as it stands. -/

/-- Every pinned derivation is an amended derivation. -/
theorem Instrs_ok.to_amended {C : Context} {is : List Instr} {it : InstrType}
    (h : Instrs_ok C is it) : Instrs_ok' C is it := by
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case empty => exact .empty
  case seq _ _ _ _ _ _ _ _ _ hd hlen hall _ _ ihs =>
      have := Instrs_ok'.seq (ts₀ := []) (Instr_ok'.lift hd) hlen hall rt_ok_nil'
        (by simpa using ihs)
      simpa using this
  case sub _ _ _ _ _ hsub hok ih => exact .sub ih hsub hok
  case frame _ _ _ _ _ _ _ hok ih => exact .frame ih hok
  all_goals trivial

/-- ... and hence every pinned `Expr_ok` is an amended one. -/
theorem Expr_ok.to_amended {C : Context} {e : Expr} {ts : List ValType}
    (h : Expr_ok C e ts) : Expr_ok' C e ts := by
  cases h with
  | mk hseq => exact .mk hseq.to_amended

/-! ## NON-WIDENING: the amended rules keep the pinned arity discipline

The amendment supplies operands from the frame.  It must not invent them.  Each
theorem below holds for EVERY context and EVERY instruction type. -/

/-- The empty sequence is balanced under the amended rules, exactly as under the
pinned ones: `sub` preserves both lengths and `frame` grows both equally. -/
theorem Instrs_ok'.nil_length {C : Context} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok' C is it →
      is = [] → it.dom.length = it.cod.length := by
  intro is it h
  induction h using Instrs_ok'.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro _; rfl
  case seq => intro he; exact absurd he (by simp)
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, hcod, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      obtain ⟨hcl, _⟩ := hcod
      have hih := ih he
      simp only [] at hdl hcl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-- Under the amended rules `(CONST nt c)` still pushes EXACTLY one operand: its
codomain is one longer than its domain, in every context, at every type. -/
theorem Instrs_ok'.const_length {C : Context} {nt : NumType} {c : Num_ nt} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok' C is it →
      is = [Instr.const nt c] → it.cod.length = it.dom.length + 1 := by
  intro is it h
  induction h using Instrs_ok'.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ _ hi _ _ _ htail _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, he₂⟩ := he
      subst he₁
      cases hi with
      | lift hl =>
        cases hl
        have hnil := Instrs_ok'.nil_length htail he₂
        simp only [List.length_append, List.append_nil, List.length_cons,
          List.length_nil] at hnil ⊢
        omega
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, hcod, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      obtain ⟨hcl, _⟩ := hcod
      have hih := ih he
      simp only [] at hdl hcl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-- THE NON-WIDENING CHECK THAT MATTERS.  This is the pinned lemma
`Instrs_ok.binop_dom_length` re-proved for the AMENDED relation: every amended
type of the one-instruction sequence `(BINOP nt op)` still has a domain of at
least two operands.  The amendment bought composability by supplying operands
from the frame, NOT by letting a domain shrink. -/
theorem Instrs_ok'.binop_dom_length {C : Context} {nt : NumType} {op : Binop} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok' C is it →
      is = [Instr.binop nt op] → 2 ≤ it.dom.length := by
  intro is it h
  induction h using Instrs_ok'.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ _ hi _ _ _ _ _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, _⟩ := he
      subst he₁
      cases hi with
      | lift hl =>
        cases hl
        simp
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, _, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      have hih := ih he
      simp only [] at hdl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-- Under the amended rules `(BINOP nt op)` still NETS one operand off the
stack: its codomain is exactly one shorter than its domain. -/
theorem Instrs_ok'.binop_length {C : Context} {nt : NumType} {op : Binop} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok' C is it →
      is = [Instr.binop nt op] → it.cod.length + 1 = it.dom.length := by
  intro is it h
  induction h using Instrs_ok'.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ _ hi _ _ _ htail _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, he₂⟩ := he
      subst he₁
      cases hi with
      | lift hl =>
        cases hl
        have hnil := Instrs_ok'.nil_length htail he₂
        simp only [List.length_append, List.length_cons, List.length_nil] at hnil ⊢
        omega
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, hcod, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      obtain ⟨hcl, _⟩ := hcod
      have hih := ih he
      simp only [] at hdl hcl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-! ### Concrete rejections the amended rules still make

Each is an immediate consequence of the arity theorems above, and each is a
thing the PINNED rules also reject.  They are stated separately because they are
the failure modes an over-wide "fix" would exhibit. -/

/-- A pushed constant cannot vanish: `(CONST nt c)` has no amended type
`eps -> eps`. -/
theorem Instrs_ok'.not_const_nil {C : Context} {nt : NumType} {c : Num_ nt} :
    ¬ Instrs_ok' C [Instr.const nt c] ⟨[], [], []⟩ := by
  intro h
  have := Instrs_ok'.const_length h rfl
  simp at this

/-- `BINOP` cannot be fed one operand: the amended rules give it no type
`nt -> nt`. -/
theorem Instrs_ok'.not_binop_unary {C : Context} {nt : NumType} {op : Binop} :
    ¬ Instrs_ok' C [Instr.binop nt op] ⟨[.num nt], [], [.num nt]⟩ := by
  intro h
  have := Instrs_ok'.binop_dom_length h rfl
  simp at this

/-- `BINOP` cannot leave both its operands behind: the amended rules give it no
type `nt nt -> nt nt`. -/
theorem Instrs_ok'.not_binop_balanced {C : Context} {nt : NumType} {op : Binop} :
    ¬ Instrs_ok' C [Instr.binop nt op] ⟨[.num nt, .num nt], [], [.num nt, .num nt]⟩ := by
  intro h
  have := Instrs_ok'.binop_length h rfl
  simp at this

/-! ## ANTI-VACUITY: derivations the amended judgment admits

The pinned judgment has none of these.  Each is checked by the kernel. -/

/-- `C |- I32 : OK`. -/
private theorem rt_ok_i32 {C : Context} : Resulttype_ok C [ValType.i32] :=
  rt_ok_cons' (.num .mk) rt_ok_nil'

/-- `C |- eps ->_(eps) I32 : OK`. -/
private theorem it_ok_nil_i32 {C : Context} : Instrtype_ok C ⟨[], [], [ValType.i32]⟩ :=
  .mk rt_ok_nil' rt_ok_i32 seq_all_nil'

/-- `C |- eps ->_(eps) I32 I32 : OK`. -/
private theorem it_ok_nil_i32i32 {C : Context} :
    Instrtype_ok C ⟨[], [], [ValType.i32, ValType.i32]⟩ :=
  .mk rt_ok_nil' (rt_ok_cons' (.num .mk) rt_ok_i32) seq_all_nil'

/-- The empty sequence at `t -> t`, for any single well-formed `t`. -/
private theorem instrs_ok'_nil_i32 {C : Context} :
    Instrs_ok' C [] ⟨[ValType.i32], [], [ValType.i32]⟩ :=
  Instrs_ok'.frame (ts := [ValType.i32]) Instrs_ok'.empty rt_ok_i32

/-- The empty sequence at `I32 I32 -> I32 I32`. -/
private theorem instrs_ok'_nil_i32i32 {C : Context} :
    Instrs_ok' C [] ⟨[ValType.i32, ValType.i32], [], [ValType.i32, ValType.i32]⟩ :=
  Instrs_ok'.frame (ts := [ValType.i32, ValType.i32]) Instrs_ok'.empty
    (rt_ok_cons' (.num .mk) rt_ok_i32)

/-- `(BINOP I32 ADD) : I32 I32 -> I32`, in any context. -/
private theorem instrs_ok'_binop {C : Context} :
    Instrs_ok' C [Instr.binop .i32 (.int .add)]
      ⟨[ValType.i32, ValType.i32], [], [ValType.i32]⟩ := by
  have h := Instrs_ok'.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_ok'.lift (Instr_ok.binop (nt := .i32) (op := .int .add) rfl)) rfl seq_all₂_nil' rt_ok_nil'
    (by simpa using instrs_ok'_nil_i32)
  simpa using h

/-- **THE DERIVATION THE PINNED RULES CANNOT EXPRESS.**
`C |- (I32.CONST c) (BINOP I32 ADD) : I32 -> I32`, in EVERY context.
Compare `Instrs_ok.const_binop_untypable`, which proves the pinned rules give
this sequence no type in any context. -/
theorem Instrs_ok'.const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_ok' C [Instr.const .i32 c, Instr.binop .i32 (.int .add)]
      ⟨[ValType.i32], [], [ValType.i32]⟩ := by
  have h := Instrs_ok'.seq (C := C) (ts₀ := [ValType.i32]) (ts := [])
    (Instr_ok'.lift (Instr_ok.const hc)) rfl seq_all₂_nil' rt_ok_i32
    (by simpa using instrs_ok'_binop)
  simpa using h

/-- ... and one instruction further out: `(CONST) (CONST) (BINOP) : eps -> I32`,
the shape of every constant-folded arithmetic expression.  Compare
`Instrs_ok.const_const_binop_untypable`. -/
theorem Instrs_ok'.const_const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_ok' C [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)]
      ⟨[], [], [ValType.i32]⟩ := by
  have h := Instrs_ok'.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_ok'.lift (Instr_ok.const hc)) rfl seq_all₂_nil' rt_ok_nil'
    (by simpa using Instrs_ok'.const_binop (C := _) hc)
  simpa using h

/-- The same sequence as an EXPRESSION.  `Expr_ok.const_const_binop_untypable`
proves the pinned rules give this expression no result type in any context; the
amendment gives it the type every engine gives it. -/
theorem Expr_ok'.const_const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Expr_ok' C (InstrSeq.ofList
        [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)])
      [ValType.i32] := by
  refine .mk ?_
  rw [InstrSeq.toList_ofList]
  exact Instrs_ok'.const_const_binop hc

/-- STACK POLYMORPHISM.  `(UNREACHABLE) (BINOP I32 ADD) : eps -> I32`: the
polymorphic head invents the two operands the binary instruction consumes.
(This one the pinned rules can also derive --- at the type `eps -> I32 I32` for
`UNREACHABLE` rather than the `eps -> I32` the spec's own prose names --- and it
is included so that the positive witnesses cover the polymorphic rule too.) -/
theorem Instrs_ok'.unreachable_binop {C : Context} :
    Instrs_ok' C [Instr.unreachable, Instr.binop .i32 (.int .add)]
      ⟨[], [], [ValType.i32]⟩ := by
  have h := Instrs_ok'.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_ok'.lift (Instr_ok.unreachable it_ok_nil_i32i32)) rfl seq_all₂_nil'
    rt_ok_nil' (by simpa using instrs_ok'_binop)
  simpa using h

/-- A BLOCK whose body needs the amendment.  `(BLOCK (RESULT I32)
(I32.CONST c) (I32.CONST c) (BINOP I32 ADD)) : eps -> I32`.

This is the witness that the amendment had to be propagated through
`Instr_ok/block`: the body is exactly the sequence the pinned rules cannot type,
so under a `Instrs_ok`-only amendment this block would still be untypable. -/
theorem Instrs_ok'.block_const_const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_ok' C
      [Instr.block (.result (some ValType.i32))
        (InstrSeq.ofList
          [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)])]
      ⟨[], [], [ValType.i32]⟩ := by
  have hbody : Instrs_ok' (Context.pushLabel [ValType.i32] C)
      (InstrSeq.toList (InstrSeq.ofList
        [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)]))
      ⟨[], [], [ValType.i32]⟩ := by
    rw [InstrSeq.toList_ofList]
    exact Instrs_ok'.const_const_binop hc
  have hbt : Blocktype_ok C (.result (some ValType.i32)) ⟨[], [], [ValType.i32]⟩ :=
    Blocktype_ok.valtype (t := some ValType.i32) (fun a ha => by
      cases ha; exact .num .mk)
  have h := Instrs_ok'.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_ok'.block hbt hbody) rfl seq_all₂_nil' rt_ok_nil'
    (by simpa using instrs_ok'_nil_i32)
  simpa using h

/-- A BR inside a block, again over a body the pinned rules cannot type.
`(BLOCK (RESULT I32) (I32.CONST c) (I32.CONST c) (BINOP I32 ADD) (BR 0))
 : eps -> I32`.  Inside the block the innermost label carries `I32`, so
`BR 0 : I32 -> I32` by `Instr_ok/br` with `t_1* = eps`, `t* = I32`,
`t_2* = I32`. -/
theorem Instrs_ok'.block_br {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_ok' C
      [Instr.block (.result (some ValType.i32))
        (InstrSeq.ofList
          [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add),
           Instr.br ⟨0, two_pow_pos 32⟩])]
      ⟨[], [], [ValType.i32]⟩ := by
  have hlab : (Context.pushLabel [ValType.i32] C).labels[(0 : Nat)]? =
      some [ValType.i32] := rfl
  -- `BR 0 : I32 -> I32`, then the empty tail at `I32 -> I32`.
  have hbr : Instrs_ok' (Context.pushLabel [ValType.i32] C) [Instr.br ⟨0, two_pow_pos 32⟩] ⟨[ValType.i32], [], [ValType.i32]⟩ := by
    have h := Instrs_ok'.seq (C := Context.pushLabel [ValType.i32] C) (ts₀ := []) (ts := [])
      (Instr_ok'.lift (Instr_ok.br (l := ⟨0, two_pow_pos 32⟩) (ts₁ := []) (ts₂ := [ValType.i32]) hlab it_ok_nil_i32))
      rfl seq_all₂_nil' rt_ok_nil' (by simpa using instrs_ok'_nil_i32)
    simpa using h
  -- `(BINOP) (BR 0) : I32 I32 -> I32`.
  have hbinop_br : Instrs_ok' (Context.pushLabel [ValType.i32] C) [Instr.binop .i32 (.int .add), Instr.br ⟨0, two_pow_pos 32⟩]
      ⟨[ValType.i32, ValType.i32], [], [ValType.i32]⟩ := by
    have h := Instrs_ok'.seq (C := Context.pushLabel [ValType.i32] C) (ts₀ := []) (ts := [])
      (Instr_ok'.lift (Instr_ok.binop (nt := .i32) (op := .int .add) rfl)) rfl seq_all₂_nil' rt_ok_nil'
      (by simpa using hbr)
    simpa using h
  -- `(CONST) (BINOP) (BR 0) : I32 -> I32`, using the AMENDED frame `ts₀ = I32`.
  have hc_binop_br : Instrs_ok' (Context.pushLabel [ValType.i32] C)
      [Instr.const .i32 c, Instr.binop .i32 (.int .add), Instr.br ⟨0, two_pow_pos 32⟩]
      ⟨[ValType.i32], [], [ValType.i32]⟩ := by
    have h := Instrs_ok'.seq (C := Context.pushLabel [ValType.i32] C) (ts₀ := [ValType.i32]) (ts := [])
      (Instr_ok'.lift (Instr_ok.const hc)) rfl seq_all₂_nil' rt_ok_i32
      (by simpa using hbinop_br)
    simpa using h
  have hbody : Instrs_ok' (Context.pushLabel [ValType.i32] C)
      [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add),
       Instr.br ⟨0, two_pow_pos 32⟩] ⟨[], [], [ValType.i32]⟩ := by
    have h := Instrs_ok'.seq (C := Context.pushLabel [ValType.i32] C) (ts₀ := []) (ts := [])
      (Instr_ok'.lift (Instr_ok.const hc)) rfl seq_all₂_nil' rt_ok_nil'
      (by simpa using hc_binop_br)
    simpa using h
  have hbt : Blocktype_ok C (.result (some ValType.i32)) ⟨[], [], [ValType.i32]⟩ :=
    Blocktype_ok.valtype (t := some ValType.i32) (fun a ha => by
      cases ha; exact .num .mk)
  have h := Instrs_ok'.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_ok'.block hbt (by rw [InstrSeq.toList_ofList]; exact hbody))
    rfl seq_all₂_nil' rt_ok_nil' (by simpa using instrs_ok'_nil_i32)
  simpa using h

end WasmGemmGnaf.Wasm.Core
