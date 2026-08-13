/-
  Wasm/Core/ValidateSeq.lean --- the equivalence of the validation ALGORITHM of
  `vendor/wasm-spec/document/core/appendix/algorithm.rst` with the AMENDED
  declarative instruction judgment `Instrs_ok'` of
  `Core/Validation/InstructionsAmended.lean`.

  WHY THE AMENDED RELATION AND NOT THE PINNED ONE.  `Core/ValidateInstr.lean`
  proves, kernel-checked, that the pinned `Instrs_ok` gives
  `(I32.CONST c) (BINOP I32 ADD)` no instruction type in any context
  (`Instrs_ok.const_binop_untypable`); the algorithm accepts that sequence, as
  every engine does, so a soundness theorem against the PINNED relation would be
  FALSE.  That is DEV-006 in `model/spec-deviations.json`; upstream filed the
  same finding as WebAssembly/spec issue #2194 and fixed it in PR #2197
  (`bd4633ac...`), nine months after the pin.  The two theorems below are stated
  over `Instrs_ok'`, the one-premise amendment of `Instrs_ok/seq` that
  `Core/Validation/InstructionsAmended.lean` states and proves to CONTAIN the
  pinned judgment.

  WHAT IS PROVED.

    `checkSeq_sound`     --- everything the single pass accepts, `Instrs_ok'`
                             derives, in EVERY context, with no fragment
                             hypothesis on the context or the instructions.
    `checkSeq_complete`  --- everything `Instrs_ok'` derives over the decided
                             fragment (`Context.frag`, `Instr.frag`), the single
                             pass accepts.
    `checkExpr_sound` / `checkExpr_complete` --- the same two at the level of
                             `Expr_ok'`, which is what the module rules consume.

  THE SHAPE OF THE TWO STATEMENTS.  The algorithm is a single pass over an
  abstract operand stack (`St`), so neither direction is a plain implication
  between two propositions about the same objects; each has to say how the
  abstract state relates to a concrete `resulttype`:

    * SOUNDNESS reads the final state back.  `St.Sat st ts` --- `pop_vals(ts)`
      succeeds and lands exactly on the frame's `val_height` --- is that reading.
      From `checkSeq C st is = some st'` and `st'.Sat ts₂` the theorem produces a
      `ts₁` the INITIAL state satisfies together with an `Instrs_ok'` derivation
      at `ts₁ ->_(x*) ts₂`.  Nothing is assumed about `C` or about the
      instructions: `checkInstr` returns `none` outside the decided fragment.

    * COMPLETENESS runs the pass forward.  `St.le` --- `st₁` is at least as
      general as `st₂` --- is the ordering that makes a single pass principal,
      and the theorem says the state the pass computes is at least as general as
      the one any declarative typing predicts.  This direction is fragment
      scoped, because the algorithm decides a fragment: `Context.frag` and
      `Instr.frag` are exactly the hypotheses `Core/ValidateInstr.lean` already
      carries for `instrType_complete`.

  THE RECURSION.  Both directions recur on the SYNTAX (`InstrSeq.size`), not on
  the derivation.  For soundness that is forced by `checkSeq` itself; for
  completeness it is forced by `Instrs_ok'/sub` and `Instrs_ok'/frame`, which do
  not change the subject, and by `Instr_ok'/lift`, which carries a PINNED
  `Instr_ok` whose `block`/`loop`/`if` bodies are pinned `Instrs_ok` derivations
  and hence supply no induction hypothesis of their own.  Recurring on the
  syntax makes the body of a structured instruction available in both cases, and
  the derivation is then consumed by an inner induction (completeness) or by
  inversion (soundness).

  NO COVERAGE MARKER.  Nothing here transcribes a pinned rule, so no declaration
  in this file carries one; the Core 3.0 inventory is unchanged.
-/
import WasmGemmGnaf.Wasm.Core.ValidateInstr
import WasmGemmGnaf.Wasm.Core.Validation.InstructionsAmended

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

open St

/-! ## Small list facts -/

/-- Setting a position to the value it already holds changes nothing. -/
theorem list_set_self {α : Type} : ∀ (l : List α) (i : Nat) (a : α),
    l[i]? = some a → l.set i a = l
  | [], _, _, h => by simp at h
  | b :: l, 0, a, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | b :: l, i + 1, a, h => by
      simp only [List.getElem?_cons_succ] at h
      show b :: l.set i a = b :: l
      rw [list_set_self l i a h]

theorem all_of_append_left {α : Type} {p : α → Bool} {as bs : List α}
    (h : (as ++ bs).all p = true) : as.all p = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1

theorem all_of_append_right {α : Type} {p : α → Bool} {as bs : List α}
    (h : (as ++ bs).all p = true) : bs.all p = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.2

theorem nvs_nvb {ts : List ValType} (h : nvs ts = true) : ts.all ValType.nvb = true :=
  List.all_eq_true.mpr (fun t ht => ValType.nvb_of_nv (List.all_eq_true.mp h t ht))

/-! ## Further stack lemmas

`Core/ValidateStack.lean` has the arithmetic of `push_vals` / `pop_vals` and the
generality ordering `St.le`; these are the four facts the two directions below
need on top of it. -/

namespace St

/-- A frame that pops `ts` onto a frame reading as `rs` reads as `rs ts`. -/
theorem sat_append {st st₀ : St} {ts rs : List ValType}
    (h : st.pops ts = some st₀) (hsat : st₀.Sat rs) : st.Sat (rs ++ ts) := by
  obtain ⟨st', hp, hv⟩ := hsat
  exact ⟨st', by rw [pops_append, h]; exact hp, hv⟩

/-- `unreachable()` reads as EVERY result type: that is what stack polymorphism
means for the final state of a frame. -/
theorem pops_unreach : ∀ ts : List ValType,
    (St.mk true []).pops ts = some (St.mk true [])
  | [] => rfl
  | t :: ts => by
      rw [pops_cons, pops_unreach ts]
      show (St.mk true []).popE t = _
      rw [popE_nil (show (St.mk true []).vals = [] from rfl)]
      simp

theorem sat_unreach (ts : List ValType) : (St.mk true []).Sat ts :=
  ⟨_, pops_unreach ts, rfl⟩

/-- The untyped `pop_val` succeeds wherever the checking one does, returns the
same frame, and returns an operand type the expectation accepts. -/
theorem pop_of_popE {st st' : St} {t : ValType} (h : st.popE t = some st') :
    ∃ u, st.pop = some (u, st') ∧ subOf u t = true := by
  cases hv : st.vals with
  | nil =>
      rw [popE_nil hv] at h
      by_cases hb : st.poly = true
      · rw [hb] at h
        simp only [if_pos, Option.some.injEq] at h
        subst h
        refine ⟨.bot, ?_, by simp⟩
        unfold pop; rw [hv, hb]; simp
      · have hb' : st.poly = false := by simpa using hb
        rw [hb'] at h; exact absurd h (by simp)
  | cons a rest =>
      rw [popE_cons hv] at h
      by_cases hs : subOf a t
      · rw [if_pos hs] at h
        injection h with h
        subst h
        refine ⟨a, ?_, hs⟩
        unfold pop; rw [hv]
      · rw [if_neg hs] at h; exact absurd h (by simp)

/-- One `pop_val` step: the frame before is at least as general as the frame
after with the popped operand pushed back. -/
theorem popE_le {st st' : St} {t : ValType} (h : st.popE t = some st') :
    le st (st'.push t) := by
  cases hv : st.vals with
  | nil =>
      rw [popE_nil hv] at h
      by_cases hb : st.poly = true
      · rw [hb] at h
        simp only [if_pos, Option.some.injEq] at h
        subst h
        exact Or.inl ⟨hb, [], (st.push t).vals, by simp, by rw [hv]; rfl⟩
      · have hb' : st.poly = false := by simpa using hb
        rw [hb'] at h; exact absurd h (by simp)
  | cons a rest =>
      rw [popE_cons hv] at h
      by_cases hs : subOf a t
      · rw [if_pos hs] at h
        injection h with h
        subst h
        have hv' : ((St.mk st.poly rest).push t).vals = t :: rest := rfl
        have hsubs : subs st.vals (t :: rest) = true := by
          rw [hv]; simp [hs, subs_refl]
        by_cases hb : st.poly = true
        · exact Or.inl ⟨hb, t :: rest, [], by rw [hv']; simp, hsubs⟩
        · have hb' : st.poly = false := by simpa using hb
          exact Or.inr ⟨hb', hb', hsubs⟩
      · rw [if_neg hs] at h; exact absurd h (by simp)

/-- ... and the same for a whole `pop_vals`. -/
theorem pops_le {st st₀ : St} : ∀ {ts : List ValType},
    st.pops ts = some st₀ → le st (st₀.pushs ts) := by
  intro ts
  induction ts generalizing st₀ with
  | nil => intro h; cases h; exact le_refl _
  | cons t ts ih =>
      intro h
      rw [pops_cons] at h
      cases hp : st.pops ts with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some s =>
          rw [hp] at h
          have h₁ : le st (s.pushs ts) := ih hp
          have h₂ : le s (st₀.push t) := popE_le h
          have h₃ : le (s.pushs ts) ((st₀.push t).pushs ts) := pushs_mono h₂ ts
          exact le_trans h₁ h₃

theorem subs_reverse : ∀ {as bs : List ValType}, subs as bs = true →
    subs as.reverse bs.reverse = true
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [subs_cons, Bool.and_eq_true] at h
      rw [List.reverse_cons, List.reverse_cons]
      exact subs_append (subs_reverse h.2) (by simp [h.1])
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Pushing a more precise sequence yields a more general frame. -/
theorem pushs_le_of_subs {st : St} {ts ts' : List ValType} (h : subs ts ts' = true) :
    le (st.pushs ts) (st.pushs ts') := by
  rw [pushs_eq, pushs_eq]
  by_cases hb : st.poly = true
  · exact Or.inl ⟨hb, ts'.reverse ++ st.vals, [], by simp,
      subs_append (subs_reverse h) (subs_refl _)⟩
  · have hb' : st.poly = false := by simpa using hb
    exact Or.inr ⟨hb', hb', subs_append (subs_reverse h) (subs_refl _)⟩

/-- `matches_val` is sound in the other argument too: a `numtype`, `vectype` or
`BOT` is a subtype only of itself or of a supertype `subOf` accepts. -/
theorem subOf_of_valtype_sub_left {C : Context} {t₁ t₂ : ValType}
    (h : Valtype_sub C t₁ t₂) (h₁ : ValType.nvb t₁ = true) : subOf t₁ t₂ = true := by
  cases h with
  | num hn => cases hn; simp
  | vec hv => cases hv; simp
  | ref _ => simp [ValType.nvb] at h₁
  | bot => simp

/-- `pop_val` against a SUPERTYPE succeeds wherever it succeeds against the
subtype, with the same remaining frame.  The frame's operands are `numtype`s,
`vectype`s or `BOT`, so a pop that succeeded against a reference type succeeded
through `BOT`, where the expectation is irrelevant. -/
theorem popE_sub {C : Context} {st st' : St} {t t' : ValType}
    (hnvb : st.vals.all ValType.nvb = true) (h : st.popE t = some st')
    (hsub : Valtype_sub C t t') : st.popE t' = some st' := by
  cases hv : st.vals with
  | nil => rw [popE_nil hv] at h ⊢; exact h
  | cons a rest =>
      rw [popE_cons hv] at h ⊢
      by_cases hs : subOf a t
      · rw [if_pos hs] at h
        have ha : ValType.nvb a = true := by
          rw [hv] at hnvb
          simp only [List.all_cons, Bool.and_eq_true] at hnvb
          exact hnvb.1
        have hs' : subOf a t' = true := by
          simp only [subOf, Bool.or_eq_true, beq_iff_eq] at hs ⊢
          rcases hs with hs | hs
          · exact Or.inl hs
          · subst hs
            have := subOf_of_valtype_sub_left hsub ha
            simp only [subOf, Bool.or_eq_true, beq_iff_eq] at this
            exact this
        rw [if_pos hs']; exact h
      · rw [if_neg hs] at h; exact absurd h (by simp)

/-- ... and the same for a whole `pop_vals`: this is what makes
`Instrs_ok'/sub` computable by the single pass. -/
theorem pops_sub {C : Context} {st st₀ : St} : ∀ {ts ts' : List ValType},
    st.vals.all ValType.nvb = true → st.pops ts = some st₀ →
    Resulttype_sub C ts ts' → st.pops ts' = some st₀ := by
  intro ts
  induction ts generalizing st₀ with
  | nil =>
      intro ts' hnvb h hsub
      cases hsub with
      | mk hlen _ =>
          cases ts' with
          | nil => exact h
          | cons _ _ => simp only [SeqLen₂, List.length_nil, List.length_cons] at hlen; omega
  | cons t ts ih =>
      intro ts' hnvb h hsub
      cases ts' with
      | nil =>
          cases hsub with
          | mk hlen _ => simp only [SeqLen₂, List.length_nil, List.length_cons] at hlen; omega
      | cons t' ts' =>
          cases hsub with
          | mk hlen hall =>
              rw [pops_cons] at h
              cases hp : st.pops ts with
              | none => rw [hp] at h; exact absurd h (by simp)
              | some s =>
                  rw [hp] at h
                  have hsubtail : Resulttype_sub C ts ts' :=
                    .mk (by simp only [SeqLen₂, List.length_cons] at hlen ⊢; omega)
                      (fun i a b ha hb => hall (i + 1) a b (by simpa using ha) (by simpa using hb))
                  have hp' : st.pops ts' = some s := ih hnvb hp hsubtail
                  rw [pops_cons, hp']
                  exact popE_sub (pops_nvb hp hnvb) h (hall 0 t t' (by simp) (by simp))

end St

/-! ## The block type, decided

`blockType` is `Blocktype_ok` read as a function; these are its two directions.
`Blocktype_ok` never binds a local, so the `x*` component of the instruction
type it produces is always empty. -/

theorem blockType_sound {C : Context} {bt : BlockType} {ts₁ ts₂ : List ValType}
    (h : blockType C bt = some (ts₁, ts₂)) :
    Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ ∧ nvs ts₁ = true ∧ nvs ts₂ = true := by
  cases bt with
  | result t =>
      cases t with
      | none =>
          simp only [blockType, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h₁, h₂⟩ := h
          subst h₁; subst h₂
          exact ⟨.valtype (t := none) (fun a ha => by simp at ha), rfl, rfl⟩
      | some t =>
          simp only [blockType] at h
          by_cases hnv : ValType.nv t = true
          · rw [if_pos hnv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h₁, h₂⟩ := h
            subst h₁; subst h₂
            refine ⟨.valtype (t := some t) (fun a ha => ?_), rfl, by simp [nvs, hnv]⟩
            simp only [Option.some.injEq] at ha
            subst ha
            exact valtype_ok_of_nvb (ValType.nvb_of_nv hnv)
          · rw [if_neg hnv] at h; exact absurd h (by simp)
  | idx x =>
      simp only [blockType] at h
      cases hty : C.types[x.val]? with
      | none => simp only [hty] at h; exact absurd h (by simp)
      | some dt =>
          simp only [hty] at h
          rw [funcTypeOf] at h
          cases hexp : expandDt dt with
          | none => simp only [hexp] at h; exact absurd h (by simp)
          | some ct =>
              cases ct with
              | func dom cod =>
                  simp only [hexp] at h
                  by_cases hif : (nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)) = true
                  · rw [if_pos hif] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨h₁, h₂⟩ := h
                    subst h₁; subst h₂
                    simp only [Bool.and_eq_true] at hif
                    exact ⟨.typeidx hty (.mk hexp), hif.1, hif.2⟩
                  · rw [if_neg hif] at h; exact absurd h (by simp)
              | _ => simp only [hexp] at h; exact absurd h (by simp)

theorem blockType_complete {C : Context} {bt : BlockType} {ts₁ ts₂ : List ValType}
    (hC : Context.frag C = true) (hfrag : BlockType.frag bt = true)
    (h : Blocktype_ok C bt ⟨ts₁, [], ts₂⟩) : blockType C bt = some (ts₁, ts₂) := by
  cases h with
  | valtype hok =>
      rename_i t
      cases t with
      | none => rfl
      | some t =>
          simp only [BlockType.frag] at hfrag
          simp [blockType, hfrag]
  | typeidx hty hexp =>
      rename_i x dt dom cod
      simp only [blockType, hty]
      exact funcTypeOf_of_expand hexp (frag_type hC hty)

/-! ## The single pass, unfolded

`checkInstr` handles the nine instructions whose declarative rule leaves
something free in the appendix's own terms and dispatches everything else
through `instrType`; `checkSeq` is the fold.  These are those two facts as
rewrite rules. -/

@[simp] theorem checkSeq_nil (C : Context) (st : St) : checkSeq C st .nil = some st := rfl

@[simp] theorem checkSeq_cons (C : Context) (st : St) (i : Instr) (rest : InstrSeq) :
    checkSeq C st (.cons i rest) =
      match checkInstr C st i with
      | some st' => checkSeq C st' rest
      | none => none := rfl

/-- Every instruction outside `Instr.special` goes through `instrType`. -/
theorem checkInstr_eq_default {C : Context} {st : St} {i : Instr}
    (hsp : Instr.special i = false) :
    checkInstr C st i =
      (match instrType C i with
       | some it =>
           (match st.pops it.dom with
            | some st₀ => some (st₀.pushs it.cod)
            | none => none)
       | none => none) := by
  unfold checkInstr
  split
  all_goals first
    | rfl
    | simp_all [Instr.special]

/-! ## What the computed instruction types say about `LOCALS`

`Instrs_ok'/seq` re-types the tail under `$with_locals(C, x_1*, (SET t)*)`.  Only
`LOCAL.SET` and `LOCAL.TEE` give `instrType` a non-empty `x*`, and both require
the local to be `SET` at that very type already, so the re-typed context is `C`
itself. -/

theorem instrType_locals {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) :
    it.locals = [] ∨
      ∃ (x : LocalIdx) (t : ValType),
        it.locals = [x] ∧ C.locals[x.val]? = some ⟨Init.set, t⟩ := by
  rw [instrType] at h
  split at h
  · unfold instrTypeRaw at h
    split at h
    all_goals (try (split at h))
    all_goals (try (split at h))
    all_goals first
      | (injection h with h; subst h; exact Or.inl rfl)
      | (injection h with h; subst h; exact Or.inr ⟨_, _, rfl, by assumption⟩)
      | (simp at h)
  · exact absurd h (by simp)

theorem instrType_withLocals {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) :
    ∃ lts : List ValType, SeqLen₂ it.locals lts ∧
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
        ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) it.locals lts ∧
      Context.withLocals C it.locals (lts.map (fun t => ⟨Init.set, t⟩)) = C := by
  rcases instrType_locals h with hnil | ⟨x, t, hx, hloc⟩
  · refine ⟨[], by rw [hnil]; rfl, ?_, by rw [hnil]; rfl⟩
    rw [hnil]; intro i a b ha _; simp at ha
  · refine ⟨[t], by rw [hx]; rfl, ?_, ?_⟩
    · rw [hx]
      intro j a b ha hb
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
          subst ha; subst hb
          exact ⟨.set, hloc⟩
      | succ n => simp at ha
    · rw [hx]
      show Context.setLocal C x ⟨Init.set, t⟩ = C
      unfold Context.setLocal
      rw [list_set_self C.locals x.val ⟨Init.set, t⟩ hloc]

/-! ## The operand stack of a run carries only `numtype`s, `vectype`s and `BOT`

Every operand the algorithm pushes comes from a computed instruction type
(`instrType_nv`), from a `blocktype` (`blockType_sound`) or from an operand it
just popped, so the invariant is preserved by every step. -/

theorem checkInstr_nvb {C : Context} {st st' : St} {i : Instr}
    (h : checkInstr C st i = some st') (hnvb : st.vals.all ValType.nvb = true) :
    st'.vals.all ValType.nvb = true := by
  unfold checkInstr at h
  split at h
  · -- UNREACHABLE
    injection h with h; subst h; rfl
  · -- DROP
    split at h
    · rename_i hp
      injection h with h; subst h
      exact (pop_nvb hp hnvb).2
    · exact absurd h (by simp)
  · -- SELECT, unannotated
    split at h
    · rename_i h₁
      split at h
      · rename_i h₂
        split at h
        · rename_i h₃
          split at h
          · rename_i hc
            injection h with h; subst h
            simp only [St.push, List.all_cons, Bool.and_eq_true] at *
            refine ⟨?_, (pop_nvb h₃ (pop_nvb h₂ (popE_nvb h₁ hnvb)).2).2⟩
            split
            · exact hc.1.2
            · exact hc.1.1
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- BR
    split at h
    · split at h
      · split at h
        · injection h with h; subst h; rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- RETURN
    split at h
    · split at h
      · split at h
        · injection h with h; subst h; rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- BLOCK
    split at h
    · rename_i hbt
      split at h
      · rename_i hpop
        split at h
        · split at h
          · injection h with h; subst h
            exact pushs_nvb (pops_nvb hpop hnvb) (nvs_nvb (blockType_sound hbt).2.2)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- LOOP
    split at h
    · rename_i hbt
      split at h
      · rename_i hpop
        split at h
        · split at h
          · injection h with h; subst h
            exact pushs_nvb (pops_nvb hpop hnvb) (nvs_nvb (blockType_sound hbt).2.2)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- IF
    split at h
    · rename_i hbt
      split at h
      · rename_i hcond
        split at h
        · rename_i hpop
          split at h
          · split at h
            · injection h with h; subst h
              exact pushs_nvb (pops_nvb hpop (popE_nvb hcond hnvb))
                (nvs_nvb (blockType_sound hbt).2.2)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- everything else
    split at h
    · rename_i hit
      split at h
      · rename_i hpop
        injection h with h; subst h
        exact pushs_nvb (pops_nvb hpop hnvb) (nvs_nvb (instrType_nv hit).2)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem checkSeq_nvb : ∀ (s : InstrSeq) {C : Context} {st st' : St},
    checkSeq C st s = some st' → st.vals.all ValType.nvb = true →
    st'.vals.all ValType.nvb = true
  | .nil, _, _, _, h, hn => by injection h with h; subst h; exact hn
  | .cons i rest, C, st, st', h, hn => by
      rw [checkSeq_cons] at h
      cases hi : checkInstr C st i with
      | none => rw [hi] at h; exact absurd h (by simp)
      | some st₁ => rw [hi] at h; exact checkSeq_nvb rest h (checkInstr_nvb hi hn)

/-! ## The recursion measure

Both directions recur on the syntax; this is the measure they recur on. -/

mutual
/-- The syntactic size of an instruction: one plus the size of its bodies. -/
def Instr.size : Instr → Nat
  | .block _ body => InstrSeq.size body + 1
  | .loop _ body => InstrSeq.size body + 1
  | .ifElse _ thn els => InstrSeq.size thn + InstrSeq.size els + 1
  | _ => 1

/-- The syntactic size of an instruction sequence. -/
def InstrSeq.size : InstrSeq → Nat
  | .nil => 0
  | .cons i rest => Instr.size i + InstrSeq.size rest + 1
end

theorem Instr.size_pos (i : Instr) : 0 < Instr.size i := by
  cases i <;> simp [Instr.size]

theorem InstrSeq.size_body_block (bt : BlockType) (body : InstrSeq) :
    InstrSeq.size body < Instr.size (.block bt body) := by simp [Instr.size]

theorem InstrSeq.size_body_loop (bt : BlockType) (body : InstrSeq) :
    InstrSeq.size body < Instr.size (.loop bt body) := by simp [Instr.size]

theorem InstrSeq.size_body_thn (bt : BlockType) (thn els : InstrSeq) :
    InstrSeq.size thn < Instr.size (.ifElse bt thn els) := by simp [Instr.size]; omega

theorem InstrSeq.size_body_els (bt : BlockType) (thn els : InstrSeq) :
    InstrSeq.size els < Instr.size (.ifElse bt thn els) := by simp [Instr.size]; omega

theorem InstrSeq.size_head (i : Instr) (rest : InstrSeq) :
    Instr.size i < InstrSeq.size (.cons i rest) := by simp [InstrSeq.size]; omega

theorem InstrSeq.size_tail (i : Instr) (rest : InstrSeq) :
    InstrSeq.size rest < InstrSeq.size (.cons i rest) := by
  have := Instr.size_pos i
  simp [InstrSeq.size]; omega

/-! ## The nine arms of `checkInstr`, as equations

`checkInstr` is a `mutual` definition, so its arms are spelled out here once and
used by name below rather than unfolded at every site. -/

theorem checkInstr_unreachable (C : Context) (st : St) :
    checkInstr C st .unreachable = some st.unreach := rfl

theorem checkInstr_drop (C : Context) (st : St) :
    checkInstr C st .drop =
      (match st.pop with
       | some (_, st₀) => some st₀
       | none => none) := rfl

theorem checkInstr_select (C : Context) (st : St) :
    checkInstr C st (.select none) =
      (match st.popE ValType.i32 with
       | some st₁ =>
           (match st₁.pop with
            | some (t₁, st₂) =>
                (match st₂.pop with
                 | some (t₂, st₃) =>
                     if (ValType.nvb t₁ && ValType.nvb t₂) &&
                         (subOf t₁ t₂ || subOf t₂ t₁) then
                       some (st₃.push (if t₁ == ValType.bot then t₂ else t₁))
                     else none
                 | none => none)
            | none => none)
       | none => none) := rfl

theorem checkInstr_br (C : Context) (st : St) (l : LabelIdx) :
    checkInstr C st (.br l) =
      (match C.labels[l.val]? with
       | some ts =>
           if nvs ts then
             (match st.pops ts with
              | some _ => some st.unreach
              | none => none)
           else none
       | none => none) := rfl

theorem checkInstr_ret (C : Context) (st : St) :
    checkInstr C st .ret =
      (match C.ret with
       | some ts =>
           if nvs ts then
             (match st.pops ts with
              | some _ => some st.unreach
              | none => none)
           else none
       | none => none) := rfl

theorem checkInstr_block (C : Context) (st : St) (bt : BlockType) (body : InstrSeq) :
    checkInstr C st (.block bt body) =
      (match blockType C bt with
       | some (ts₁, ts₂) =>
           (match st.pops ts₁ with
            | some st₀ =>
                (match checkSeq (Context.pushLabel ts₂ C) ((St.mk false []).pushs ts₁) body with
                 | some stB => if stB.finish ts₂ then some (st₀.pushs ts₂) else none
                 | none => none)
            | none => none)
       | none => none) := rfl

theorem checkInstr_loop (C : Context) (st : St) (bt : BlockType) (body : InstrSeq) :
    checkInstr C st (.loop bt body) =
      (match blockType C bt with
       | some (ts₁, ts₂) =>
           (match st.pops ts₁ with
            | some st₀ =>
                (match checkSeq (Context.pushLabel ts₁ C) ((St.mk false []).pushs ts₁) body with
                 | some stB => if stB.finish ts₂ then some (st₀.pushs ts₂) else none
                 | none => none)
            | none => none)
       | none => none) := rfl

theorem checkInstr_if (C : Context) (st : St) (bt : BlockType) (thn els : InstrSeq) :
    checkInstr C st (.ifElse bt thn els) =
      (match blockType C bt with
       | some (ts₁, ts₂) =>
           (match st.popE ValType.i32 with
            | some st' =>
                (match st'.pops ts₁ with
                 | some st₀ =>
                     (match checkSeq (Context.pushLabel ts₂ C) ((St.mk false []).pushs ts₁) thn,
                            checkSeq (Context.pushLabel ts₂ C) ((St.mk false []).pushs ts₁) els with
                      | some stT, some stE =>
                          if stT.finish ts₂ && stE.finish ts₂ then some (st₀.pushs ts₂) else none
                      | _, _ => none)
                 | none => none)
            | none => none)
       | none => none) := rfl

/-! ## Small facts about the declarative side -/

theorem all_reverse {α : Type} {p : α → Bool} {l : List α} (h : l.all p = true) :
    l.reverse.all p = true := by
  simp only [List.all_eq_true] at h ⊢
  intro a ha
  exact h a (by simpa using ha)

theorem resulttype_sub_refl {C : Context} (ts : List ValType) : Resulttype_sub C ts ts :=
  .mk rfl (fun _ a b ha hb => by
    rw [ha] at hb
    injection hb with hb
    subst hb
    exact valtype_sub_refl a)

/-- Every `numtype`, `vectype` or `BOT` is below a `numtype` or a `vectype`,
which is the side condition of `Instr_ok/select-impl`. -/
theorem valtype_sub_numvec {C : Context} {t : ValType} (h : ValType.nvb t = true) :
    ∃ t' : ValType, Valtype_sub C t t' ∧ t'.isNumOrVec = true := by
  cases t with
  | num n => exact ⟨.num n, valtype_sub_refl _, rfl⟩
  | vec v => exact ⟨.vec v, valtype_sub_refl _, rfl⟩
  | ref _ => simp [ValType.nvb] at h
  | bot => exact ⟨ValType.i32, .bot, rfl⟩

/-- `Instrs_ok'/sub` at `eps ->_(x*) t*  <:  eps ->_(eps) t*`: an instruction
sequence that sets locals still has the expression type its results give it.
`$setminus_(localidx, eps, x*)` is empty, so the rule's third premise is
vacuous. -/
theorem Instrs_ok'.drop_locals {C : Context} {is : List Instr} {xs : List LocalIdx}
    {ts : List ValType} (h : Instrs_ok' C is ⟨[], xs, ts⟩)
    (hts : ts.all ValType.nvb = true) : Instrs_ok' C is ⟨[], [], ts⟩ :=
  .sub h
    (.mk (resulttype_sub_refl []) (resulttype_sub_refl ts) (fun a ha => by simp [setminus] at ha))
    (.mk (resulttype_ok_of_nvb (by simp)) (resulttype_ok_of_nvb hts) (fun a ha => by simp at ha))

/-! ## SOUNDNESS

Everything the single pass accepts, the amended judgment derives.  There is no
fragment hypothesis in either statement: `checkInstr` returns `none` on every
instruction outside the decided fragment, and `instrType` on every context
component outside it. -/

/-- The soundness statement for one instruction.  `ts₀` is the frame the
amended `Instrs_ok'/seq` carries INSIDE the composition --- the operands that
were on the stack before this instruction and are still there after it. -/
def InstrSound (i : Instr) : Prop :=
  ∀ (C : Context) (st st' : St) (tsm : List ValType),
    checkInstr C st i = some st' → st.vals.all ValType.nvb = true →
    st'.Sat tsm → tsm.all ValType.nvb = true →
    ∃ (ts₀ ts₁ ts₂ : List ValType) (xs : List LocalIdx) (lts : List ValType),
      tsm = ts₀ ++ ts₂ ∧ st.Sat (ts₀ ++ ts₁) ∧ (ts₀ ++ ts₁).all ValType.nvb = true ∧
      Instr_ok' C i ⟨ts₁, xs, ts₂⟩ ∧
      SeqLen₂ xs lts ∧
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
        ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs lts ∧
      Context.withLocals C xs (lts.map (fun t => ⟨Init.set, t⟩)) = C

/-- The soundness statement for a sequence. -/
def SeqSound (s : InstrSeq) : Prop :=
  ∀ (C : Context) (st st' : St) (ts₂ : List ValType),
    checkSeq C st s = some st' → st.vals.all ValType.nvb = true →
    st'.Sat ts₂ → ts₂.all ValType.nvb = true →
    ∃ (ts₁ : List ValType) (xs : List LocalIdx),
      st.Sat ts₁ ∧ ts₁.all ValType.nvb = true ∧
      Instrs_ok' C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩

/-- Every instruction the appendix dispatches through `instrType`. -/
theorem instr_sound_default {i : Instr} (hsp : Instr.special i = false) : InstrSound i := by
  intro C st st' tsm h hnvb hsat hts
  rw [checkInstr_eq_default hsp] at h
  cases hit : instrType C i with
  | none => simp only [hit] at h; exact absurd h (by simp)
  | some it =>
      simp only [hit] at h
      cases hpop : st.pops it.dom with
      | none => simp only [hpop] at h; exact absurd h (by simp)
      | some st₀ =>
          simp only [hpop] at h
          injection h with h; subst h
          obtain ⟨rs, cs, he, hs, hsat₀⟩ := pops_split_sat it.cod hsat
          have hnv := instrType_nv hit
          have hcs : it.cod = cs := subs_eq_of_nv hs hnv.2
          obtain ⟨lts, hlen, hall, hwl⟩ := instrType_withLocals hit
          have hrs : rs.all ValType.nvb = true := by
            rw [he] at hts; exact all_of_append_left hts
          refine ⟨rs, it.dom, it.cod, it.locals, lts, by rw [he, hcs],
            sat_append hpop hsat₀, ?_, Instr_ok'.lift (instrType_sound hit), hlen, hall, hwl⟩
          simp only [List.all_append, Bool.and_eq_true]
          exact ⟨hrs, nvs_nvb hnv.1⟩

theorem instr_sound_step (i : Instr)
    (hbody : ∀ body : InstrSeq, InstrSeq.size body < Instr.size i → SeqSound body) :
    InstrSound i := by
  cases i
  case unreachable =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_unreachable] at h
      injection h with h; subst h
      have hrev : st.vals.reverse.all ValType.nvb = true := all_reverse hnvb
      refine ⟨[], st.vals.reverse, tsm, [], [], rfl, sat_own st, hrev, ?_, rfl,
        (fun j a b ha _ => by simp at ha), rfl⟩
      exact Instr_ok'.lift (Instr_ok.unreachable
        (.mk (resulttype_ok_of_nvb hrev) (resulttype_ok_of_nvb hts) (fun a ha => by simp at ha)))
  case drop =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_drop] at h
      cases hp : st.pop with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨u, st₀⟩ := p
          simp only [hp] at h
          injection h with h; subst h
          have hu := pop_nvb hp hnvb
          refine ⟨tsm, [u], [], [], [], by simp, ?_, ?_, ?_, rfl,
            (fun j a b ha _ => by simp at ha), rfl⟩
          · exact sat_append (show st.pops [u] = some st₀ from pop_popE hp) hsat
          · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true]
            exact ⟨hts, hu.1, trivial⟩
          · exact Instr_ok'.lift (Instr_ok.drop (valtype_ok_of_nvb hu.1))
  case select ts =>
      cases ts with
      | some l => exact instr_sound_default rfl
      | none =>
          intro C st st' tsm h hnvb hsat hts
          rw [checkInstr_select] at h
          cases h₁ : st.popE ValType.i32 with
          | none => simp only [h₁] at h; exact absurd h (by simp)
          | some st₁ =>
              simp only [h₁] at h
              cases h₂ : st₁.pop with
              | none => simp only [h₂] at h; exact absurd h (by simp)
              | some p₂ =>
                  obtain ⟨t₁, st₂⟩ := p₂
                  simp only [h₂] at h
                  cases h₃ : st₂.pop with
                  | none => simp only [h₃] at h; exact absurd h (by simp)
                  | some p₃ =>
                      obtain ⟨t₂, st₃⟩ := p₃
                      simp only [h₃] at h
                      split at h
                      · rename_i hc
                        injection h with h; subst h
                        obtain ⟨rs, w, he, hw, hsat₃⟩ := push_sat hsat
                        simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
                        have hwn : ValType.nvb w = true := by
                          rw [he] at hts
                          have := all_of_append_right hts
                          simpa using this
                        have hs₁ : subOf t₁ w = true := by
                          refine subOf_trans ?_ hw
                          by_cases hb : (t₁ == ValType.bot) = true
                          · simp only [hb, if_pos]
                            simp only [beq_iff_eq] at hb
                            simp [hb]
                          · simp only [hb, Bool.false_eq_true, if_false]
                            simp
                        have hs₂ : subOf t₂ w = true := by
                          refine subOf_trans ?_ hw
                          by_cases hb : (t₁ == ValType.bot) = true
                          · simp only [hb, if_pos]; simp
                          · simp only [hb, Bool.false_eq_true, if_false]
                            simp only [beq_iff_eq] at hb
                            rcases hc.2 with hcc | hcc
                            · simp only [subOf, Bool.or_eq_true, beq_iff_eq] at hcc
                              rcases hcc with hcc | hcc
                              · exact absurd hcc hb
                              · simp [subOf, hcc]
                            · exact hcc
                        have e1 : st.pops [ValType.i32] = some st₁ := h₁
                        have e2 : st.pops [w, ValType.i32] = some st₂ := by
                          rw [pops_cons, e1]; exact pop_popE_of_subOf h₂ hs₁
                        have hpops : st.pops [w, w, ValType.i32] = some st₃ := by
                          rw [pops_cons, e2]; exact pop_popE_of_subOf h₃ hs₂
                        obtain ⟨t', hsub', hnv'⟩ := valtype_sub_numvec (C := C) hwn
                        refine ⟨rs, [w, w, ValType.i32], [w], [], [], he, ?_, ?_, ?_, rfl,
                          (fun j a b ha _ => by simp at ha), rfl⟩
                        · exact sat_append hpops hsat₃
                        · have hrs : rs.all ValType.nvb = true := by
                            rw [he] at hts; exact all_of_append_left hts
                          simp only [List.all_append, List.all_cons, List.all_nil,
                            Bool.and_eq_true]
                          exact ⟨hrs, hwn, hwn, rfl, trivial⟩
                        · exact Instr_ok'.lift
                            (Instr_ok.select_impl (valtype_ok_of_nvb hwn) hsub' hnv')
                      · exact absurd h (by simp)
  case br l =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_br] at h
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at h; exact absurd h (by simp)
      | some ts =>
          simp only [hl] at h
          split at h
          · rename_i hnvs
            cases hp : st.pops ts with
            | none => simp only [hp] at h; exact absurd h (by simp)
            | some s =>
                simp only [hp] at h
                injection h with h; subst h
                have hsv : s.vals.reverse.all ValType.nvb = true :=
                  all_reverse (pops_nvb hp hnvb)
                have hall : (s.vals.reverse ++ ts).all ValType.nvb = true := by
                  simp only [List.all_append, Bool.and_eq_true]
                  exact ⟨hsv, nvs_nvb hnvs⟩
                refine ⟨[], s.vals.reverse ++ ts, tsm, [], [], rfl,
                  sat_append (ts := ts) hp (sat_own s), hall, ?_, rfl,
                  (fun j a b ha _ => by simp at ha), rfl⟩
                exact Instr_ok'.lift (Instr_ok.br hl
                  (.mk (resulttype_ok_of_nvb hsv) (resulttype_ok_of_nvb hts)
                    (fun a ha => by simp at ha)))
          · exact absurd h (by simp)
  case ret =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_ret] at h
      cases hl : C.ret with
      | none => simp only [hl] at h; exact absurd h (by simp)
      | some ts =>
          simp only [hl] at h
          split at h
          · rename_i hnvs
            cases hp : st.pops ts with
            | none => simp only [hp] at h; exact absurd h (by simp)
            | some s =>
                simp only [hp] at h
                injection h with h; subst h
                have hsv : s.vals.reverse.all ValType.nvb = true :=
                  all_reverse (pops_nvb hp hnvb)
                have hall : (s.vals.reverse ++ ts).all ValType.nvb = true := by
                  simp only [List.all_append, Bool.and_eq_true]
                  exact ⟨hsv, nvs_nvb hnvs⟩
                refine ⟨[], s.vals.reverse ++ ts, tsm, [], [], rfl,
                  sat_append (ts := ts) hp (sat_own s), hall, ?_, rfl,
                  (fun j a b ha _ => by simp at ha), rfl⟩
                exact Instr_ok'.lift (Instr_ok.ret hl
                  (.mk (resulttype_ok_of_nvb hsv) (resulttype_ok_of_nvb hts)
                    (fun a ha => by simp at ha)))
          · exact absurd h (by simp)
  case block bt body =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_block] at h
      cases hbt : blockType C bt with
      | none => simp only [hbt] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨ts₁, ts₂⟩ := p
          simp only [hbt] at h
          cases hp : st.pops ts₁ with
          | none => simp only [hp] at h; exact absurd h (by simp)
          | some st₀ =>
              simp only [hp] at h
              cases hb : checkSeq (Context.pushLabel ts₂ C) ((St.mk false []).pushs ts₁) body with
              | none => simp only [hb] at h; exact absurd h (by simp)
              | some stB =>
                  simp only [hb] at h
                  split at h
                  · rename_i hfin
                    injection h with h; subst h
                    obtain ⟨hbtok, hnv₁, hnv₂⟩ := blockType_sound hbt
                    obtain ⟨rs, cs, he, hs, hsat₀⟩ := pops_split_sat ts₂ hsat
                    have hcs : ts₂ = cs := subs_eq_of_nv hs hnv₂
                    obtain ⟨tsA, xsA, hsatA, hnvbA, hokA⟩ :=
                      hbody body (InstrSeq.size_body_block bt body)
                        (Context.pushLabel ts₂ C) _ stB ts₂ hb
                        (pushs_nvb rfl (nvs_nvb hnv₁)) (finish_iff_sat.mp hfin) (nvs_nvb hnv₂)
                    obtain ⟨rs', cs', heA, hsA, hsatE⟩ := pops_split_sat ts₁ hsatA
                    have hrs' : rs' = [] := sat_empty_false hsatE
                    have htsA : tsA = ts₁ := by
                      rw [heA, hrs', ← subs_eq_of_nv hsA hnv₁]; rfl
                    rw [htsA] at hokA
                    have hrs : rs.all ValType.nvb = true := by
                      rw [he] at hts; exact all_of_append_left hts
                    refine ⟨rs, ts₁, ts₂, [], [], by rw [he, hcs],
                      sat_append (ts := ts₁) hp hsat₀, ?_, ?_,
                      rfl, (fun j a b ha _ => by simp at ha), rfl⟩
                    · simp only [List.all_append, Bool.and_eq_true]
                      exact ⟨hrs, nvs_nvb hnv₁⟩
                    · exact Instr_ok'.block hbtok hokA
                  · exact absurd h (by simp)
  case loop bt body =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_loop] at h
      cases hbt : blockType C bt with
      | none => simp only [hbt] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨ts₁, ts₂⟩ := p
          simp only [hbt] at h
          cases hp : st.pops ts₁ with
          | none => simp only [hp] at h; exact absurd h (by simp)
          | some st₀ =>
              simp only [hp] at h
              cases hb : checkSeq (Context.pushLabel ts₁ C) ((St.mk false []).pushs ts₁) body with
              | none => simp only [hb] at h; exact absurd h (by simp)
              | some stB =>
                  simp only [hb] at h
                  split at h
                  · rename_i hfin
                    injection h with h; subst h
                    obtain ⟨hbtok, hnv₁, hnv₂⟩ := blockType_sound hbt
                    obtain ⟨rs, cs, he, hs, hsat₀⟩ := pops_split_sat ts₂ hsat
                    have hcs : ts₂ = cs := subs_eq_of_nv hs hnv₂
                    obtain ⟨tsA, xsA, hsatA, hnvbA, hokA⟩ :=
                      hbody body (InstrSeq.size_body_loop bt body)
                        (Context.pushLabel ts₁ C) _ stB ts₂ hb
                        (pushs_nvb rfl (nvs_nvb hnv₁)) (finish_iff_sat.mp hfin) (nvs_nvb hnv₂)
                    obtain ⟨rs', cs', heA, hsA, hsatE⟩ := pops_split_sat ts₁ hsatA
                    have hrs' : rs' = [] := sat_empty_false hsatE
                    have htsA : tsA = ts₁ := by
                      rw [heA, hrs', ← subs_eq_of_nv hsA hnv₁]; rfl
                    rw [htsA] at hokA
                    have hrs : rs.all ValType.nvb = true := by
                      rw [he] at hts; exact all_of_append_left hts
                    refine ⟨rs, ts₁, ts₂, [], [], by rw [he, hcs],
                      sat_append (ts := ts₁) hp hsat₀, ?_, ?_,
                      rfl, (fun j a b ha _ => by simp at ha), rfl⟩
                    · simp only [List.all_append, Bool.and_eq_true]
                      exact ⟨hrs, nvs_nvb hnv₁⟩
                    · exact Instr_ok'.loop hbtok hokA
                  · exact absurd h (by simp)
  case ifElse bt thn els =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_if] at h
      cases hbt : blockType C bt with
      | none => simp only [hbt] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨ts₁, ts₂⟩ := p
          simp only [hbt] at h
          cases hcond : st.popE ValType.i32 with
          | none => simp only [hcond] at h; exact absurd h (by simp)
          | some s =>
              simp only [hcond] at h
              cases hp : s.pops ts₁ with
              | none => simp only [hp] at h; exact absurd h (by simp)
              | some st₀ =>
                  simp only [hp] at h
                  cases hT : checkSeq (Context.pushLabel ts₂ C) ((St.mk false []).pushs ts₁) thn with
                  | none => simp only [hT] at h; exact absurd h (by simp)
                  | some stT =>
                      cases hE : checkSeq (Context.pushLabel ts₂ C)
                          ((St.mk false []).pushs ts₁) els with
                      | none => simp only [hT, hE] at h; exact absurd h (by simp)
                      | some stE =>
                          simp only [hT, hE] at h
                          split at h
                          · rename_i hfin
                            injection h with h; subst h
                            simp only [Bool.and_eq_true] at hfin
                            obtain ⟨hbtok, hnv₁, hnv₂⟩ := blockType_sound hbt
                            obtain ⟨rs, cs, he, hs, hsat₀⟩ := pops_split_sat ts₂ hsat
                            have hcs : ts₂ = cs := subs_eq_of_nv hs hnv₂
                            have hstart : ((St.mk false []).pushs ts₁).vals.all ValType.nvb = true :=
                              pushs_nvb rfl (nvs_nvb hnv₁)
                            obtain ⟨tsT, xsT, hsatT, _, hokT⟩ :=
                              hbody thn (InstrSeq.size_body_thn bt thn els)
                                (Context.pushLabel ts₂ C) _ stT ts₂ hT hstart
                                (finish_iff_sat.mp hfin.1) (nvs_nvb hnv₂)
                            obtain ⟨tsE, xsE, hsatE', _, hokE⟩ :=
                              hbody els (InstrSeq.size_body_els bt thn els)
                                (Context.pushLabel ts₂ C) _ stE ts₂ hE hstart
                                (finish_iff_sat.mp hfin.2) (nvs_nvb hnv₂)
                            obtain ⟨rsT, csT, heT, hsT, hsatET⟩ := pops_split_sat ts₁ hsatT
                            obtain ⟨rsE, csE, heE, hsE, hsatEE⟩ := pops_split_sat ts₁ hsatE'
                            have htsT : tsT = ts₁ := by
                              rw [heT, sat_empty_false hsatET, ← subs_eq_of_nv hsT hnv₁]; rfl
                            have htsE : tsE = ts₁ := by
                              rw [heE, sat_empty_false hsatEE, ← subs_eq_of_nv hsE hnv₁]; rfl
                            have hrs : rs.all ValType.nvb = true := by
                              rw [he] at hts; exact all_of_append_left hts
                            have hpops : st.pops (ts₁ ++ [ValType.i32]) = some st₀ := by
                              rw [pops_append]
                              show (match st.popE ValType.i32 with
                                    | some s => s.pops ts₁ | none => none) = some st₀
                              rw [hcond]; exact hp
                            rw [htsT] at hokT
                            rw [htsE] at hokE
                            refine ⟨rs, ts₁ ++ [ValType.i32], ts₂, [], [], by rw [he, hcs],
                              sat_append (ts := ts₁ ++ [ValType.i32]) hpops hsat₀, ?_, ?_,
                              rfl, (fun j a b ha _ => by simp at ha), rfl⟩
                            · simp only [List.all_append, List.all_cons, List.all_nil,
                                Bool.and_eq_true]
                              exact ⟨hrs, nvs_nvb hnv₁, rfl, trivial⟩
                            · exact Instr_ok'.if_ hbtok hokT hokE
                          · exact absurd h (by simp)
  all_goals exact instr_sound_default rfl

theorem seq_sound_step (s : InstrSeq)
    (hi : ∀ i : Instr, Instr.size i < InstrSeq.size s → InstrSound i)
    (hr : ∀ s' : InstrSeq, InstrSeq.size s' < InstrSeq.size s → SeqSound s') :
    SeqSound s := by
  cases s with
  | nil =>
      intro C st st' ts₂ h hnvb hsat hts
      injection h with h; subst h
      refine ⟨ts₂, [], hsat, hts, ?_⟩
      have hf := Instrs_ok'.frame (C := C) (is := []) (ts := ts₂) (ts₁ := []) (ts₂ := [])
        (xs := []) Instrs_ok'.empty (resulttype_ok_of_nvb hts)
      simpa using hf
  | cons i rest =>
      intro C st st' ts₃ h hnvb hsat hts
      rw [checkSeq_cons] at h
      cases hI : checkInstr C st i with
      | none => rw [hI] at h; exact absurd h (by simp)
      | some st₁ =>
          rw [hI] at h
          obtain ⟨tsm, xs₂, hsatm, hnvbm, hokTail⟩ :=
            hr rest (InstrSeq.size_tail i rest) C st₁ st' ts₃ h (checkInstr_nvb hI hnvb) hsat hts
          obtain ⟨ts₀, ts₁, ts₂, xs₁, lts, hem, hsat₀, hnvb₀, hokHead, hlen, hall, hwl⟩ :=
            hi i (InstrSeq.size_head i rest) C st st₁ tsm hI hnvb hsatm hnvbm
          refine ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, hsat₀, hnvb₀, ?_⟩
          show Instrs_ok' C (i :: InstrSeq.toList rest) ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, ts₃⟩
          refine Instrs_ok'.seq hokHead hlen hall (resulttype_ok_of_nvb ?_) ?_
          · rw [hem] at hnvbm; exact all_of_append_left hnvbm
          · rw [hwl, ← hem]; exact hokTail

theorem seq_sound : ∀ (n : Nat) (s : InstrSeq), InstrSeq.size s ≤ n → SeqSound s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      exact seq_sound_step s (fun i hi => absurd hi (by omega))
        (fun s' hs' => absurd hs' (by omega))
  | succ n ih =>
      intro s hs
      refine seq_sound_step s (fun i hi => instr_sound_step i (fun body hb => ih body (by omega)))
        (fun s' hs' => ih s' (by omega))

/-- **SOUNDNESS OF THE SINGLE PASS.**  If the appendix's pass accepts the
sequence from the frame `st` and the frame it ends in reads as `ts₂`, then the
AMENDED declarative judgment derives the sequence at `ts₁ ->_(x*) ts₂` for a
`ts₁` the initial frame reads as.  Holds in EVERY context, for EVERY instruction
sequence: the algorithm rejects everything outside the decided fragment. -/
theorem checkSeq_sound {C : Context} {s : InstrSeq} {st st' : St} {ts₂ : List ValType}
    (h : checkSeq C st s = some st') (hnvb : st.vals.all ValType.nvb = true)
    (hsat : st'.Sat ts₂) (hts : ts₂.all ValType.nvb = true) :
    ∃ (ts₁ : List ValType) (xs : List LocalIdx),
      st.Sat ts₁ ∧ Instrs_ok' C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩ := by
  obtain ⟨ts₁, xs, h₁, _, h₂⟩ :=
    seq_sound (InstrSeq.size s) s (Nat.le_refl _) C st st' ts₂ h hnvb hsat hts
  exact ⟨ts₁, xs, h₁, h₂⟩

/-- ... and at the level of expressions, which is what the module rules
consume. -/
theorem checkExpr_sound {C : Context} {e : Expr} {ts : List ValType}
    (h : checkExpr C e ts = true) (hts : nvs ts = true) : Expr_ok' C e ts := by
  rw [checkExpr] at h
  cases hs : checkSeq C (St.mk false []) e with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some st =>
      rw [hs] at h
      obtain ⟨ts₁, xs, hsat, hok⟩ :=
        checkSeq_sound hs rfl (finish_iff_sat.mp h) (nvs_nvb hts)
      have hnil : ts₁ = [] := sat_empty_false hsat
      subst hnil
      exact .mk (Instrs_ok'.drop_locals hok (nvs_nvb hts))

/-! ## COMPLETENESS

Everything the amended judgment derives over the decided fragment, the single
pass accepts.  `Context.frag` and `Instr.frag` are the hypotheses
`Core/ValidateInstr.lean` already carries for `instrType_complete`; they are
what "the decided fragment" means. -/

theorem frag_pushLabel {C : Context} {ts : List ValType} (hC : Context.frag C = true)
    (hts : nvs ts = true) : Context.frag (Context.pushLabel ts C) = true := by
  simp only [Context.frag, Context.pushLabel, Bool.and_eq_true, List.all_cons] at hC ⊢
  exact ⟨⟨⟨⟨⟨hC.1.1.1.1.1, hts, hC.1.1.1.1.2⟩, hC.1.1.1.2⟩, hC.1.1.2⟩, hC.1.2⟩, hC.2⟩

/-- In a context of the decided fragment every local is already `SET`, so
`$with_locals` at the types the locals already have is the identity. -/
theorem withLocals_frag {C : Context} : ∀ {xs : List LocalIdx} {ts : List ValType},
    Context.frag C = true → SeqLen₂ xs ts →
    SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
      ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs ts →
    Context.withLocals C xs (ts.map (fun t => ⟨Init.set, t⟩)) = C := by
  intro xs
  induction xs with
  | nil =>
      intro ts _ hlen _
      cases ts with
      | nil => rfl
      | cons _ _ => simp only [SeqLen₂, List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      intro ts hC hlen hall
      cases ts with
      | nil => simp only [SeqLen₂, List.length_nil, List.length_cons] at hlen; omega
      | cons t ts =>
          obtain ⟨ini, hloc⟩ := hall 0 x t (by simp) (by simp)
          have hset := (frag_local hC hloc).1
          simp only at hset
          subst hset
          have hC' : Context.setLocal C x ⟨Init.set, t⟩ = C := by
            unfold Context.setLocal
            rw [list_set_self C.locals x.val ⟨Init.set, t⟩ hloc]
          show Context.withLocals (Context.setLocal C x ⟨Init.set, t⟩) xs
            (ts.map (fun t => ⟨Init.set, t⟩)) = C
          rw [hC']
          exact ih hC (by simp only [SeqLen₂, List.length_cons] at hlen ⊢; omega)
            (fun j a b ha hb => hall (j + 1) a b (by simpa using ha) (by simpa using hb))

theorem all_nvb_of_subs : ∀ {as bs : List ValType}, subs as bs = true →
    bs.all ValType.nvb = true → as.all ValType.nvb = true
  | [], _, _, _ => rfl
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hb => by
      simp only [subs_cons, Bool.and_eq_true] at h
      simp only [List.all_cons, Bool.and_eq_true] at hb ⊢
      refine ⟨?_, all_nvb_of_subs h.2 hb.2⟩
      simp only [subOf, Bool.or_eq_true, beq_iff_eq] at h
      rcases h.1 with h₁ | h₁
      · rw [h₁]; rfl
      · rw [h₁]; exact hb.1

/-- The completeness statement for one instruction. -/
def InstrComplete (i : Instr) : Prop :=
  ∀ (C : Context) (it : InstrType), Context.frag C = true → Instr.frag i = true →
    Instr_ok' C i it →
    ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
      ∃ st', checkInstr C st i = some st' ∧ le st' (st₀.pushs it.cod)

/-- The completeness statement for a sequence. -/
def SeqComplete (s : InstrSeq) : Prop :=
  ∀ (C : Context) (it : InstrType), Context.frag C = true → InstrSeq.frag s = true →
    Instrs_ok' C (InstrSeq.toList s) it → it.cod.all ValType.nvb = true →
    ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
      ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod)

/-! ### The three structured instructions

Their bodies are typed by the sequence judgment, so each is proved once and used
twice: from `Instr_ok'/block` and from `Instr_ok'/lift` carrying the pinned
`Instr_ok/block`, whose body derivation `Instrs_ok.to_amended` converts. -/

theorem block_complete {C : Context} {bt : BlockType} {body : InstrSeq}
    {ts₁ ts₂ : List ValType} {xs : List LocalIdx} {st st₀ : St}
    (hbody : SeqComplete body) (hC : Context.frag C = true)
    (hfragbt : BlockType.frag bt = true) (hfragb : InstrSeq.frag body = true)
    (hbt : Blocktype_ok C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩)
    (hpop : st.pops ts₁ = some st₀) :
    checkInstr C st (.block bt body) = some (st₀.pushs ts₂) := by
  have hbtok : blockType C bt = some (ts₁, ts₂) := blockType_complete hC hfragbt hbt
  obtain ⟨_, hnv₁, hnv₂⟩ := blockType_sound hbtok
  obtain ⟨stB, hB, hleB⟩ :=
    hbody (Context.pushLabel ts₂ C) ⟨ts₁, xs, ts₂⟩ (frag_pushLabel hC hnv₂) hfragb hok
      (nvs_nvb hnv₂) ((St.mk false []).pushs ts₁) (St.mk false [])
      (pushs_nvb rfl (nvs_nvb hnv₁)) (pushs_pops _ ts₁)
  have hsatB : stB.Sat ts₂ :=
    sat_mono hleB ⟨St.mk false [], pushs_pops _ ts₂, rfl⟩
  rw [checkInstr_block]
  simp only [hbtok, hpop, hB, if_pos (finish_iff_sat.mpr hsatB)]

theorem loop_complete {C : Context} {bt : BlockType} {body : InstrSeq}
    {ts₁ ts₂ : List ValType} {xs : List LocalIdx} {st st₀ : St}
    (hbody : SeqComplete body) (hC : Context.frag C = true)
    (hfragbt : BlockType.frag bt = true) (hfragb : InstrSeq.frag body = true)
    (hbt : Blocktype_ok C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_ok' (Context.pushLabel ts₁ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩)
    (hpop : st.pops ts₁ = some st₀) :
    checkInstr C st (.loop bt body) = some (st₀.pushs ts₂) := by
  have hbtok : blockType C bt = some (ts₁, ts₂) := blockType_complete hC hfragbt hbt
  obtain ⟨_, hnv₁, hnv₂⟩ := blockType_sound hbtok
  obtain ⟨stB, hB, hleB⟩ :=
    hbody (Context.pushLabel ts₁ C) ⟨ts₁, xs, ts₂⟩ (frag_pushLabel hC hnv₁) hfragb hok
      (nvs_nvb hnv₂) ((St.mk false []).pushs ts₁) (St.mk false [])
      (pushs_nvb rfl (nvs_nvb hnv₁)) (pushs_pops _ ts₁)
  have hsatB : stB.Sat ts₂ :=
    sat_mono hleB ⟨St.mk false [], pushs_pops _ ts₂, rfl⟩
  rw [checkInstr_loop]
  simp only [hbtok, hpop, hB, if_pos (finish_iff_sat.mpr hsatB)]

theorem if_complete {C : Context} {bt : BlockType} {thn els : InstrSeq}
    {ts₁ ts₂ : List ValType} {xs₁ xs₂ : List LocalIdx} {st s st₀ : St}
    (hthn : SeqComplete thn) (hels : SeqComplete els) (hC : Context.frag C = true)
    (hfragbt : BlockType.frag bt = true) (hfragT : InstrSeq.frag thn = true)
    (hfragE : InstrSeq.frag els = true)
    (hbt : Blocktype_ok C bt ⟨ts₁, [], ts₂⟩)
    (hokT : Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList thn) ⟨ts₁, xs₁, ts₂⟩)
    (hokE : Instrs_ok' (Context.pushLabel ts₂ C) (InstrSeq.toList els) ⟨ts₁, xs₂, ts₂⟩)
    (hcond : st.popE ValType.i32 = some s) (hpop : s.pops ts₁ = some st₀) :
    checkInstr C st (.ifElse bt thn els) = some (st₀.pushs ts₂) := by
  have hbtok : blockType C bt = some (ts₁, ts₂) := blockType_complete hC hfragbt hbt
  obtain ⟨_, hnv₁, hnv₂⟩ := blockType_sound hbtok
  have hstart : ((St.mk false []).pushs ts₁).vals.all ValType.nvb = true :=
    pushs_nvb rfl (nvs_nvb hnv₁)
  obtain ⟨stT, hT, hleT⟩ :=
    hthn (Context.pushLabel ts₂ C) ⟨ts₁, xs₁, ts₂⟩ (frag_pushLabel hC hnv₂) hfragT hokT
      (nvs_nvb hnv₂) _ (St.mk false []) hstart (pushs_pops _ ts₁)
  obtain ⟨stE, hE, hleE⟩ :=
    hels (Context.pushLabel ts₂ C) ⟨ts₁, xs₂, ts₂⟩ (frag_pushLabel hC hnv₂) hfragE hokE
      (nvs_nvb hnv₂) _ (St.mk false []) hstart (pushs_pops _ ts₁)
  have hsatT : stT.Sat ts₂ := sat_mono hleT ⟨St.mk false [], pushs_pops _ ts₂, rfl⟩
  have hsatE : stE.Sat ts₂ := sat_mono hleE ⟨St.mk false [], pushs_pops _ ts₂, rfl⟩
  rw [checkInstr_if]
  simp only [hbtok, hcond, hpop, hT, hE,
    if_pos (by simp [finish_iff_sat.mpr hsatT, finish_iff_sat.mpr hsatE] :
      (stT.finish ts₂ && stE.finish ts₂) = true)]

/-! ### One instruction -/

theorem instr_complete_default {C : Context} {i : Instr} {it : InstrType} {st st₀ : St}
    (hC : Context.frag C = true) (hfrag : Instr.frag i = true)
    (hsp : Instr.special i = false) (hd : Instr_ok C i it)
    (hpop : st.pops it.dom = some st₀) :
    checkInstr C st i = some (st₀.pushs it.cod) := by
  rw [checkInstr_eq_default hsp]
  simp only [instrType_complete hC hfrag hsp hd, hpop]

theorem instr_complete_step (i : Instr)
    (hbodies : ∀ body : InstrSeq, InstrSeq.size body < Instr.size i → SeqComplete body) :
    InstrComplete i := by
  intro C it hC hfrag hok st st₀ hnvb hpop
  cases hok with
  | block hbt hokb =>
      rename_i bt body _ _ _
      simp only [Instr.frag, Bool.and_eq_true] at hfrag
      exact ⟨_, block_complete (hbodies body (InstrSeq.size_body_block bt body)) hC
        hfrag.1 hfrag.2 hbt hokb hpop, le_refl _⟩
  | loop hbt hokb =>
      rename_i bt body _ _ _
      simp only [Instr.frag, Bool.and_eq_true] at hfrag
      exact ⟨_, loop_complete (hbodies body (InstrSeq.size_body_loop bt body)) hC
        hfrag.1 hfrag.2 hbt hokb hpop, le_refl _⟩
  | if_ hbt hokT hokE =>
      rename_i bt thn els ts₁ _ _ _
      simp only [Instr.frag, Bool.and_eq_true] at hfrag
      have hpop' : st.pops (ts₁ ++ [ValType.i32]) = some st₀ := hpop
      rw [pops_append] at hpop'
      cases hcond : st.pops [ValType.i32] with
      | none => rw [hcond] at hpop'; exact absurd hpop' (by simp)
      | some s =>
          rw [hcond] at hpop'
          exact ⟨_, if_complete (hbodies thn (InstrSeq.size_body_thn bt thn els))
            (hbodies els (InstrSeq.size_body_els bt thn els)) hC
            hfrag.1.1 hfrag.1.2 hfrag.2 hbt hokT hokE hcond hpop', le_refl _⟩
  | lift hd =>
      cases i
      case unreachable =>
          exact ⟨st.unreach, checkInstr_unreachable C st, le_unreach _ _ rfl rfl⟩
      case drop =>
          cases hd with
          | drop _ =>
              obtain ⟨u, hp, _⟩ := pop_of_popE (show st.popE _ = some st₀ from hpop)
              refine ⟨st₀, ?_, le_refl _⟩
              rw [checkInstr_drop]
              simp only [hp]
      case select ts =>
          cases ts with
          | some l => exact ⟨_, instr_complete_default hC hfrag rfl hd hpop, le_refl _⟩
          | none =>
              cases hd with
              | select_impl hokt hsub hnv =>
                  rename_i t _
                  have hpop' : st.pops [t, t, ValType.i32] = some st₀ := hpop
                  rw [pops_cons] at hpop'
                  cases hA : st.pops [t, ValType.i32] with
                  | none => rw [hA] at hpop'; exact absurd hpop' (by simp)
                  | some s₂ =>
                      rw [hA] at hpop'
                      rw [pops_cons] at hA
                      cases hB : st.pops [ValType.i32] with
                      | none => rw [hB] at hA; exact absurd hA (by simp)
                      | some s₁ =>
                          rw [hB] at hA
                          have hB' : st.popE ValType.i32 = some s₁ := hB
                          obtain ⟨t₁, hp₁, hs₁⟩ := pop_of_popE hA
                          obtain ⟨t₂, hp₂, hs₂⟩ := pop_of_popE hpop'
                          have hn₁ := popE_nvb hB' hnvb
                          have hn₂ := pop_nvb hp₁ hn₁
                          have hn₃ := pop_nvb hp₂ hn₂.2
                          have hor : (subOf t₁ t₂ || subOf t₂ t₁) = true := by
                            simp only [subOf, Bool.or_eq_true, beq_iff_eq] at hs₁ hs₂ ⊢
                            rcases hs₁ with h₁ | h₁
                            · exact Or.inl (Or.inl h₁)
                            · rcases hs₂ with h₂ | h₂
                              · exact Or.inr (Or.inl h₂)
                              · exact Or.inl (Or.inr (by rw [h₁, h₂]))
                          have hu : subOf (if t₁ == ValType.bot then t₂ else t₁) t = true := by
                            by_cases hb : (t₁ == ValType.bot) = true
                            · simp only [hb, if_pos]; exact hs₂
                            · simp only [hb, Bool.false_eq_true, if_false]; exact hs₁
                          refine ⟨st₀.push (if t₁ == ValType.bot then t₂ else t₁), ?_, ?_⟩
                          · rw [checkInstr_select]
                            simp only [hB', hp₁, hp₂,
                              if_pos (by simp [hn₂.1, hn₃.1, hor] :
                                ((ValType.nvb t₁ && ValType.nvb t₂) &&
                                  (subOf t₁ t₂ || subOf t₂ t₁)) = true)]
                          · refine pushs_le_of_subs (ts := [_]) (ts' := [t]) ?_
                            simp only [subs_cons, subs_nil, Bool.and_true]
                            exact hu
      case br l =>
          cases hd with
          | br hlab hitok =>
              rename_i ts ts₁ _
              have hpop' : st.pops (ts₁ ++ ts) = some st₀ := hpop
              rw [pops_append] at hpop'
              cases hs : st.pops ts with
              | none => rw [hs] at hpop'; exact absurd hpop' (by simp)
              | some s =>
                  refine ⟨st.unreach, ?_, le_unreach _ _ rfl rfl⟩
                  rw [checkInstr_br]
                  simp only [hlab, if_pos (frag_label hC hlab), hs]
      case ret =>
          cases hd with
          | ret hret hitok =>
              rename_i ts ts₁ _
              have hpop' : st.pops (ts₁ ++ ts) = some st₀ := hpop
              rw [pops_append] at hpop'
              cases hs : st.pops ts with
              | none => rw [hs] at hpop'; exact absurd hpop' (by simp)
              | some s =>
                  refine ⟨st.unreach, ?_, le_unreach _ _ rfl rfl⟩
                  rw [checkInstr_ret]
                  simp only [hret, if_pos (frag_ret hC hret), hs]
      case block bt body =>
          cases hd with
          | block hbt hokb =>
              simp only [Instr.frag, Bool.and_eq_true] at hfrag
              exact ⟨_, block_complete (hbodies body (InstrSeq.size_body_block bt body)) hC
                hfrag.1 hfrag.2 hbt hokb.to_amended hpop, le_refl _⟩
      case loop bt body =>
          cases hd with
          | loop hbt hokb =>
              simp only [Instr.frag, Bool.and_eq_true] at hfrag
              exact ⟨_, loop_complete (hbodies body (InstrSeq.size_body_loop bt body)) hC
                hfrag.1 hfrag.2 hbt hokb.to_amended hpop, le_refl _⟩
      case ifElse bt thn els =>
          cases hd with
          | if_ hbt hokT hokE =>
              rename_i ts₁ _ _ _
              simp only [Instr.frag, Bool.and_eq_true] at hfrag
              have hpop' : st.pops (ts₁ ++ [ValType.i32]) = some st₀ := hpop
              rw [pops_append] at hpop'
              cases hcond : st.pops [ValType.i32] with
              | none => rw [hcond] at hpop'; exact absurd hpop' (by simp)
              | some s =>
                  rw [hcond] at hpop'
                  exact ⟨_, if_complete (hbodies thn (InstrSeq.size_body_thn bt thn els))
                    (hbodies els (InstrSeq.size_body_els bt thn els)) hC
                    hfrag.1.1 hfrag.1.2 hfrag.2 hbt hokT.to_amended hokE.to_amended
                    hcond hpop', le_refl _⟩
      all_goals exact ⟨_, instr_complete_default hC hfrag rfl hd hpop, le_refl _⟩

/-! ### One sequence -/

theorem seq_complete_aux : ∀ {C : Context} {js : List Instr} {it : InstrType},
    Instrs_ok' C js it → ∀ s : InstrSeq, js = InstrSeq.toList s →
      (∀ i : Instr, Instr.size i < InstrSeq.size s → InstrComplete i) →
      (∀ s' : InstrSeq, InstrSeq.size s' < InstrSeq.size s → SeqComplete s') →
      Context.frag C = true → InstrSeq.frag s = true → it.cod.all ValType.nvb = true →
      ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
        ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod) := by
  intro C js it h
  induction h using Instrs_ok'.rec (motive_1 := fun _ _ _ _ => True)
  case empty =>
      intro s he _ _ _ _ _ st st₀ _ hpop
      have hs : s = InstrSeq.nil := by rw [← InstrSeq.ofList_toList s, ← he]; rfl
      subst hs
      have hpop' : st.pops [] = some st₀ := hpop
      injection hpop' with hpop'
      subst hpop'
      exact ⟨st, rfl, le_refl _⟩
  case seq C₁ i₁ is ts₀ ts₁ ts₂ ts₃ tsL xs₁ xs₂ hd hlen hall hrt htail _ _ =>
      intro s he hi hr hC hfrag hcod st st₀ hnvb hpop
      have hs : s = InstrSeq.cons i₁ (InstrSeq.ofList is) := by
        rw [← InstrSeq.ofList_toList s, ← he]; rfl
      subst hs
      simp only [InstrSeq.frag, Bool.and_eq_true] at hfrag
      have hpop' : st.pops (ts₀ ++ ts₁) = some st₀ := hpop
      rw [pops_append] at hpop'
      cases hsp : st.pops ts₁ with
      | none => rw [hsp] at hpop'; exact absurd hpop' (by simp)
      | some s₁ =>
          rw [hsp] at hpop'
          obtain ⟨stH, hI, hleH⟩ :=
            hi i₁ (InstrSeq.size_head i₁ (InstrSeq.ofList is)) C₁ ⟨ts₁, xs₁, ts₂⟩ hC hfrag.1 hd
              st s₁ hnvb hsp
          have hbig : (s₁.pushs ts₂).pops (ts₀ ++ ts₂) = some st₀ := by
            rw [pops_append, pushs_pops]; exact hpop'
          obtain ⟨stH', hp', hle'⟩ := pops_mono hleH hbig
          rw [withLocals_frag hC hlen hall] at htail
          obtain ⟨stR, hR, hleR⟩ :=
            hr (InstrSeq.ofList is) (InstrSeq.size_tail i₁ (InstrSeq.ofList is)) C₁
              ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ hC hfrag.2 (by rw [InstrSeq.toList_ofList]; exact htail)
              hcod stH stH' (checkInstr_nvb hI hnvb) hp'
          refine ⟨stR, ?_, le_trans hleR (pushs_mono hle' ts₃)⟩
          rw [checkSeq_cons, hI]
          exact hR
  case sub C₁ is it₁ it₂ hbase hsub hitok ih =>
      intro s he hi hr hC hfrag hcod st st₀ hnvb hpop
      obtain ⟨hdomsub, hcodsub, _⟩ := hsub
      have hpop' : st.pops it₁.dom = some st₀ := pops_sub hnvb hpop hdomsub
      have hsubs : subs it₁.cod it₂.cod = true := subs_of_resulttype_sub hcodsub hcod
      obtain ⟨st', hRun, hle⟩ :=
        ih s he hi hr hC hfrag (all_nvb_of_subs hsubs hcod) st st₀ hnvb hpop'
      exact ⟨st', hRun, le_trans hle (pushs_le_of_subs hsubs)⟩
  case frame C₁ is ts ts₁ ts₂ xs hbase hrt ih =>
      intro s he hi hr hC hfrag hcod st st₀ hnvb hpop
      have hpop' : st.pops (ts ++ ts₁) = some st₀ := hpop
      rw [pops_append] at hpop'
      cases hs : st.pops ts₁ with
      | none => rw [hs] at hpop'; exact absurd hpop' (by simp)
      | some s₁ =>
          rw [hs] at hpop'
          have hcod' : ts₂.all ValType.nvb = true :=
            all_of_append_right (show (ts ++ ts₂).all ValType.nvb = true from hcod)
          obtain ⟨st', hRun, hle⟩ := ih s he hi hr hC hfrag hcod' st s₁ hnvb hs
          refine ⟨st', hRun, ?_⟩
          show le st' (st₀.pushs (ts ++ ts₂))
          rw [pushs_append]
          exact le_trans hle (pushs_mono (pops_le hpop') ts₂)
  all_goals trivial

theorem seq_complete_step (s : InstrSeq)
    (hi : ∀ i : Instr, Instr.size i < InstrSeq.size s → InstrComplete i)
    (hr : ∀ s' : InstrSeq, InstrSeq.size s' < InstrSeq.size s → SeqComplete s') :
    SeqComplete s := by
  intro C it hC hfrag hok hcod st st₀ hnvb hpop
  exact seq_complete_aux hok s rfl hi hr hC hfrag hcod st st₀ hnvb hpop

theorem seq_complete : ∀ (n : Nat) (s : InstrSeq), InstrSeq.size s ≤ n → SeqComplete s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      exact seq_complete_step s (fun i hi => absurd hi (by omega))
        (fun s' hs' => absurd hs' (by omega))
  | succ n ih =>
      intro s hs
      exact seq_complete_step s
        (fun i hi => instr_complete_step i (fun body hb => ih body (by omega)))
        (fun s' hs' => ih s' (by omega))

/-- **COMPLETENESS OF THE SINGLE PASS.**  Over the decided fragment, every
instruction type the AMENDED declarative judgment gives a sequence is one the
appendix's pass computes: from a frame the declarative domain can be popped
from, the pass succeeds and lands in a frame at least as general as the one the
declarative codomain predicts. -/
theorem checkSeq_complete {C : Context} {s : InstrSeq} {it : InstrType} {st st₀ : St}
    (hC : Context.frag C = true) (hfrag : InstrSeq.frag s = true)
    (hok : Instrs_ok' C (InstrSeq.toList s) it) (hcod : it.cod.all ValType.nvb = true)
    (hnvb : st.vals.all ValType.nvb = true) (hpop : st.pops it.dom = some st₀) :
    ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod) :=
  seq_complete (InstrSeq.size s) s (Nat.le_refl _) C it hC hfrag hok hcod st st₀ hnvb hpop

/-- ... and at the level of expressions. -/
theorem checkExpr_complete {C : Context} {e : Expr} {ts : List ValType}
    (hC : Context.frag C = true) (hfrag : InstrSeq.frag e = true)
    (hok : Expr_ok' C e ts) (hts : nvs ts = true) : checkExpr C e ts = true := by
  cases hok with
  | mk hseq =>
      obtain ⟨st, hrun, hle⟩ :=
        checkSeq_complete (st := St.mk false []) (st₀ := St.mk false []) hC hfrag hseq
          (nvs_nvb hts) rfl rfl
      rw [checkExpr, hrun]
      exact finish_iff_sat.mpr (sat_mono hle ⟨St.mk false [], pushs_pops _ ts, rfl⟩)

end Validate
end WasmGemmGnaf.Wasm.Core
