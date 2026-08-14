/-
  Wasm/Core/ValidateSeq.lean --- the equivalence of the validation ALGORITHM of
  `vendor/wasm-spec/document/core/appendix/algorithm.rst` with the AMENDED
  declarative instruction judgment `Instrs_okA` of
  `Core/Validation/InstructionsCombinedAmended.lean`.

  WHY THE AMENDED RELATION AND NOT THE PINNED ONE.  `Core/ValidateInstr.lean`
  proves, kernel-checked, that the pinned `Instrs_ok` gives
  `(I32.CONST c) (BINOP I32 ADD)` no instruction type in any context
  (`Instrs_ok.const_binop_untypable`); the algorithm accepts that sequence, as
  every engine does, so a soundness theorem against the PINNED relation would be
  FALSE.  That is DEV-006 in `model/spec-deviations.json`; upstream filed the
  same finding as WebAssembly/spec issue #2194 and fixed it in PR #2197
  (`bd4633ac...`), nine months after the pin.  The two theorems below are stated
  over `Instrs_okA`, the combined amended hierarchy that carries the framed
  `Instrs_ok/seq` composition and corrected type/subtyping premises together.

  WHAT IS PROVED.

    `checkSeq_sound`     --- everything the single pass accepts, `Instrs_okA`
                             derives, in EVERY context, with no fragment
                             hypothesis on the context or the instructions.
    `checkSeq_complete`  --- everything `Instrs_okA` derives over the decided
                             fragment (`Context.frag`, `Instr.frag`), the single
                             pass accepts.
    `checkExpr_sound` / `checkExpr_complete` --- the same two at the level of
                             `Expr_okA`, which is what the module rules consume.

  THE SHAPE OF THE TWO STATEMENTS.  The algorithm is a single pass over an
  abstract operand stack (`St`), so neither direction is a plain implication
  between two propositions about the same objects; each has to say how the
  abstract state relates to a concrete `resulttype`:

    * SOUNDNESS reads the final state back.  `St.Sat st ts` --- `pop_vals(ts)`
      succeeds and lands exactly on the frame's `val_height` --- is that reading.
      From `checkSeq C st is = some st'` and `st'.Sat ts₂` the theorem produces a
      `ts₁` the INITIAL state satisfies together with an `Instrs_okA` derivation
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
  completeness it is forced by `Instrs_okA/sub` and `Instrs_okA/frame`, which do
  not change the subject, and by `Instr_okA/lift`, which carries a PINNED
  `Instr_ok` whose `block`/`loop`/`if` bodies are pinned `Instrs_ok` derivations
  and hence supply no induction hypothesis of their own.  Recurring on the
  syntax makes the body of a structured instruction available in both cases, and
  the derivation is then consumed by an inner induction (completeness) or by
  inversion (soundness).

  NO COVERAGE MARKER.  Nothing here transcribes a pinned rule, so no declaration
  in this file carries one; the Core 3.0 inventory is unchanged.
-/
import WasmGemmGnaf.Wasm.Core.ValidateInstr
import WasmGemmGnaf.Wasm.Core.Validation.InstructionsCombinedAmended

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

open St

/-! ## The type-bearing part of a validation context

Local initialization and control labels change while the single pass runs, but
the type and recursive-type components do not.  The predicates below state
validity uniformly over every context with the same two components.  This
avoids treating a local-set update or a pushed label as a change of the type
environment. -/

def SameTypeEnv (C D : Context) : Prop :=
  C.types = D.types ∧ C.recs = D.recs

namespace SameTypeEnv

theorem refl (C : Context) : SameTypeEnv C C := ⟨rfl, rfl⟩

theorem symm {C D : Context} (h : SameTypeEnv C D) : SameTypeEnv D C :=
  ⟨h.1.symm, h.2.symm⟩

theorem trans {C D E : Context} (h₁ : SameTypeEnv C D)
    (h₂ : SameTypeEnv D E) : SameTypeEnv C E :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end SameTypeEnv

/-- Full result-type matching is unaffected by local-initialization and
control-label updates. -/
theorem subsA_sameTypeEnv {C D : Context} (hCD : SameTypeEnv C D)
    (ts us : List ValType) : subsA C ts us = subsA D ts us := by
  have hf : C.subtypeFuel = D.subtypeFuel := by
    simp only [Context.subtypeFuel, hCD.1, hCD.2]
  unfold subsA
  rw [hf]
  exact decResulttypeSubN_eq_of_types_eq hCD.1 D.subtypeFuel ts us

theorem subOfA_sameTypeEnv {C D : Context} (hCD : SameTypeEnv C D)
    (t u : ValType) : subOfA C t u = subOfA D t u := by
  have hf : C.subtypeFuel = D.subtypeFuel := by
    simp only [Context.subtypeFuel, hCD.1, hCD.2]
  unfold subOfA
  rw [hf]
  exact decValtypeSubN_eq_of_types_eq hCD.1 D.subtypeFuel t u

theorem St.popEA_sameTypeEnv {C D : Context} (hCD : SameTypeEnv C D)
    (st : St) (t : ValType) : st.popEA C t = st.popEA D t := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil => rfl
      | cons a rest => simp [St.popEA, subOfA_sameTypeEnv hCD]

theorem St.popsA_sameTypeEnv {C D : Context} (hCD : SameTypeEnv C D) :
    ∀ (st : St) (ts : List ValType), st.popsA C ts = st.popsA D ts := by
  intro st ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [St.popsA, ih]
      cases hp : st.popsA D ts with
      | none => rfl
      | some s => exact St.popEA_sameTypeEnv hCD s t

theorem St.SatA.transport {C D : Context} (hCD : SameTypeEnv C D)
    {st : St} {ts : List ValType} (h : St.SatA C st ts) : St.SatA D st ts := by
  obtain ⟨st', hp, hv⟩ := h
  exact ⟨st', by rw [← St.popsA_sameTypeEnv hCD]; exact hp, hv⟩

/-- A result type remains valid while only locals, labels, or return state are
changed. -/
def ResultValidA (C : Context) (ts : List ValType) : Prop :=
  ∀ D : Context, SameTypeEnv C D → Resulttype_okA D ts

/-- Single-value form of `ResultValidA`. -/
def ValValidA (C : Context) (t : ValType) : Prop :=
  ∀ D : Context, SameTypeEnv C D → Valtype_okA D t

namespace ResultValidA

theorem transport {C D : Context} {ts : List ValType} (hCD : SameTypeEnv C D)
    (h : ResultValidA C ts) : ResultValidA D ts := by
  intro E hDE
  exact h E (SameTypeEnv.trans hCD hDE)

theorem nil (C : Context) : ResultValidA C [] := by
  intro _ _
  exact .mk (fun t ht => nomatch ht)

theorem cons {C : Context} {t : ValType} {ts : List ValType}
    (ht : ∀ D : Context, SameTypeEnv C D → Valtype_okA D t)
    (hts : ResultValidA C ts) : ResultValidA C (t :: ts) := by
  intro D hCD
  exact .mk (fun u hu => by
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ht D hCD
    · cases hts D hCD with
      | mk hall => exact hall u hu)

theorem append {C : Context} {ts us : List ValType}
    (hts : ResultValidA C ts) (hus : ResultValidA C us) :
    ResultValidA C (ts ++ us) := by
  intro D hCD
  cases hts D hCD with
  | mk hts' =>
      cases hus D hCD with
      | mk hus' =>
          exact .mk (fun t ht => by
            rw [List.mem_append] at ht
            exact ht.elim (hts' t) (hus' t))

theorem of_append_left {C : Context} {ts us : List ValType}
    (h : ResultValidA C (ts ++ us)) : ResultValidA C ts := by
  intro D hCD
  cases h D hCD with
  | mk hall => exact .mk (fun t ht => hall t (List.mem_append_left _ ht))

theorem of_append_right {C : Context} {ts us : List ValType}
    (h : ResultValidA C (ts ++ us)) : ResultValidA C us := by
  intro D hCD
  cases h D hCD with
  | mk hall => exact .mk (fun t ht => hall t (List.mem_append_right _ ht))

theorem reverse {C : Context} {ts : List ValType}
    (h : ResultValidA C ts) : ResultValidA C ts.reverse := by
  intro D hCD
  cases h D hCD with
  | mk hall => exact .mk (fun t ht => hall t (by simpa using ht))

end ResultValidA

namespace ValValidA

theorem transport {C D : Context} {t : ValType} (hCD : SameTypeEnv C D)
    (h : ValValidA C t) : ValValidA D t := by
  intro E hDE
  exact h E (SameTypeEnv.trans hCD hDE)

theorem num (C : Context) (nt : NumType) : ValValidA C (.num nt) := by
  intro _ _
  exact .num .mk

theorem vec (C : Context) (vt : VecType) : ValValidA C (.vec vt) := by
  intro _ _
  exact .vec .mk

theorem bot (C : Context) : ValValidA C .bot := by
  intro _ _
  exact .bot

theorem refAbs (C : Context) (nul : Option Null) (a : AbsHeapType) :
    ValValidA C (.ref (.ref nul (.abs a))) := by
  intro _ _
  exact .ref (.mk .abs)

theorem addr (C : Context) (a : AddrType) : ValValidA C a.toValType := by
  cases a <;> exact ValValidA.num C _

theorem refIdx {C : Context} {x : TypeIdx} {dt : DefType}
    (hx : C.types[x.val]? = some dt) (nul : Option Null) :
    ValValidA C (.ref (.ref nul (.use (.idx x)))) := by
  intro D hD
  exact .ref (.mk (.typeuse (.typeidx (by simpa [← hD.1] using hx))))

end ValValidA

theorem ResultValidA.singleton {C : Context} {t : ValType}
    (h : ValValidA C t) : ResultValidA C [t] :=
  ResultValidA.cons h (ResultValidA.nil C)

theorem ResultValidA.pair {C : Context} {t₁ t₂ : ValType}
    (h₁ : ValValidA C t₁) (h₂ : ValValidA C t₂) :
    ResultValidA C [t₁, t₂] :=
  ResultValidA.cons h₁ (ResultValidA.singleton h₂)

theorem ResultValidA.triple {C : Context} {t₁ t₂ t₃ : ValType}
    (h₁ : ValValidA C t₁) (h₂ : ValValidA C t₂) (h₃ : ValValidA C t₃) :
    ResultValidA C [t₁, t₂, t₃] :=
  ResultValidA.cons h₁ (ResultValidA.pair h₂ h₃)

theorem valValidA_of_result_singleton {C : Context} {t : ValType}
    (h : ResultValidA C [t]) : ValValidA C t := by
  intro D hD
  cases h D hD with
  | mk hall => exact hall t (by simp)

theorem valValidA_unpack {C : Context} {zt : StorageType}
    (h : ∀ D : Context, SameTypeEnv C D → Storagetype_okA D zt) :
    ValValidA C zt.unpack := by
  intro D hD
  cases zt with
  | val t =>
      cases h D hD with
      | val ht => exact ht
  | pack pt => exact .num .mk

theorem valtype_okA_unpack {C : Context} {zt : StorageType}
    (h : Storagetype_okA C zt) : Valtype_okA C zt.unpack := by
  cases h with
  | val ht => exact ht
  | pack _ => exact .num .mk

theorem ResultValidA.replicate {C : Context} {t : ValType}
    (ht : ValValidA C t) (n : Nat) : ResultValidA C (List.replicate n t) := by
  intro D hD
  exact .mk (fun u hu => by
    rw [List.mem_replicate] at hu
    have hut : u = t := hu.2
    subst u
    exact ht D hD)

theorem checkHeaptypeOkA_same {C D : Context} (hCD : SameTypeEnv C D)
    (ht : HeapType) : checkHeaptypeOkA C ht = checkHeaptypeOkA D ht := by
  cases ht with
  | abs _ => rfl
  | use tu =>
      cases tu with
      | idx x => simp [checkHeaptypeOkA, hCD.1]
      | recu i => simp [checkHeaptypeOkA, hCD.2]
      | defd _ => rfl

theorem valValidA_ref_of_checkHeap {C : Context} {ht : HeapType}
    (h : checkHeaptypeOkA C ht = true) (nul : Option Null) :
    ValValidA C (.ref (.ref nul ht)) := by
  intro D hCD
  exact .ref (.mk (checkHeaptypeOkA_sound (by
    rw [← checkHeaptypeOkA_same hCD]
    exact h)))

theorem checkValtypeOkA_same {C D : Context} (hCD : SameTypeEnv C D)
    (t : ValType) : checkValtypeOkA C t = checkValtypeOkA D t := by
  cases t with
  | num _ | vec _ | bot => rfl
  | ref rt =>
      cases rt with
      | ref _ ht => exact checkHeaptypeOkA_same hCD ht

theorem valValidA_of_check {C : Context} {t : ValType}
    (h : checkValtypeOkA C t = true) : ValValidA C t := by
  intro D hCD
  exact checkValtypeOkA_sound (by
    rw [← checkValtypeOkA_same hCD]
    exact h)

theorem valValidA_ref_of_check {C : Context} {rt : RefType}
    (h : checkReftypeOkA C rt = true) : ValValidA C (.ref rt) :=
  valValidA_of_check (by simpa [checkValtypeOkA] using h)

/-- Exactly the context facts that can place a value type on the operand stack
or in a control signature.  Every type judgment is quantified over dynamic
context variants with the same `TYPES` and `RECS` components. -/
structure Context.ValidA (C : Context) : Prop where
  types {D : Context} (hD : SameTypeEnv C D) {x : TypeIdx} {dt : DefType}
      {ct : CompType} :
    C.types[x.val]? = some dt → Expand dt ct → Comptype_okA D ct
  funcs {D : Context} (hD : SameTypeEnv C D) {x : FuncIdx} {dt : DefType}
      {ct : CompType} :
    C.funcs[x.val]? = some dt → Expand dt ct → Comptype_okA D ct
  funcHeap {D : Context} (hD : SameTypeEnv C D) {x : FuncIdx} {dt : DefType} :
    C.funcs[x.val]? = some dt → Heaptype_okA D (.use (.defd dt))
  tags {D : Context} (hD : SameTypeEnv C D) {x : TagIdx} {jt : TagType}
      {dt : DefType} {dom : ValTypes} :
    C.tags[x.val]? = some jt → asDefType jt = some dt →
    Expand dt (.func dom .nil) → Resulttype_okA D (ValTypes.toList dom)
  globals {D : Context} (hD : SameTypeEnv C D) {x : GlobalIdx}
      {gt : GlobalType} :
    C.globals[x.val]? = some gt → Valtype_okA D gt.valtype
  tables {D : Context} (hD : SameTypeEnv C D) {x : TableIdx}
      {tt : TableType} :
    C.tables[x.val]? = some tt → Reftype_okA D tt.elem
  elems {D : Context} (hD : SameTypeEnv C D) {x : ElemIdx} {rt : RefType} :
    C.elems[x.val]? = some rt → Reftype_okA D rt
  locals {D : Context} (hD : SameTypeEnv C D) {x : LocalIdx}
      {lt : LocalType} :
    C.locals[x.val]? = some lt → Valtype_okA D lt.valtype
  labels {D : Context} (hD : SameTypeEnv C D) {x : LabelIdx}
      {ts : List ValType} :
    C.labels[x.val]? = some ts → Resulttype_okA D ts
  ret {D : Context} (hD : SameTypeEnv C D) {ts : List ValType} :
    C.ret = some ts → Resulttype_okA D ts

namespace Context.ValidA

theorem pushLabel {C : Context} {ts : List ValType} (hC : ValidA C)
    (hts : ResultValidA C ts) : ValidA (Context.pushLabel ts C) := by
  constructor
  · intro D hD x dt ct hx he
    exact hC.types (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx) he
  · intro D hD x dt ct hx he
    exact hC.funcs (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx) he
  · intro D hD x dt hx
    exact hC.funcHeap (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)
  · intro D hD x jt dt dom hx hj he
    exact hC.tags (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx) hj he
  · intro D hD x gt hx
    exact hC.globals (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)
  · intro D hD x tt hx
    exact hC.tables (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)
  · intro D hD x rt hx
    exact hC.elems (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)
  · intro D hD x lt hx
    exact hC.locals (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)
  · intro D hD x us hx
    have hCD : SameTypeEnv C D := by
      simpa [SameTypeEnv, Context.pushLabel] using hD
    cases hn : x.val with
    | zero =>
        have hx' : some ts = some us := by
          simpa [Context.pushLabel, hn] using hx
        have heq : us = ts := (Option.some.inj hx').symm
        subst us
        exact hts D hCD
    | succ n =>
        let y : LabelIdx := ⟨n, by have hb := x.property; omega⟩
        exact hC.labels (x := y) hCD
          (by simpa [Context.pushLabel, hn, y] using hx)
  · intro D hD us hx
    exact hC.ret (D := D) (by simpa [SameTypeEnv, Context.pushLabel] using hD)
      (by simpa [Context.pushLabel] using hx)

theorem setLocal {C : Context} {x : LocalIdx} {lt : LocalType}
    (hC : ValidA C) (hx : C.locals[x.val]? = some lt) :
    ValidA (C.setLocal x ⟨.set, lt.valtype⟩) := by
  constructor
  · intro D hD y dt ct hy he
    exact hC.types (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy) he
  · intro D hD y dt ct hy he
    exact hC.funcs (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy) he
  · intro D hD y dt hy
    exact hC.funcHeap (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)
  · intro D hD y jt dt dom hy hj he
    exact hC.tags (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy) hj he
  · intro D hD y gt hy
    exact hC.globals (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)
  · intro D hD y tt hy
    exact hC.tables (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)
  · intro D hD y rt hy
    exact hC.elems (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)
  · intro D hD y lty hy
    have hCD : SameTypeEnv C D := by
      simpa [SameTypeEnv, Context.setLocal] using hD
    by_cases heq : y.val = x.val
    · have hyx : y = x := Subtype.ext heq
      subst y
      have hlt : x.val < C.locals.length :=
        (List.getElem?_eq_some_iff.mp hx).1
      have hy' : some ⟨Init.set, lt.valtype⟩ = some lty := by
        simpa [Context.setLocal, List.getElem?_set_self hlt] using hy
      have hly : lty = ⟨Init.set, lt.valtype⟩ := (Option.some.inj hy').symm
      subst lty
      exact hC.locals (x := x) (lt := lt) hCD hx
    · exact hC.locals (x := y) (lt := lty) hCD (by
        simpa [Context.setLocal, List.getElem?_set_ne (Ne.symm heq)] using hy)
  · intro D hD y us hy
    exact hC.labels (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)
  · intro D hD us hy
    exact hC.ret (D := D) (by simpa [SameTypeEnv, Context.setLocal] using hD)
      (by simpa [Context.setLocal] using hy)

theorem setEffects : ∀ {C C' : Context} {xs : List LocalIdx},
    ValidA C → Context.setEffects C xs = some C' → ValidA C'
  | C, C', [], hC, h => by
      simp only [Context.setEffects, Option.some.injEq] at h
      subst C'
      exact hC
  | C, C', x :: xs, hC, h => by
      simp only [Context.setEffects] at h
      cases hx : C.locals[x.val]? with
      | none => simp only [hx] at h; contradiction
      | some lt =>
          simp only [hx] at h
          exact setEffects (setLocal hC hx) h

end Context.ValidA

namespace Context.ValidA

theorem typeFuncDom {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {dom cod : ValTypes} (hx : C.types[x.val]? = some dt)
    (he : Expand dt (.func dom cod)) :
    ResultValidA C (ValTypes.toList dom) := by
  intro D hD
  cases hC.types hD hx he with
  | func hdom _ => exact hdom

theorem typeFuncCod {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {dom cod : ValTypes} (hx : C.types[x.val]? = some dt)
    (he : Expand dt (.func dom cod)) :
    ResultValidA C (ValTypes.toList cod) := by
  intro D hD
  cases hC.types hD hx he with
  | func _ hcod => exact hcod

theorem funcDom {C : Context} (hC : ValidA C) {x : FuncIdx}
    {dt : DefType} {dom cod : ValTypes} (hx : C.funcs[x.val]? = some dt)
    (he : Expand dt (.func dom cod)) :
    ResultValidA C (ValTypes.toList dom) := by
  intro D hD
  cases hC.funcs hD hx he with
  | func hdom _ => exact hdom

theorem funcCod {C : Context} (hC : ValidA C) {x : FuncIdx}
    {dt : DefType} {dom cod : ValTypes} (hx : C.funcs[x.val]? = some dt)
    (he : Expand dt (.func dom cod)) :
    ResultValidA C (ValTypes.toList cod) := by
  intro D hD
  cases hC.funcs hD hx he with
  | func _ hcod => exact hcod

theorem typeStructField {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {fts : FieldTypes} {i : Nat} {ft : FieldType}
    (hx : C.types[x.val]? = some dt) (he : Expand dt (.struct fts))
    (hi : (FieldTypes.toList fts)[i]? = some ft) :
    ∀ D : Context, SameTypeEnv C D → Fieldtype_okA D ft := by
  intro D hD
  cases hC.types hD hx he with
  | struct hall =>
      exact hall ft (List.mem_of_getElem? hi)

theorem typeStructUnpacked {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {fts : FieldTypes} (hx : C.types[x.val]? = some dt)
    (he : Expand dt (.struct fts)) : ResultValidA C fts.unpacked := by
  intro D hD
  cases hC.types hD hx he with
  | struct hall =>
      exact .mk (fun t ht => by
        obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp ht
        cases hall ft hft with
        | mk hzt => exact valtype_okA_unpack hzt)

theorem typeArrayField {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {ft : FieldType} (hx : C.types[x.val]? = some dt)
    (he : Expand dt (.array ft)) :
    ∀ D : Context, SameTypeEnv C D → Fieldtype_okA D ft := by
  intro D hD
  cases hC.types hD hx he with
  | array hft => exact hft

theorem typeArrayUnpack {C : Context} (hC : ValidA C) {x : TypeIdx}
    {dt : DefType} {ft : FieldType} (hx : C.types[x.val]? = some dt)
    (he : Expand dt (.array ft)) : ValValidA C ft.storage.unpack := by
  intro D hD
  cases hC.typeArrayField hx he D hD with
  | mk hzt => exact valtype_okA_unpack hzt

theorem localVal {C : Context} (hC : ValidA C) {x : LocalIdx}
    {lt : LocalType} (hx : C.locals[x.val]? = some lt) :
    ValValidA C lt.valtype := fun D hD => hC.locals hD hx

theorem globalVal {C : Context} (hC : ValidA C) {x : GlobalIdx}
    {gt : GlobalType} (hx : C.globals[x.val]? = some gt) :
    ValValidA C gt.valtype := fun D hD => hC.globals hD hx

theorem tableVal {C : Context} (hC : ValidA C) {x : TableIdx}
    {tt : TableType} (hx : C.tables[x.val]? = some tt) :
    ValValidA C (.ref tt.elem) := fun D hD => .ref (hC.tables hD hx)

theorem elemVal {C : Context} (hC : ValidA C) {x : ElemIdx}
    {rt : RefType} (hx : C.elems[x.val]? = some rt) :
    ValValidA C (.ref rt) := fun D hD => .ref (hC.elems hD hx)

end Context.ValidA

/-! ## Result validity of the unrestricted fixed dispatcher -/

theorem instrTypeA_cod_valid {C : Context} {i : Instr} {it : InstrType}
    (hC : Context.ValidA C) (h : instrTypeA C i = some it) :
    ResultValidA C it.cod := by
  rw [instrTypeA] at h
  by_cases hwf : Instr.wf i = true
  · rw [if_pos hwf] at h
    unfold instrTypeRawA at h
    split at h
    · rename_i t
      split at h
      · rename_i ht
        injection h with h; subst h
        exact ResultValidA.singleton (valValidA_of_check ht)
      · contradiction
    · contradiction
    · rename_i l
      split at h
      · rename_i ts hl
        injection h with h; subst h
        exact fun D hD => hC.labels hD hl
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact hC.funcCod hx (.mk he)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact hC.typeFuncCod hx (.mk he)
        · contradiction
      · contradiction
    · contradiction
    · rename_i x y
      split at h
      · rename_i tt dt hx hy
        split at h
        · unfold funcTypeOfA at h
          split at h
          · rename_i dom cod he
            injection h with h; subst h
            exact hC.typeFuncCod hy (.mk he)
          · contradiction
        · contradiction
      · contradiction
    · contradiction
    · rename_i x
      split at h
      · rename_i t hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.localVal hx)
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · rename_i ini t hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.localVal hx)
      · contradiction
    · rename_i x
      split at h
      · rename_i gt hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.globalVal hx)
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i ht
      split at h
      · rename_i hok
        injection h with h; subst h
        exact ResultValidA.singleton
          (valValidA_ref_of_checkHeap hok (some .null))
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · injection h with h; subst h
          exact ResultValidA.singleton (fun D hD =>
            .ref (.mk (hC.funcHeap hD hx)))
        · contradiction
      · contradiction
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.refAbs C none .i31)
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.num C .i32)
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.num C .i32)
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · injection h with h; subst h
          exact ResultValidA.singleton (ValValidA.refIdx hx none)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (ValValidA.refIdx hx none)
          · contradiction
        · contradiction
      · contradiction
    · rename_i sx x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          split at h
          · rename_i m zt hft
            split at h
            · injection h with h; subst h
              exact ResultValidA.singleton (valValidA_unpack (fun D hD => by
                cases hC.typeStructField hx (.mk he) hft D hD with
                | mk hzt => exact hzt))
            · contradiction
          · contradiction
        · contradiction
      · contradiction
    · rename_i x n
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.nil C
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · injection h with h; subst h
          exact ResultValidA.singleton (ValValidA.refIdx hx none)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (ValValidA.refIdx hx none)
          · contradiction
        · contradiction
      · contradiction
    · rename_i x n
      split at h
      · rename_i dt hx
        split at h
        · injection h with h; subst h
          exact ResultValidA.singleton (ValValidA.refIdx hx none)
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · rename_i dt rt hx hy
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (ValValidA.refIdx hx none)
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · rename_i dt hx hy
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (ValValidA.refIdx hx none)
          · contradiction
        · contradiction
      · contradiction
    · rename_i sx x
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (valValidA_unpack (fun D hD => by
              cases hC.typeArrayField hx (.mk he) D hD with
              | mk hzt => exact hzt))
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · split at h
        · injection h with h; subst h
          exact ResultValidA.nil C
        · contradiction
      · contradiction
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.num C .i32)
    · rename_i x
      split at h
      · split at h
        · injection h with h; subst h
          exact ResultValidA.nil C
        · contradiction
      · contradiction
    · rename_i x₁ x₂
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.nil C
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.nil C
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.nil C
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.tableVal hx)
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        cases tt.addr <;>
          exact ResultValidA.singleton (ValValidA.num C _)
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.singleton (ValValidA.num C .i32)
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x₁ x₂
      split at h
      · split at h
        · injection h with h; subst h
          exact ResultValidA.nil C
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · split at h
        · injection h with h; subst h
          exact ResultValidA.nil C
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · contradiction
  · rw [if_neg hwf] at h
    contradiction

theorem instrTypeA_dom_valid {C : Context} {i : Instr} {it : InstrType}
    (hC : Context.ValidA C) (h : instrTypeA C i = some it) :
    ResultValidA C it.dom := by
  rw [instrTypeA] at h
  by_cases hwf : Instr.wf i = true
  · rw [if_pos hwf] at h
    unfold instrTypeRawA at h
    split at h
    · rename_i t
      split at h
      · rename_i ht
        injection h with h; subst h
        exact ResultValidA.triple (valValidA_of_check ht)
          (valValidA_of_check ht) (ValValidA.num C .i32)
      · contradiction
    · contradiction
    · rename_i l
      split at h
      · rename_i ts hl
        injection h with h; subst h
        exact ResultValidA.append (fun D hD => hC.labels hD hl)
          (ResultValidA.singleton (ValValidA.num C .i32))
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact hC.funcDom hx (.mk he)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact ResultValidA.append (hC.typeFuncDom hx (.mk he))
            (ResultValidA.singleton (ValValidA.refIdx hx (some .null)))
        · contradiction
      · contradiction
    · contradiction
    · rename_i x y
      split at h
      · rename_i tt dt hx hy
        split at h
        · unfold funcTypeOfA at h
          split at h
          · rename_i dom cod he
            injection h with h; subst h
            exact ResultValidA.append (hC.typeFuncDom hy (.mk he))
              (ResultValidA.singleton (ValValidA.addr C tt.addr))
          · contradiction
        · contradiction
      · contradiction
    · contradiction
    · split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · rename_i ini t hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.localVal hx)
      · contradiction
    · rename_i x
      split at h
      · rename_i ini t hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.localVal hx)
      · contradiction
    · split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · rename_i t hx
        injection h with h; subst h
        exact ResultValidA.singleton (hC.globalVal hx)
      · contradiction
    · split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · split at h
        · injection h with h; subst h
          exact ResultValidA.nil C
        · contradiction
      · contradiction
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.num C .i32)
    · injection h with h; subst h
      exact ResultValidA.pair
        (ValValidA.refAbs C (some .null) .eq)
        (ValValidA.refAbs C (some .null) .eq)
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.refAbs C (some .null) .i31)
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          injection h with h; subst h
          exact hC.typeStructUnpacked hx (.mk he)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.nil C
          · contradiction
        · contradiction
      · contradiction
    · rename_i sx x n
      split at h
      · rename_i dt hx
        split at h
        · split at h
          · split at h
            · injection h with h; subst h
              exact ResultValidA.singleton (ValValidA.refIdx hx (some .null))
            · contradiction
          · contradiction
        · contradiction
      · contradiction
    · rename_i x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          split at h
          · rename_i zt hft
            injection h with h; subst h
            exact ResultValidA.pair (ValValidA.refIdx hx (some .null))
              (valValidA_unpack (fun D hD => by
                cases hC.typeStructField hx (.mk he) hft D hD with
                | mk hzt => exact hzt))
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          injection h with h; subst h
          exact ResultValidA.pair (hC.typeArrayUnpack hx (.mk he))
            (ValValidA.num C .i32)
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.singleton (ValValidA.num C .i32)
          · contradiction
        · contradiction
      · contradiction
    · rename_i x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          injection h with h; subst h
          exact ResultValidA.replicate (hC.typeArrayUnpack hx (.mk he)) n.val
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.pair (ValValidA.num C .i32)
              (ValValidA.num C .i32)
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.pair (ValValidA.num C .i32)
              (ValValidA.num C .i32)
          · contradiction
        · contradiction
      · contradiction
    · rename_i sx x
      split at h
      · rename_i dt hx
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.pair (ValValidA.refIdx hx (some .null))
              (ValValidA.num C .i32)
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i zt he
          injection h with h; subst h
          exact ResultValidA.cons (ValValidA.refIdx hx (some .null))
            (ResultValidA.pair (ValValidA.num C .i32)
              (hC.typeArrayUnpack hx (.mk he)))
        · contradiction
      · contradiction
    · injection h with h; subst h
      exact ResultValidA.singleton (ValValidA.refAbs C (some .null) .array)
    · rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i zt he
          injection h with h; subst h
          exact ResultValidA.cons (ValValidA.refIdx hx (some .null))
            (ResultValidA.cons (ValValidA.num C .i32)
              (ResultValidA.pair (hC.typeArrayUnpack hx (.mk he))
                (ValValidA.num C .i32)))
        · contradiction
      · contradiction
    · rename_i x₁ x₂
      split at h
      · rename_i dt₁ dt₂ hx₁ hx₂
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.cons (ValValidA.refIdx hx₁ (some .null))
              (ResultValidA.cons (ValValidA.num C .i32)
                (ResultValidA.cons (ValValidA.refIdx hx₂ (some .null))
                  (ResultValidA.pair (ValValidA.num C .i32)
                    (ValValidA.num C .i32))))
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · rename_i dt rt hx hy
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.cons (ValValidA.refIdx hx (some .null))
              (ResultValidA.triple (ValValidA.num C .i32)
                (ValValidA.num C .i32) (ValValidA.num C .i32))
          · contradiction
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · rename_i dt hx hy
        split at h
        · split at h
          · injection h with h; subst h
            exact ResultValidA.cons (ValValidA.refIdx hx (some .null))
              (ResultValidA.triple (ValValidA.num C .i32)
                (ValValidA.num C .i32) (ValValidA.num C .i32))
          · contradiction
        · contradiction
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact ResultValidA.singleton (ValValidA.addr C tt.addr)
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact ResultValidA.pair (ValValidA.addr C tt.addr) (hC.tableVal hx)
      · contradiction
    · split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact ResultValidA.pair (hC.tableVal hx) (ValValidA.addr C tt.addr)
      · contradiction
    · rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact ResultValidA.triple (ValValidA.addr C tt.addr) (hC.tableVal hx)
          (ValValidA.addr C tt.addr)
      · contradiction
    · rename_i x₁ x₂
      split at h
      · rename_i tt₁ tt₂ hx₁ hx₂
        split at h
        · injection h with h; subst h
          exact ResultValidA.triple (ValValidA.addr C tt₁.addr)
            (ValValidA.addr C tt₂.addr) (ValValidA.addr C (AddrType.min tt₁.addr tt₂.addr))
        · contradiction
      · contradiction
    · rename_i x y
      split at h
      · rename_i tt rt hx hy
        split at h
        · injection h with h; subst h
          exact ResultValidA.triple (ValValidA.addr C tt.addr)
            (ValValidA.num C .i32) (ValValidA.num C .i32)
        · contradiction
      · contradiction
    · split at h
      · injection h with h; subst h
        exact ResultValidA.nil C
      · contradiction
    · contradiction
  · rw [if_neg hwf] at h
    contradiction

theorem instrType_cod_valid {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) : ResultValidA C it.cod := by
  intro D _
  exact resulttype_okA_of_nvb (List.all_eq_true.mpr (fun t ht =>
    ValType.nvb_of_nv (List.all_eq_true.mp (instrType_nv h).2 t ht)))

theorem instrType_dom_valid {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) : ResultValidA C it.dom := by
  intro D _
  exact resulttype_okA_of_nvb (List.all_eq_true.mpr (fun t ht =>
    ValType.nvb_of_nv (List.all_eq_true.mp (instrType_nv h).1 t ht)))

/-! ## Operand-stack validity for the unrestricted pass -/

def St.ValidA (C : Context) (st : St) : Prop := ResultValidA C st.vals

namespace St.ValidA

theorem transport {C D : Context} {st : St} (hCD : SameTypeEnv C D)
    (h : St.ValidA C st) : St.ValidA D st := ResultValidA.transport hCD h

theorem empty (C : Context) (p : Bool) : St.ValidA C (St.mk p []) :=
  ResultValidA.nil C

theorem push {C : Context} {st : St} {t : ValType} (hs : St.ValidA C st)
    (ht : ValValidA C t) : St.ValidA C (st.push t) :=
  ResultValidA.cons ht hs

theorem pushs {C : Context} {st : St} {ts : List ValType}
    (hs : St.ValidA C st) (hts : ResultValidA C ts) :
    St.ValidA C (st.pushs ts) := by
  induction ts generalizing st with
  | nil => exact hs
  | cons t ts ih =>
      have ht : ValValidA C t := by
        intro D hD
        cases hts D hD with
        | mk hall => exact hall t (by simp)
      have hrest : ResultValidA C ts := by
        intro D hD
        cases hts D hD with
        | mk hall => exact .mk (fun u hu => hall u (by simp [hu]))
      exact ih (push hs ht) hrest

theorem popEA {C : Context} {st st' : St} {t : ValType}
    (hs : St.ValidA C st) (h : st.popEA C t = some st') :
    St.ValidA C st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at h
          subst st'
          exact hs
      | cons a rest =>
          simp only [St.popEA] at h
          split at h
          · injection h with h; subst h
            intro D hD
            cases hs D hD with
            | mk hall => exact .mk (fun u hu => hall u (by simp [hu]))
          · contradiction

theorem popsA {C : Context} {st st' : St} {ts : List ValType}
    (hs : St.ValidA C st) (h : st.popsA C ts = some st') :
    St.ValidA C st' := by
  induction ts generalizing st st' with
  | nil =>
      simp only [St.popsA, Option.some.injEq] at h
      subst st'
      exact hs
  | cons t ts ih =>
      simp only [St.popsA] at h
      cases hp : st.popsA C ts with
      | none => simp only [hp] at h; contradiction
      | some s =>
          simp only [hp] at h
          exact popEA (ih hs hp) h

theorem pop {C : Context} {st st' : St} {t : ValType}
    (hs : St.ValidA C st) (h : st.pop = some (t, st')) :
    ValValidA C t ∧ St.ValidA C st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.pop] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ValValidA.bot C, hs⟩
      | cons a rest =>
          simp only [St.pop, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          constructor
          · intro D hD
            cases hs D hD with
            | mk hall => exact hall a (by simp)
          · intro D hD
            cases hs D hD with
            | mk hall => exact .mk (fun u hu => hall u (by simp [hu]))

theorem unreach (C : Context) (st : St) : St.ValidA C st.unreach :=
  ResultValidA.nil C

end St.ValidA

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

theorem setminus1_eq_nil_of_mem {X : Type} [DecidableEq X] {w : X} :
    ∀ {vs : List X}, w ∈ vs → setminus1 w vs = []
  | [], h => by simp at h
  | v :: vs, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp [setminus1]
      · by_cases hw : w = v
        · simp [setminus1, hw]
        · simp [setminus1, hw, setminus1_eq_nil_of_mem h]

theorem setminus_eq_nil_of_subset {X : Type} [DecidableEq X] :
    ∀ {ws vs : List X}, (∀ w, w ∈ ws → w ∈ vs) → setminus ws vs = []
  | [], _, _ => rfl
  | w :: ws, vs, h => by
      rw [setminus]
      rw [setminus1_eq_nil_of_mem (h w (by simp))]
      simp only [List.nil_append]
      exact setminus_eq_nil_of_subset (fun u hu => h u (by simp [hu]))

@[simp] theorem setminus_self {X : Type} [DecidableEq X] (xs : List X) :
    setminus xs xs = [] :=
  setminus_eq_nil_of_subset (fun _ h => h)

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

/-- `popN` is PRINCIPAL: whatever sequence the frame can pop, the sequence
`popN` reads off is below it.  Together with `popN_pops` this is what decides
the existential `Instr_ok/br_table` quantifies over --- the rule leaves the
operand type `t*` free and constrains it only from above, by every label --- so
a single pass can check `popN`'s answer against the labels instead of searching
for `t*`. -/
theorem popN_principal : ∀ {ts : List ValType} {st st' : St},
    st.pops ts = some st' → ∃ (us : List ValType) (s : St),
      st.popN ts.length = some (us, s) ∧ subs us ts = true := by
  intro ts
  induction ts with
  | nil => intro st _ _; exact ⟨[], st, rfl, rfl⟩
  | cons t ts ih =>
      intro st st' h
      rw [pops_cons] at h
      cases hp : st.pops ts with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some s₁ =>
          simp only [hp] at h
          obtain ⟨us, s, hpn, hsub⟩ := ih hp
          have hs : s = s₁ :=
            eq_of (by rw [popN_poly hpn, pops_poly hp])
              (by rw [popN_vals hpn, pops_vals hp])
          obtain ⟨u, hpop, hsu⟩ := pop_of_popE h
          refine ⟨u :: us, st', ?_, by simp [hsu, hsub]⟩
          rw [List.length_cons, popN_succ]
          simp only [hpn, hs, hpop]

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
    (h : Valtype_subA C t₁ t₂) (h₁ : ValType.nvb t₁ = true) : subOf t₁ t₂ = true := by
  cases h with
  | num hn => cases hn; simp
  | vec hv => cases hv; simp
  | ref _ => simp [ValType.nvb] at h₁
  | bot => simp

/-- `matches_val` composes with the declarative subtyping on its right, as long
as the concrete side is in the decided fragment.  This is what lets the operands
`popN` reads off be compared against EVERY label of a `BR_TABLE` at once. -/
theorem subs_trans_sub {C : Context} {as bs cs : List ValType}
    (hab : subs as bs = true) (hbc : Resulttype_subA C bs cs)
    (ha : as.all ValType.nvb = true) : subs as cs = true := by
  cases hbc with
  | mk hlen hall =>
      refine subs_of_getElem (by rw [subs_length hab, hlen]) (fun i a c hia hic => ?_)
      have hib : i < bs.length := by
        rw [hlen]
        rcases Nat.lt_or_ge i cs.length with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none hge] at hic; exact absurd hic (by simp)
      have hbi : bs[i]? = some bs[i] := List.getElem?_eq_getElem hib
      have hab' : subOf a bs[i] = true := subs_getElem hab hia hbi
      have hbc' : Valtype_subA C bs[i] c := hall i _ c hbi hic
      have hna : ValType.nvb a = true := List.all_eq_true.mp ha a (List.mem_of_getElem? hia)
      simp only [subOf, Bool.or_eq_true, beq_iff_eq] at hab' ⊢
      rcases hab' with h1 | h1
      · exact Or.inl h1
      · rw [h1] at hna ⊢
        have := subOf_of_valtype_sub_left hbc' hna
        simp only [subOf, Bool.or_eq_true, beq_iff_eq] at this
        exact this

/-- `pop_val` against a SUPERTYPE succeeds wherever it succeeds against the
subtype, with the same remaining frame.  The frame's operands are `numtype`s,
`vectype`s or `BOT`, so a pop that succeeded against a reference type succeeded
through `BOT`, where the expectation is irrelevant. -/
theorem popE_sub {C : Context} {st st' : St} {t t' : ValType}
    (hnvb : st.vals.all ValType.nvb = true) (h : st.popE t = some st')
    (hsub : Valtype_subA C t t') : st.popE t' = some st' := by
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
`Instrs_okA/sub` computable by the single pass. -/
theorem pops_sub {C : Context} {st st₀ : St} : ∀ {ts ts' : List ValType},
    st.vals.all ValType.nvb = true → st.pops ts = some st₀ →
    Resulttype_subA C ts ts' → st.pops ts' = some st₀ := by
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
                  have hsubtail : Resulttype_subA C ts ts' :=
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
    Blocktype_okA C bt ⟨ts₁, [], ts₂⟩ ∧ nvs ts₁ = true ∧ nvs ts₂ = true := by
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
            exact valtype_okA_of_nvb (ValType.nvb_of_nv hnv)
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
    (h : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩) : blockType C bt = some (ts₁, ts₂) := by
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

`Instrs_okA/seq` re-types the tail under `$with_locals(C, x_1*, (SET t)*)`.  Only
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
  · -- BR_TABLE
    split at h
    · split at h
      · split at h
        · split at h
          · injection h with h; subst h; rfl
          · exact absurd h (by simp)
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
  · -- RETURN_CALL
    split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · injection h with h; subst h; rfl
            · exact absurd h (by simp)
          · exact absurd h (by simp)
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
  | .tryTable _ _ body => InstrSeq.size body + 1
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

theorem InstrSeq.size_body_tryTable (bt : BlockType) (cs : List_ Catch)
    (body : InstrSeq) :
    InstrSeq.size body < Instr.size (.tryTable bt cs body) := by simp [Instr.size]

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

theorem checkInstr_brTable (C : Context) (st : St) (ls : List LabelIdx) (l : LabelIdx) :
    checkInstr C st (.brTable ls l) =
      (match st.popE ValType.i32 with
       | some st₁ =>
           (match C.labels[l.val]? with
            | some ts =>
                (match st₁.popN ts.length with
                 | some (us, _) =>
                     if subs us ts &&
                         ls.all (fun l' =>
                           match C.labels[l'.val]? with
                           | some ts' => subs us ts'
                           | none => false) then
                       some st.unreach
                     else none
                 | none => none)
            | none => none)
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

theorem checkInstr_returnCall (C : Context) (st : St) (x : FuncIdx) :
    checkInstr C st (.returnCall x) =
      (match C.funcs[x.val]? with
       | some dt =>
           (match funcTypeOf dt with
            | some (dom, cod) =>
                (match C.ret with
                 | some ts =>
                     if cod == ts then
                       (match st.pops dom with
                        | some _ => some st.unreach
                        | none => none)
                     else none
                 | none => none)
            | none => none)
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

theorem resulttype_sub_refl {C : Context} (ts : List ValType) : Resulttype_subA C ts ts :=
  .mk rfl (fun _ a b ha hb => by
    rw [ha] at hb
    injection hb with hb
    subst hb
    exact valtype_subA_refl a)

/-- Every `numtype`, `vectype` or `BOT` is below a `numtype` or a `vectype`,
which is the side condition of `Instr_ok/select-impl`. -/
theorem valtype_sub_numvec {C : Context} {t : ValType} (h : ValType.nvb t = true) :
    ∃ t' : ValType, Valtype_subA C t t' ∧ t'.isNumOrVec = true := by
  cases t with
  | num n => exact ⟨.num n, valtype_subA_refl _, rfl⟩
  | vec v => exact ⟨.vec v, valtype_subA_refl _, rfl⟩
  | ref _ => simp [ValType.nvb] at h
  | bot => exact ⟨ValType.i32, .bot, rfl⟩

/-- `Instrs_okA/sub` at `eps ->_(x*) t*  <:  eps ->_(eps) t*`: an instruction
sequence that sets locals still has the expression type its results give it.
`$setminus_(localidx, eps, x*)` is empty, so the rule's third premise is
vacuous. -/
theorem Instrs_okA.drop_locals {C : Context} {is : List Instr} {xs : List LocalIdx}
    {ts : List ValType} (h : Instrs_okA C is ⟨[], xs, ts⟩)
    (hts : ts.all ValType.nvb = true) : Instrs_okA C is ⟨[], [], ts⟩ :=
  .sub h
    (.mk (resulttype_sub_refl []) (resulttype_sub_refl ts) (fun a ha => by simp [setminus] at ha))
    (.mk (resulttype_okA_of_nvb (by simp)) (resulttype_okA_of_nvb hts) (fun a ha => by simp at ha))

/-- Full amended form of `drop_locals`, with no numeric/vector restriction on
the expression result. -/
theorem Instrs_okA.drop_locals_valid {C : Context} {is : List Instr}
    {xs : List LocalIdx} {ts : List ValType}
    (h : Instrs_okA C is ⟨[], xs, ts⟩) (hts : ResultValidA C ts) :
    Instrs_okA C is ⟨[], [], ts⟩ :=
  .sub h
    (.mk (resulttype_sub_refl []) (resulttype_sub_refl ts)
      (fun a ha => by simp [setminus] at ha))
    (.mk ((ResultValidA.nil C) C (SameTypeEnv.refl C))
      (hts C (SameTypeEnv.refl C)) (fun a ha => by simp at ha))

/-- The local-initialization effect carried by an amended instruction is
exactly the context update performed by the full checker. -/
theorem Instr_okA.setEffects {C : Context} {i : Instr} {it : InstrType}
    (h : Instr_okA C i it) :
    ∃ lts : List ValType,
      SeqLen₂ it.locals lts ∧
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
        ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) it.locals lts ∧
      Context.setEffects C it.locals = some
        (Context.withLocals C it.locals (lts.map fun t => ⟨.set, t⟩)) := by
  cases h <;>
    first
      | (rename_i x ini t hx
         exact ⟨[t], rfl,
           (fun n a b ha hb => by
             cases n with
             | zero =>
                 simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
                 subst a; subst b
                 exact ⟨ini, hx⟩
             | succ n => simp at ha),
           by simp [Context.setEffects, Context.withLocals, hx]⟩)
      | exact ⟨[], rfl, (fun _ _ _ ha _ => by simp at ha), rfl⟩

@[simp] theorem subsA_refl (C : Context) : ∀ ts : List ValType,
    subsA C ts ts = true
  | [] => rfl
  | t :: ts => by
      simp only [subsA, decResulttypeSubN, decSeq₂, Bool.and_eq_true]
      exact ⟨subOfA_refl C t, subsA_refl C ts⟩

theorem subsA_append (C : Context) : ∀ {as bs cs ds : List ValType},
    subsA C as bs = true → subsA C cs ds = true →
      subsA C (as ++ cs) (bs ++ ds) = true
  | [], [], _, _ => fun _ h => by simpa using h
  | a :: as, b :: bs, cs, ds => fun h₁ h₂ => by
      change (subOfA C a b && subsA C as bs) = true at h₁
      change (subOfA C a b && subsA C (as ++ cs) (bs ++ ds)) = true
      rw [Bool.and_eq_true] at h₁ ⊢
      exact ⟨h₁.1, subsA_append C h₁.2 h₂⟩
  | [], _ :: _, _, _ => fun h _ => by simp [subsA, decResulttypeSubN, decSeq₂] at h
  | _ :: _, [], _, _ => fun h _ => by simp [subsA, decResulttypeSubN, decSeq₂] at h

theorem ResultValidA.ok {C : Context} {ts : List ValType}
    (h : ResultValidA C ts) : Resulttype_okA C ts := h C (SameTypeEnv.refl C)

/-- Weakening one amended expected stack type through a declarative subtype.
The only computational converse used is derived from the context's genuine
heap-subtyping completeness certificate. -/
theorem St.popEA_weakenA {C : Context} {st st' : St} {t₁ t₂ : ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hst : St.ValidA C st) (ht₁ : Valtype_okA C t₁)
    (hsub : Valtype_subA C t₁ t₂)
    (hp : st.popEA C t₁ = some st') : st.popEA C t₂ = some st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at hp ⊢
          exact hp
      | cons a rest =>
          simp only [St.popEA] at hp ⊢
          split at hp
          · rename_i ha₁
            have ha₂ : decValtypeSubN C C.subtypeFuel a t₂ = true :=
              decValtypeSubN_complete_of_heap hheap
                (Valtype_subA.trans ht₁ (decValtypeSubN_sound ha₁) hsub)
            change subOfA C a t₂ = true at ha₂
            rw [if_pos ha₂]
            exact hp
          · contradiction

/-- Pointwise weakening of `popsA`. -/
theorem St.popsA_weakenA {C : Context}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true) :
    ∀ {ts₁ ts₂ : List ValType} {st st' : St},
      St.ValidA C st → Resulttype_okA C ts₁ →
      Resulttype_subA C ts₁ ts₂ →
      st.popsA C ts₁ = some st' → st.popsA C ts₂ = some st' := by
  intro ts₁
  induction ts₁ with
  | nil =>
      intro ts₂ st st' hst hok hsub hp
      cases hsub with
      | mk hlen _ =>
          have : ts₂ = [] := List.eq_nil_of_length_eq_zero (by simpa [SeqLen₂] using hlen.symm)
          subst ts₂
          exact hp
  | cons t₁ ts₁ ih =>
      intro ts₂ st st' hst hok hsub hp
      cases ts₂ with
      | nil =>
          cases hsub with
          | mk hlen _ => simp [SeqLen₂] at hlen
      | cons t₂ ts₂ =>
          cases hok with
          | mk hok =>
              cases hsub with
              | mk hlen hall =>
                  simp only [St.popsA] at hp ⊢
                  cases hp₁ : st.popsA C ts₁ with
                  | none => simp only [hp₁] at hp; contradiction
                  | some s =>
                      simp only [hp₁] at hp
                      have htailOk : Resulttype_okA C ts₁ :=
                        .mk (fun u hu => hok u (by simp [hu]))
                      have htailSub : Resulttype_subA C ts₁ ts₂ := by
                        refine .mk (by simpa [SeqLen₂] using Nat.succ.inj hlen) ?_
                        intro i a b ha hb
                        exact hall (i + 1) a b (by simpa using ha) (by simpa using hb)
                      have hp₂ : st.popsA C ts₂ = some s :=
                        ih hst htailOk htailSub hp₁
                      simp only [hp₂]
                      exact St.popEA_weakenA hheap (St.ValidA.popsA hst hp₁)
                        (hok t₁ (by simp)) (hall 0 t₁ t₂ rfl rfl) hp

/-- A state satisfying a result type also satisfies any valid supertype. -/
theorem St.SatA.weaken {C : Context} {st : St} {ts₁ ts₂ : List ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hst : St.ValidA C st) (hts₁ : Resulttype_okA C ts₁)
    (hsub : Resulttype_subA C ts₁ ts₂) (hsat : St.SatA C st ts₁) :
    St.SatA C st ts₂ := by
  obtain ⟨s, hp, hv⟩ := hsat
  exact ⟨s, St.popsA_weakenA hheap hst hts₁ hsub hp, hv⟩

/-- Applying a fixed instruction type preserves an arbitrary carried stack
frame exactly. -/
theorem applyTypeA_complete_frame {C : Context} {st : St} {it : InstrType}
    {frame : List ValType} (hsat : St.SatA C st (frame ++ it.dom)) :
    ∃ st', applyTypeA C st it = some st' ∧
      St.SatA C st' (frame ++ it.cod) := by
  obtain ⟨base, hp, hv⟩ := hsat
  rw [St.popsA_append] at hp
  cases hdom : st.popsA C it.dom with
  | none => simp only [hdom] at hp; contradiction
  | some s =>
      simp only [hdom] at hp
      refine ⟨s.pushs it.cod, ?_, base, ?_, hv⟩
      · simp [applyTypeA, hdom]
      · rw [St.popsA_append, St.pushs_popsA]
        exact hp

theorem Context.setEffects_locals_length : ∀ {C C' : Context} {xs : List LocalIdx},
    Context.setEffects C xs = some C' → C'.locals.length = C.locals.length
  | C, C', [], h => by
      simp only [Context.setEffects, Option.some.injEq] at h
      subst C'
      rfl
  | C, C', x :: xs, h => by
      simp only [Context.setEffects] at h
      cases hx : C.locals[x.val]? with
      | none => simp only [hx] at h; contradiction
      | some lt =>
          simp only [hx] at h
          rw [Context.setEffects_locals_length h]
          simp [Context.setLocal]

theorem Context.setEffects_sameTypeEnv : ∀ {C C' : Context} {xs : List LocalIdx},
    Context.setEffects C xs = some C' → SameTypeEnv C C'
  | C, C', [], h => by
      simp only [Context.setEffects, Option.some.injEq] at h
      subst C'
      exact SameTypeEnv.refl C
  | C, C', x :: xs, h => by
      simp only [Context.setEffects] at h
      cases hx : C.locals[x.val]? with
      | none => simp only [hx] at h; contradiction
      | some lt =>
          simp only [hx] at h
          exact SameTypeEnv.trans
            (by simp [SameTypeEnv, Context.setLocal])
            (Context.setEffects_sameTypeEnv h)

theorem Context.local_exists_of_setEffects {C C' : Context} {xs : List LocalIdx}
    (h : Context.setEffects C xs = some C') {x : LocalIdx}
    (hx : ∃ lt : LocalType, C'.locals[x.val]? = some lt) :
    ∃ lt : LocalType, C.locals[x.val]? = some lt := by
  obtain ⟨lt, hx⟩ := hx
  have hlt : x.val < C'.locals.length := (List.getElem?_eq_some_iff.mp hx).1
  have hlt' : x.val < C.locals.length := by
    rw [← Context.setEffects_locals_length h]
    exact hlt
  exact ⟨C.locals[x.val], List.getElem?_eq_getElem hlt'⟩

theorem splitLast?_eq_append {X : Type} : ∀ {xs : List X} {ys : List X} {y : X},
    splitLast? xs = some (ys, y) → xs = ys ++ [y]
  | [], _, _, h => by simp [splitLast?] at h
  | [x], ys, y, h => by
      simp only [splitLast?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | x :: z :: xs, ys, y, h => by
      simp only [splitLast?] at h
      cases hr : splitLast? (z :: xs) with
      | none => simp only [hr] at h; contradiction
      | some p =>
          obtain ⟨zs, w⟩ := p
          simp only [hr, Option.map, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [splitLast?_eq_append hr]
          rfl

theorem blockTypeA_valid {C : Context} (hC : Context.ValidA C) {bt : BlockType}
    {dom cod : List ValType} (h : blockTypeA C bt = some (dom, cod)) :
    ResultValidA C dom ∧ ResultValidA C cod := by
  cases bt with
  | result ot =>
      cases ot with
      | none =>
          simp only [blockTypeA, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ResultValidA.nil C, ResultValidA.nil C⟩
      | some t =>
          simp only [blockTypeA] at h
          split at h
          · rename_i ht
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨ResultValidA.nil C, ResultValidA.singleton (valValidA_of_check ht)⟩
          · contradiction
  | idx x =>
      simp only [blockTypeA] at h
      cases hx : C.types[x.val]? with
      | none => simp only [hx] at h; contradiction
      | some dt =>
          simp only [hx] at h
          obtain ⟨ds, cs, rfl, rfl, he⟩ := funcTypeOfA_sound h
          exact ⟨hC.typeFuncDom hx he, hC.typeFuncCod hx he⟩

def poppedRefValType : Option RefType → ValType
  | some rt => .ref rt
  | none => .bot

theorem St.popRef_popsA {C : Context} {st s : St} {rt : Option RefType}
    (h : st.popRef = some (rt, s)) :
    st.popsA C [poppedRefValType rt] = some s := by
  cases hp : st.pop with
  | none => simp [St.popRef, hp] at h
  | some p =>
      obtain ⟨t, s'⟩ := p
      cases t with
      | ref r =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [St.popsA]
          exact St.popEA_of_pop hp
      | bot =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [St.popsA]
          exact St.popEA_of_pop hp
      | num _ | vec _ => simp [St.popRef, hp] at h

theorem St.popRef_valid {C : Context} {st s : St} {rt : Option RefType}
    (hst : St.ValidA C st) (h : st.popRef = some (rt, s)) :
    St.ValidA C s ∧ ValValidA C (poppedRefValType rt) := by
  cases hp : st.pop with
  | none => simp [St.popRef, hp] at h
  | some p =>
      obtain ⟨t, s'⟩ := p
      obtain ⟨ht, hs⟩ := St.ValidA.pop hst hp
      cases t with
      | ref r =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hs, ht⟩
      | bot =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hs, ht⟩
      | num _ | vec _ => simp [St.popRef, hp] at h

theorem St.ValidA.popN {C : Context} : ∀ {n : Nat} {st s : St}
    {ts : List ValType}, St.ValidA C st → st.popN n = some (ts, s) →
      ResultValidA C ts ∧ St.ValidA C s
  | 0, st, s, ts, hst, h => by
      simp only [St.popN, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ResultValidA.nil C, hst⟩
  | n + 1, st, s, ts, hst, h => by
      simp only [St.popN] at h
      cases hp : st.popN n with
      | none => simp only [hp] at h; contradiction
      | some p =>
          obtain ⟨us, st₁⟩ := p
          simp only [hp] at h
          obtain ⟨hus, hs₁⟩ := St.ValidA.popN hst hp
          cases hq : st₁.pop with
          | none => simp only [hq] at h; contradiction
          | some q =>
              obtain ⟨u, st₂⟩ := q
              simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hu, hs₂⟩ := St.ValidA.pop hs₁ hq
              exact ⟨ResultValidA.cons hu hus, hs₂⟩

theorem St.popEA_of_pop_subOfA {C : Context} {st s : St} {t u : ValType}
    (hp : st.pop = some (t, s)) (hsub : subOfA C t u = true) :
    st.popEA C u = some s := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.pop] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rfl
      | cons a rest =>
          simp only [St.pop, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simp [St.popEA, hsub]

theorem St.popRef_popsA_of_sub {C : Context} {st s : St} {rt : Option RefType}
    {u : ValType} (h : st.popRef = some (rt, s))
    (hsub : subOfA C (poppedRefValType rt) u = true) :
    st.popsA C [u] = some s := by
  cases hp : st.pop with
  | none => simp [St.popRef, hp] at h
  | some p =>
      obtain ⟨t, s'⟩ := p
      cases t with
      | ref r =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [St.popsA]
          exact St.popEA_of_pop_subOfA hp hsub
      | bot =>
          simp only [St.popRef, hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [St.popsA]
          exact St.popEA_of_pop_subOfA hp hsub
      | num _ | vec _ => simp [St.popRef, hp] at h

theorem subOfA_ref_nullable (C : Context) (nul : Option Null) (ht : HeapType) :
    subOfA C (.ref (.ref nul ht)) (.ref (.ref (some .null) ht)) = true := by
  cases nul <;>
    simp [subOfA, decValtypeSubN, decReftypeSubN, decHeaptypeSub_refl]

theorem subOfA_ref_heap {C : Context} {nul : Option Null} {ht ht' : HeapType}
    (h : decHeaptypeSubN C C.subtypeFuel ht ht' = true) :
    subOfA C (.ref (.ref nul ht)) (.ref (.ref nul ht')) = true := by
  cases nul <;> simp [subOfA, decValtypeSubN, decReftypeSubN, h]

theorem subOfA_symm_of_numvec {C : Context} {t₁ t₂ : ValType}
    (h₁ : t₁.isNumOrVec = true) (h₂ : t₂.isNumOrVec = true)
    (h : subOfA C t₁ t₂ = true) : subOfA C t₂ t₁ = true := by
  cases t₁ <;> cases t₂ <;>
    simp_all [ValType.isNumOrVec, subOfA, decValtypeSubN,
      decNumtypeSub, decVectypeSub]

theorem valValidA_ref_null {C : Context} {nul : Option Null} {ht : HeapType}
    (h : ValValidA C (.ref (.ref nul ht))) :
    ValValidA C (.ref (.ref (some .null) ht)) := by
  intro D hD
  cases h D hD with
  | ref hr => cases hr with | mk hh => exact .ref (.mk hh)

theorem valValidA_ref_nonnull {C : Context} {nul : Option Null} {ht : HeapType}
    (h : ValValidA C (.ref (.ref nul ht))) :
    ValValidA C (.ref (.ref none ht)) := by
  intro D hD
  cases h D hD with
  | ref hr => cases hr with | mk hh => exact .ref (.mk hh)

theorem valValidA_ref_diff {C : Context} {rt₁ rt₂ : RefType}
    (h : ValValidA C (.ref rt₁)) : ValValidA C (.ref (RefType.diff rt₁ rt₂)) := by
  cases rt₁ with
  | ref nul₁ ht₁ =>
      cases rt₂ with
      | ref nul₂ ht₂ =>
          cases nul₂ with
          | none => exact h
          | some n => cases n; exact valValidA_ref_nonnull h

theorem heaptype_okA_of_valValid_ref {C : Context} {nul : Option Null}
    {ht : HeapType} (h : ValValidA C (.ref (.ref nul ht))) : Heaptype_okA C ht := by
  cases h C (SameTypeEnv.refl C) with
  | ref hr => cases hr with | mk hh => exact hh

theorem reftype_okA_of_valValid_ref {C : Context} {rt : RefType}
    (h : ValValidA C (.ref rt)) : Reftype_okA C rt := by
  cases h C (SameTypeEnv.refl C) with
  | ref hr => exact hr

/-! ## Soundness interface for the unrestricted pass -/

/-- A full-checker step exposes its principal declarative instruction type and
the (possibly wider) type at which the following sequence reads its results. -/
def InstrSoundFullA (i : Instr) : Prop :=
  ∀ (C : Context), Context.ValidA C → ∀ (st st' : St) (xs : List LocalIdx),
    checkInstrA C st i = some (xs, st') →
    St.ValidA C st →
    St.ValidA C st' ∧ ∀ (tsm : List ValType),
      St.SatA C st' tsm → ResultValidA C tsm →
      ∃ (ts₀ ts₁ ts₂ ts₂' lts : List ValType),
        tsm = ts₀ ++ ts₂' ∧
        St.SatA C st (ts₀ ++ ts₁) ∧
        ResultValidA C ts₀ ∧ ResultValidA C ts₁ ∧ ResultValidA C ts₂ ∧
        Instr_okA C i ⟨ts₁, xs, ts₂⟩ ∧
        subsA C ts₂ ts₂' = true ∧
        SeqLen₂ xs lts ∧
        SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs lts ∧
        Context.setEffects C xs = some
          (Context.withLocals C xs (lts.map fun t => ⟨.set, t⟩))

theorem instrSoundFullA_apply {C : Context} {i : Instr} {it : InstrType}
    {st st' : St}
    (hok : Instr_okA C i it)
    (hdom : ResultValidA C it.dom) (hcod : ResultValidA C it.cod)
    (hrun : applyTypeA C st it = some st')
    (hst : St.ValidA C st) :
    St.ValidA C st' ∧ ∀ (tsm : List ValType),
      St.SatA C st' tsm → ResultValidA C tsm →
      ∃ (ts₀ ts₁ ts₂ ts₂' lts : List ValType),
        tsm = ts₀ ++ ts₂' ∧
        St.SatA C st (ts₀ ++ ts₁) ∧
        ResultValidA C ts₀ ∧ ResultValidA C ts₁ ∧ ResultValidA C ts₂ ∧
        Instr_okA C i ⟨ts₁, it.locals, ts₂⟩ ∧
        subsA C ts₂ ts₂' = true ∧
        SeqLen₂ it.locals lts ∧
        SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) it.locals lts ∧
        Context.setEffects C it.locals = some
          (Context.withLocals C it.locals (lts.map fun t => ⟨.set, t⟩)) := by
  unfold applyTypeA at hrun
  cases hp : st.popsA C it.dom with
  | none => simp only [hp] at hrun; contradiction
  | some st₀ =>
      simp only [hp, Option.some.injEq] at hrun
      subst st'
      constructor
      · exact St.ValidA.pushs (St.ValidA.popsA hst hp) hcod
      · intro tsm hsat htsm
        obtain ⟨rs, cs, he, hsub, hsat₀⟩ := St.pops_split_satA C it.cod hsat
        have hrs : ResultValidA C rs := by
          apply ResultValidA.of_append_left
          simpa [he] using htsm
        obtain ⟨lts, hlen, hall, heff⟩ :=
          WasmGemmGnaf.Wasm.Core.Validate.Instr_okA.setEffects hok
        exact ⟨rs, it.dom, it.cod, cs, lts, he,
          St.satA_append hp hsat₀, hrs, hdom, hcod, hok,
          hsub, hlen, hall, heff⟩

theorem instrSoundFullA_dispatch {C : Context} {i : Instr} {st st' : St}
    {xs : List LocalIdx} (hC : Context.ValidA C)
    (hrun :
      (match instrTypeA C i with
       | some it => (applyTypeA C st it).map (it.locals, ·)
       | none => match instrType C i with
         | some it => (applyTypeA C st it).map (it.locals, ·)
         | none => none) = some (xs, st'))
    (hst : St.ValidA C st) :
    St.ValidA C st' ∧ ∀ (tsm : List ValType),
      St.SatA C st' tsm → ResultValidA C tsm →
      ∃ (ts₀ ts₁ ts₂ ts₂' lts : List ValType),
        tsm = ts₀ ++ ts₂' ∧
        St.SatA C st (ts₀ ++ ts₁) ∧
        ResultValidA C ts₀ ∧ ResultValidA C ts₁ ∧ ResultValidA C ts₂ ∧
        Instr_okA C i ⟨ts₁, xs, ts₂⟩ ∧
        subsA C ts₂ ts₂' = true ∧
        SeqLen₂ xs lts ∧
        SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs lts ∧
        Context.setEffects C xs = some
          (Context.withLocals C xs (lts.map fun t => ⟨.set, t⟩)) := by
  cases hitA : instrTypeA C i with
  | some it =>
      simp only [hitA, Option.map_eq_some_iff] at hrun
      obtain ⟨s, hs, hp⟩ := hrun
      obtain ⟨rfl, rfl⟩ := hp
      exact instrSoundFullA_apply (instrTypeA_sound hitA)
        (instrTypeA_dom_valid hC hitA) (instrTypeA_cod_valid hC hitA) hs hst
  | none =>
      simp only [hitA] at hrun
      cases hit : instrType C i with
      | none => simp only [hit] at hrun; contradiction
      | some it =>
          simp only [hit, Option.map_eq_some_iff] at hrun
          obtain ⟨s, hs, hp⟩ := hrun
          obtain ⟨rfl, rfl⟩ := hp
          exact instrSoundFullA_apply (instrType_sound hit)
            (instrType_dom_valid hit) (instrType_cod_valid hit) hs hst

/-- Common proof for stack-polymorphic instructions.  Once their mandatory
operands have been popped, the remaining concrete frame supplies the free
input prefix and the unreachable output supplies the free result type. -/
theorem instrSoundFullA_unreach {C : Context} {i : Instr} {st s : St}
    {args : List ValType} (hargs : ResultValidA C args)
    (hp : st.popsA C args = some s)
    (hok : ∀ (base out : List ValType), ResultValidA C base →
      ResultValidA C out → Instr_okA C i ⟨base ++ args, [], out⟩)
    (hst : St.ValidA C st) :
    St.ValidA C st.unreach ∧ ∀ (tsm : List ValType),
      St.SatA C st.unreach tsm → ResultValidA C tsm →
      ∃ (ts₀ ts₁ ts₂ ts₂' lts : List ValType),
        tsm = ts₀ ++ ts₂' ∧
        St.SatA C st (ts₀ ++ ts₁) ∧
        ResultValidA C ts₀ ∧ ResultValidA C ts₁ ∧ ResultValidA C ts₂ ∧
        Instr_okA C i ⟨ts₁, [], ts₂⟩ ∧
        subsA C ts₂ ts₂' = true ∧
        SeqLen₂ ([] : List LocalIdx) lts ∧
        SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) [] lts ∧
        Context.setEffects C [] = some
          (Context.withLocals C [] (lts.map fun t => ⟨.set, t⟩)) := by
  have hs : St.ValidA C s := St.ValidA.popsA hst hp
  have hbase : ResultValidA C s.vals.reverse := ResultValidA.reverse hs
  constructor
  · exact St.ValidA.unreach C st
  · intro tsm hsat htsm
    exact ⟨[], s.vals.reverse ++ args, tsm, tsm, [], by simp,
      by simpa using St.satA_append hp (St.satA_own C s),
      ResultValidA.nil C, ResultValidA.append hbase hargs, htsm,
      hok s.vals.reverse tsm hbase htsm, subsA_refl C tsm,
      rfl, (fun _ _ _ hx _ => by simp at hx), rfl⟩

/-- The unrestricted sequence pass produces one amended declarative typing and
an independently useful validity certificate for that instruction type. -/
def SeqSoundFullA (s : InstrSeq) : Prop :=
  ∀ (C : Context), Context.ValidA C → ∀ (st st' : St) (xs : List LocalIdx)
      (ts₂ : List ValType),
    checkSeqA C st s = some (xs, st') → St.ValidA C st →
    St.SatA C st' ts₂ → ResultValidA C ts₂ →
    ∃ ts₁ : List ValType,
      St.SatA C st ts₁ ∧ ResultValidA C ts₁ ∧
      Instrs_okA C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩ ∧
      Instrtype_okA C ⟨ts₁, xs, ts₂⟩

theorem seqSoundFullA_step (s : InstrSeq)
    (hi : ∀ i : Instr, Instr.size i < InstrSeq.size s → InstrSoundFullA i)
    (hr : ∀ rest : InstrSeq, InstrSeq.size rest < InstrSeq.size s →
      SeqSoundFullA rest) : SeqSoundFullA s := by
  cases s with
  | nil =>
      intro C hC st st' xs ts₂ hrun hst hsat hts₂
      simp only [checkSeqA, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨ts₂, hsat, hts₂, ?_, ?_⟩
      · simpa using Instrs_okA.frame (C := C) (is := [])
          (ts := ts₂) (ts₁ := []) (ts₂ := []) (xs := [])
          Instrs_okA.empty hts₂.ok
      · exact .mk hts₂.ok hts₂.ok (fun x hx => by simp at hx)
  | cons i rest =>
      intro C hC st st' xs ts₃ hrun hst hsat hts₃
      simp only [checkSeqA] at hrun
      cases hI : checkInstrA C st i with
      | none => simp only [hI] at hrun; contradiction
      | some p₁ =>
          obtain ⟨xs₁, st₁⟩ := p₁
          simp only [hI] at hrun
          cases hE : Context.setEffects C xs₁ with
          | none => simp only [hE] at hrun; contradiction
          | some C₁ =>
              simp only [hE] at hrun
              cases hR : checkSeqA C₁ st₁ rest with
              | none => simp only [hR] at hrun; contradiction
              | some p₂ =>
                  obtain ⟨xs₂, st₂⟩ := p₂
                  simp only [hR, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨rfl, rfl⟩ := hrun
                  obtain ⟨hst₁, hhead⟩ :=
                    hi i (InstrSeq.size_head i rest) C hC st st₁ xs₁ hI hst
                  have hCC₁ : SameTypeEnv C C₁ := Context.setEffects_sameTypeEnv hE
                  have hC₁ : Context.ValidA C₁ := hC.setEffects hE
                  obtain ⟨tsm, hsatm, htsm, htail, htailOk⟩ :=
                    hr rest (InstrSeq.size_tail i rest) C₁ hC₁ st₁ st₂ xs₂ ts₃
                      hR (St.ValidA.transport hCC₁ hst₁)
                      (St.SatA.transport hCC₁ hsat)
                      (ResultValidA.transport hCC₁ hts₃)
                  obtain ⟨ts₀, ts₁, ts₂, ts₂', lts, htm, hsat₀, hts₀,
                      hts₁, hts₂, hokI, hsub, hlen, hall, heff⟩ :=
                    hhead tsm
                      (St.SatA.transport (SameTypeEnv.symm hCC₁) hsatm)
                      (ResultValidA.transport (SameTypeEnv.symm hCC₁) htsm)
                  have hmatchC : subsA C (ts₀ ++ ts₂) tsm = true := by
                    rw [htm]
                    exact subsA_append C (subsA_refl C ts₀) hsub
                  have hmatchC₁ : subsA C₁ (ts₀ ++ ts₂) tsm = true := by
                    rw [← subsA_sameTypeEnv hCC₁]
                    exact hmatchC
                  have htailLoc : SeqAll (fun x : LocalIdx =>
                      ∃ lct : LocalType, C₁.locals[x.val]? = some lct) xs₂ := by
                    cases htailOk with
                    | mk _ _ hloc => exact hloc
                  have htailOk' : Instrtype_okA C₁ ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ :=
                    .mk
                      (ResultValidA.ok (ResultValidA.transport hCC₁
                        (ResultValidA.append hts₀ hts₂)))
                      (ResultValidA.ok (ResultValidA.transport hCC₁ hts₃))
                      htailLoc
                  have htail' : Instrs_okA C₁ (InstrSeq.toList rest)
                      ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ :=
                    .sub htail
                      (.mk (resulttype_subA_of_subsA hmatchC₁)
                        (resulttype_sub_refl ts₃)
                        (fun x hx => by simp [setminus] at hx))
                      htailOk'
                  have hctx : C₁ = Context.withLocals C xs₁
                      (lts.map fun t => ⟨Init.set, t⟩) := by
                    rw [hE] at heff
                    exact Option.some.inj heff
                  have htailW : Instrs_okA (Context.withLocals C xs₁
                      (lts.map fun t => ⟨Init.set, t⟩)) (InstrSeq.toList rest)
                      ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ := by
                    rw [← hctx]
                    exact htail'
                  have hok : Instrs_okA C (i :: InstrSeq.toList rest)
                      ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, ts₃⟩ :=
                    .seq hokI hlen hall hts₀.ok htailW
                  have hlocals : SeqAll (fun x : LocalIdx =>
                      ∃ lct : LocalType, C.locals[x.val]? = some lct) (xs₁ ++ xs₂) := by
                    intro x hx
                    rw [List.mem_append] at hx
                    rcases hx with hx | hx
                    · obtain ⟨n, hn⟩ := List.getElem?_of_mem hx
                      have hnlt : n < lts.length := by
                        rw [← hlen]
                        exact (List.getElem?_eq_some_iff.mp hn).1
                      have hnt : lts[n]? = some lts[n] := List.getElem?_eq_getElem hnlt
                      obtain ⟨ini, hloc⟩ := hall n x lts[n] hn hnt
                      exact ⟨⟨ini, lts[n]⟩, hloc⟩
                    · exact Context.local_exists_of_setEffects hE (htailLoc x hx)
                  exact ⟨ts₀ ++ ts₁, hsat₀, ResultValidA.append hts₀ hts₁, hok,
                    .mk (ResultValidA.ok (ResultValidA.append hts₀ hts₁))
                      hts₃.ok hlocals⟩

theorem seqSoundFullA_exact_start {C : Context} {body : InstrSeq}
    {dom cod : List ValType} {xs : List LocalIdx} {stB : St}
    (hbody : SeqSoundFullA body) (hC : Context.ValidA C)
    (hdom : ResultValidA C dom) (hcod : ResultValidA C cod)
    (hrun : checkSeqA C ((St.mk false []).pushs dom) body = some (xs, stB))
    (hfin : St.SatA C stB cod) :
    Instrs_okA C (InstrSeq.toList body) ⟨dom, xs, cod⟩ := by
  have hstart : St.ValidA C ((St.mk false []).pushs dom) :=
    St.ValidA.pushs (St.ValidA.empty C false) hdom
  obtain ⟨input, hsat, hinput, hok, hokTy⟩ :=
    hbody C hC _ stB xs cod hrun hstart hfin hcod
  obtain ⟨rs, cs, he, hsub, hsatE⟩ := St.pops_split_satA C dom hsat
  have hrs : rs = [] := St.satA_empty_false hsatE
  subst rs
  simp only [List.nil_append] at he
  subst input
  have hlocals : SeqAll (fun x : LocalIdx =>
      ∃ lct : LocalType, C.locals[x.val]? = some lct) xs := by
    cases hokTy with
    | mk _ _ h => exact h
  exact Instrs_okA.sub hok
    (.mk (resulttype_subA_of_subsA hsub) (resulttype_sub_refl cod)
      (fun x hx => by simp at hx))
    (.mk hdom.ok hcod.ok hlocals)

theorem instrSoundFullA_step (i : Instr)
    (hbody : ∀ body : InstrSeq, InstrSeq.size body < Instr.size i →
      SeqSoundFullA body) : InstrSoundFullA i := by
  cases i
  case unreachable =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact instrSoundFullA_unreach (args := []) (ResultValidA.nil C) rfl
        (fun base out hbase hout => by
          simpa using Instr_okA.unreachable
            (.mk hbase.ok hout.ok (fun x hx => by simp at hx))) hst
  case drop =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hp : st.pop with
      | none => simp only [hp] at hrun; contradiction
      | some p =>
          obtain ⟨t, s⟩ := p
          simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨ht, hs⟩ := St.ValidA.pop hst hp
          apply instrSoundFullA_apply (i := Instr.drop)
            (Instr_okA.drop (ht C (SameTypeEnv.refl C)))
            (ResultValidA.singleton ht) (ResultValidA.nil C) ?_ hst
          unfold applyTypeA
          rw [show st.popsA C [t] = some s by
            simp only [St.popsA]
            exact St.popEA_of_pop hp]
          rfl
  case select ot =>
      cases ot with
      | some ts =>
          intro C hC st st' xs hrun hst
          exact instrSoundFullA_dispatch hC
            (by simpa only [checkInstrA] using hrun) hst
      | none =>
          intro C hC st st' xs hrun hst
          simp only [checkInstrA] at hrun
          cases hi32 : st.popEA C ValType.i32 with
          | none => simp only [hi32] at hrun; contradiction
          | some s₁ =>
              simp only [hi32] at hrun
              cases h₁ : s₁.pop with
              | none => simp only [h₁] at hrun; contradiction
              | some p₁ =>
                  obtain ⟨t₁, s₂⟩ := p₁
                  simp only [h₁] at hrun
                  cases h₂ : s₂.pop with
                  | none => simp only [h₂] at hrun; contradiction
                  | some p₂ =>
                      obtain ⟨t₂, s₃⟩ := p₂
                      simp only [h₂] at hrun
                      split at hrun
                      · rename_i hc
                        simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
                        have hnb : (t₁ == ValType.bot) = false := by
                          cases t₁ <;> simp_all [ValType.isNumOrVec]
                        simp only [hnb, Bool.false_eq_true, if_false,
                          Option.some.injEq, Prod.mk.injEq] at hrun
                        obtain ⟨rfl, rfl⟩ := hrun
                        have hs₁ : St.ValidA C s₁ := St.ValidA.popEA hst hi32
                        obtain ⟨ht₁, hs₂⟩ := St.ValidA.pop hs₁ h₁
                        obtain ⟨ht₂, hs₃⟩ := St.ValidA.pop hs₂ h₂
                        have ht₂₁ : subOfA C t₂ t₁ = true := by
                          rcases hc.2 with h | h
                          · exact subOfA_symm_of_numvec hc.1.1 hc.1.2 h
                          · exact h
                        have hp : st.popsA C [t₁, t₁, ValType.i32] = some s₃ := by
                          simp only [St.popsA, hi32,
                            St.popEA_of_pop_subOfA h₁ (subOfA_refl C t₁),
                            St.popEA_of_pop_subOfA h₂ ht₂₁]
                        apply instrSoundFullA_apply
                          (Instr_okA.select_impl (ht₁ C (SameTypeEnv.refl C))
                            (valtype_subA_refl t₁) hc.1.1)
                          (ResultValidA.triple ht₁ ht₁ (ValValidA.num C .i32))
                          (ResultValidA.singleton ht₁) ?_ hst
                        unfold applyTypeA
                        simp only [hp]
                        rfl
                      · contradiction
  case br l =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at hrun; contradiction
      | some ts =>
          simp only [hl] at hrun
          cases hp : st.popsA C ts with
          | none => simp only [hp] at hrun; contradiction
          | some s =>
              simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              exact instrSoundFullA_unreach (fun D hD => hC.labels hD hl) hp
                (fun base out hbase hout =>
                  .br hl (.mk hbase.ok hout.ok (fun x hx => by simp at hx))) hst
  case brTable ls l =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hi32 : st.popEA C ValType.i32 with
      | none => simp only [hi32] at hrun; contradiction
      | some s₁ =>
          simp only [hi32] at hrun
          cases hl : C.labels[l.val]? with
          | none => simp only [hl] at hrun; contradiction
          | some ts =>
              simp only [hl] at hrun
              cases hpn : s₁.popN ts.length with
              | none => simp only [hpn] at hrun; contradiction
              | some p =>
                  obtain ⟨us, s₂⟩ := p
                  simp only [hpn] at hrun
                  split at hrun
                  · rename_i hc
                    simp only [Bool.and_eq_true] at hc
                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    have hs₁ : St.ValidA C s₁ := St.ValidA.popEA hst hi32
                    obtain ⟨hus, hs₂⟩ := St.ValidA.popN hs₁ hpn
                    have hp : st.popsA C (us ++ [ValType.i32]) = some s₂ := by
                      rw [St.popsA_append]
                      simp only [St.popsA, hi32, St.popN_popsA hpn]
                    have hargs := ResultValidA.append hus
                      (ResultValidA.singleton (ValValidA.num C .i32))
                    apply instrSoundFullA_unreach hargs hp
                      (fun base out hbase hout => ?_) hst
                    have hall : SeqAll (fun l' : LabelIdx =>
                        ∃ ts', C.labels[l'.val]? = some ts' ∧
                          Resulttype_subA C us ts') ls := by
                      intro l' hl'
                      have hc' := List.all_eq_true.mp hc.2 l' hl'
                      cases hlabel : C.labels[l'.val]? with
                      | none => simp only [hlabel] at hc'; contradiction
                      | some ts' =>
                          simp only [hlabel] at hc'
                          exact ⟨ts', rfl, resulttype_subA_of_subsA hc'⟩
                    simpa [List.append_assoc] using
                      (Instr_okA.br_table hall hl (resulttype_subA_of_subsA hc.1)
                        (Instrtype_okA.mk
                          (ResultValidA.append (ResultValidA.append hbase hus)
                            (ResultValidA.singleton (ValValidA.num C .i32))).ok hout.ok
                          (fun y hy => by simp at hy)))
                  · contradiction
  case brOnNull l =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at hrun; contradiction
      | some ts =>
          cases href : st.popRef with
          | none => simp only [hl, href] at hrun; contradiction
          | some p =>
              obtain ⟨rt, s₁⟩ := p
              simp only [hl, href] at hrun
              cases hp : s₁.popsA C ts with
              | none => simp only [hp] at hrun; contradiction
              | some s₀ =>
                  simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨rfl, rfl⟩ := hrun
                  have hts : ResultValidA C ts := fun D hD => hC.labels hD hl
                  obtain ⟨hs₁, hrt⟩ := St.popRef_valid hst href
                  cases rt with
                  | none =>
                      let ht : HeapType := .abs .bot
                      have hnul : ValValidA C (.ref (.ref (some .null) ht)) :=
                        ValValidA.refAbs C (some .null) .bot
                      have hnon : ValValidA C (.ref (.ref none ht)) :=
                        ValValidA.refAbs C none .bot
                      have href' : st.popsA C [.ref (.ref (some .null) ht)] = some s₁ :=
                        St.popRef_popsA_of_sub href (by rfl)
                      apply instrSoundFullA_apply
                        (Instr_okA.br_on_null hl (heaptype_okA_of_valValid_ref hnul))
                        (ResultValidA.append hts (ResultValidA.singleton hnul))
                        (ResultValidA.append hts (ResultValidA.singleton hnon)) ?_ hst
                      unfold applyTypeA
                      simp only [St.popsA_append, href', hp, ht]
                  | some r =>
                      cases r with
                      | ref nul ht =>
                          have hnul : ValValidA C (.ref (.ref (some .null) ht)) :=
                            valValidA_ref_null hrt
                          have hnon : ValValidA C (.ref (.ref none ht)) :=
                            valValidA_ref_nonnull hrt
                          have href' : st.popsA C [.ref (.ref (some .null) ht)] = some s₁ :=
                            St.popRef_popsA_of_sub href (subOfA_ref_nullable C nul ht)
                          apply instrSoundFullA_apply
                            (Instr_okA.br_on_null hl (heaptype_okA_of_valValid_ref hnul))
                            (ResultValidA.append hts (ResultValidA.singleton hnul))
                            (ResultValidA.append hts (ResultValidA.singleton hnon)) ?_ hst
                          unfold applyTypeA
                          simp only [St.popsA_append, href', hp]
  case brOnNonNull l =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at hrun; contradiction
      | some label =>
          simp only [hl] at hrun
          cases hs : splitLast? label with
          | none => simp only [hs] at hrun; contradiction
          | some p =>
              obtain ⟨ts, t⟩ := p
              cases t with
              | num _ | vec _ | bot => simp only [hs] at hrun; contradiction
              | ref rt =>
                  cases rt with
                  | ref nul ht =>
                      simp only [hs, Option.map_eq_some_iff] at hrun
                      obtain ⟨s, happ, heq⟩ := hrun
                      simp only [Prod.mk.injEq] at heq
                      obtain ⟨rfl, rfl⟩ := heq
                      have hlabel : C.labels[l.val]? =
                          some (ts ++ [.ref (.ref nul ht)]) := by
                        rw [← splitLast?_eq_append hs]
                        exact hl
                      have hv : ResultValidA C (ts ++ [.ref (.ref nul ht)]) :=
                        fun D hD => hC.labels hD hlabel
                      have hts : ResultValidA C ts := ResultValidA.of_append_left hv
                      have hlast : ValValidA C (.ref (.ref nul ht)) :=
                        valValidA_of_result_singleton (ResultValidA.of_append_right hv)
                      exact instrSoundFullA_apply
                        (Instr_okA.br_on_non_null hlabel)
                        (ResultValidA.append hts
                          (ResultValidA.singleton (valValidA_ref_null hlast)))
                        hts happ hst
  case brOnCast l rt₁ rt₂ =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at hrun; contradiction
      | some label =>
          simp only [hl] at hrun
          cases hs : splitLast? label with
          | none => simp only [hs] at hrun; contradiction
          | some p =>
              obtain ⟨ts, t⟩ := p
              cases t with
              | num _ | vec _ | bot => simp only [hs] at hrun; contradiction
              | ref rt =>
                  simp only [hs] at hrun
                  split at hrun
                  · rename_i hc
                    simp only [Bool.and_eq_true] at hc
                    simp only [Option.map_eq_some_iff] at hrun
                    obtain ⟨s, happ, heq⟩ := hrun
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl⟩ := heq
                    have hlabel : C.labels[l.val]? = some (ts ++ [.ref rt]) := by
                      rw [← splitLast?_eq_append hs]
                      exact hl
                    have hv : ResultValidA C (ts ++ [.ref rt]) :=
                      fun D hD => hC.labels hD hlabel
                    have hts := ResultValidA.of_append_left hv
                    have hrt₁ := valValidA_ref_of_check hc.1.1.1
                    have hrt₂ := valValidA_ref_of_check hc.1.1.2
                    exact instrSoundFullA_apply
                      (Instr_okA.br_on_cast hlabel
                        (reftype_okA_of_valValid_ref hrt₁)
                        (reftype_okA_of_valValid_ref hrt₂)
                        (decReftypeSubN_sound hc.1.2)
                        (decReftypeSubN_sound hc.2))
                      (ResultValidA.append hts (ResultValidA.singleton hrt₁))
                      (ResultValidA.append hts
                        (ResultValidA.singleton (valValidA_ref_diff hrt₁))) happ hst
                  · contradiction
  case brOnCastFail l rt₁ rt₂ =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hl : C.labels[l.val]? with
      | none => simp only [hl] at hrun; contradiction
      | some label =>
          simp only [hl] at hrun
          cases hs : splitLast? label with
          | none => simp only [hs] at hrun; contradiction
          | some p =>
              obtain ⟨ts, t⟩ := p
              cases t with
              | num _ | vec _ | bot => simp only [hs] at hrun; contradiction
              | ref rt =>
                  simp only [hs] at hrun
                  split at hrun
                  · rename_i hc
                    simp only [Bool.and_eq_true] at hc
                    simp only [Option.map_eq_some_iff] at hrun
                    obtain ⟨s, happ, heq⟩ := hrun
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl⟩ := heq
                    have hlabel : C.labels[l.val]? = some (ts ++ [.ref rt]) := by
                      rw [← splitLast?_eq_append hs]
                      exact hl
                    have hv : ResultValidA C (ts ++ [.ref rt]) :=
                      fun D hD => hC.labels hD hlabel
                    have hts := ResultValidA.of_append_left hv
                    have hrt₁ := valValidA_ref_of_check hc.1.1.1
                    have hrt₂ := valValidA_ref_of_check hc.1.1.2
                    exact instrSoundFullA_apply
                      (Instr_okA.br_on_cast_fail hlabel
                        (reftype_okA_of_valValid_ref hrt₁)
                        (reftype_okA_of_valValid_ref hrt₂)
                        (decReftypeSubN_sound hc.1.2)
                        (decReftypeSubN_sound hc.2))
                      (ResultValidA.append hts (ResultValidA.singleton hrt₁))
                      (ResultValidA.append hts (ResultValidA.singleton hrt₂)) happ hst
                  · contradiction
  case ret =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hret : C.ret with
      | none => simp only [hret] at hrun; contradiction
      | some ts =>
          simp only [hret] at hrun
          cases hp : st.popsA C ts with
          | none => simp only [hp] at hrun; contradiction
          | some s =>
              simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              exact instrSoundFullA_unreach (fun D hD => hC.ret hD hret) hp
                (fun base out hbase hout =>
                  .ret hret (.mk hbase.ok hout.ok (fun x hx => by simp at hx))) hst
  case returnCall x =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hfun : C.funcs[x.val]? with
      | none => simp only [hfun] at hrun; contradiction
      | some dt =>
          cases hret : C.ret with
          | none => simp only [hfun, hret] at hrun; contradiction
          | some ret =>
              simp only [hfun, hret] at hrun
              cases hft : funcTypeOfA dt with
              | none => simp only [hft] at hrun; contradiction
              | some p =>
                  obtain ⟨dom, cod⟩ := p
                  simp only [hft] at hrun
                  split at hrun
                  · rename_i hsub
                    cases hp : st.popsA C dom with
                    | none => simp only [hp] at hrun; contradiction
                    | some s =>
                        simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
                        obtain ⟨rfl, rfl⟩ := hrun
                        obtain ⟨ds, cs, rfl, rfl, he⟩ := funcTypeOfA_sound hft
                        exact instrSoundFullA_unreach (hC.funcDom hfun he) hp
                          (fun base out hbase hout =>
                            .return_call hfun he hret (resulttype_subA_of_subsA hsub)
                              (.mk hbase.ok hout.ok (fun y hy => by simp at hy))) hst
                  · contradiction
  case returnCallRef tu =>
      cases tu with
      | recu i | defd i =>
          intro C hC st st' xs hrun hst
          simp only [checkInstrA] at hrun
          contradiction
      | idx x =>
          intro C hC st st' xs hrun hst
          simp only [checkInstrA] at hrun
          cases hty : C.types[x.val]? with
          | none => simp only [hty] at hrun; contradiction
          | some dt =>
              cases hret : C.ret with
              | none => simp only [hty, hret] at hrun; contradiction
              | some ret =>
                  simp only [hty, hret] at hrun
                  cases hft : funcTypeOfA dt with
                  | none => simp only [hft] at hrun; contradiction
                  | some p =>
                      obtain ⟨dom, cod⟩ := p
                      simp only [hft] at hrun
                      split at hrun
                      · rename_i hsub
                        cases hp : st.popsA C
                            (dom ++ [.ref (.ref (some .null) (.use (.idx x)))]) with
                        | none => simp only [hp] at hrun; contradiction
                        | some s =>
                            simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
                            obtain ⟨rfl, rfl⟩ := hrun
                            obtain ⟨ds, cs, rfl, rfl, he⟩ := funcTypeOfA_sound hft
                            have hargs := ResultValidA.append (hC.typeFuncDom hty he)
                              (ResultValidA.singleton (ValValidA.refIdx hty (some .null)))
                            exact instrSoundFullA_unreach hargs hp
                              (fun base out hbase hout =>
                                by simpa [List.append_assoc] using
                                  (Instr_okA.return_call_ref hty he hret
                                    (resulttype_subA_of_subsA hsub)
                                    (Instrtype_okA.mk (ResultValidA.ok hbase)
                                      (ResultValidA.ok hout)
                                      (fun _ hy => by simp at hy)))) hst
                      · contradiction
  case returnCallIndirect x tu =>
      cases tu with
      | recu i | defd i =>
          intro C hC st st' xs hrun hst
          simp only [checkInstrA] at hrun
          contradiction
      | idx y =>
          intro C hC st st' xs hrun hst
          simp only [checkInstrA] at hrun
          cases htab : C.tables[x.val]? with
          | none => simp only [htab] at hrun; contradiction
          | some tt =>
              cases hty : C.types[y.val]? with
              | none => simp only [htab, hty] at hrun; contradiction
              | some dt =>
                  cases hret : C.ret with
                  | none => simp only [htab, hty, hret] at hrun; contradiction
                  | some ret =>
                      simp only [htab, hty, hret] at hrun
                      cases hft : funcTypeOfA dt with
                      | none => simp only [hft] at hrun; contradiction
                      | some p =>
                          obtain ⟨dom, cod⟩ := p
                          simp only [hft] at hrun
                          split at hrun
                          · rename_i hc
                            simp only [Bool.and_eq_true] at hc
                            cases hp : st.popsA C (dom ++ [tt.addr.toValType]) with
                            | none => simp only [hp] at hrun; contradiction
                            | some s =>
                                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
                                obtain ⟨rfl, rfl⟩ := hrun
                                obtain ⟨ds, cs, rfl, rfl, he⟩ := funcTypeOfA_sound hft
                                have hargs := ResultValidA.append (hC.typeFuncDom hty he)
                                  (ResultValidA.singleton (ValValidA.addr C tt.addr))
                                exact instrSoundFullA_unreach hargs hp
                                  (fun base out hbase hout =>
                                    by simpa [List.append_assoc] using
                                      (Instr_okA.return_call_indirect htab
                                        (decReftypeSubN_sound hc.1) hty he hret
                                        (resulttype_subA_of_subsA hc.2)
                                        (Instrtype_okA.mk (ResultValidA.ok hbase)
                                          (ResultValidA.ok hout)
                                          (fun _ hz => by simp at hz)))) hst
                          · contradiction
  case throw x =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases htag : C.tags[x.val]? with
      | none => simp only [htag] at hrun; contradiction
      | some jt =>
          simp only [htag] at hrun
          cases hj : asDefType jt with
          | none => simp only [hj] at hrun; contradiction
          | some dt =>
              simp only [hj] at hrun
              cases he : expandDt dt with
              | none => simp only [he] at hrun; contradiction
              | some ct =>
                  cases ct with
                  | struct _ | array _ => simp only [he] at hrun; contradiction
                  | func dom cod =>
                      cases cod with
                      | cons t ts => simp only [he] at hrun; contradiction
                      | nil =>
                          simp only [he] at hrun
                          cases hp : st.popsA C (ValTypes.toList dom) with
                          | none => simp only [hp] at hrun; contradiction
                          | some s =>
                              simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
                              obtain ⟨rfl, rfl⟩ := hrun
                              have hargs : ResultValidA C (ValTypes.toList dom) :=
                                fun D hD => hC.tags hD htag hj (.mk he)
                              exact instrSoundFullA_unreach hargs hp
                                (fun base out hbase hout =>
                                  .throw_ htag hj (.mk he)
                                    (.mk hbase.ok hout.ok
                                      (fun y hy => by simp at hy))) hst
  case throwRef =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hp : st.popEA C (.ref (.ref (some .null) (.abs .exn))) with
      | none => simp only [hp] at hrun; contradiction
      | some s =>
          simp only [hp, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          apply instrSoundFullA_unreach
            (ResultValidA.singleton (ValValidA.refAbs C (some .null) .exn))
            (s := s) ?_
            (fun base out hbase hout =>
              .throw_ref (.mk hbase.ok hout.ok (fun x hx => by simp at hx))) hst
          simp only [St.popsA, hp]
  case refIsNull =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases href : st.popRef with
      | none => simp only [href] at hrun; contradiction
      | some p =>
          obtain ⟨rt, s⟩ := p
          simp only [href, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hs, hrt⟩ := St.popRef_valid hst href
          cases rt with
          | none =>
              let ht : HeapType := .abs .bot
              have hv : ValValidA C (.ref (.ref (some .null) ht)) :=
                ValValidA.refAbs C (some .null) .bot
              apply instrSoundFullA_apply (Instr_okA.ref_is_null
                (heaptype_okA_of_valValid_ref hv))
                (ResultValidA.singleton hv)
                (ResultValidA.singleton (ValValidA.num C .i32)) ?_ hst
              unfold applyTypeA
              simp only [St.popRef_popsA_of_sub href (by rfl), ht]
              rfl
          | some r =>
              cases r with
              | ref nul ht =>
                  have hv := valValidA_ref_null hrt
                  apply instrSoundFullA_apply (Instr_okA.ref_is_null
                    (heaptype_okA_of_valValid_ref hv))
                    (ResultValidA.singleton hv)
                    (ResultValidA.singleton (ValValidA.num C .i32)) ?_ hst
                  unfold applyTypeA
                  simp only [St.popRef_popsA_of_sub href
                    (subOfA_ref_nullable C nul ht)]
                  rfl
  case refAsNonNull =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases href : st.popRef with
      | none => simp only [href] at hrun; contradiction
      | some p =>
          obtain ⟨rt, s⟩ := p
          simp only [href, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hs, hrt⟩ := St.popRef_valid hst href
          cases rt with
          | none =>
              let ht : HeapType := .abs .bot
              have hnul : ValValidA C (.ref (.ref (some .null) ht)) :=
                ValValidA.refAbs C (some .null) .bot
              have hnon : ValValidA C (.ref (.ref none ht)) :=
                ValValidA.refAbs C none .bot
              apply instrSoundFullA_apply (Instr_okA.ref_as_non_null
                (heaptype_okA_of_valValid_ref hnul))
                (ResultValidA.singleton hnul) (ResultValidA.singleton hnon) ?_ hst
              unfold applyTypeA
              simp only [St.popRef_popsA_of_sub href (by rfl), ht]
              rfl
          | some r =>
              cases r with
              | ref nul ht =>
                  have hnul := valValidA_ref_null hrt
                  have hnon := valValidA_ref_nonnull hrt
                  apply instrSoundFullA_apply (Instr_okA.ref_as_non_null
                    (heaptype_okA_of_valValid_ref hnul))
                    (ResultValidA.singleton hnul) (ResultValidA.singleton hnon) ?_ hst
                  unfold applyTypeA
                  simp only [St.popRef_popsA_of_sub href
                    (subOfA_ref_nullable C nul ht)]
                  rfl
  case refTest rt =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      split at hrun
      · rename_i hrt
        cases href : st.popRef with
        | none => simp only [href] at hrun; contradiction
        | some p =>
            obtain ⟨rt', s⟩ := p
            simp only [href] at hrun
            split at hrun
            · rename_i hsub
              simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have htarget := valValidA_ref_of_check hrt
              obtain ⟨hs, hactual⟩ := St.popRef_valid hst href
              cases rt' with
              | none =>
                  apply instrSoundFullA_apply
                    (Instr_okA.ref_test (reftype_okA_of_valValid_ref htarget)
                      (reftype_okA_of_valValid_ref htarget)
                      (decReftypeSubN_sound hsub))
                    (ResultValidA.singleton htarget)
                    (ResultValidA.singleton (ValValidA.num C .i32)) ?_ hst
                  unfold applyTypeA
                  simp only [St.popRef_popsA_of_sub href (by rfl)]
                  rfl
              | some actual =>
                  apply instrSoundFullA_apply
                    (Instr_okA.ref_test (reftype_okA_of_valValid_ref htarget)
                      (reftype_okA_of_valValid_ref hactual)
                      (decReftypeSubN_sound hsub))
                    (ResultValidA.singleton hactual)
                    (ResultValidA.singleton (ValValidA.num C .i32)) ?_ hst
                  unfold applyTypeA
                  rw [show st.popsA C [.ref actual] = some s by
                    simpa [poppedRefValType] using St.popRef_popsA (C := C) href]
                  rfl
            · contradiction
      · contradiction
  case refCast rt =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      split at hrun
      · rename_i hrt
        cases href : st.popRef with
        | none => simp only [href] at hrun; contradiction
        | some p =>
            obtain ⟨rt', s⟩ := p
            simp only [href] at hrun
            split at hrun
            · rename_i hsub
              simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have htarget := valValidA_ref_of_check hrt
              obtain ⟨hs, hactual⟩ := St.popRef_valid hst href
              cases rt' with
              | none =>
                  apply instrSoundFullA_apply
                    (Instr_okA.ref_cast (reftype_okA_of_valValid_ref htarget)
                      (reftype_okA_of_valValid_ref htarget)
                      (decReftypeSubN_sound hsub))
                    (ResultValidA.singleton htarget)
                    (ResultValidA.singleton htarget) ?_ hst
                  unfold applyTypeA
                  simp only [St.popRef_popsA_of_sub href (by rfl)]
                  rfl
              | some actual =>
                  apply instrSoundFullA_apply
                    (Instr_okA.ref_cast (reftype_okA_of_valValid_ref htarget)
                      (reftype_okA_of_valValid_ref hactual)
                      (decReftypeSubN_sound hsub))
                    (ResultValidA.singleton hactual)
                    (ResultValidA.singleton htarget) ?_ hst
                  unfold applyTypeA
                  rw [show st.popsA C [.ref actual] = some s by
                    simpa [poppedRefValType] using St.popRef_popsA (C := C) href]
                  rfl
            · contradiction
      · contradiction
  case externConvertAny =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases href : st.popRef with
      | none => simp only [href] at hrun; contradiction
      | some p =>
          obtain ⟨rt, s⟩ := p
          cases rt with
          | none =>
              simp only [href, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have hany := ValValidA.refAbs C none .any
              have hext := ValValidA.refAbs C none .extern
              apply instrSoundFullA_apply Instr_okA.extern_convert_any
                (ResultValidA.singleton hany) (ResultValidA.singleton hext) ?_ hst
              unfold applyTypeA
              simp only [St.popRef_popsA_of_sub href (by rfl)]
              rfl
          | some r =>
              cases r with
              | ref nul ht =>
                  simp only [href] at hrun
                  split at hrun
                  · rename_i hsub
                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    have hany := ValValidA.refAbs C nul .any
                    have hext := ValValidA.refAbs C nul .extern
                    apply instrSoundFullA_apply Instr_okA.extern_convert_any
                      (ResultValidA.singleton hany) (ResultValidA.singleton hext) ?_ hst
                    unfold applyTypeA
                    simp only [St.popRef_popsA_of_sub href (subOfA_ref_heap hsub)]
                    rfl
                  · contradiction
  case anyConvertExtern =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases href : st.popRef with
      | none => simp only [href] at hrun; contradiction
      | some p =>
          obtain ⟨rt, s⟩ := p
          cases rt with
          | none =>
              simp only [href, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have hext := ValValidA.refAbs C none .extern
              have hany := ValValidA.refAbs C none .any
              apply instrSoundFullA_apply Instr_okA.any_convert_extern
                (ResultValidA.singleton hext) (ResultValidA.singleton hany) ?_ hst
              unfold applyTypeA
              simp only [St.popRef_popsA_of_sub href (by rfl)]
              rfl
          | some r =>
              cases r with
              | ref nul ht =>
                  simp only [href] at hrun
                  split at hrun
                  · rename_i hsub
                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    have hext := ValValidA.refAbs C nul .extern
                    have hany := ValValidA.refAbs C nul .any
                    apply instrSoundFullA_apply Instr_okA.any_convert_extern
                      (ResultValidA.singleton hext) (ResultValidA.singleton hany) ?_ hst
                    unfold applyTypeA
                    simp only [St.popRef_popsA_of_sub href (subOfA_ref_heap hsub)]
                    rfl
                  · contradiction
  case block bt body =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hbt : blockTypeA C bt with
      | none => simp only [hbt] at hrun; contradiction
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hbt] at hrun
          cases hp : st.popsA C dom with
          | none => simp only [hp] at hrun; contradiction
          | some s₀ =>
              simp only [hp] at hrun
              cases hb : checkSeqA (Context.pushLabel cod C)
                  ((St.mk false []).pushs dom) body with
              | none => simp only [hb] at hrun; contradiction
              | some pB =>
                  obtain ⟨xsB, stB⟩ := pB
                  simp only [hb] at hrun
                  split at hrun
                  · rename_i hfin
                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbt
                    have hCB := hC.pushLabel hcod
                    have hokB := seqSoundFullA_exact_start
                      (hbody body (InstrSeq.size_body_block bt body)) hCB
                      (ResultValidA.transport (by simp [SameTypeEnv, Context.pushLabel]) hdom)
                      (ResultValidA.transport (by simp [SameTypeEnv, Context.pushLabel]) hcod)
                      hb (St.finishA_iff_satA.mp hfin)
                    apply instrSoundFullA_apply
                      (Instr_okA.block (blockTypeA_sound hbt) hokB) hdom hcod ?_ hst
                    unfold applyTypeA
                    simp only [hp]
                  · contradiction
  case loop bt body =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hbt : blockTypeA C bt with
      | none => simp only [hbt] at hrun; contradiction
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hbt] at hrun
          cases hp : st.popsA C dom with
          | none => simp only [hp] at hrun; contradiction
          | some s₀ =>
              simp only [hp] at hrun
              cases hb : checkSeqA (Context.pushLabel dom C)
                  ((St.mk false []).pushs dom) body with
              | none => simp only [hb] at hrun; contradiction
              | some pB =>
                  obtain ⟨xsB, stB⟩ := pB
                  simp only [hb] at hrun
                  split at hrun
                  · rename_i hfin
                    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbt
                    have hCB := hC.pushLabel hdom
                    have hokB := seqSoundFullA_exact_start
                      (hbody body (InstrSeq.size_body_loop bt body)) hCB
                      (ResultValidA.transport (by simp [SameTypeEnv, Context.pushLabel]) hdom)
                      (ResultValidA.transport (by simp [SameTypeEnv, Context.pushLabel]) hcod)
                      hb (St.finishA_iff_satA.mp hfin)
                    apply instrSoundFullA_apply
                      (Instr_okA.loop (blockTypeA_sound hbt) hokB) hdom hcod ?_ hst
                    unfold applyTypeA
                    simp only [hp]
                  · contradiction
  case ifElse bt thn els =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hbt : blockTypeA C bt with
      | none => simp only [hbt] at hrun; contradiction
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hbt] at hrun
          cases hi32 : st.popEA C ValType.i32 with
          | none => simp only [hi32] at hrun; contradiction
          | some s =>
              simp only [hi32] at hrun
              cases hp : s.popsA C dom with
              | none => simp only [hp] at hrun; contradiction
              | some s₀ =>
                  simp only [hp] at hrun
                  cases hT : checkSeqA (Context.pushLabel cod C)
                      ((St.mk false []).pushs dom) thn with
                  | none => simp only [hT] at hrun; contradiction
                  | some pT =>
                      obtain ⟨xsT, stT⟩ := pT
                      cases hE : checkSeqA (Context.pushLabel cod C)
                          ((St.mk false []).pushs dom) els with
                      | none => simp only [hT, hE] at hrun; contradiction
                      | some pE =>
                          obtain ⟨xsE, stE⟩ := pE
                          simp only [hT, hE] at hrun
                          split at hrun
                          · rename_i hfin
                            simp only [Bool.and_eq_true] at hfin
                            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                            obtain ⟨rfl, rfl⟩ := hrun
                            obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbt
                            have hCB := hC.pushLabel hcod
                            have hokT := seqSoundFullA_exact_start
                              (hbody thn (InstrSeq.size_body_thn bt thn els)) hCB
                              (ResultValidA.transport
                                (by simp [SameTypeEnv, Context.pushLabel]) hdom)
                              (ResultValidA.transport
                                (by simp [SameTypeEnv, Context.pushLabel]) hcod)
                              hT (St.finishA_iff_satA.mp hfin.1)
                            have hokE := seqSoundFullA_exact_start
                              (hbody els (InstrSeq.size_body_els bt thn els)) hCB
                              (ResultValidA.transport
                                (by simp [SameTypeEnv, Context.pushLabel]) hdom)
                              (ResultValidA.transport
                                (by simp [SameTypeEnv, Context.pushLabel]) hcod)
                              hE (St.finishA_iff_satA.mp hfin.2)
                            apply instrSoundFullA_apply
                              (Instr_okA.if_ (blockTypeA_sound hbt) hokT hokE)
                              (ResultValidA.append hdom
                                (ResultValidA.singleton (ValValidA.num C .i32)))
                              hcod ?_ hst
                            unfold applyTypeA
                            rw [St.popsA_append]
                            have hi32' : st.popsA C [ValType.i32] = some s := by
                              simp only [St.popsA, hi32]
                            simp only [hi32', hp]
                          · contradiction
  case tryTable bt cs body =>
      intro C hC st st' xs hrun hst
      simp only [checkInstrA] at hrun
      cases hbt : blockTypeA C bt with
      | none => simp only [hbt] at hrun; contradiction
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hbt] at hrun
          split at hrun
          · rename_i hcs
            cases hp : st.popsA C dom with
            | none => simp only [hp] at hrun; contradiction
            | some s₀ =>
                simp only [hp] at hrun
                cases hb : checkSeqA (Context.pushLabel cod C)
                    ((St.mk false []).pushs dom) body with
                | none => simp only [hb] at hrun; contradiction
                | some pB =>
                    obtain ⟨xsB, stB⟩ := pB
                    simp only [hb] at hrun
                    split at hrun
                    · rename_i hfin
                      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
                      obtain ⟨rfl, rfl⟩ := hrun
                      obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbt
                      have hCB := hC.pushLabel hcod
                      have hokB := seqSoundFullA_exact_start
                        (hbody body (InstrSeq.size_body_tryTable bt cs body)) hCB
                        (ResultValidA.transport
                          (by simp [SameTypeEnv, Context.pushLabel]) hdom)
                        (ResultValidA.transport
                          (by simp [SameTypeEnv, Context.pushLabel]) hcod)
                        hb (St.finishA_iff_satA.mp hfin)
                      have hcatches : SeqAll (Catch_okA C) cs.val := by
                        intro c hc
                        exact checkCatchA_sound (List.all_eq_true.mp hcs c hc)
                      apply instrSoundFullA_apply
                        (Instr_okA.try_table (blockTypeA_sound hbt) hokB hcatches)
                        hdom hcod ?_ hst
                      unfold applyTypeA
                      simp only [hp]
                    · contradiction
          · contradiction
  all_goals
    first
    | (intro C hC st st' xs hrun hst
       exact instrSoundFullA_dispatch hC (by simpa only [checkInstrA] using hrun) hst)

/-- Well-founded closure of the unrestricted amended sequence pass.  The
instruction and sequence measures include every recursive structured body. -/
theorem seqSoundFullA : ∀ (n : Nat) (s : InstrSeq),
    InstrSeq.size s ≤ n → SeqSoundFullA s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      exact seqSoundFullA_step s
        (fun i hi => absurd hi (by omega))
        (fun rest hr => absurd hr (by omega))
  | succ n ih =>
      intro s hs
      refine seqSoundFullA_step s
        (fun i hi => instrSoundFullA_step i
          (fun body hb => ih body (by omega)))
        (fun rest hr => ih rest (by omega))

/-- Soundness of the full amended sequence checker in a valid context. -/
theorem checkSeqA_sound {C : Context} {s : InstrSeq} {st st' : St}
    {xs : List LocalIdx} {ts₂ : List ValType}
    (hC : Context.ValidA C) (hrun : checkSeqA C st s = some (xs, st'))
    (hst : St.ValidA C st) (hsat : St.SatA C st' ts₂)
    (hts₂ : ResultValidA C ts₂) :
    ∃ ts₁ : List ValType,
      St.SatA C st ts₁ ∧ ResultValidA C ts₁ ∧
      Instrs_okA C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩ := by
  obtain ⟨ts₁, hsat₁, hts₁, hok, _⟩ :=
    seqSoundFullA (InstrSeq.size s) s (Nat.le_refl _) C hC
      st st' xs ts₂ hrun hst hsat hts₂
  exact ⟨ts₁, hsat₁, hts₁, hok⟩

/-- Soundness of the full amended expression checker. -/
theorem checkExprA_sound {C : Context} {e : Expr} {ts : List ValType}
    (hC : Context.ValidA C) (hts : ResultValidA C ts)
    (h : checkExprA C e ts = true) : Expr_okA C e ts := by
  unfold checkExprA at h
  cases hs : checkSeqA C (St.mk false []) e with
  | none => simp only [hs] at h; contradiction
  | some p =>
      obtain ⟨xs, st⟩ := p
      simp only [hs] at h
      obtain ⟨ts₁, hsat, _, hok⟩ := checkSeqA_sound hC hs
        (St.ValidA.empty C false) (St.finishA_iff_satA.mp h) hts
      have hnil : ts₁ = [] := St.satA_empty_false hsat
      subst ts₁
      exact .mk (Instrs_okA.drop_locals_valid hok hts)

/-! ## SOUNDNESS

Everything the single pass accepts, the amended judgment derives.  There is no
fragment hypothesis in either statement: `checkInstr` returns `none` on every
instruction outside the decided fragment, and `instrType` on every context
component outside it. -/

/-- The soundness statement for one instruction.  `ts₀` is the frame the
amended `Instrs_okA/seq` carries INSIDE the composition --- the operands that
were on the stack before this instruction and are still there after it. -/
def InstrSound (i : Instr) : Prop :=
  ∀ (C : Context) (st st' : St) (tsm : List ValType),
    checkInstr C st i = some st' → st.vals.all ValType.nvb = true →
    st'.Sat tsm → tsm.all ValType.nvb = true →
    ∃ (ts₀ ts₁ ts₂ : List ValType) (xs : List LocalIdx) (lts : List ValType),
      tsm = ts₀ ++ ts₂ ∧ st.Sat (ts₀ ++ ts₁) ∧ (ts₀ ++ ts₁).all ValType.nvb = true ∧
      Instr_okA C i ⟨ts₁, xs, ts₂⟩ ∧
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
      Instrs_okA C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩

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
            sat_append hpop hsat₀, ?_, instrType_sound hit, hlen, hall, hwl⟩
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
      exact Instr_okA.unreachable
        (.mk (resulttype_okA_of_nvb hrev) (resulttype_okA_of_nvb hts) (fun a ha => by simp at ha))
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
          · exact Instr_okA.drop (valtype_okA_of_nvb hu.1)
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
                        · exact Instr_okA.select_impl (valtype_okA_of_nvb hwn) hsub' hnv'
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
                exact Instr_okA.br hl
                  (.mk (resulttype_okA_of_nvb hsv) (resulttype_okA_of_nvb hts)
                    (fun a ha => by simp at ha))
          · exact absurd h (by simp)
  case brTable ls l =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_brTable] at h
      cases hi32 : st.popE ValType.i32 with
      | none => simp only [hi32] at h; exact absurd h (by simp)
      | some st₁ =>
          simp only [hi32] at h
          cases hlab : C.labels[l.val]? with
          | none => simp only [hlab] at h; exact absurd h (by simp)
          | some ts =>
              simp only [hlab] at h
              cases hpn : st₁.popN ts.length with
              | none => simp only [hpn] at h; exact absurd h (by simp)
              | some p =>
                  obtain ⟨us, s⟩ := p
                  simp only [hpn] at h
                  split at h
                  · rename_i hcond
                    injection h with h; subst h
                    simp only [Bool.and_eq_true] at hcond
                    have hnvb1 : st₁.vals.all ValType.nvb = true := popE_nvb hi32 hnvb
                    obtain ⟨hus, hsv⟩ := popN_nvb hpn hnvb1
                    have hsvr : s.vals.reverse.all ValType.nvb = true := all_reverse hsv
                    have hall :
                        ((s.vals.reverse ++ us) ++ [ValType.i32]).all ValType.nvb = true := by
                      simp only [List.all_append, Bool.and_eq_true]
                      exact ⟨⟨hsvr, hus⟩, by decide⟩
                    have hsat1 : st₁.Sat (s.vals.reverse ++ us) :=
                      sat_append (ts := us) (popN_pops hpn) (sat_own s)
                    have hsat0 : st.Sat ((s.vals.reverse ++ us) ++ [ValType.i32]) :=
                      sat_append (ts := [ValType.i32])
                        (show st.pops [ValType.i32] = some st₁ from hi32) hsat1
                    refine ⟨[], (s.vals.reverse ++ us) ++ [ValType.i32], tsm, [], [], rfl,
                      hsat0, hall, ?_, rfl, (fun j a b ha _ => by simp at ha), rfl⟩
                    refine Instr_okA.br_table (fun l' hl' => ?_) hlab
                      (resulttype_subA_of_subs hcond.1)
                      (.mk (resulttype_okA_of_nvb hall) (resulttype_okA_of_nvb hts)
                        (fun a ha => by simp at ha))
                    have hml := List.all_eq_true.mp hcond.2 l' hl'
                    cases hl2 : C.labels[l'.val]? with
                    | none => simp only [hl2] at hml; exact absurd hml (by simp)
                    | some ts' =>
                        simp only [hl2] at hml
                        exact ⟨ts', hl2, resulttype_subA_of_subs hml⟩
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
                exact Instr_okA.ret hl
                  (.mk (resulttype_okA_of_nvb hsv) (resulttype_okA_of_nvb hts)
                    (fun a ha => by simp at ha))
          · exact absurd h (by simp)
  case returnCall x =>
      intro C st st' tsm h hnvb hsat hts
      rw [checkInstr_returnCall] at h
      cases hfun : C.funcs[x.val]? with
      | none => simp only [hfun] at h; exact absurd h (by simp)
      | some dt =>
          simp only [hfun] at h
          cases hft : funcTypeOf dt with
          | none => simp only [hft] at h; exact absurd h (by simp)
          | some p =>
              obtain ⟨dom, cod⟩ := p
              simp only [hft] at h
              cases hret : C.ret with
              | none => simp only [hret] at h; exact absurd h (by simp)
              | some ts =>
                  simp only [hret] at h
                  split at h
                  · rename_i heqb
                    simp only [beq_iff_eq] at heqb
                    cases hp : st.pops dom with
                    | none => simp only [hp] at h; exact absurd h (by simp)
                    | some s =>
                        simp only [hp] at h
                        injection h with h; subst h
                        obtain ⟨d, c, hexp, hd, hc⟩ := funcTypeOf_expand hft
                        have hsv : s.vals.reverse.all ValType.nvb = true :=
                          all_reverse (pops_nvb hp hnvb)
                        have hnvdom : dom.all ValType.nvb = true :=
                          nvs_nvb (funcTypeOf_nv hft).1
                        have hall : (s.vals.reverse ++ dom).all ValType.nvb = true := by
                          simp only [List.all_append, Bool.and_eq_true]
                          exact ⟨hsv, hnvdom⟩
                        refine ⟨[], s.vals.reverse ++ dom, tsm, [], [], rfl,
                          sat_append (ts := dom) hp (sat_own s), hall, ?_, rfl,
                          (fun j a b ha _ => by simp at ha), rfl⟩
                        have hokd : Instr_okA C (.returnCall x)
                            ⟨s.vals.reverse ++ ValTypes.toList d, [], tsm⟩ :=
                          Instr_okA.return_call hfun hexp hret
                            (by rw [hc, heqb]; exact resulttype_sub_refl ts)
                            (.mk (resulttype_okA_of_nvb hsv) (resulttype_okA_of_nvb hts)
                              (fun a ha => by simp at ha))
                        rw [hd] at hokd
                        exact hokd
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
                    · exact Instr_okA.block hbtok hokA
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
                    · exact Instr_okA.loop hbtok hokA
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
                            · exact Instr_okA.if_ hbtok hokT hokE
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
      have hf := Instrs_okA.frame (C := C) (is := []) (ts := ts₂) (ts₁ := []) (ts₂ := [])
        (xs := []) Instrs_okA.empty (resulttype_okA_of_nvb hts)
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
          show Instrs_okA C (i :: InstrSeq.toList rest) ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, ts₃⟩
          refine Instrs_okA.seq hokHead hlen hall (resulttype_okA_of_nvb ?_) ?_
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
      st.Sat ts₁ ∧ Instrs_okA C (InstrSeq.toList s) ⟨ts₁, xs, ts₂⟩ := by
  obtain ⟨ts₁, xs, h₁, _, h₂⟩ :=
    seq_sound (InstrSeq.size s) s (Nat.le_refl _) C st st' ts₂ h hnvb hsat hts
  exact ⟨ts₁, xs, h₁, h₂⟩

/-- ... and at the level of expressions, which is what the module rules
consume. -/
theorem checkExpr_sound {C : Context} {e : Expr} {ts : List ValType}
    (h : checkExpr C e ts = true) (hts : nvs ts = true) : Expr_okA C e ts := by
  rw [checkExpr] at h
  cases hs : checkSeq C (St.mk false []) e with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some st =>
      rw [hs] at h
      obtain ⟨ts₁, xs, hsat, hok⟩ :=
        checkSeq_sound hs rfl (finish_iff_sat.mp h) (nvs_nvb hts)
      have hnil : ts₁ = [] := sat_empty_false hsat
      subst hnil
      exact .mk (Instrs_okA.drop_locals hok (nvs_nvb hts))

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
    Instr_okA C i it →
    ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
      ∃ st', checkInstr C st i = some st' ∧ le st' (st₀.pushs it.cod)

/-- The completeness statement for a sequence. -/
def SeqComplete (s : InstrSeq) : Prop :=
  ∀ (C : Context) (it : InstrType), Context.frag C = true → InstrSeq.frag s = true →
    Instrs_okA C (InstrSeq.toList s) it → it.cod.all ValType.nvb = true →
    ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
      ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod)

/-! ### The three structured instructions

Their bodies are typed recursively by the combined amended sequence judgment. -/

theorem block_complete {C : Context} {bt : BlockType} {body : InstrSeq}
    {ts₁ ts₂ : List ValType} {xs : List LocalIdx} {st st₀ : St}
    (hbody : SeqComplete body) (hC : Context.frag C = true)
    (hfragbt : BlockType.frag bt = true) (hfragb : InstrSeq.frag body = true)
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩)
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
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_okA (Context.pushLabel ts₁ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩)
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
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hokT : Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList thn) ⟨ts₁, xs₁, ts₂⟩)
    (hokE : Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList els) ⟨ts₁, xs₂, ts₂⟩)
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
    (hsp : Instr.special i = false) (hd : Instr_okA C i it)
    (hpop : st.pops it.dom = some st₀) :
    checkInstr C st i = some (st₀.pushs it.cod) := by
  rw [checkInstr_eq_default hsp]
  simp only [instrType_complete hC hfrag hsp hd, hpop]

theorem instr_complete_step (i : Instr)
    (hbodies : ∀ body : InstrSeq, InstrSeq.size body < Instr.size i → SeqComplete body) :
    InstrComplete i := by
  intro C it hC hfrag hok st st₀ hnvb hpop
  cases i
  case unreachable =>
      exact ⟨st.unreach, checkInstr_unreachable C st, le_unreach _ _ rfl rfl⟩
  case drop =>
      cases hok with
      | drop _ =>
          obtain ⟨u, hp, _⟩ := pop_of_popE (show st.popE _ = some st₀ from hpop)
          refine ⟨st₀, ?_, le_refl _⟩
          rw [checkInstr_drop]
          simp only [hp]
  case select ts =>
      cases ts with
      | some l => exact ⟨_, instr_complete_default hC hfrag rfl hok hpop, le_refl _⟩
      | none =>
          cases hok with
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
      cases hok with
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
  case brTable ls l =>
      cases hok with
      | br_table hls hlab hsub hitok =>
          rename_i ts ts₁ _ ts''
          have hlen : ts.length = ts''.length := by
            cases hsub with | mk hl _ => exact hl
          have hpop' : st.pops ((ts₁ ++ ts) ++ [ValType.i32]) = some st₀ := hpop
          rw [pops_append] at hpop'
          cases hi32 : st.pops [ValType.i32] with
          | none => rw [hi32] at hpop'; exact absurd hpop' (by simp)
          | some st₁ =>
              simp only [hi32] at hpop'
              rw [pops_append] at hpop'
              cases hts : st₁.pops ts with
              | none => simp only [hts] at hpop'; exact absurd hpop' (by simp)
              | some s =>
                  have hi32' : st.popE ValType.i32 = some st₁ := hi32
                  obtain ⟨us, s', hpn, hsubus⟩ := popN_principal hts
                  have hnvb1 : st₁.vals.all ValType.nvb = true := popE_nvb hi32' hnvb
                  obtain ⟨hus, _⟩ := popN_nvb hpn hnvb1
                  have hpn' : st₁.popN ts''.length = some (us, s') := by
                    rw [← hlen]; exact hpn
                  have hallls : ls.all (fun l' =>
                      match C.labels[l'.val]? with
                      | some ts' => subs us ts'
                      | none => false) = true := by
                    refine List.all_eq_true.mpr (fun l' hl' => ?_)
                    obtain ⟨ts', hl2, hsub'⟩ := hls l' hl'
                    simp only [hl2]
                    exact subs_trans_sub hsubus hsub' hus
                  have hcond : (subs us ts'' &&
                      ls.all (fun l' =>
                        match C.labels[l'.val]? with
                        | some ts' => subs us ts'
                        | none => false)) = true := by
                    simp only [Bool.and_eq_true]
                    exact ⟨subs_trans_sub hsubus hsub hus, hallls⟩
                  refine ⟨st.unreach, ?_, le_unreach _ _ rfl rfl⟩
                  rw [checkInstr_brTable]
                  simp only [hi32', hlab, hpn', if_pos hcond]
  case ret =>
      cases hok with
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
  case returnCall x =>
      cases hok with
      | return_call hfun hexp hret hsub hitok =>
          rename_i dt dom cod ts₂' ts₃ _
          have hft : funcTypeOf dt = some (ValTypes.toList dom, ValTypes.toList cod) :=
            funcTypeOf_of_expand hexp (frag_func hC hfun)
          have hnvret : ts₂'.all ValType.nvb = true := nvs_nvb (frag_ret hC hret)
          have heqc : ValTypes.toList cod = ts₂' :=
            subs_eq_of_nv (subs_of_resulttype_subA hsub hnvret)
              (by simpa [nvs] using (funcTypeOf_nv hft).2)
          have hpop' : st.pops (ts₃ ++ ValTypes.toList dom) = some st₀ := hpop
          rw [pops_append] at hpop'
          cases hs : st.pops (ValTypes.toList dom) with
          | none => rw [hs] at hpop'; exact absurd hpop' (by simp)
          | some s =>
              refine ⟨st.unreach, ?_, le_unreach _ _ rfl rfl⟩
              rw [checkInstr_returnCall]
              simp only [hfun, hft, hret, heqc, beq_self_eq_true, if_true, hs]
  case block bt body =>
      cases hok with
      | block hbt hokb =>
          simp only [Instr.frag, Bool.and_eq_true] at hfrag
          exact ⟨_, block_complete (hbodies body (InstrSeq.size_body_block bt body)) hC
            hfrag.1 hfrag.2 hbt hokb hpop, le_refl _⟩
  case loop bt body =>
      cases hok with
      | loop hbt hokb =>
          simp only [Instr.frag, Bool.and_eq_true] at hfrag
          exact ⟨_, loop_complete (hbodies body (InstrSeq.size_body_loop bt body)) hC
            hfrag.1 hfrag.2 hbt hokb hpop, le_refl _⟩
  case ifElse bt thn els =>
      cases hok with
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
                hfrag.1.1 hfrag.1.2 hfrag.2 hbt hokT hokE
                hcond hpop', le_refl _⟩
  all_goals exact ⟨_, instr_complete_default hC hfrag rfl hok hpop, le_refl _⟩

/-! ### One sequence -/

theorem seq_complete_aux : ∀ {C : Context} {js : List Instr} {it : InstrType},
    Instrs_okA C js it → ∀ s : InstrSeq, js = InstrSeq.toList s →
      (∀ i : Instr, Instr.size i < InstrSeq.size s → InstrComplete i) →
      (∀ s' : InstrSeq, InstrSeq.size s' < InstrSeq.size s → SeqComplete s') →
      Context.frag C = true → InstrSeq.frag s = true → it.cod.all ValType.nvb = true →
      ∀ st st₀ : St, st.vals.all ValType.nvb = true → st.pops it.dom = some st₀ →
        ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod) := by
  intro C js it h
  induction h using Instrs_okA.rec (motive_1 := fun _ _ _ _ => True)
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
      have hsubs : subs it₁.cod it₂.cod = true := subs_of_resulttype_subA hcodsub hcod
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
    (hok : Instrs_okA C (InstrSeq.toList s) it) (hcod : it.cod.all ValType.nvb = true)
    (hnvb : st.vals.all ValType.nvb = true) (hpop : st.pops it.dom = some st₀) :
    ∃ st', checkSeq C st s = some st' ∧ le st' (st₀.pushs it.cod) :=
  seq_complete (InstrSeq.size s) s (Nat.le_refl _) C it hC hfrag hok hcod st st₀ hnvb hpop

/-- ... and at the level of expressions. -/
theorem checkExpr_complete {C : Context} {e : Expr} {ts : List ValType}
    (hC : Context.frag C = true) (hfrag : InstrSeq.frag e = true)
    (hok : Expr_okA C e ts) (hts : nvs ts = true) : checkExpr C e ts = true := by
  cases hok with
  | mk hseq =>
      obtain ⟨st, hrun, hle⟩ :=
        checkSeq_complete (st := St.mk false []) (st₀ := St.mk false []) hC hfrag hseq
          (nvs_nvb hts) rfl rfl
      rw [checkExpr, hrun]
      exact finish_iff_sat.mpr (sat_mono hle ⟨St.mk false [], pushs_pops _ ts, rfl⟩)

end Validate
end WasmGemmGnaf.Wasm.Core
