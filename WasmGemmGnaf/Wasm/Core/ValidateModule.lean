/-
  Wasm/Core/ValidateModule.lean --- SOUNDNESS of the executable module
  validator against the AMENDED declarative module judgment.

  `Core/Validate.lean` defines `Wasm.Core.validate : Module -> Bool`, the
  algorithm of `appendix/algorithm.rst` wrapped in the module-level checks of
  `2.4-validation.modules.spectec`, and states plainly why it carried no
  soundness theorem: the PINNED `Instrs_ok` cannot type `i32.const c; i32.add`
  (`Instrs_ok.const_binop_untypable`), so `validate m = true -> Module_ok m mt`
  is FALSE and stating it would be stating a falsehood.  That is DEV-006, filed
  upstream as WebAssembly/spec issue #2194 and fixed there in PR #2197
  (`bd4633ac...`), nine months after the pin.

  `Core/Validation/ModulesCombinedAmended.lean` carries the combined correction
  up to the module level as `Module_okA`.  Every dependent instruction, type,
  subtyping, and amended free-index premise is routed through that one
  coverage-neutral hierarchy.

  `Module_okA` is NOT defined through `validate`.  It is an inductive relation
  in `Core/Validation/ModulesCombinedAmended.lean`, which does not import this one
  and cannot mention the checker; the theorem below is a genuine reflection
  statement and not a restatement of the checker's own booleans.

  WHAT IS PROVED HERE, AND WHAT IS NOT.

    `validate_sound`   -- `validate m = true -> exists mt, Module_okA m mt`.
                          Proved, for every module, with no side hypothesis.

    `validate_complete` -- NOT proved HERE.  `Core/ValidateComplete.lean`
                          proves it only under explicit `Module.wf` and
                          legacy `Module.frag` hypotheses, and proves the
                          correspondingly restricted
                          `validate_iff_declarative_fragment`.  Full
                          completeness and a hypothesis-free Core equivalence
                          remain open.
-/
import WasmGemmGnaf.Wasm.Core.Validate
import WasmGemmGnaf.Wasm.Core.ValidateSeq
import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## Constant expressions at reference result types

Until the reference opcodes are added to the single-pass dispatcher, the
constant-expression grammar accepted by `Instr.isConst` can only leave numeric
or vector values.  These state invariants make that fact explicit; they let the
module checker carry table and element checks now without assuming a reference
typing judgment it has not constructed. -/

theorem isConst_special_false {C : Context} {i : Instr}
    (h : Instr.isConst C i = true) : Instr.special i = false := by
  cases i <;> simp_all [Instr.isConst, Instr.special]

theorem popE_all {p : ValType → Bool} {st st' : St} {t : ValType}
    (h : st.popE t = some st') (hall : st.vals.all p = true) :
    st'.vals.all p = true := by
  cases hv : st.vals with
  | nil =>
      rw [St.popE_nil hv] at h
      split at h
      · cases h; exact hall
      · simp at h
  | cons _ _ =>
      rw [St.popE_cons hv] at h
      split at h
      · cases h
        rw [hv, List.all_cons, Bool.and_eq_true] at hall
        exact hall.2
      · simp at h

theorem pops_all {p : ValType → Bool} {st st' : St} : ∀ {ts : List ValType},
    st.pops ts = some st' → st.vals.all p = true → st'.vals.all p = true := by
  intro ts
  induction ts generalizing st' with
  | nil => intro h hall; cases h; exact hall
  | cons t ts ih =>
      intro h hall
      rw [St.pops_cons] at h
      cases hp : st.pops ts with
      | none => rw [hp] at h; simp at h
      | some s =>
          rw [hp] at h
          exact popE_all h (ih hp hall)

theorem pushs_all {p : ValType → Bool} {st : St} {ts : List ValType}
    (hst : st.vals.all p = true) (hts : ts.all p = true) :
    (st.pushs ts).vals.all p = true := by
  rw [St.pushs_eq, List.all_append, List.all_reverse, hst, hts]
  rfl

theorem checkInstr_const_nv {C : Context} {st st' : St} {i : Instr}
    (hc : Instr.isConst C i = true) (h : checkInstr C st i = some st')
    (hnv : st.vals.all ValType.nv = true) : st'.vals.all ValType.nv = true := by
  rw [checkInstr_eq_default (isConst_special_false hc)] at h
  split at h
  · rename_i it hit
    split at h
    · rename_i s hp
      cases h
      exact pushs_all (pops_all hp hnv) (instrType_nv hit).2
    · simp at h
  · simp at h

theorem checkSeq_const_nv : ∀ (e : InstrSeq) {C : Context} {st st' : St},
    checkSeq C st e = some st' →
    (InstrSeq.toList e).all (Instr.isConst C) = true →
    st.vals.all ValType.nv = true → st'.vals.all ValType.nv = true
  | .nil, _, _, _, h, _, hnv => by cases h; exact hnv
  | .cons i rest, C, st, st', h, hc, hnv => by
      rw [checkSeq_cons] at h
      simp only [InstrSeq.toList, List.all_cons, Bool.and_eq_true] at hc
      cases hi : checkInstr C st i with
      | none => rw [hi] at h; simp at h
      | some s =>
          rw [hi] at h
          exact checkSeq_const_nv rest h hc.2 (checkInstr_const_nv hc.1 hi hnv)

theorem checkSeq_const_poly : ∀ (e : InstrSeq) {C : Context} {st st' : St},
    checkSeq C st e = some st' →
    (InstrSeq.toList e).all (Instr.isConst C) = true →
    st.poly = false → st'.poly = false
  | .nil, _, _, _, h, _, hp => by cases h; exact hp
  | .cons i rest, C, st, st', h, hc, hp => by
      rw [checkSeq_cons] at h
      simp only [InstrSeq.toList, List.all_cons, Bool.and_eq_true] at hc
      cases hi : checkInstr C st i with
      | none => rw [hi] at h; simp at h
      | some s =>
          rw [hi] at h
          apply checkSeq_const_poly rest h hc.2
          rw [checkInstr_eq_default (isConst_special_false hc.1)] at hi
          cases hit : instrType C i with
          | none => rw [hit] at hi; simp at hi
          | some it =>
              rw [hit] at hi
              simp only at hi
              cases hpop : st.pops it.dom with
              | none => rw [hpop] at hi; simp at hi
              | some st₀ =>
                  rw [hpop] at hi
                  cases hi
                  rw [St.pushs_poly, St.pops_poly hpop, hp]

theorem finish_ref_false {st : St} {rt : RefType}
    (hp : st.poly = false) (hnv : st.vals.all ValType.nv = true) :
    st.finish [.ref rt] = false := by
  unfold St.finish
  rw [St.pops_cons, St.pops_nil]
  cases hv : st.vals with
  | nil => simp [St.popE, hv, hp]
  | cons a rest =>
      rw [hv, List.all_cons, Bool.and_eq_true] at hnv
      cases a <;> simp_all [St.popE, subOf, ValType.nv]

theorem checkConstExpr_ref_not_true {C : Context} {e : Expr} {rt : RefType} :
    checkConstExpr C e (.ref rt) ≠ true := by
  intro h
  rw [checkConstExpr, Bool.and_eq_true] at h
  unfold checkExpr at h
  cases hr : checkSeq C (St.mk false []) e with
  | none => rw [hr] at h; simp at h
  | some st =>
      rw [hr] at h
      simp only at h
      have hp : st.poly = false := checkSeq_const_poly e hr h.2 rfl
      have hnv : st.vals.all ValType.nv = true := checkSeq_const_nv e hr h.2 rfl
      rw [finish_ref_false hp hnv] at h
      simp at h

/-! ## Constant expressions -/

/-- `Instr.isConst` decides `Instr_const` on the fragment: everything it accepts
has a `Instr_const` derivation. -/
theorem Instr.isConst_sound {C : Context} {i : Instr} (h : Instr.isConst C i = true) :
    Instr_const C i := by
  unfold Instr.isConst at h
  split at h
  · exact .const h
  · exact .vconst
  · exact .ref_null
  · exact .ref_i31
  · exact .ref_func
  · exact .struct_new
  · exact .struct_new_default
  · exact .array_new
  · exact .array_new_default
  · exact .array_new_fixed
  · exact .any_convert_extern
  · exact .extern_convert_any
  · split at h
    · exact .global_get (by assumption)
    · exact absurd h (by simp)
  · rename_i nt op
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hnt, hop⟩ := h
    have hop' : op = .add ∨ op = .sub ∨ op = .mul := by
      cases op <;> simp_all
    rcases hnt with rfl | rfl
    · exact Instr_const.binop (n := .i32) hop'
    · exact Instr_const.binop (n := .i64) hop'
  · exact absurd h (by simp)

theorem checkConstExpr_sound {C : Context} {e : Expr} {t : ValType}
    (h : checkConstExpr C e t = true) (ht : ValType.nv t = true) :
    Expr_ok_constA C e t := by
  simp only [checkConstExpr, Bool.and_eq_true] at h
  refine .mk (checkExpr_sound h.1 (by simp [nvs, ht])) (.mk (fun i hi => ?_))
  exact Instr.isConst_sound (List.all_eq_true.mp h.2 i hi)

/-- A singleton constant instruction at source type `s`, followed by corrected
subsumption to `t`, forms an amended constant expression. -/
theorem singletonConstExprA {C : Context} {i : Instr} {s t : ValType}
    (hs : Valtype_okA C s) (ht : Valtype_okA C t)
    (hst : Valtype_subA C s t) (hi : Instr_okA C i ⟨[], [], [s]⟩)
    (hc : Instr_const C i) : Expr_ok_constA C (.cons i .nil) t := by
  have hnil : Resulttype_okA C [] := .mk (fun _ h => nomatch h)
  have hsok : Resulttype_okA C [s] := .mk (fun a ha => by
    simp only [List.mem_singleton] at ha
    subst a
    exact hs)
  have htok : Resulttype_okA C [t] := .mk (fun a ha => by
    simp only [List.mem_singleton] at ha
    subst a
    exact ht)
  have htail : Instrs_okA C [] ⟨[s], [], [s]⟩ :=
    .frame .empty hsok
  have hseq : Instrs_okA C [i] ⟨[], [], [s]⟩ := by
    have h := Instrs_okA.seq (C := C) (ts₀ := []) (ts := []) hi rfl
      (fun _ _ _ hx _ => nomatch hx) hnil htail
    simpa using h
  have hsub : Instrtype_subA C ⟨[], [], [s]⟩ ⟨[], [], [t]⟩ := by
    refine .mk (.mk rfl (fun _ _ _ ha _ => nomatch ha)) (.mk rfl ?_)
      (fun _ hx => nomatch hx)
    intro j a b ha hb
    cases j with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst a; subst b
        exact hst
    | succ j => simp at ha
  have hitok : Instrtype_okA C ⟨[], [], [t]⟩ :=
    .mk hnil htok (fun _ hx => nomatch hx)
  exact .mk (.mk (by simpa using Instrs_okA.sub hseq hsub hitok))
    (.mk (by
      intro j hj
      simp only [InstrSeq.toList, List.mem_singleton] at hj
      subst j
      exact hc))

/-- Soundness of the reference-valued singleton constant-expression check. -/
theorem checkRefConstExprA_sound {C : Context} {e : Expr} {t : ValType}
    (h : checkRefConstExprA C e t = true) : Expr_ok_constA C e t := by
  unfold checkRefConstExprA at h
  rw [Bool.and_eq_true] at h
  obtain ⟨ht, hrest⟩ := h
  have htok := checkValtypeOkA_sound ht
  split at hrest
  · rename_i ht' he
    rw [Bool.and_eq_true] at hrest
    have hht := checkHeaptypeOkA_sound hrest.1
    exact singletonConstExprA (.ref (.mk hht)) htok
      (valtype_subA_of_subOfA hrest.2) (.ref_null hht) .ref_null
  · simp at hrest

/-- Soundness of the combined numeric/vector and reference constant checker. -/
theorem checkConstExprA_sound {C : Context} {e : Expr} {t : ValType}
    (h : checkConstExprA C e t = true) : Expr_ok_constA C e t := by
  rw [checkConstExprA, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Bool.and_eq_true] at h
    exact checkConstExpr_sound h.2 h.1
  · exact checkRefConstExprA_sound h

/-! ## The type section -/

/-- Every type definition of the decided fragment is a well-formed `rectype` in
every context: one supertype-free function type over `numtype`s and `vectype`s,
final or not. -/
theorem type_ok_of_frag {C : Context} {td : TypeDef}
    (h : TypeDef.frag td = true) (hcheck : checkTypeOkA C td = true) :
    Type_okA C td (rollDt (TypeIdx.ofNat C.types.length) td.rectype) := by
  simp only [checkTypeOkA, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hrange : TypeGroupRangeOk C td := hcheck.1
  refine Type_okA.mk hrange ?_ rfl ?_
  · simp [TypeIdx.ofNat, Nat.mod_eq_of_lt hrange.1]
  unfold TypeDef.frag at h
  split at h
  · rename_i fin dom cod heq
    rw [heq]
    simp only [Bool.and_eq_true] at h
    refine Rectype_okA.cons ?_ (by rfl) Rectype_okA.empty
    refine Subtype_okA.mk (xs := []) (cts' := []) (by simp) rfl
      (fun j a b ha _ => by simp at ha) (Comptype_okA.func ?_ ?_) (fun a ha => by simp at ha)
    · exact resulttype_okA_of_nvb (nvs_nvb h.1)
    · exact resulttype_okA_of_nvb (nvs_nvb h.2)
  · exact absurd h (by simp)

/-- `rollTypes` is `Types_okA` read as a function: the `deftype*` it computes is
exactly the one the two rules of `Types_okA` derive. -/
theorem types_ok_of_frag : ∀ (tds : List TypeDef) (C : Context),
    tds.all TypeDef.frag = true →
    checkTypesOkA C tds = true →
    ∃ ds : List DefType, rollTypes C.types tds = C.types ++ ds ∧ Types_okA C tds ds := by
  intro tds
  induction tds with
  | nil => intro C _ _; exact ⟨[], by simp [rollTypes], Types_okA.empty⟩
  | cons td tds ih =>
      intro C h hcheck
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [checkTypesOkA, Bool.and_eq_true] at hcheck
      have hty := type_ok_of_frag (C := C) h.1 hcheck.1
      obtain ⟨ds, hroll, hok⟩ :=
        ih (Context.append C
          { types := rollDt (TypeIdx.ofNat C.types.length) td.rectype })
          h.2 hcheck.2
      refine ⟨rollDt (TypeIdx.ofNat C.types.length) td.rectype ++ ds, ?_,
        Types_okA.cons hty hok⟩
      have hty' : (Context.append C
          { types := rollDt (TypeIdx.ofNat C.types.length) td.rectype }).types =
          C.types ++ rollDt (TypeIdx.ofNat C.types.length) td.rectype := rfl
      rw [hty'] at hroll
      show rollTypes (C.types ++ rollDt (TypeIdx.ofNat C.types.length) td.rectype) tds = _
      rw [hroll, List.append_assoc]

/-! ## The remaining module-level checks -/

theorem checkLimits_sound {C : Context} {lim : Limits} {k : Nat}
    (h : checkLimits lim k = true) : Limits_ok C lim k := by
  simp only [checkLimits, Bool.and_eq_true, decide_eq_true_eq] at h
  refine .mk h.1 (fun mx hmx => ?_)
  have h2 := h.2
  rw [hmx] at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact h2

theorem checkFunc_sound {C : Context} {f : Func} (h : checkFunc C f = true) :
    ∃ dt : DefType, C.types[f.typeidx.val]? = some dt ∧ Func_okA C f dt := by
  unfold checkFunc at h
  cases hty : C.types[f.typeidx.val]? with
  | none => simp only [hty] at h; exact absurd h (by simp)
  | some dt =>
      simp only [hty] at h
      cases hft : funcTypeOf dt with
      | none => simp only [hft] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hft, Bool.and_eq_true] at h
          obtain ⟨d, c, hexp, hd, hc⟩ := funcTypeOf_expand hft
          obtain ⟨hnvdom, hnvcod⟩ := funcTypeOf_nv hft
          refine ⟨dt, rfl, .mk (lcts := f.locals.map (fun l => ⟨Init.set, l.valtype⟩))
            hty hexp (by simp only [SeqLen₂, List.length_map]) ?_ ?_⟩
          · intro j a b ha hb
            rw [List.getElem?_map, ha] at hb
            simp only [Option.map_some, Option.some.injEq] at hb
            subst hb
            have hnv := List.all_eq_true.mp h.1 a (List.mem_of_getElem? ha)
            refine .set (valtype_okA_of_nvb (ValType.nvb_of_nv hnv)) (.mk ?_)
            cases hv : a.valtype with
            | num _ => rfl
            | vec _ => rfl
            | ref _ => rw [hv] at hnv; exact absurd hnv (by simp [ValType.nv])
            | bot => rw [hv] at hnv; exact absurd hnv (by simp [ValType.nv])
          · rw [hd, hc]
            exact checkExpr_sound h.2 hnvcod

theorem checkData_sound {C : Context} {d : Data} (h : checkData C d = true) :
    Data_okA C d .ok := by
  unfold checkData at h
  refine .mk ?_
  split at h
  · rename_i heq; rw [heq]; exact .passive
  · rename_i x e heq
    rw [heq]
    cases hmem : C.mems[x.val]? with
    | none => simp only [hmem] at h; exact absurd h (by simp)
    | some mt =>
        simp only [hmem] at h
        refine .active hmem (checkConstExpr_sound h ?_)
        cases mt.addr <;> rfl

theorem checkStart_sound {C : Context} {s : Start} (h : checkStart C s = true) :
    Start_okA C s := by
  unfold checkStart at h
  cases hfun : C.funcs[s.funcidx.val]? with
  | none => simp only [hfun] at h; exact absurd h (by simp)
  | some dt =>
      simp only [hfun] at h
      cases hexp : expandDt dt with
      | none => simp only [hexp] at h; exact absurd h (by simp)
      | some ct =>
          cases ct with
          | func d c =>
              cases d with
              | nil =>
                  cases c with
                  | nil => exact .mk hfun (.mk hexp)
                  | cons _ _ => simp only [hexp] at h; exact absurd h (by simp)
              | cons _ _ => simp only [hexp] at h; exact absurd h (by simp)
          | _ => simp only [hexp] at h; exact absurd h (by simp)

/-! ## Type uses, heap types, external types, tags and imports

None of the five judgments below reaches an expression or a subtyping relation,
so each check discharges its rule's premises outright. -/

/-- `isFuncDt` is the `Expand` premise of `Tagtype_ok` and `Externtype_okA/func`,
read as a decision. -/
theorem isFuncDt_iff {dt : DefType} :
    isFuncDt dt = true ↔ ∃ dom cod : ValTypes, expandDt dt = some (.func dom cod) := by
  unfold isFuncDt
  constructor
  · intro h
    split at h
    · rename_i dom cod heq
      exact ⟨dom, cod, heq⟩
    · exact absurd h (by simp)
  · rintro ⟨dom, cod, heq⟩
    rw [heq]

/-- `checkFuncTypeUse` discharges both premises of `Tagtype_ok` and of
`Externtype_okA/func` at once. -/
theorem checkFuncTypeUse_sound {C : Context} {tu : TypeUse}
    (h : checkFuncTypeUse C tu = true) :
    Typeuse_okA C tu ∧ ∃ dom cod : ValTypes, Expand_use C tu (.func dom cod) := by
  cases tu with
  | recu i => exact absurd h (by simp [checkFuncTypeUse])
  | defd dt => exact absurd h (by simp [checkFuncTypeUse])
  | idx x =>
      cases hx : C.types[x.val]? with
      | none => rw [checkFuncTypeUse, hx] at h; exact absurd h (by simp)
      | some dt =>
          rw [checkFuncTypeUse, hx] at h
          obtain ⟨dom, cod, hexp⟩ := isFuncDt_iff.mp h
          exact ⟨.typeidx hx, dom, cod, .typeidx hx (.mk hexp)⟩

theorem checkHeapType_sound {C : Context} {ht : HeapType}
    (h : checkHeapType C ht = true) : Heaptype_okA C ht := by
  cases ht with
  | abs a => exact .abs
  | use tu =>
      cases tu with
      | recu i => exact absurd h (by simp [checkHeapType])
      | defd dt => exact absurd h (by simp [checkHeapType])
      | idx x =>
          cases hx : C.types[x.val]? with
          | none => rw [checkHeapType, hx] at h; exact absurd h (by simp)
          | some dt => exact .typeuse (.typeidx hx)

theorem checkRefType_sound {C : Context} {rt : RefType}
    (h : checkRefType C rt = true) : Reftype_okA C rt := by
  cases rt with
  | ref nul ht => exact .mk (checkHeapType_sound h)

theorem checkExternType_sound {C : Context} {xt : ExternType}
    (h : checkExternType C xt = true) : Externtype_okA C xt := by
  cases xt with
  | tag jt =>
      obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := jt) h
      exact .tag (.mk hok hexp)
  | func tu =>
      obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := tu) h
      exact .func hok hexp
  | global gt =>
      have h' : ValType.nv gt.valtype = true := h
      exact .global (.mk (valtype_okA_of_nvb (ValType.nvb_of_nv h')))
  | mem mt =>
      have h' : checkLimits mt.lim (2 ^ 16) = true := h
      exact .mem (.mk (checkLimits_sound h'))
  | table tt =>
      have h' : (checkLimits tt.lim (2 ^ 32 - 1) && checkRefType C tt.elem) = true := h
      rw [Bool.and_eq_true] at h'
      exact .table (.mk (checkLimits_sound h'.1) (checkRefType_sound h'.2))

/-- `Tag_okA` back from `checkTag`, at the tag type the context determines. -/
theorem checkTag_sound {C : Context} {tg : Tag} (h : checkTag C tg = true) :
    Tag_okA C tg (C.closTagType tg.tagtype) := by
  obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := tg.tagtype) h
  exact .mk (.mk hok hexp)

/-- The tag section, typed lockstep with the tag types the context determines. -/
theorem tags_ok {C : Context} (tgs : List Tag) (h : tgs.all (checkTag C) = true) :
    SeqAll₂ (Tag_okA C) tgs (tgs.map (fun tg => C.closTagType tg.tagtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst hb
  exact checkTag_sound (List.all_eq_true.mp h a (List.mem_of_getElem? ha))

/-- The import section, typed lockstep with `$clos_externtype` of each. -/
theorem imports_ok {C : Context} (is : List Import)
    (h : is.all (fun i => checkExternType C i.externtype) = true) :
    SeqAll₂ (Import_okA C) is (is.map (fun i => C.closExternType i.externtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst hb
  exact .mk (checkExternType_sound (List.all_eq_true.mp h a (List.mem_of_getElem? ha)))

theorem checkExternIdx_sound {C : Context} {xi : ExternIdx}
    (h : checkExternIdx C xi = true) : ∃ xt : ExternType, Externidx_okA C xi xt := by
  cases xi with
  | func x =>
      cases hx : C.funcs[x.val]? with
      | none => rw [checkExternIdx, hx] at h; exact absurd h (by simp)
      | some dt => exact ⟨_, .func hx⟩
  | global x =>
      cases hx : C.globals[x.val]? with
      | none => rw [checkExternIdx, hx] at h; exact absurd h (by simp)
      | some gt => exact ⟨_, .global hx⟩
  | mem x =>
      cases hx : C.mems[x.val]? with
      | none => rw [checkExternIdx, hx] at h; exact absurd h (by simp)
      | some mt => exact ⟨_, .mem hx⟩
  | table x =>
      cases hx : C.tables[x.val]? with
      | none => rw [checkExternIdx, hx] at h; exact absurd h (by simp)
      | some tt => exact ⟨_, .table hx⟩
  | tag x =>
      cases hx : C.tags[x.val]? with
      | none => rw [checkExternIdx, hx] at h; exact absurd h (by simp)
      | some jt => exact ⟨_, .tag hx⟩

theorem checkGlobals_sound : ∀ (gs : List Global) (C : Context) (gts : List GlobalType),
    checkGlobals C gs = some gts → Globals_okA C gs gts := by
  intro gs
  induction gs with
  | nil =>
      intro C gts h
      rw [checkGlobals] at h
      injection h with h; subst h
      exact .empty
  | cons g gs ih =>
      intro C gts h
      rw [checkGlobals] at h
      split at h
      · rename_i hcond
        simp only [Bool.and_eq_true] at hcond
        cases hrest : checkGlobals (Context.append C { globals := [g.globaltype] }) gs with
        | none => simp only [hrest] at h; exact absurd h (by simp)
        | some gts' =>
            simp only [hrest] at h
            injection h with h; subst h
            refine .cons (.mk (.mk ?_) (checkConstExpr_sound hcond.2 hcond.1)) (ih _ _ hrest)
            exact valtype_okA_of_nvb (ValType.nvb_of_nv hcond.1)
      · exact absurd h (by simp)

theorem exports_ok : ∀ (es : List Export) (C : Context),
    es.all (fun e => checkExternIdx C e.externidx) = true →
    ∃ xts : List ExternType, SeqLen₃ es (es.map Export.name) xts ∧
      SeqAll₃ (Export_okA C) es (es.map Export.name) xts := by
  intro es
  induction es with
  | nil => intro C _; exact ⟨[], ⟨rfl, rfl⟩, fun _ _ _ _ ha _ _ => by simp at ha⟩
  | cons e es ih =>
      intro C h
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨xt, hxt⟩ := checkExternIdx_sound h.1
      obtain ⟨xts, hlen, hall⟩ := ih C h.2
      refine ⟨xt :: xts, ?_, ?_⟩
      · refine ⟨by simp, ?_⟩
        have h2 : (List.map Export.name es).length = xts.length := hlen.2
        simp only [List.length_map] at h2
        simp only [List.length_cons, List.length_map]
        omega
      · intro j a b c ha hb hc
        cases j with
        | zero =>
            simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at ha hb hc
            subst ha; subst hb; subst hc
            exact .mk hxt
        | succ n =>
            simp only [List.map_cons, List.getElem?_cons_succ] at ha hb hc
            exact hall n a b c ha hb hc

/-- A checked table has the combined amended table judgment. -/
theorem checkTable_sound {C : Context} {t : Table}
    (h : checkTable C t = true) : Table_okA C t t.tabletype := by
  simp only [checkTable, Bool.and_eq_true] at h
  exact .mk (.mk (checkLimits_sound h.1.1) (checkRefType_sound h.1.2))
    (checkConstExprA_sound h.2)

/-- Soundness of the element-mode check. -/
theorem checkElemMode_sound {C : Context} {rt : RefType} {mode : ElemMode}
    (h : checkElemMode C rt mode = true) : Elemmode_okA C mode rt := by
  cases mode with
  | passive => exact .passive
  | declare => exact .declare
  | active x e =>
      cases htt : C.tables[x.val]? with
      | none => rw [checkElemMode, htt] at h; exact absurd h (by simp)
      | some tt =>
          rw [checkElemMode, htt, Bool.and_eq_true] at h
          refine .active htt (decReftypeSubN_sound h.1) (checkConstExpr_sound h.2 ?_)
          cases tt.addr <;> rfl

/-- A checked element segment has the combined amended element judgment. -/
theorem checkElem_sound {C : Context} {e : Elem}
    (h : checkElem C e = true) : Elem_okA C e e.reftype := by
  simp only [checkElem, Bool.and_eq_true] at h
  refine .mk (checkRefType_sound h.1.1) ?_ (checkElemMode_sound h.2)
  intro ex hex
  have hx := List.all_eq_true.mp h.1.2 ex hex
  exact checkConstExprA_sound hx

/-- `List.mapM` over `Option`, read pointwise. -/
theorem mapM_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (a : α) (b : β), xs[i]? = some a → ys[i]? = some b → f a = some b := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have h' : (some [] : Option (List β)) = some ys := h
      injection h' with h'
      subst h'
      exact ⟨rfl, fun i a b ha _ => by simp at ha⟩
  | cons a as ih =>
      intro ys h
      simp only [List.mapM_cons] at h
      cases hfa : f a with
      | none => simp only [hfa] at h; exact absurd h (by simp)
      | some b =>
          cases hrest : as.mapM f with
          | none => simp only [hfa, hrest] at h; exact absurd h (by simp)
          | some bs =>
              simp only [hfa, hrest] at h
              have h' : (some (b :: bs) : Option (List β)) = some ys := h
              injection h' with h'
              subst h'
              obtain ⟨hlen, hall⟩ := ih hrest
              refine ⟨by simp [hlen], fun i x y hx hy => ?_⟩
              cases i with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
                  subst hx; subst hy; exact hfa
              | succ n =>
                  simp only [List.getElem?_cons_succ] at hx hy
                  exact hall n x y hx hy

/-! ## SOUNDNESS OF THE MODULE VALIDATOR -/

/-- **`Wasm.Core.validate` IS SOUND FOR THE AMENDED DECLARATIVE JUDGMENT.**
Every module the algorithm of `appendix/algorithm.rst` accepts, under the
module-level checks of `2.4-validation.modules.spectec`, has a module type in
the amended judgment `Module_okA` of
`Core/Validation/ModulesCombinedAmended.lean`.

Stated over `Module_okA` and NOT over the pinned `Module_ok`, for the reason
`Core/Validate.lean` gives and `gapModule_not_ok` proves: the pinned relation
cannot type ordinary WebAssembly, so the same statement over it is FALSE.  This
is DEV-006. -/
theorem validate_sound {m : Module} (h : Validate.validate m = true) :
    ∃ mt : ModuleType, Module_okA m mt := by
  simp only [Validate.validate, Bool.and_eq_true] at h
  obtain ⟨⟨_hwf, htypes⟩, hrest⟩ := h
  cases hctx : Module.contexts m with
  | none => simp only [hctx] at hrest; exact absurd hrest (by simp)
  | some p =>
      obtain ⟨C', C⟩ := p
      simp only [hctx, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨himp, htags⟩, hmem⟩, htables⟩, hfuncs⟩, hdatas⟩,
        helems⟩, hstart⟩, hexp⟩, hdisj⟩ := hrest
      -- unpack `Module.contexts`
      unfold Module.contexts at hctx
      cases hfx : funcsXt (Module.importTypes m) with
      | none => simp only [hfx] at hctx; exact absurd hctx (by simp)
      | some dtsI =>
      simp only [hfx] at hctx
      cases hmap : m.funcs.mapM (fun f => (rollTypes [] m.types)[f.typeidx.val]?) with
      | none => simp only [hmap] at hctx; exact absurd hctx (by simp)
      | some fdts =>
          simp only [hmap] at hctx
          cases hgl : checkGlobals
              { types := rollTypes [] m.types,
                globals := ExternType.globals (Module.importTypes m),
                funcs := dtsI ++ fdts,
                refs := funcidxNonfuncs' m.globals m.mems m.tables m.elems } m.globals with
          | none => simp only [hgl] at hctx; exact absurd hctx (by simp)
          | some gts =>
              simp only [hgl, Option.some.injEq, Prod.mk.injEq] at hctx
              obtain ⟨hC', hC⟩ := hctx
              obtain ⟨hmlen, hmall⟩ := mapM_getElem hmap
              let ds := checkedTypes Context.empty m.types
              have htyok : Types_okA Context.empty m.types ds :=
                checkTypesOkA_sound Context.empty m.types htypes
              obtain ⟨xts, hxlen, hxall⟩ := exports_ok m.exports C hexp
              have hdts : rollTypes [] m.types = ds := by
                simpa [ds] using rollTypes_eq_append_checkedTypes Context.empty m.types
              have htc : Module.typeContext m = { Context.empty with types := ds } := by
                rw [Module.typeContext, hdts]; rfl
              refine ⟨_, Module_okA.mk (C := C) (C' := C') (dts' := ds)
                (xtsI := Module.importTypes m) (xtsE := xts)
                (jts := m.tags.map (fun tg => C'.closTagType tg.tagtype)) (gts := gts)
                (mts := m.mems.map Mem.memtype) (tts := m.tables.map Table.tabletype)
                (dts := fdts) (oks := m.datas.map (fun _ => DataType.ok))
                (rts := m.elems.map Elem.reftype)
                (nms := m.exports.map Export.name)
                (jtsI := ExternType.tags (Module.importTypes m))
                (gtsI := ExternType.globals (Module.importTypes m))
                (mtsI := ExternType.mems (Module.importTypes m))
                (ttsI := ExternType.tables (Module.importTypes m)) (dtsI := dtsI)
                (xs := funcidxNonfuncs' m.globals m.mems m.tables m.elems)
                htyok ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hxlen hxall hdisj
                ?_ ?_ rfl rfl rfl rfl rfl ?_⟩
              · -- SeqLen₂ m.imports xt_I*
                simp only [SeqLen₂, Module.importTypes, List.length_map]
              · -- Import_okA
                rw [← htc]
                exact imports_ok m.imports himp
              · -- SeqLen₂ m.tags jt*
                simp only [SeqLen₂, List.length_map]
              · -- Tag_okA
                exact tags_ok m.tags htags
              · -- Globals_okA
                rw [← hC']
                exact checkGlobals_sound m.globals _ gts hgl
              · simp only [SeqLen₂, List.length_map]
              · -- Mem_ok
                intro i a b ha hb
                rw [List.getElem?_map, ha] at hb
                simp only [Option.map_some, Option.some.injEq] at hb
                subst hb
                refine .mk (.mk ?_)
                exact checkLimits_sound (List.all_eq_true.mp hmem a (List.mem_of_getElem? ha))
              · simp only [SeqLen₂, List.length_map]
              · -- Table_okA
                intro i a b ha hb
                rw [List.getElem?_map, ha] at hb
                simp only [Option.map_some, Option.some.injEq] at hb
                subst hb
                exact checkTable_sound
                  (List.all_eq_true.mp htables a (List.mem_of_getElem? ha))
              · -- SeqLen₂ m.funcs fdts
                exact hmlen
              · -- Func_okA
                intro i a b ha hb
                obtain ⟨dt, hty, hok⟩ :=
                  checkFunc_sound (List.all_eq_true.mp hfuncs a (List.mem_of_getElem? ha))
                have hlk := hmall i a b ha hb
                rw [hdts] at hlk
                have hCty : C.types = ds := by
                  rw [← hC]
                  show rollTypes [] m.types ++ [] = ds
                  simp [hdts]
                rw [hCty] at hty
                rw [hty] at hlk
                injection hlk with hlk
                exact hlk ▸ hok
              · simp only [SeqLen₂, List.length_map]
              · -- Data_okA
                intro i a b ha _
                cases b
                exact checkData_sound (List.all_eq_true.mp hdatas a (List.mem_of_getElem? ha))
              · simp only [SeqLen₂, List.length_map]
              · -- Elem_okA
                intro i a b ha hb
                rw [List.getElem?_map, ha] at hb
                simp only [Option.map_some, Option.some.injEq] at hb
                subst hb
                exact checkElem_sound
                  (List.all_eq_true.mp helems a (List.mem_of_getElem? ha))
              · -- Start_okA
                intro s hs
                simp only [hs] at hstart
                exact checkStart_sound hstart
              · rw [← hC, ← hC']
              · rw [← hC', hdts]
              · exact hfx

end Validate

/-- `Wasm.Core.validate_sound`: the soundness of this development's executable
module validator against the amended declarative judgment. -/
theorem validate_sound {m : Module} (h : validate m = true) :
    ∃ mt : ModuleType, Module_okA m mt :=
  Validate.validate_sound h

/-! ## Completeness status

This file proves unconditional soundness for the complete set of modules that
`Wasm.Core.validate` accepts.  `Core/ValidateComplete.lean` proves the
reverse direction only under explicit `Module.wf` and legacy
`Validate.Module.frag` hypotheses, and its equivalence theorem is named
`Wasm.Core.validate_iff_declarative_fragment` with those same
hypotheses.

`Module.frag` is not part of the validator and does not characterize
accepted modules.  The executable amended subtype decision procedure also now
exists.  What remains open is the proof of completeness for all amended
declaratively valid modules, and therefore the hypothesis-free public Core
equivalence.  The theorem named `Wasm.validate_iff_declarative` in
`Wasm/Declarative.lean` remains a non-release legacy-subset theorem. -/

end WasmGemmGnaf.Wasm.Core
