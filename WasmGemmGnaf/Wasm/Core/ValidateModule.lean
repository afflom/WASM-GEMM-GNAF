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

  `Core/Validation/ModulesAmended.lean` carries the amendment up to the module
  level as `Module_ok'`: `Func_ok`, `Global_ok`, `Table_ok`, `Data_ok` and
  `Elem_ok` reach the instruction judgment through `Expr_ok` / `Expr_ok_const`
  and each gets ONE primed premise; the other twenty-two premises of
  `Module_ok`, the two staged contexts, `$funcidx_nonfuncs`, `$disjoint_` and
  `$clos_moduletype` are the pinned ones.  `Module_ok.to_amended` proves the
  amendment rejects no module the pinned rule accepts, so nothing here is a
  weakening in the direction that would make the theorem cheap.

  `Module_ok'` is NOT defined through `validate`.  It is an inductive relation
  in `Core/Validation/ModulesAmended.lean`, a file that does not import this one
  and cannot mention the checker; the theorem below is a genuine reflection
  statement and not a restatement of the checker's own booleans.

  WHAT IS PROVED HERE, AND WHAT IS NOT.

    `validate_sound`   -- `validate m = true -> exists mt, Module_ok' m mt`.
                          Proved, for every module, with no side hypothesis.

    `validate_complete` -- NOT proved HERE.  The obstruction it needed --- a
                          lemma about `$rolldt` --- is named exactly in the
                          section at the end of this file, and is DISCHARGED in
                          `Core/ValidateComplete.lean`, which then proves
                          `validate_complete` and `validate_iff_declarative`
                          over the same amended judgment.  The section at the
                          end of this file is kept as the record of what the
                          obstruction was; it now points forward rather than
                          declaring an open obligation.
-/
import WasmGemmGnaf.Wasm.Core.Validate
import WasmGemmGnaf.Wasm.Core.ValidateSeq
import WasmGemmGnaf.Wasm.Core.Validation.ModulesAmended

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## Constant expressions -/

/-- `Instr.isConst` decides `Instr_const` on the fragment: everything it accepts
has a `Instr_const` derivation. -/
theorem Instr.isConst_sound {C : Context} {i : Instr} (h : Instr.isConst C i = true) :
    Instr_const C i := by
  unfold Instr.isConst at h
  split at h
  · exact .const h
  · exact .vconst
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
    Expr_ok_const' C e t := by
  simp only [checkConstExpr, Bool.and_eq_true] at h
  refine .mk (checkExpr_sound h.1 (by simp [nvs, ht])) (.mk (fun i hi => ?_))
  exact Instr.isConst_sound (List.all_eq_true.mp h.2 i hi)

/-! ## The type section -/

/-- Every type definition of the decided fragment is a well-formed `rectype` in
every context: one final, supertype-free function type over `numtype`s and
`vectype`s. -/
theorem type_ok_of_frag {C : Context} {td : TypeDef} (h : TypeDef.frag td = true) :
    Type_ok C td (rollDt (TypeIdx.ofNat C.types.length) td.rectype) := by
  refine Type_ok.mk rfl rfl ?_
  unfold TypeDef.frag at h
  split at h
  · rename_i dom cod heq
    rw [heq]
    simp only [Bool.and_eq_true] at h
    refine Rectype_ok.cons ?_ Rectype_ok.empty
    refine Subtype_ok.mk (xs := []) (cts' := []) (by simp) rfl
      (fun j a b ha _ => by simp at ha) (Comptype_ok.func ?_ ?_) (fun a ha => by simp at ha)
    · exact resulttype_ok_of_nvb (nvs_nvb h.1)
    · exact resulttype_ok_of_nvb (nvs_nvb h.2)
  · exact absurd h (by simp)

/-- `rollTypes` is `Types_ok` read as a function: the `deftype*` it computes is
exactly the one the two rules of `Types_ok` derive. -/
theorem types_ok_of_frag : ∀ (tds : List TypeDef) (C : Context),
    tds.all TypeDef.frag = true →
    ∃ ds : List DefType, rollTypes C.types tds = C.types ++ ds ∧ Types_ok C tds ds := by
  intro tds
  induction tds with
  | nil => intro C _; exact ⟨[], by simp [rollTypes], Types_ok.empty⟩
  | cons td tds ih =>
      intro C h
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hty := type_ok_of_frag (C := C) h.1
      obtain ⟨ds, hroll, hok⟩ :=
        ih (Context.append C { types := rollDt (TypeIdx.ofNat C.types.length) td.rectype }) h.2
      refine ⟨rollDt (TypeIdx.ofNat C.types.length) td.rectype ++ ds, ?_,
        Types_ok.cons hty hok⟩
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

/-- `funcTypeOf` is `Expand` at a function type of the fragment, read as a
function. -/
theorem funcTypeOf_expand {dt : DefType} {dom cod : List ValType}
    (h : funcTypeOf dt = some (dom, cod)) :
    ∃ d c : ValTypes, Expand dt (.func d c) ∧
      ValTypes.toList d = dom ∧ ValTypes.toList c = cod := by
  rw [funcTypeOf] at h
  cases hexp : expandDt dt with
  | none => simp only [hexp] at h; exact absurd h (by simp)
  | some ct =>
      cases ct with
      | func d c =>
          simp only [hexp] at h
          by_cases hif : (nvs (ValTypes.toList d) && nvs (ValTypes.toList c)) = true
          · rw [if_pos hif] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨d, c, .mk hexp, h.1.symm ▸ rfl, h.2.symm ▸ rfl⟩
          · rw [if_neg hif] at h; exact absurd h (by simp)
      | _ => simp only [hexp] at h; exact absurd h (by simp)

theorem checkFunc_sound {C : Context} {f : Func} (h : checkFunc C f = true) :
    ∃ dt : DefType, C.types[f.typeidx.val]? = some dt ∧ Func_ok' C f dt := by
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
            refine .set (.mk ?_)
            have := List.all_eq_true.mp h.1 a (List.mem_of_getElem? ha)
            cases hv : a.valtype with
            | num _ => rfl
            | vec _ => rfl
            | ref _ => rw [hv] at this; exact absurd this (by simp [ValType.nv])
            | bot => rw [hv] at this; exact absurd this (by simp [ValType.nv])
          · rw [hd, hc]
            exact checkExpr_sound h.2 hnvcod

theorem checkData_sound {C : Context} {d : Data} (h : checkData C d = true) :
    Data_ok' C d .ok := by
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
    Start_ok C s := by
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

/-- `isFuncDt` is the `Expand` premise of `Tagtype_ok` and `Externtype_ok/func`,
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
`Externtype_ok/func` at once. -/
theorem checkFuncTypeUse_sound {C : Context} {tu : TypeUse}
    (h : checkFuncTypeUse C tu = true) :
    Typeuse_ok C tu ∧ ∃ dom cod : ValTypes, Expand_use C tu (.func dom cod) := by
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
    (h : checkHeapType C ht = true) : Heaptype_ok C ht := by
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
    (h : checkRefType C rt = true) : Reftype_ok C rt := by
  cases rt with
  | ref nul ht => exact .mk (checkHeapType_sound h)

theorem checkExternType_sound {C : Context} {xt : ExternType}
    (h : checkExternType C xt = true) : Externtype_ok C xt := by
  cases xt with
  | tag jt =>
      obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := jt) h
      exact .tag (.mk hok hexp)
  | func tu =>
      obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := tu) h
      exact .func hok hexp
  | global gt =>
      have h' : ValType.nv gt.valtype = true := h
      exact .global (.mk (valtype_ok_of_nvb (ValType.nvb_of_nv h')))
  | mem mt =>
      have h' : checkLimits mt.lim (2 ^ 16) = true := h
      exact .mem (.mk (checkLimits_sound h'))
  | table tt =>
      have h' : (checkLimits tt.lim (2 ^ 32 - 1) && checkRefType C tt.elem) = true := h
      rw [Bool.and_eq_true] at h'
      exact .table (.mk (checkLimits_sound h'.1) (checkRefType_sound h'.2))

/-- `Tag_ok` back from `checkTag`, at the tag type the context determines. -/
theorem checkTag_sound {C : Context} {tg : Tag} (h : checkTag C tg = true) :
    Tag_ok C tg (C.closTagType tg.tagtype) := by
  obtain ⟨hok, _, _, hexp⟩ := checkFuncTypeUse_sound (C := C) (tu := tg.tagtype) h
  exact .mk (.mk hok hexp)

/-- The tag section, typed lockstep with the tag types the context determines. -/
theorem tags_ok {C : Context} (tgs : List Tag) (h : tgs.all (checkTag C) = true) :
    SeqAll₂ (Tag_ok C) tgs (tgs.map (fun tg => C.closTagType tg.tagtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst hb
  exact checkTag_sound (List.all_eq_true.mp h a (List.mem_of_getElem? ha))

/-- The import section, typed lockstep with `$clos_externtype` of each. -/
theorem imports_ok {C : Context} (is : List Import)
    (h : is.all (fun i => checkExternType C i.externtype) = true) :
    SeqAll₂ (Import_ok C) is (is.map (fun i => C.closExternType i.externtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst hb
  exact .mk (checkExternType_sound (List.all_eq_true.mp h a (List.mem_of_getElem? ha)))

theorem checkExternIdx_sound {C : Context} {xi : ExternIdx}
    (h : checkExternIdx C xi = true) : ∃ xt : ExternType, Externidx_ok C xi xt := by
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
    checkGlobals C gs = some gts → Globals_ok' C gs gts := by
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
            exact valtype_ok_of_nvb (ValType.nvb_of_nv hcond.1)
      · exact absurd h (by simp)

theorem exports_ok : ∀ (es : List Export) (C : Context),
    es.all (fun e => checkExternIdx C e.externidx) = true →
    ∃ xts : List ExternType, SeqLen₃ es (es.map Export.name) xts ∧
      SeqAll₃ (Export_ok C) es (es.map Export.name) xts := by
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
the amended judgment `Module_ok'` of `Core/Validation/ModulesAmended.lean`.

Stated over `Module_ok'` and NOT over the pinned `Module_ok`, for the reason
`Core/Validate.lean` gives and `gapModule_not_ok` proves: the pinned relation
cannot type ordinary WebAssembly, so the same statement over it is FALSE.  This
is DEV-006. -/
theorem validate_sound {m : Module} (h : Validate.validate m = true) :
    ∃ mt : ModuleType, Module_ok' m mt := by
  simp only [Validate.validate, Bool.and_eq_true] at h
  obtain ⟨hfrag, hrest⟩ := h
  simp only [Module.frag, Bool.and_eq_true] at hfrag
  obtain ⟨⟨⟨⟨⟨⟨⟨_him, _htg⟩, htb⟩, hel⟩, htys⟩, hglob⟩, hfun⟩, hdat⟩ := hfrag
  -- the two sections outside the decided fragment are empty
  have htb' : m.tables = [] := List.isEmpty_iff.mp htb
  have hel' : m.elems = [] := List.isEmpty_iff.mp hel
  cases hctx : Module.contexts m with
  | none => simp only [hctx] at hrest; exact absurd hrest (by simp)
  | some p =>
      obtain ⟨C', C⟩ := p
      simp only [hctx, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨⟨⟨himp, htags⟩, hmem⟩, hfuncs⟩, hdatas⟩, hstart⟩, hexp⟩, hdisj⟩ := hrest
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
                refs := funcidxNonfuncs m.globals m.mems m.tables m.elems } m.globals with
          | none => simp only [hgl] at hctx; exact absurd hctx (by simp)
          | some gts =>
              simp only [hgl, Option.some.injEq, Prod.mk.injEq] at hctx
              obtain ⟨hC', hC⟩ := hctx
              obtain ⟨hmlen, hmall⟩ := mapM_getElem hmap
              obtain ⟨ds, hroll, htyok⟩ := types_ok_of_frag m.types Context.empty htys
              obtain ⟨xts, hxlen, hxall⟩ := exports_ok m.exports C hexp
              have hdts : rollTypes [] m.types = ds := by
                have : (Context.empty).types = ([] : List DefType) := rfl
                rw [this] at hroll
                simpa using hroll
              have htc : Module.typeContext m = { Context.empty with types := ds } := by
                rw [Module.typeContext, hdts]; rfl
              refine ⟨_, Module_ok'.mk (C := C) (C' := C') (dts' := ds)
                (xtsI := Module.importTypes m) (xtsE := xts)
                (jts := m.tags.map (fun tg => C'.closTagType tg.tagtype)) (gts := gts)
                (mts := m.mems.map Mem.memtype) (tts := []) (dts := fdts)
                (oks := m.datas.map (fun _ => DataType.ok)) (rts := [])
                (nms := m.exports.map Export.name)
                (jtsI := ExternType.tags (Module.importTypes m))
                (gtsI := ExternType.globals (Module.importTypes m))
                (mtsI := ExternType.mems (Module.importTypes m))
                (ttsI := ExternType.tables (Module.importTypes m)) (dtsI := dtsI)
                (xs := funcidxNonfuncs m.globals m.mems m.tables m.elems)
                htyok ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hxlen hxall hdisj
                ?_ ?_ rfl rfl rfl rfl rfl ?_⟩
              · -- SeqLen₂ m.imports xt_I*
                simp only [SeqLen₂, Module.importTypes, List.length_map]
              · -- Import_ok
                rw [← htc]
                exact imports_ok m.imports himp
              · -- SeqLen₂ m.tags jt*
                simp only [SeqLen₂, List.length_map]
              · -- Tag_ok
                exact tags_ok m.tags htags
              · -- Globals_ok'
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
              · rw [htb']; rfl
              · rw [htb']; intro i a b ha _; simp at ha
              · -- SeqLen₂ m.funcs fdts
                exact hmlen
              · -- Func_ok'
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
              · -- Data_ok'
                intro i a b ha _
                cases b
                exact checkData_sound (List.all_eq_true.mp hdatas a (List.mem_of_getElem? ha))
              · rw [hel']; rfl
              · rw [hel']; intro i a b ha _; simp at ha
              · -- Start_ok
                intro s hs
                simp only [hs] at hstart
                exact checkStart_sound hstart
              · rw [← hC, ← hC']; simp
              · rw [← hC', hdts]
              · exact hfx

end Validate

/-- `Wasm.Core.validate_sound`: the soundness of this development's executable
module validator against the amended declarative judgment. -/
theorem validate_sound {m : Module} (h : validate m = true) :
    ∃ mt : ModuleType, Module_ok' m mt :=
  Validate.validate_sound h

/-! ## WHAT BLOCKED `validate_complete`, AND WHERE IT IS DISCHARGED

This section is the record of the obstruction as it stood when this file was
written.  It is discharged in `Core/ValidateComplete.lean`: `substValType_nv`
is the missing lemma, `rollDt_frag` / `expandDt_frag` / `funcTypeOf_rollDt`
carry it through `$rollrt`, `$rolldt`, `$unrollrt` and `$expanddt`,
`types_ok_roll` is the `Types_ok` inversion, `checkGlobals_complete` and
`funcs_complete` are the other two, and `Validate.validate_complete` there is
the theorem.  Nothing below has been weakened to get it; the paragraph stands
as written, with its verdict now superseded rather than edited away.

The statement it would have is

    `Module_ok' m mt -> Module.frag m = true -> Wasm.Core.validate m = true`

--- the `Module.frag` hypothesis is not a weakening but a fact about the
checker.  When this paragraph was written `validate` rejected every module with
an import, a tag, a table or an element segment outright; IMPORTS and TAGS have
since been brought inside, with a per-entry guard rather than a per-section one
(`checkExternType`, `checkTag`, `imports_ok` and `tags_ok` above are the
soundness half).  What `Module.frag` still excludes outright is the TABLE and
ELEMENT sections, whose initialisers are reference-typed and therefore need
`Heaptype_sub`.  `Module.frag` is the checker's own statement of which modules it
decides.

Every instruction-level ingredient is in place.  `checkSeq_complete` and
`checkExpr_complete` of `Core/ValidateSeq.lean` are proved, over exactly the
hypotheses `Context.frag C` and `InstrSeq.frag e`, and `Module.frag m` supplies
the second one for every expression of the module.  What is NOT available is the
first one, and the reason is one specific missing lemma:

  `Context.frag C` requires `C.TYPES` and `C.FUNCS` to consist of `deftype`s
  that `funcTypeOf` accepts --- that is, whose expansion is a function type over
  `numtype`s and `vectype`s.  `Module.frag m` says that of the SOURCE `rectype`s
  (`TypeDef.frag`), and `Module.contexts` puts `$rolldt` of them into `C.TYPES`.
  Closing the gap needs

      $rolldt, and then $expanddt, carry a function type over numtypes and
      vectypes to the SAME function type

  i.e. that the substitutions `$rollrt` and `$unrollrt` perform are the identity
  on a `comptype` that mentions no `typevar`.  `Core/Subst.lean`'s
  `substValType` does return `.num nt` and `.vec vt` unchanged, so the lemma is
  true and is not deep; it is simply not proved in this development, and neither
  is the chain of inversions (`Types_ok` back to `rollTypes`, `Globals_ok'` back
  to `checkGlobals`, `Func_ok'` back to `checkFunc`) that would consume it.

That was the whole of the obstruction, stated so it could be checked rather
than taken on trust.  It IS discharged, in `Core/ValidateComplete.lean`, and
both theorems are there: `Wasm.Core.validate_complete` and
`Wasm.Core.validate_iff_declarative`.  The `Module.frag` premise is still
present and is still not a weakening --- the equivalence carries it as a
CONJUNCT on both sides and so has no hypothesis at all --- but it is now the
only thing separating this equivalence from all of Core, and what its two
remaining excluded sections cost is exactly a decision procedure for
`Heaptype_sub`.

SPEC 15's required name `Wasm.validate_iff_declarative` is a DIFFERENT
declaration, in `Wasm/Declarative.lean`, still bound to the i32-subset model;
nothing here moves it.  Pointing it at `Wasm.Core` is the release-path
migration, not this file's business. -/

end WasmGemmGnaf.Wasm.Core
