/-
  Wasm/Core/ValidateComplete.lean --- COMPLETENESS of the executable module
  validator against the AMENDED declarative module judgment, and the
  equivalence.

  `Core/ValidateModule.lean` proves `validate_sound` and then names, exactly,
  what stood between this development and the converse:

      `$rolldt`, and then `$expanddt`, carry a function type over numtypes and
      vectypes to the SAME function type

  together with the chain of inversions --- `Types_ok` back to `rollTypes`,
  `Globals_ok'` back to `checkGlobals`, `Func_ok'` back to `checkFunc` --- that
  consumes it.  Both are discharged below: `substValType_nv` is the observation
  that `$subst_valtype` is the identity on `numtype`s and `vectype`s, and
  `rollDt_frag` / `expandDt_frag` carry it through `$rollrt`, `$rolldt`,
  `$unrollrt` and `$expanddt` to `funcTypeOf_rollDt`, which is the fact
  `Context.frag` needs about the contexts `Module.contexts` builds.

  WHAT IS PROVED HERE.

    `validate_complete`        -- `Module.frag m = true -> Module_ok' m mt ->
                                  validate m = true`.
    `validate_iff_declarative` -- `validate m = true <->
                                  Module.frag m = true /\ exists mt, Module_ok' m mt`.
                                  NO hypothesis: the fragment condition is a
                                  CONJUNCT of the equivalence, not a side
                                  condition on it, because `validate` decides it
                                  (`validate m = Module.frag m && ...`).

  WHY `Module.frag` IS THERE AT ALL.  It is the checker's own statement of which
  modules it decides, and it is not a weakening of the equivalence: it appears
  on BOTH sides.  `validate` rejects every module with an import, a tag, a table
  or an element segment outright, because each of those needs `Heaptype_sub`,
  whose decidability this development does not have; a module with a table has a
  `Module_ok'` derivation and is rejected, so `Module_ok' m mt -> validate m =
  true` with no further premise is FALSE and is not stated.  Closing the
  remaining gap is a decision procedure for `Heaptype_sub`, not a repair of
  anything below.

  STATED OVER THE AMENDED RELATION, WITH DEV-006 CITED.  As in
  `Core/ValidateModule.lean`: the pinned `Instrs_ok` cannot type
  `i32.const c; i32.add` (`Instrs_ok.const_binop_untypable`), so the same
  statement over the pinned `Module_ok` is FALSE in the soundness direction.
  That is DEV-006, filed upstream as WebAssembly/spec issue #2194 and fixed
  there in PR #2197 (`bd4633ac...`) nine months after the pin.  `Module_ok'` is
  an inductive relation of `Core/Validation/ModulesAmended.lean`, a file that
  does not import this one and cannot mention the checker, so the biconditional
  below is a reflection theorem and not a restatement of the checker's own
  booleans.
-/
import WasmGemmGnaf.Wasm.Core.ValidateModule

set_option autoImplicit false
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## Lists, pointwise

The declarative rules relate two sequences by `SeqLen₂` plus `SeqAll₂`; the
checker consumes ordinary list equalities and `List.mapM`.  These are the two
translations. -/

/-- Two sequences of equal length whose elements agree pointwise are equal. -/
theorem list_eq_of_getElem? {α : Type} : ∀ {as bs : List α}, as.length = bs.length →
    (∀ (i : Nat) (a b : α), as[i]? = some a → bs[i]? = some b → a = b) → as = bs := by
  intro as
  induction as with
  | nil =>
      intro bs hlen _
      cases bs with
      | nil => rfl
      | cons b bs => exact absurd hlen (by simp)
  | cons a as ih =>
      intro bs hlen h
      cases bs with
      | nil => exact absurd hlen (by simp)
      | cons b bs =>
          have hab : a = b := h 0 a b rfl rfl
          subst hab
          have : as = bs :=
            ih (by simpa using hlen)
              (fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy))
          rw [this]

/-- `List.mapM` over `Option`, built pointwise: the converse of
`mapM_getElem`. -/
theorem mapM_of_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ (i : Nat) (a : α) (b : β), xs[i]? = some a → ys[i]? = some b → f a = some b) →
      xs.mapM f = some ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen _
      cases ys with
      | nil => rfl
      | cons b bs => exact absurd hlen (by simp)
  | cons a as ih =>
      intro ys hlen h
      cases ys with
      | nil => exact absurd hlen (by simp)
      | cons b bs =>
          have hfa : f a = some b := h 0 a b rfl rfl
          have hrest : as.mapM f = some bs :=
            ih (by simpa using hlen)
              (fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy))
          simp only [List.mapM_cons, hfa, hrest]
          rfl

/-- A sequence the rules pair with the empty sequence is empty. -/
theorem eq_nil_of_length_zero {α : Type} {l : List α} (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a as => exact absurd h (by simp)

/-! ## A. `$subst_valtype` is the identity on the fragment

This is the lemma `Core/ValidateModule.lean` names as the whole of the
obstruction.  `$subst_valtype` descends only into `REF`; a `numtype` or a
`vectype` has no `typevar` inside it and is returned unchanged, in EVERY
substitution. -/

/-- `$subst_valtype` fixes every `numtype` and every `vectype`. -/
theorem substValType_nv {t : ValType} (h : ValType.nv t = true)
    (tvs : List TypeVar) (tus : List TypeUse) : substValType t tvs tus = t := by
  cases t with
  | num _ => rfl
  | vec _ => rfl
  | ref _ => exact absurd h (by simp [ValType.nv])
  | bot => exact absurd h (by simp [ValType.nv])

/-- ... hence it fixes every `resulttype` of the decided fragment.  `ValTypes`
is one leg of the mutual knot of `Core/Types.lean`, so this is a structural
recursion rather than an `induction`. -/
theorem substValTypes_nvs : ∀ (ts : ValTypes), nvs (ValTypes.toList ts) = true →
    ∀ (tvs : List TypeVar) (tus : List TypeUse), substValTypes ts tvs tus = ts
  | .nil, _, _, _ => rfl
  | .cons t rest, h, tvs, tus => by
      simp only [nvs, ValTypes.toList, List.all_cons, Bool.and_eq_true] at h
      show ValTypes.cons (substValType t tvs tus) (substValTypes rest tvs tus) = _
      rw [substValType_nv h.1, substValTypes_nvs rest (by simpa [nvs] using h.2) tvs tus]

/-- The shape of a type definition of the decided fragment: one final,
supertype-free function type over the fragment's value types. -/
theorem frag_rectype {td : TypeDef} (h : TypeDef.frag td = true) :
    ∃ dom cod : ValTypes,
      td.rectype = .recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil) ∧
      nvs (ValTypes.toList dom) = true ∧ nvs (ValTypes.toList cod) = true := by
  unfold TypeDef.frag at h
  split at h
  · rename_i dom cod heq
    simp only [Bool.and_eq_true] at h
    exact ⟨dom, cod, heq, h.1, h.2⟩
  · exact absurd h (by simp)

/-- `$subst_subtype` fixes the single `subtype` of such a definition: its
supertype list is empty and its component type is a function type over the
fragment. -/
theorem substSubTypes_frag {dom cod : ValTypes}
    (hd : nvs (ValTypes.toList dom) = true) (hc : nvs (ValTypes.toList cod) = true)
    (tvs : List TypeVar) (tus : List TypeUse) :
    substSubTypes (.cons (.sub (some .final) .nil (.func dom cod)) .nil) tvs tus =
      .cons (.sub (some .final) .nil (.func dom cod)) .nil := by
  show SubTypes.cons (substSubType (.sub (some .final) .nil (.func dom cod)) tvs tus)
      (substSubTypes .nil tvs tus) = _
  show SubTypes.cons (.sub (some .final) (substTypeUses .nil tvs tus)
      (substCompType (.func dom cod) tvs tus)) .nil = _
  show SubTypes.cons (.sub (some .final) .nil
      (.func (substValTypes dom tvs tus) (substValTypes cod tvs tus))) .nil = _
  rw [substValTypes_nvs dom hd, substValTypes_nvs cod hc]

/-- **`$rollrt` IS THE IDENTITY ON THE FRAGMENT.**  It replaces the group's own
absolute type indices by `REC` variables, and a function type over `numtype`s
and `vectype`s contains no type index to replace. -/
theorem rollRt_frag {dom cod : ValTypes}
    (hd : nvs (ValTypes.toList dom) = true) (hc : nvs (ValTypes.toList cod) = true)
    (x : TypeIdx) :
    rollRt x (.recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil)) =
      .recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil) := by
  show RecType.recr (substSubTypes _ _ _) = _
  rw [substSubTypes_frag hd hc]

/-- **`$unrollrt` IS THE IDENTITY ON THE FRAGMENT**, for the same reason. -/
theorem unrollRt_frag {dom cod : ValTypes}
    (hd : nvs (ValTypes.toList dom) = true) (hc : nvs (ValTypes.toList cod) = true) :
    unrollRt (.recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil)) =
      .recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil) := by
  show RecType.recr (substSubTypes _ _ _) = _
  rw [substSubTypes_frag hd hc]

/-- `$rolldt` of a type definition of the fragment is the single `deftype` that
selects its only member. -/
theorem rollDt_frag {td : TypeDef} (h : TypeDef.frag td = true) (x : TypeIdx) :
    rollDt x td.rectype = [DefType.defd td.rectype 0] := by
  obtain ⟨dom, cod, heq, hd, hc⟩ := frag_rectype h
  rw [heq, rollDt, rollRt_frag hd hc]
  rfl

/-- `$expanddt` of that `deftype` is the function type the definition writes:
`$unrolldt` reads member `0` back out of a group `$unrollrt` has not changed. -/
theorem expandDt_frag {td : TypeDef} {dom cod : ValTypes}
    (heq : td.rectype = .recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil))
    (hd : nvs (ValTypes.toList dom) = true) (hc : nvs (ValTypes.toList cod) = true) :
    expandDt (DefType.defd td.rectype 0) = some (.func dom cod) := by
  rw [expandDt, unrollDt, heq, unrollRt_frag hd hc]
  rfl

/-- **THE LEMMA THE OBSTRUCTION NAMED.**  Every `deftype` the type section of a
module of the decided fragment elaborates to is one the checker's `funcTypeOf`
accepts --- which is exactly what `Context.frag` requires of `C.TYPES`. -/
theorem funcTypeOf_rollDt {td : TypeDef} (h : TypeDef.frag td = true) (x : TypeIdx) :
    ∀ dt ∈ rollDt x td.rectype, (funcTypeOf dt).isSome = true := by
  obtain ⟨dom, cod, heq, hd, hc⟩ := frag_rectype h
  rw [rollDt_frag h]
  intro dt hdt
  have hdt' : dt = DefType.defd td.rectype 0 := by
    simpa using hdt
  subst hdt'
  rw [funcTypeOf, expandDt_frag heq hd hc]
  simp only [hd, hc, Bool.and_self, if_true]
  rfl

/-- ... and `rollTypes`, the fold that computes the whole type section, keeps
that property. -/
theorem funcTypeOf_rollTypes : ∀ (tds : List TypeDef) (acc : List DefType),
    tds.all TypeDef.frag = true →
    acc.all (fun dt => (funcTypeOf dt).isSome) = true →
    (rollTypes acc tds).all (fun dt => (funcTypeOf dt).isSome) = true := by
  intro tds
  induction tds with
  | nil => intro acc _ hacc; exact hacc
  | cons td tds ih =>
      intro acc h hacc
      simp only [List.all_cons, Bool.and_eq_true] at h
      refine ih _ h.2 ?_
      rw [List.all_append, hacc, Bool.true_and, List.all_eq_true]
      intro dt hdt
      exact funcTypeOf_rollDt h.1 _ dt hdt

/-! ## B. `Types_ok` back to `rollTypes`

The declarative type-section rule fixes `dt* = $rolldt(x, rectype)` with
`x = |C.TYPES|`, and its `cons` rule extends the context by exactly what it
just rolled.  So the relation determines its own right-hand side, and the
function that computes it is `rollTypes`. -/

/-- The `deftype*` a `Types_ok` derivation produces is the one `rollTypes`
computes. -/
theorem types_ok_roll : ∀ {C : Context} {tds : List TypeDef} {ds : List DefType},
    Types_ok C tds ds → rollTypes C.types tds = C.types ++ ds := by
  intro C tds ds h
  induction h with
  | empty => simp [rollTypes]
  | @cons C td tds dts₁ dts hty _ ih =>
      cases hty with
      | mk hx hdts _ =>
          subst hx
          subst hdts
          show rollTypes (C.types ++ rollDt (TypeIdx.ofNat C.types.length) td.rectype) tds = _
          have hC : (Context.append C
              { types := rollDt (TypeIdx.ofNat C.types.length) td.rectype }).types =
              C.types ++ rollDt (TypeIdx.ofNat C.types.length) td.rectype := rfl
          rw [hC] at ih
          rw [ih, List.append_assoc]

/-! ## C. Contexts of the fragment

`Context.frag` is a conjunction over the components `checkSeq` reads, so it is
preserved by `Context.append` componentwise. -/

/-- `Context.frag` is closed under the context extension the rules use. -/
theorem frag_append {C D : Context} (hC : Context.frag C = true)
    (hD : Context.frag D = true) : Context.frag (Context.append C D) = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC hD ⊢
  obtain ⟨⟨⟨⟨⟨hl, hlb⟩, hr⟩, hg⟩, hf⟩, ht⟩ := hC
  obtain ⟨⟨⟨⟨⟨hl', hlb'⟩, hr'⟩, hg'⟩, hf'⟩, ht'⟩ := hD
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show (C.locals ++ D.locals).all _ = true
    rw [List.all_append, hl, hl']; rfl
  · show (C.labels ++ D.labels).all _ = true
    rw [List.all_append, hlb, hlb']; rfl
  · show (match (Context.append C D).ret with | none => true | some ts => nvs ts) = true
    have : (Context.append C D).ret = match C.ret with | some r => some r | none => D.ret := rfl
    rw [this]
    cases hCr : C.ret with
    | none => simpa [hCr] using hr'
    | some r => rw [hCr] at hr; simpa using hr
  · show (C.globals ++ D.globals).all _ = true
    rw [List.all_append, hg, hg']; rfl
  · show (C.funcs ++ D.funcs).all _ = true
    rw [List.all_append, hf, hf']; rfl
  · show (C.types ++ D.types).all _ = true
    rw [List.all_append, ht, ht']; rfl

/-- The one-global extension of `Globals_ok/cons` and `checkGlobals`. -/
theorem frag_global_ext {gt : GlobalType} (h : ValType.nv gt.valtype = true) :
    Context.frag { globals := [gt] } = true := by
  simp [Context.frag, h]

/-! ## D. `Instr_const` back to `Instr.isConst`

`Instr_const` has fourteen rules; ten of them are reference or aggregate
instructions, which `Instr.frag` does not admit, so on the decided fragment the
relation and the test agree. -/

/-- Every constant instruction of the decided fragment passes `Instr.isConst`. -/
theorem isConst_complete {C : Context} {i : Instr} (hfrag : Instr.frag i = true)
    (h : Instr_const C i) : Instr.isConst C i = true := by
  cases h with
  | const hwf => simpa [Instr.isConst] using hwf
  | vconst => rfl
  | ref_null => exact absurd hfrag (by simp [Instr.frag])
  | ref_i31 => exact absurd hfrag (by simp [Instr.frag])
  | ref_func => exact absurd hfrag (by simp [Instr.frag])
  | struct_new => exact absurd hfrag (by simp [Instr.frag])
  | struct_new_default => exact absurd hfrag (by simp [Instr.frag])
  | array_new => exact absurd hfrag (by simp [Instr.frag])
  | array_new_default => exact absurd hfrag (by simp [Instr.frag])
  | array_new_fixed => exact absurd hfrag (by simp [Instr.frag])
  | any_convert_extern => exact absurd hfrag (by simp [Instr.frag])
  | extern_convert_any => exact absurd hfrag (by simp [Instr.frag])
  | global_get hg => rw [Instr.isConst, hg]
  | @binop n op hop =>
      rcases hop with rfl | rfl | rfl <;> cases n <;> rfl

/-- Every instruction of a sequence in the decided fragment is. -/
theorem frag_mem : ∀ (s : InstrSeq), InstrSeq.frag s = true →
    ∀ i ∈ InstrSeq.toList s, Instr.frag i = true
  | .nil, _, i, hi => absurd hi (by simp [InstrSeq.toList])
  | .cons j rest, h, i, hi => by
      rw [InstrSeq.frag, Bool.and_eq_true] at h
      rcases List.mem_cons.mp (by simpa [InstrSeq.toList] using hi) with rfl | hrest
      · exact h.1
      · exact frag_mem rest h.2 i hrest

/-- `Expr_ok_const'` back to `checkConstExpr`: the typing half is
`checkExpr_complete`, the syntactic half is `isConst_complete`. -/
theorem checkConstExpr_complete {C : Context} {e : Expr} {t : ValType}
    (hC : Context.frag C = true) (hfrag : InstrSeq.frag e = true)
    (ht : ValType.nv t = true) (h : Expr_ok_const' C e t) :
    checkConstExpr C e t = true := by
  cases h with
  | mk hok hconst =>
      simp only [checkConstExpr, Bool.and_eq_true]
      refine ⟨checkExpr_complete hC hfrag hok (by simp [nvs, ht]), ?_⟩
      cases hconst with
      | mk hall =>
          rw [List.all_eq_true]
          intro i hi
          exact isConst_complete (frag_mem e hfrag i hi) (hall i hi)

/-! ## E. The module-level judgments, back to their checks -/

/-- `Limits_ok` back to `checkLimits`. -/
theorem checkLimits_complete {C : Context} {lim : Limits} {k : Nat}
    (h : Limits_ok C lim k) : checkLimits lim k = true := by
  cases h with
  | mk hmin hmax =>
      simp only [checkLimits, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hmin, ?_⟩
      cases hm : lim.max with
      | none => rfl
      | some mx =>
          obtain ⟨h1, h2⟩ := hmax mx hm
          simp [h1, h2]

/-- A value type of the fragment has a default, so `Local_ok/unset` cannot
apply to it. -/
theorem noDefault_of_nv {t : ValType} (h : ValType.nv t = true) :
    ValType.noDefault t = false := by
  cases t <;> simp_all [ValType.nv, ValType.noDefault]

/-- `Local_ok` on a local of the fragment gives exactly the `SET` local type the
checker builds. -/
theorem local_ok_set {C : Context} {l : Local} {lct : LocalType}
    (hnv : ValType.nv l.valtype = true) (h : Local_ok C l lct) :
    lct = ⟨Init.set, l.valtype⟩ := by
  cases h with
  | set _ => rfl
  | unset hnd =>
      cases hnd with
      | mk hnd => rw [noDefault_of_nv hnv] at hnd; exact absurd hnd (by simp)

/-- The context a function body is checked in is in the decided fragment. -/
theorem frag_func_ext {dom cod : List ValType} {locals : List Local}
    (hd : nvs dom = true) (hc : nvs cod = true)
    (hl : locals.all (fun l => ValType.nv l.valtype) = true) :
    Context.frag
      { locals := dom.map (fun t => ⟨Init.set, t⟩) ++
                  locals.map (fun l => ⟨Init.set, l.valtype⟩),
        labels := [cod], ret := some cod } = true := by
  have hd' : dom.all ValType.nv = true := hd
  have hl' : locals.all (fun l => ValType.nv l.valtype) = true := hl
  have h1 : ((dom.map (fun t => (⟨Init.set, t⟩ : LocalType)) ++
      locals.map (fun l => (⟨Init.set, l.valtype⟩ : LocalType))).all
        (fun lt => (lt.init == Init.set) && ValType.nv lt.valtype)) = true := by
    rw [List.all_eq_true]
    intro lt hlt
    rcases List.mem_append.mp hlt with hmem | hmem
    · obtain ⟨t, ht, hlt'⟩ := List.mem_map.mp hmem
      rw [← hlt']
      simpa using List.all_eq_true.mp hd' t ht
    · obtain ⟨l, hlm, hlt'⟩ := List.mem_map.mp hmem
      rw [← hlt']
      simpa using List.all_eq_true.mp hl' l hlm
  simp [Context.frag, h1, hc]

/-- `Func_ok'` back to `checkFunc`. -/
theorem checkFunc_complete {C : Context} {f : Func} {dt : DefType}
    (hC : Context.frag C = true)
    (hlocals : f.locals.all (fun l => ValType.nv l.valtype) = true)
    (hbody : InstrSeq.frag f.body = true) (h : Func_ok' C f dt) :
    checkFunc C f = true := by
  cases h with
  | @mk dom cod lcts hty hexp hlen hall hok =>
      have hft := funcTypeOf_of_expand hexp (frag_type hC hty)
      obtain ⟨hnvd, hnvc⟩ := funcTypeOf_nv hft
      have hlcts : lcts = f.locals.map (fun l => (⟨Init.set, l.valtype⟩ : LocalType)) := by
        refine list_eq_of_getElem? (by simp [← hlen]) ?_
        intro i a b ha hb
        rw [List.getElem?_map] at hb
        cases hl : f.locals[i]? with
        | none => rw [hl] at hb; exact absurd hb (by simp)
        | some l =>
            rw [hl] at hb
            simp only [Option.map_some, Option.some.injEq] at hb
            rw [← hb]
            refine local_ok_set ?_ (hall i l a hl ha)
            exact List.all_eq_true.mp hlocals l (List.mem_of_getElem? hl)
      rw [hlcts] at hok
      simp only [checkFunc, hty, hft, Bool.and_eq_true]
      exact ⟨hlocals, checkExpr_complete
        (frag_append hC (frag_func_ext hnvd hnvc hlocals)) hbody hok hnvc⟩

/-- `Data_ok'` back to `checkData`. -/
theorem checkData_complete {C : Context} {d : Data} (hC : Context.frag C = true)
    (hfrag : (match d.mode with
              | .passive => true
              | .active _ e => InstrSeq.frag e) = true)
    (h : Data_ok' C d .ok) : checkData C d = true := by
  cases h with
  | mk hm =>
      generalize hmode : d.mode = md at hm hfrag
      cases hm with
      | passive => simp only [checkData, hmode]
      | active hmem hconst =>
          rename_i x e mt
          have hfrag' : InstrSeq.frag e = true := hfrag
          simp only [checkData, hmode, hmem]
          exact checkConstExpr_complete hC hfrag' (by cases mt.addr <;> rfl) hconst

/-- `Start_ok` back to `checkStart`. -/
theorem checkStart_complete {C : Context} {s : Start} (h : Start_ok C s) :
    checkStart C s = true := by
  cases h with
  | mk hfun hexp =>
      cases hexp with
      | mk he => simp only [checkStart, hfun, he]

/-- `Externidx_ok` back to `checkExternIdx`. -/
theorem checkExternIdx_complete {C : Context} {xi : ExternIdx} {xt : ExternType}
    (h : Externidx_ok C xi xt) : checkExternIdx C xi = true := by
  cases h with
  | tag hx => rw [checkExternIdx, hx]; rfl
  | global hx => rw [checkExternIdx, hx]; rfl
  | mem hx => rw [checkExternIdx, hx]; rfl
  | table hx => rw [checkExternIdx, hx]; rfl
  | func hx => rw [checkExternIdx, hx]; rfl

/-- `Globals_ok'` determines the global types: they are the declared ones. -/
theorem globals_types : ∀ {C : Context} {gs : List Global} {gts : List GlobalType},
    Globals_ok' C gs gts → gts = gs.map Global.globaltype := by
  intro C gs gts h
  induction h with
  | empty => rfl
  | cons hg _ ih =>
      cases hg with
      | mk _ _ => rw [List.map_cons, ih]

/-- `Globals_ok'` back to `checkGlobals`, staged context by staged context. -/
theorem checkGlobals_complete : ∀ (gs : List Global) (C : Context) (gts : List GlobalType),
    Context.frag C = true →
    gs.all (fun g => ValType.nv g.globaltype.valtype && InstrSeq.frag g.init) = true →
    Globals_ok' C gs gts → checkGlobals C gs = some gts := by
  intro gs
  induction gs with
  | nil =>
      intro C gts _ _ h
      cases h with
      | empty => rfl
  | cons g gs ih =>
      intro C gts hC hfrag h
      simp only [List.all_cons, Bool.and_eq_true] at hfrag
      cases h with
      | cons hg hrest =>
          cases hg with
          | mk _ hconst =>
              have hcond : (ValType.nv g.globaltype.valtype &&
                  checkConstExpr C g.init g.globaltype.valtype) = true := by
                rw [Bool.and_eq_true]
                exact ⟨hfrag.1.1,
                  checkConstExpr_complete hC hfrag.1.2 hfrag.1.1 hconst⟩
              have hsub := ih (Context.append C { globals := [g.globaltype] }) _
                (frag_append hC (frag_global_ext hfrag.1.1)) hfrag.2 hrest
              rw [checkGlobals, if_pos hcond, hsub]

/-- `Mem_ok` determines the memory types and discharges the limits check. -/
theorem mems_complete {C : Context} : ∀ (ms : List Mem) (mts : List MemType),
    ms.length = mts.length → SeqAll₂ (Mem_ok C) ms mts →
    mts = ms.map Mem.memtype ∧
      ms.all (fun mem => checkLimits mem.memtype.lim (2 ^ 16)) = true := by
  intro ms
  induction ms with
  | nil =>
      intro mts hlen _
      cases mts with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs => exact absurd hlen (by simp)
  | cons a ms ih =>
      intro mts hlen hall
      cases mts with
      | nil => exact absurd hlen (by simp)
      | cons b mts =>
          have hhead := hall 0 a b rfl rfl
          cases hhead with
          | mk hmt =>
              obtain ⟨hb, hck⟩ := ih mts (by simpa using hlen)
                (fun i x y hx hy => hall (i + 1) x y (by simpa using hx) (by simpa using hy))
              refine ⟨by rw [List.map_cons, ← hb], ?_⟩
              simp only [List.all_cons, Bool.and_eq_true]
              cases hmt with
              | mk hlim => exact ⟨checkLimits_complete hlim, hck⟩

/-- `Data_ok'` determines the data types and discharges the data check. -/
theorem datas_complete {C : Context} (hC : Context.frag C = true) :
    ∀ (ds : List Data) (oks : List DataType),
      ds.length = oks.length → SeqAll₂ (Data_ok' C) ds oks →
      ds.all (fun d => match d.mode with
                       | .passive => true
                       | .active _ e => InstrSeq.frag e) = true →
      oks = ds.map (fun _ => DataType.ok) ∧ ds.all (checkData C) = true := by
  intro ds
  induction ds with
  | nil =>
      intro oks hlen _ _
      cases oks with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs => exact absurd hlen (by simp)
  | cons a ds ih =>
      intro oks hlen hall hfrag
      cases oks with
      | nil => exact absurd hlen (by simp)
      | cons b oks =>
          simp only [List.all_cons, Bool.and_eq_true] at hfrag
          have hhead := hall 0 a b rfl rfl
          cases hhead with
          | mk hm =>
              obtain ⟨hb, hck⟩ := ih oks (by simpa using hlen)
                (fun i x y hx hy => hall (i + 1) x y (by simpa using hx) (by simpa using hy))
                hfrag.2
              refine ⟨by rw [List.map_cons, ← hb], ?_⟩
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨checkData_complete hC hfrag.1 (.mk hm), hck⟩

/-- `Export_ok` determines the exported names and discharges the index check. -/
theorem exports_complete {C : Context} :
    ∀ (es : List Export) (nms : List Name) (xts : List ExternType),
      es.length = nms.length → nms.length = xts.length →
      SeqAll₃ (Export_ok C) es nms xts →
      nms = es.map Export.name ∧
        es.all (fun e => checkExternIdx C e.externidx) = true := by
  intro es
  induction es with
  | nil =>
      intro nms xts hlen _ _
      cases nms with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs => exact absurd hlen (by simp)
  | cons e es ih =>
      intro nms xts hlen hlen' hall
      cases nms with
      | nil => exact absurd hlen (by simp)
      | cons nm nms =>
          cases xts with
          | nil => exact absurd hlen' (by simp)
          | cons xt xts =>
              have hhead := hall 0 e nm xt rfl rfl rfl
              cases hhead with
              | mk hidx =>
                  obtain ⟨hn, hck⟩ := ih nms xts (by simpa using hlen) (by simpa using hlen')
                    (fun i x y z hx hy hz =>
                      hall (i + 1) x y z (by simpa using hx) (by simpa using hy)
                        (by simpa using hz))
                  refine ⟨by rw [List.map_cons, ← hn], ?_⟩
                  simp only [List.all_cons, Bool.and_eq_true]
                  exact ⟨checkExternIdx_complete hidx, hck⟩

/-- The type index every function of a validated module names is the one the
declarative rule assigns it. -/
theorem funcs_type_lookup {C : Context} {fs : List Func} {dts : List DefType}
    (h : SeqAll₂ (Func_ok' C) fs dts) :
    ∀ (i : Nat) (f : Func) (dt : DefType), fs[i]? = some f → dts[i]? = some dt →
      C.types[f.typeidx.val]? = some dt := by
  intro i f dt hf hdt
  cases h i f dt hf hdt with
  | mk hty _ _ _ _ => exact hty

/-- `Func_ok'` back to `checkFunc`, over the whole function section. -/
theorem funcs_complete {C : Context} (hC : Context.frag C = true)
    {fs : List Func} {dts : List DefType} (hlen : fs.length = dts.length)
    (h : SeqAll₂ (Func_ok' C) fs dts)
    (hfrag : fs.all (fun f =>
      f.locals.all (fun l => ValType.nv l.valtype) && InstrSeq.frag f.body) = true) :
    fs.all (checkFunc C) = true := by
  rw [List.all_eq_true]
  intro f hf
  obtain ⟨i, hi, hfi⟩ := List.mem_iff_getElem.mp hf
  have hi' : i < dts.length := hlen ▸ hi
  have hok := h i f dts[i] (by rw [List.getElem?_eq_getElem hi, hfi])
    (List.getElem?_eq_getElem hi')
  have hfr := List.all_eq_true.mp hfrag f hf
  rw [Bool.and_eq_true] at hfr
  exact checkFunc_complete hC hfr.1 hfr.2 hok

/-! ## F. COMPLETENESS OF THE MODULE VALIDATOR -/

/-- **`Wasm.Core.validate` IS COMPLETE FOR THE AMENDED DECLARATIVE JUDGMENT.**
Every module of the decided fragment that the amended judgment `Module_ok'` of
`Core/Validation/ModulesAmended.lean` gives a module type, the algorithm of
`appendix/algorithm.rst` accepts.

`Module.frag m` is the checker's own statement of which modules it decides ---
`validate m = Module.frag m && ...` --- so it is not a hypothesis that hides a
gap: `validate_iff_declarative` below carries it as a CONJUNCT on both sides and
needs no hypothesis at all.  Stated over `Module_ok'` and not over the pinned
`Module_ok` for the reason `Core/ValidateModule.lean` gives; that is DEV-006. -/
theorem validate_complete {m : Module} {mt : ModuleType}
    (hfrag : Module.frag m = true) (h : Module_ok' m mt) : validate m = true := by
  have hfr := hfrag
  simp only [Module.frag, Bool.and_eq_true] at hfr
  obtain ⟨⟨⟨⟨⟨⟨⟨him, htg⟩, htb⟩, hel⟩, htys⟩, hglob⟩, hfun⟩, hdat⟩ := hfr
  have him' : m.imports = [] := List.isEmpty_iff.mp him
  have htg' : m.tags = [] := List.isEmpty_iff.mp htg
  have htb' : m.tables = [] := List.isEmpty_iff.mp htb
  have hel' : m.elems = [] := List.isEmpty_iff.mp hel
  cases h with
  | @mk C C' dts' xtsI xtsE jts gts mts tts dts oks rts nms jtsI gtsI mtsI ttsI dtsI xs
      hty hli hi hlj hj hg hlm hm hlt ht hlf hf hld hd hle he hs hlx hx hdis
      hC hC' hxs hjI hgI hmI htI hdI =>
      -- the sections outside the decided fragment are empty, and so are the
      -- external type sequences the rule pairs with them
      have hxtsI : xtsI = [] := by
        refine eq_nil_of_length_zero ?_
        rw [him'] at hli; simpa using hli.symm
      have hjts : jts = [] := by
        refine eq_nil_of_length_zero ?_
        rw [htg'] at hlj; simpa using hlj.symm
      have htts : tts = [] := by
        refine eq_nil_of_length_zero ?_
        rw [htb'] at hlt; simpa using hlt.symm
      have hrts : rts = [] := by
        refine eq_nil_of_length_zero ?_
        rw [hel'] at hle; simpa using hle.symm
      subst hxtsI; subst hjts; subst htts; subst hrts
      have hdtsI : dtsI = [] := by simpa [funcsXt] using hdI
      have hjtsI : jtsI = [] := hjI
      have hgtsI : gtsI = [] := hgI
      have hmtsI : mtsI = [] := hmI
      have httsI : ttsI = [] := htI
      subst hjtsI; subst hgtsI; subst hmtsI; subst httsI; subst hdtsI; subst hxs
      -- the type section
      have hdts' : rollTypes [] m.types = dts' := by
        have hr := types_ok_roll hty
        simpa using hr
      have hdts'all : dts'.all (fun dt => (funcTypeOf dt).isSome) = true := by
        rw [← hdts']
        exact funcTypeOf_rollTypes m.types [] htys rfl
      -- the staged contexts, read componentwise
      have hC'types : C'.types = dts' := by rw [hC']
      have hC'funcs : C'.funcs = dts := by rw [hC']; simp
      have hCtypes : C.types = dts' := by
        rw [hC]; show C'.types ++ [] = dts'; rw [hC'types, List.append_nil]
      have hdtsall : dts.all (fun dt => (funcTypeOf dt).isSome) = true := by
        rw [List.all_eq_true]
        intro dt hdt
        obtain ⟨i, hi, hdti⟩ := List.mem_iff_getElem.mp hdt
        have hi' : i < m.funcs.length := by omega
        have hlk := funcs_type_lookup hf i m.funcs[i] dt
          (List.getElem?_eq_getElem hi') (by rw [List.getElem?_eq_getElem hi, hdti])
        rw [hCtypes] at hlk
        exact List.all_eq_true.mp hdts'all dt (List.mem_of_getElem? hlk)
      have hC'frag : Context.frag C' = true := by
        rw [hC']
        simp [Context.frag, hdts'all, hdtsall]
      -- the globals
      have hgtsEq : gts = m.globals.map Global.globaltype := globals_types hg
      have hgtsnv : gts.all (fun gt => ValType.nv gt.valtype) = true := by
        rw [hgtsEq, List.all_eq_true]
        intro gt hgt
        obtain ⟨g, hgm, hgt'⟩ := List.mem_map.mp hgt
        have hx' := List.all_eq_true.mp hglob g hgm
        rw [Bool.and_eq_true] at hx'
        rw [← hgt']
        exact hx'.1
      have hCfrag : Context.frag C = true := by
        rw [hC]
        refine frag_append hC'frag ?_
        simp [Context.frag, hgtsnv]
      -- the remaining sections, each with the list its rule determines
      obtain ⟨hmtsEq, hmemck⟩ := mems_complete m.mems mts hlm hm
      obtain ⟨hoksEq, hdatack⟩ := datas_complete hCfrag m.datas oks hld hd hdat
      obtain ⟨hnmsEq, hexpck⟩ := exports_complete m.exports nms xtsE hlx.1 hlx.2 hx
      subst hmtsEq; subst hoksEq; subst hnmsEq
      -- the contexts the checker computes are the contexts the rule uses
      have hmapM : m.funcs.mapM (fun f => (rollTypes [] m.types)[f.typeidx.val]?) =
          some dts := by
        refine mapM_of_getElem hlf ?_
        intro i f dt hfi hdti
        rw [hdts']
        have hlk := funcs_type_lookup hf i f dt hfi hdti
        rwa [hCtypes] at hlk
      have hgl : checkGlobals C' m.globals = some gts :=
        checkGlobals_complete m.globals C' gts hC'frag hglob hg
      have hC'eq : C' =
          { types := rollTypes [] m.types, funcs := dts,
            refs := funcidxNonfuncs m.globals m.mems m.tables m.elems } := by
        rw [hC', hdts']; simp
      have hctx : Module.contexts m = some (C', C) := by
        simp only [Module.contexts, hmapM]
        rw [← hC'eq, hgl, hC]
        rfl
      -- the start function
      have hstart : (match m.start with
                     | none => true
                     | some s => checkStart C s) = true := by
        cases hst : m.start with
        | none => rfl
        | some s => exact checkStart_complete (hs s hst)
      simp only [validate, hfrag, Bool.true_and, hctx, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨hmemck, funcs_complete hCfrag hlf hf hfun⟩, hdatack⟩, hstart⟩, hexpck⟩, hdis⟩

/-- `validate` decides the fragment condition itself: it is the first
conjunct of the checker, so every accepted module satisfies it. -/
theorem frag_of_validate {m : Module} (h : validate m = true) :
    Module.frag m = true := by
  rw [validate, Bool.and_eq_true] at h
  exact h.1

end Validate

/-- `Wasm.Core.validate_complete`: the completeness of this development's
executable module validator against the amended declarative judgment. -/
theorem validate_complete {m : Module} {mt : ModuleType}
    (hfrag : Validate.Module.frag m = true) (h : Module_ok' m mt) :
    validate m = true :=
  Validate.validate_complete hfrag h

/-- **`Wasm.Core.validate_iff_declarative`.**  The executable validator of
`Core/Validate.lean` accepts exactly the modules of its decided fragment to
which the amended declarative judgment of
`Core/Validation/ModulesAmended.lean` gives a module type.

There is NO hypothesis.  `Module.frag` --- the checker's own statement of which
modules it decides, and the first thing `validate` computes --- is a conjunct of
the right-hand side, so the biconditional is an equivalence between two
propositions about an arbitrary module, not an equivalence restricted to a
subclass by fiat.

`Module_ok'` is an inductive relation declared in a file that does not import
this one and cannot mention `validate`, so this is a reflection theorem and not
a restatement of the checker's own booleans.  It is stated over the AMENDED
relation, with DEV-006 cited: over the pinned `Module_ok` the left-to-right
direction is FALSE (`Validate.gapModule_not_ok`). -/
theorem validate_iff_declarative (m : Module) :
    validate m = true ↔
      (Validate.Module.frag m = true ∧ ∃ mt : ModuleType, Module_ok' m mt) := by
  constructor
  · intro h
    exact ⟨Validate.frag_of_validate h, validate_sound h⟩
  · intro h
    obtain ⟨hfrag, _, hok⟩ := h
    exact validate_complete hfrag hok

/-- The same equivalence in the form the module rules consume it: on the
fragment the algorithm decides, acceptance is derivability. -/
theorem validate_iff_declarative_frag {m : Module}
    (hfrag : Validate.Module.frag m = true) :
    validate m = true ↔ ∃ mt : ModuleType, Module_ok' m mt :=
  ⟨fun h => validate_sound h, fun ⟨_, hok⟩ => validate_complete hfrag hok⟩

end WasmGemmGnaf.Wasm.Core
