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
  on BOTH sides.  A module with a table section has a `Module_ok'` derivation and
  is rejected, so `Module_ok' m mt -> validate m = true` with no further premise
  is FALSE and is not stated.

  WHAT IT EXCLUDES NOW.  Exactly the TABLE and ELEMENT sections, plus a per-entry
  admissibility test on the IMPORT and TAG sections.  Imports and tags were
  excluded outright before and are not now: `imports_complete`, `tags_complete`,
  `checkExternType_complete` and `checkTag_complete` below are the four theorems
  that moved them, and `funcsXt_closExternType_mem` together with
  `closDefTypes_frag` and `globals_closExternType_nv` are what pays for putting
  the IMPORTED components into the staged contexts --- `$clos_externtype` has to
  be shown to land inside `Context.frag`, which is a statement about the CLOSED
  external types and not about the written ones.

  The residual per-entry guard is `ExternType.frag` and `Tag.frag`: a `FUNC` or
  `TAG` names its function type by a type index rather than by an explicit
  `deftype` (which would need `Deftype_ok`, hence `Comptype_sub`), a `TABLE`
  import names its element type by an abstract heap type or a type index, and an
  imported `GLOBAL` has a value type of the instruction fragment, because the
  module's own `GLOBAL.GET` reads it.

  What the two remaining sections cost is NOT more of this: a table and an
  element segment each carry an initialiser of REFERENCE type, so both need the
  reference instructions, and those need `Heaptype_sub`.

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

/-! ## A2. `$clos_deftypes` is the identity on the rolled fragment

`Module_ok` closes the imported external types against `C.TYPES` --- an import's
`FUNC _IDX x` becomes `FUNC $clos_deftypes(dt'*)[x]`, which is what makes
`$funcsxt` defined on it.  The imported `deftype`s therefore have to be shown to
be the ones `Context.frag` accepts, and the shortest route is that the closure
does not move a type section of the fragment at all. -/

/-- A `deftype` whose group is the one-member, final, supertype-free function
type over the fragment's value types --- the shape `$rolldt` produces from a
`TypeDef.frag`.  The member index is unconstrained: `$subst_all_deftype` does
not read it. -/
def DefType.frag (dt : DefType) : Bool :=
  match dt with
  | .defd (.recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil)) _ =>
      nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)
  | _ => false

/-- `$subst_all_deftype` is the identity on such a `deftype`: it descends to
`substSubTypes`, which `substSubTypes_frag` fixes. -/
theorem substAllDefType_frag {dt : DefType} (h : DefType.frag dt = true)
    (tus : List TypeUse) : substAllDefType dt tus = dt := by
  unfold DefType.frag at h
  split at h
  · rename_i dom cod i
    simp only [Bool.and_eq_true] at h
    show DefType.defd (substRecType _ _ _) i = _
    show DefType.defd (.recr (substSubTypes _ _ _)) i = _
    rw [substSubTypes_frag h.1 h.2]
  · exact absurd h (by simp)

/-- ... hence `$clos_deftypes`, which is that substitution folded over the
section, only appends. -/
theorem closDefTypesAux_frag : ∀ (dts : List DefType) (acc : List DefType),
    dts.all DefType.frag = true → closDefTypesAux acc dts = acc ++ dts := by
  intro dts
  induction dts with
  | nil => intro acc _; simp [closDefTypesAux]
  | cons dt rest ih =>
      intro acc h
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [closDefTypesAux, substAllDefType_frag h.1, ih _ h.2]
      simp

/-- **`$clos_deftypes` IS THE IDENTITY ON A TYPE SECTION OF THE FRAGMENT.** -/
theorem closDefTypes_frag {dts : List DefType} (h : dts.all DefType.frag = true) :
    closDefTypes dts = dts := by
  rw [closDefTypes, closDefTypesAux_frag dts [] h]
  simp

/-- `$rolldt` of a type definition of the fragment produces `deftype`s of the
fragment. -/
theorem defTypeFrag_rollDt {td : TypeDef} (h : TypeDef.frag td = true) (x : TypeIdx) :
    (rollDt x td.rectype).all DefType.frag = true := by
  obtain ⟨dom, cod, heq, hd, hc⟩ := frag_rectype h
  rw [rollDt_frag h]
  simp only [List.all_cons, List.all_nil, Bool.and_true, heq]
  simp [DefType.frag, hd, hc]

/-- ... and `rollTypes` keeps that property, exactly as it keeps
`funcTypeOf`'s. -/
theorem defTypeFrag_rollTypes : ∀ (tds : List TypeDef) (acc : List DefType),
    tds.all TypeDef.frag = true → acc.all DefType.frag = true →
    (rollTypes acc tds).all DefType.frag = true := by
  intro tds
  induction tds with
  | nil => intro acc _ hacc; exact hacc
  | cons td tds ih =>
      intro acc h hacc
      simp only [List.all_cons, Bool.and_eq_true] at h
      refine ih _ h.2 ?_
      rw [List.all_append, hacc, Bool.true_and]
      exact defTypeFrag_rollDt h.1 _

/-! ## A3. What a closing substitution can return

`$subst_typevar` walks two sequences in lockstep and returns either an entry of
the second one or the variable it was given.  That dichotomy --- and not the
index arithmetic --- is everything the module rule needs about `$clos_externtype`
on a `FUNC _IDX x` import: `$funcsxt` is defined on the result only in the first
case, and the entries of the second sequence are `$clos_deftypes(C.TYPES)`. -/

/-- `$subst_typevar` returns an entry of its substitution or its own
argument. -/
theorem substTypeVar_mem_or : ∀ (tv : TypeVar) (tvs : List TypeVar) (tus : List TypeUse),
    substTypeVar tv tvs tus ∈ tus ∨ substTypeVar tv tvs tus = tv.toTypeUse := by
  intro tv tvs
  induction tvs with
  | nil => intro tus; exact Or.inr rfl
  | cons tv₁ tvs ih =>
      intro tus
      cases tus with
      | nil => exact Or.inr rfl
      | cons tu₁ tus =>
          show (if tv = tv₁ then tu₁ else substTypeVar tv tvs tus) ∈ _ ∨
            (if tv = tv₁ then tu₁ else substTypeVar tv tvs tus) = _
          by_cases hb : tv = tv₁
          · rw [if_pos hb]; exact Or.inl (by simp)
          · rw [if_neg hb]
            rcases ih tus with hmem | heq
            · exact Or.inl (by simp [hmem])
            · exact Or.inr heq

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

/-! ### The type-use, heap-type, external-type, tag and import checks

Each of these is `Externtype_ok`'s or `Tag_ok`'s premise read backwards.  No
expression and no subtyping is involved, so the only residual hypothesis is the
syntactic one `ExternType.frag` / `Tag.frag` states: the `typeuse` is a type
index, and a `TABLE`'s heap type is abstract or a type index. -/

/-- `Expand_use` at a function type, back to `checkFuncTypeUse`.  `Typeuse_ok`
is not needed: `Expand_use/typeidx` already carries the lookup. -/
theorem checkFuncTypeUse_complete {C : Context} {x : TypeIdx} {dom cod : ValTypes}
    (hexp : Expand_use C (.idx x) (.func dom cod)) :
    checkFuncTypeUse C (.idx x) = true := by
  cases hexp with
  | typeidx hlk hexp' =>
      cases hexp' with
      | mk he =>
          rw [checkFuncTypeUse, hlk]
          exact isFuncDt_iff.mpr ⟨dom, cod, he⟩

/-- `Heaptype_ok` back to `checkHeapType`. -/
theorem checkHeapType_complete {C : Context} {ht : HeapType}
    (hfrag : HeapType.frag ht = true) (h : Heaptype_ok C ht) :
    checkHeapType C ht = true := by
  cases h with
  | abs => rfl
  | @typeuse _ tu htu =>
      cases tu with
      | recu _ => exact absurd hfrag (by simp [HeapType.frag])
      | defd _ => exact absurd hfrag (by simp [HeapType.frag])
      | idx x =>
          cases htu with
          | typeidx hlk => simp [checkHeapType, hlk]

/-- `Reftype_ok` back to `checkRefType`. -/
theorem checkRefType_complete {C : Context} {nul : Option Null} {ht : HeapType}
    (hfrag : HeapType.frag ht = true) (h : Reftype_ok C (.ref nul ht)) :
    checkRefType C (.ref nul ht) = true := by
  cases h with
  | mk hht => exact checkHeapType_complete hfrag hht

/-- `Externtype_ok` back to `checkExternType`, on the external types of the
fragment. -/
theorem checkExternType_complete {C : Context} {xt : ExternType}
    (hfrag : ExternType.frag xt = true) (h : Externtype_ok C xt) :
    checkExternType C xt = true := by
  cases h with
  | @tag jt hjt =>
      cases jt with
      | recu _ => exact absurd hfrag (by simp [ExternType.frag])
      | defd _ => exact absurd hfrag (by simp [ExternType.frag])
      | idx x => cases hjt with | mk _ hexp => exact checkFuncTypeUse_complete hexp
  | @func tu _ _ _ hexp =>
      cases tu with
      | recu _ => exact absurd hfrag (by simp [ExternType.frag])
      | defd _ => exact absurd hfrag (by simp [ExternType.frag])
      | idx x => exact checkFuncTypeUse_complete hexp
  | @global gt _ => exact hfrag
  | @mem mt hmt => cases hmt with | mk hlim => exact checkLimits_complete hlim
  | @table tt htt =>
      have hel : ∃ (nul : Option Null) (ht : HeapType), tt.elem = .ref nul ht := by
        cases hrt' : tt.elem with
        | ref nul ht => exact ⟨nul, ht, rfl⟩
      obtain ⟨nul, ht, hrt'⟩ := hel
      have hfr : HeapType.frag ht = true := by
        have h' : ExternType.frag (.table tt) = true := hfrag
        rw [ExternType.frag, hrt'] at h'
        exact h'
      cases htt with
      | mk hlim hrt =>
          rw [hrt'] at hrt
          simp only [checkExternType, Bool.and_eq_true]
          refine ⟨checkLimits_complete hlim, ?_⟩
          rw [hrt']
          exact checkRefType_complete hfr hrt

/-- `Tag_ok` back to `checkTag`. -/
theorem checkTag_complete {C : Context} {tg : Tag} {jt : TagType}
    (hfrag : Tag.frag tg = true) (h : Tag_ok C tg jt) : checkTag C tg = true := by
  cases h with
  | mk hjt =>
      unfold Tag.frag at hfrag
      split at hfrag
      · rename_i x heq
        rw [heq] at hjt
        cases hjt with
        | mk _ hexp => rw [checkTag, heq]; exact checkFuncTypeUse_complete hexp
      · exact absurd hfrag (by simp)

/-- `Tag_ok` determines the tag types and discharges the tag check. -/
theorem tags_complete {C : Context} : ∀ (tgs : List Tag) (jts : List TagType),
    tgs.all Tag.frag = true → tgs.length = jts.length → SeqAll₂ (Tag_ok C) tgs jts →
    jts = tgs.map (fun tg => C.closTagType tg.tagtype) ∧ tgs.all (checkTag C) = true := by
  intro tgs
  induction tgs with
  | nil =>
      intro jts _ hlen _
      cases jts with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs => exact absurd hlen (by simp)
  | cons tg tgs ih =>
      intro jts hfrag hlen hall
      cases jts with
      | nil => exact absurd hlen (by simp)
      | cons jt jts =>
          simp only [List.all_cons, Bool.and_eq_true] at hfrag
          have hhead := hall 0 tg jt rfl rfl
          obtain ⟨hb, hck⟩ := ih jts hfrag.2 (by simpa using hlen)
            (fun i x y hx hy => hall (i + 1) x y (by simpa using hx) (by simpa using hy))
          have hjt : jt = C.closTagType tg.tagtype := by cases hhead with | mk _ => rfl
          refine ⟨by rw [List.map_cons, ← hb, hjt], ?_⟩
          simp only [List.all_cons, Bool.and_eq_true]
          exact ⟨checkTag_complete hfrag.1 hhead, hck⟩

/-- `Import_ok` determines the imported external types and discharges the import
check. -/
theorem imports_complete {C : Context} : ∀ (is : List Import) (xts : List ExternType),
    is.all Import.frag = true → is.length = xts.length → SeqAll₂ (Import_ok C) is xts →
    xts = is.map (fun i => C.closExternType i.externtype) ∧
      is.all (fun i => checkExternType C i.externtype) = true := by
  intro is
  induction is with
  | nil =>
      intro xts _ hlen _
      cases xts with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs => exact absurd hlen (by simp)
  | cons i is ih =>
      intro xts hfrag hlen hall
      cases xts with
      | nil => exact absurd hlen (by simp)
      | cons xt xts =>
          simp only [List.all_cons, Bool.and_eq_true] at hfrag
          have hhead := hall 0 i xt rfl rfl
          obtain ⟨hb, hck⟩ := ih xts hfrag.2 (by simpa using hlen)
            (fun j x y hx hy => hall (j + 1) x y (by simpa using hx) (by simpa using hy))
          have hxt : xt = C.closExternType i.externtype := by cases hhead with | mk _ => rfl
          refine ⟨by rw [List.map_cons, ← hb, hxt], ?_⟩
          simp only [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, hck⟩
          cases hhead with
          | mk hxtok => exact checkExternType_complete hfrag.1 hxtok

/-! ### What the closed import types put into the staged context

`Module_ok` reads `C'.GLOBALS` and the front of `C'.FUNCS` off the CLOSED
external types, so `Context.frag C'` is a statement about
`$clos_externtype(C, xt)` and not about `xt`.  These are the two components
`Context.frag` constrains. -/

/-- `$clos_externtype` fixes a `globaltype` of the fragment, so every imported
global the checker admits is one the instruction fragment can read. -/
theorem globals_closExternType_nv (C : Context) : ∀ (is : List Import),
    is.all Import.frag = true →
    (ExternType.globals (is.map (fun i => C.closExternType i.externtype))).all
      (fun gt => ValType.nv gt.valtype) = true := by
  intro is
  induction is with
  | nil => intro _; rfl
  | cons i is ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      have h1 : ExternType.frag i.externtype = true := h.1
      have hrest := ih h.2
      rw [List.map_cons]
      cases hxt : i.externtype with
      | global gt =>
          rw [hxt] at h1
          have hnv : ValType.nv gt.valtype = true := h1
          show (ExternType.globals (ExternType.global (substAllGlobalType gt C.closTypes) ::
            is.map (fun i => C.closExternType i.externtype))).all _ = true
          rw [ExternType.globals]
          simp only [List.all_cons, Bool.and_eq_true, hrest, and_true]
          show ValType.nv (substValType gt.valtype (idxVars C.closTypes.length) C.closTypes) = true
          rw [substValType_nv hnv]
          exact hnv
      | tag jt =>
          show (ExternType.globals (ExternType.tag _ :: _)).all _ = true
          exact hrest
      | mem mt =>
          show (ExternType.globals (ExternType.mem _ :: _)).all _ = true
          exact hrest
      | table tt =>
          show (ExternType.globals (ExternType.table _ :: _)).all _ = true
          exact hrest
      | func tu =>
          show (ExternType.globals (ExternType.func _ :: _)).all _ = true
          exact hrest

/-- **EVERY `deftype` `$funcsxt` READS OUT OF THE CLOSED IMPORT TYPES IS ONE OF
`$clos_deftypes(C.TYPES)`.**  An import of the fragment writes its function type
as a type index, and `$clos_externtype` replaces that index by an entry of the
closed type section or leaves it alone --- and `$funcsxt` is undefined in the
second case, which is what makes the premise `$funcsxt(xt_I*) = dt_I*` carry the
information. -/
theorem funcsXt_closExternType_mem (C : Context) : ∀ (is : List Import) (dts : List DefType),
    is.all Import.frag = true →
    funcsXt (is.map (fun i => C.closExternType i.externtype)) = some dts →
    ∀ dt ∈ dts, TypeUse.defd dt ∈ C.closTypes := by
  intro is
  induction is with
  | nil =>
      intro dts _ hfx dt hdt
      have : dts = [] := by
        have h' : (some [] : Option (List DefType)) = some dts := hfx
        injection h' with h'; exact h'.symm
      subst this; simp at hdt
  | cons i is ih =>
      intro dts h hfx dt hdt
      simp only [List.all_cons, Bool.and_eq_true] at h
      have h1 : ExternType.frag i.externtype = true := h.1
      rw [List.map_cons] at hfx
      cases hxt : i.externtype with
      | tag jt =>
          rw [hxt] at hfx
          exact ih dts h.2 hfx dt hdt
      | global gt =>
          rw [hxt] at hfx
          exact ih dts h.2 hfx dt hdt
      | mem mt =>
          rw [hxt] at hfx
          exact ih dts h.2 hfx dt hdt
      | table tt =>
          rw [hxt] at hfx
          exact ih dts h.2 hfx dt hdt
      | func tu =>
          rw [hxt] at h1
          cases tu with
          | recu _ => exact absurd h1 (by simp [ExternType.frag])
          | defd _ => exact absurd h1 (by simp [ExternType.frag])
          | idx x =>
              rw [hxt] at hfx
              have hcl : C.closExternType (TypeUse.idx x |> ExternType.func) =
                  ExternType.func (substTypeVar (.idx x) (idxVars C.closTypes.length)
                    C.closTypes) := rfl
              rw [hcl, funcsXt] at hfx
              cases hasd : asDefType (substTypeVar (.idx x) (idxVars C.closTypes.length)
                  C.closTypes) with
              | none => rw [hasd] at hfx; exact absurd hfx (by cases funcsXt _ <;> simp)
              | some dt₀ =>
                  cases hrest : funcsXt (is.map (fun i => C.closExternType i.externtype)) with
                  | none => rw [hasd, hrest] at hfx; exact absurd hfx (by simp)
                  | some rest =>
                      rw [hasd, hrest] at hfx
                      have hds : dt₀ :: rest = dts := by
                        have h' : (some (dt₀ :: rest) : Option (List DefType)) = some dts := hfx
                        injection h' with h'
                      subst hds
                      have htu : substTypeVar (TypeVar.idx x) (idxVars C.closTypes.length)
                          C.closTypes = TypeUse.defd dt₀ := by
                        cases hs : substTypeVar (TypeVar.idx x) (idxVars C.closTypes.length)
                            C.closTypes with
                        | idx y => rw [hs] at hasd; exact absurd hasd (by simp [asDefType])
                        | recu n => rw [hs] at hasd; exact absurd hasd (by simp [asDefType])
                        | defd d =>
                            rw [hs] at hasd
                            simp only [asDefType, Option.some.injEq] at hasd
                            rw [hasd]
                      rcases List.mem_cons.mp hdt with rfl | hrest'
                      · rcases substTypeVar_mem_or (.idx x) (idxVars C.closTypes.length)
                            C.closTypes with hmem | heq
                        · rwa [htu] at hmem
                        · rw [htu] at heq; exact absurd heq (by simp [TypeVar.toTypeUse])
                      · exact ih rest h.2 hrest dt hrest'

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
  have htb' : m.tables = [] := List.isEmpty_iff.mp htb
  have hel' : m.elems = [] := List.isEmpty_iff.mp hel
  cases h with
  | @mk C C' dts' xtsI xtsE jts gts mts tts dts oks rts nms jtsI gtsI mtsI ttsI dtsI xs
      hty hli hi hlj hj hg hlm hm hlt ht hlf hf hld hd hle he hs hlx hx hdis
      hC hC' hxs hjI hgI hmI htI hdI =>
      -- the two sections outside the decided fragment are empty, and so are the
      -- type sequences the rule pairs with them
      have htts : tts = [] := by
        refine eq_nil_of_length_zero ?_
        rw [htb'] at hlt; simpa using hlt.symm
      have hrts : rts = [] := by
        refine eq_nil_of_length_zero ?_
        rw [hel'] at hle; simpa using hle.symm
      subst htts; subst hrts; subst hxs
      -- the type section
      have hdts' : rollTypes [] m.types = dts' := by
        have hr := types_ok_roll hty
        simpa using hr
      have hdts'all : dts'.all (fun dt => (funcTypeOf dt).isSome) = true := by
        rw [← hdts']
        exact funcTypeOf_rollTypes m.types [] htys rfl
      have hdts'frag : dts'.all DefType.frag = true := by
        rw [← hdts']
        exact defTypeFrag_rollTypes m.types [] htys rfl
      -- the import section: `xt_I*` is what the checker computes
      have htc : Module.typeContext m = { Context.empty with types := dts' } := by
        rw [Module.typeContext, hdts']; rfl
      obtain ⟨hxtsEq, himpck⟩ := imports_complete m.imports xtsI him hli hi
      have hxtsI : Module.importTypes m = xtsI := by
        rw [Module.importTypes, htc, hxtsEq]
      -- the staged contexts, read componentwise
      have hC'types : C'.types = dts' := by rw [hC']
      have hC'funcs : C'.funcs = dtsI ++ dts := by rw [hC']
      have hCtypes : C.types = dts' := by
        rw [hC]; show C'.types ++ [] = dts'; rw [hC'types, List.append_nil]
      have hdtsall : dts.all (fun dt => (funcTypeOf dt).isSome) = true := by
        rw [List.all_eq_true]
        intro dt hdt
        obtain ⟨i, hi', hdti⟩ := List.mem_iff_getElem.mp hdt
        have hi'' : i < m.funcs.length := by omega
        have hlk := funcs_type_lookup hf i m.funcs[i] dt
          (List.getElem?_eq_getElem hi'') (by rw [List.getElem?_eq_getElem hi', hdti])
        rw [hCtypes] at hlk
        exact List.all_eq_true.mp hdts'all dt (List.mem_of_getElem? hlk)
      -- the imported functions are `deftype`s of the fragment, because
      -- `$clos_deftypes` does not move a type section of the fragment
      have hclos : ({ Context.empty with types := dts' } : Context).closTypes =
          dts'.map TypeUse.defd := by
        show (closDefTypes dts').map TypeUse.defd = _
        rw [closDefTypes_frag hdts'frag]
      have hdtsIall : dtsI.all (fun dt => (funcTypeOf dt).isSome) = true := by
        rw [List.all_eq_true]
        intro dt hdt
        have hmem := funcsXt_closExternType_mem { Context.empty with types := dts' }
          m.imports dtsI him (by rw [← hxtsEq]; exact hdI) dt hdt
        rw [hclos] at hmem
        obtain ⟨dt', hdt', heq⟩ := List.mem_map.mp hmem
        injection heq with heq
        rw [← heq]
        exact List.all_eq_true.mp hdts'all dt' hdt'
      have hgtsInv : gtsI.all (fun gt => ValType.nv gt.valtype) = true := by
        rw [hgI, hxtsEq]
        exact globals_closExternType_nv _ m.imports him
      have hC'frag : Context.frag C' = true := by
        have hfn : (dtsI ++ dts).all (fun dt => (funcTypeOf dt).isSome) = true := by
          rw [List.all_append, hdtsIall, hdtsall]; rfl
        rw [hC']
        simp [Context.frag, hdts'all, hgtsInv, hfn]
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
      obtain ⟨hjtsEq, htagck⟩ := tags_complete m.tags jts htg hlj hj
      obtain ⟨hoksEq, hdatack⟩ := datas_complete hCfrag m.datas oks hld hd hdat
      obtain ⟨hnmsEq, hexpck⟩ := exports_complete m.exports nms xtsE hlx.1 hlx.2 hx
      subst hmtsEq; subst hoksEq; subst hnmsEq; subst hjtsEq
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
          { types := rollTypes [] m.types,
            globals := ExternType.globals xtsI,
            funcs := dtsI ++ dts,
            refs := funcidxNonfuncs m.globals m.mems m.tables m.elems } := by
        rw [hC', hdts', ← hgI]
      have hctx : Module.contexts m = some (C', C) := by
        simp only [Module.contexts, hxtsI, hdI, hmapM]
        rw [← hC'eq, hgl, hC, hjI, hmI, htI]
        simp
      -- the start function
      have hstart : (match m.start with
                     | none => true
                     | some s => checkStart C s) = true := by
        cases hst : m.start with
        | none => rfl
        | some s => exact checkStart_complete (hs s hst)
      simp only [validate, hfrag, Bool.true_and, hctx, Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨⟨⟨?_, htagck⟩, hmemck⟩, funcs_complete hCfrag hlf hf hfun⟩, hdatack⟩,
        hstart⟩, hexpck⟩, hdis⟩
      rw [htc]
      exact himpck

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
