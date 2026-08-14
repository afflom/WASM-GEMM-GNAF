/-
  Executable validation of grammar-level Core 3.0 type sections.

  The syntax phase contains only type indices in `typeuse` positions.  The
  recursive-group judgment nevertheless has two declarative presentations:
  the ordinary sequential rules and `_rec2`, which validates a group with its
  relative recursive variables installed.  The checker below decides both
  presentations and routes every type/subtype premise through the corrected
  amended hierarchy.
-/
import WasmGemmGnaf.Wasm.Core.Subtype
import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## Syntax-directed type validity -/

/-- Grammar-level `Heaptype_okA`.  Literal semantic `deftype`s are not binary
syntax and are deliberately rejected here. -/
def checkHeaptypeOkA (C : Context) : HeapType → Bool
  | .abs _ => true
  | .use (.idx x) => (C.types[x.val]?).isSome
  | .use (.recu i) => (C.recs[i]?).isSome
  | .use (.defd _) => false

def checkReftypeOkA (C : Context) : RefType → Bool
  | .ref _ ht => checkHeaptypeOkA C ht

def checkValtypeOkA (C : Context) : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref rt => checkReftypeOkA C rt
  | .bot => true

def checkStoragetypeOkA (C : Context) : StorageType → Bool
  | .val t => checkValtypeOkA C t
  | .pack _ => true

def checkFieldtypeOkA (C : Context) : FieldType → Bool
  | .mk _ zt => checkStoragetypeOkA C zt

def checkComptypeOkA (C : Context) : CompType → Bool
  | .struct fts => (FieldTypes.toList fts).all (checkFieldtypeOkA C)
  | .array ft => checkFieldtypeOkA C ft
  | .func dom cod =>
      (ValTypes.toList dom).all (checkValtypeOkA C) &&
      (ValTypes.toList cod).all (checkValtypeOkA C)

/-! ## Recursive groups -/

/-- Extract the syntax-phase index sequence required by `Subtype_okA`. -/
def TypeUses.toTypeIdxs : TypeUses → Option (List TypeIdx)
  | .nil => some []
  | .cons (.idx x) tus => (TypeUses.toTypeIdxs tus).map (x :: ·)
  | .cons _ _ => none

/-- The ordinary `Subtype_okA` presentation. -/
def checkSubtypeOkA (C : Context) (x : TypeIdx) : SubType → Bool
  | .sub _ .nil ct => checkComptypeOkA C ct
  | .sub _ (.cons (.idx y) .nil) ct =>
      decide (y.val < x.val) && checkComptypeOkA C ct &&
      match C.types[y.val]? with
      | some dt =>
          match unrollDt dt with
          | some (.sub _ sups' ct') =>
              (TypeUses.toTypeIdxs sups').isSome &&
                decComptypeSubN C C.subtypeFuel ct ct'
          | none => false
      | none => false
  | _ => false

/-- The `_rec2` presentation.  Unlike `Subtype_okA`, its supertype may be an
index, a recursive variable, or a semantic defined type. -/
def checkSubtypeOk2A (C : Context) (x : TypeIdx) (i : Nat) : SubType → Bool
  | .sub _ .nil ct => checkComptypeOkA C ct
  | .sub _ (.cons tu .nil) ct =>
      before tu x i && checkHeaptypeOkA C (.use tu) &&
      checkComptypeOkA C ct &&
      match C.unrollHt (.use tu) with
      | some (.sub _ _ ct') => decComptypeSubN C C.subtypeFuel ct ct'
      | none => false
  | _ => false

def checkSubtypeListOk2A (C : Context) : List SubType → TypeIdx → Nat → Bool
  | [], _, _ => true
  | st :: sts, x, i =>
      checkSubtypeOk2A C x i st &&
      checkSubtypeListOk2A C sts (TypeIdx.ofNat (x.val + 1)) (i + 1)

def checkRectypeOk2A (C : Context) (qt : RecType) (x : TypeIdx) (i : Nat) : Bool :=
  match qt with
  | .recr sts => checkSubtypeListOk2A C (SubTypes.toList sts) x i

/-- `Rectype_okA`, following its recursive grammar exactly.  A cons proof may
continue with either another ordinary cons proof or a `_rec2` proof for the
remaining suffix; testing only "all cons" versus "all rec2" would miss that
mixed declarative derivation. -/
def checkRectypeListA (C : Context) : List SubType → TypeIdx → Bool
  | [], _ => true
  | st :: sts, x =>
      (checkSubtypeOkA C x st &&
        checkRectypeListA C sts (TypeIdx.ofNat (x.val + 1))) ||
      checkSubtypeListOk2A (C.withRecs (st :: sts)) (st :: sts) x 0

def checkRectypeOkA (C : Context) (qt : RecType) (x : TypeIdx) : Bool :=
  match qt with
  | .recr sts => checkRectypeListA C (SubTypes.toList sts) x

/-- `Type_okA`; the result list is definitionally `$rolldt`. -/
def checkTypeOkA (C : Context) (td : TypeDef) : Bool :=
  let x := TypeIdx.ofNat C.types.length
  let dts := rollDt x td.rectype
  decide (TypeGroupRangeOk C td) &&
    checkRectypeOkA (Context.append C { types := dts }) td.rectype x

/-- The staged type-section fold. -/
def checkTypesOkA : Context → List TypeDef → Bool
  | _, [] => true
  | C, td :: tds =>
      checkTypeOkA C td &&
      checkTypesOkA (Context.append C
        { types := rollDt (TypeIdx.ofNat C.types.length) td.rectype }) tds

/-- The exact output sequence paired with `checkTypesOkA`. -/
def checkedTypes : Context → List TypeDef → List DefType
  | _, [] => []
  | C, td :: tds =>
      let dts := rollDt (TypeIdx.ofNat C.types.length) td.rectype
      dts ++ checkedTypes (Context.append C { types := dts }) tds

/-! ## Soundness -/

theorem TypeUses.toTypeIdxs_eq {tus : TypeUses} {xs : List TypeIdx}
    (h : TypeUses.toTypeIdxs tus = some xs) :
    tus = TypeUses.ofList (xs.map TypeUse.idx) := by
  cases tus with
  | nil =>
      simp [TypeUses.toTypeIdxs] at h
      subst xs
      rfl
  | cons tu tus =>
      cases tu with
      | idx x =>
          simp only [TypeUses.toTypeIdxs, Option.map_eq_some_iff] at h
          obtain ⟨ys, hys, rfl⟩ := h
          simp only [List.map_cons, TypeUses.ofList]
          exact congrArg (TypeUses.cons (.idx x)) (TypeUses.toTypeIdxs_eq hys)
      | recu _ | defd _ => simp [TypeUses.toTypeIdxs] at h
termination_by TypeUses.length tus
decreasing_by simp_all [TypeUses.length]

@[simp] theorem TypeUses.toTypeIdxs_ofList_idx (xs : List TypeIdx) :
    TypeUses.toTypeIdxs (TypeUses.ofList (xs.map TypeUse.idx)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TypeUses.ofList, TypeUses.toTypeIdxs, ih]

theorem checkHeaptypeOkA_sound {C : Context} {ht : HeapType}
    (h : checkHeaptypeOkA C ht = true) : Heaptype_okA C ht := by
  cases ht with
  | abs _ => exact .abs
  | use tu =>
      cases tu with
      | idx x =>
          simp only [checkHeaptypeOkA] at h
          rcases hx : C.types[x.val]? with _ | dt
          · simp [hx] at h
          · exact .typeuse (.typeidx hx)
      | recu i =>
          simp only [checkHeaptypeOkA] at h
          rcases hi : C.recs[i]? with _ | st
          · simp [hi] at h
          · exact .typeuse (.rec_ hi)
      | defd _ => simp [checkHeaptypeOkA] at h

theorem checkReftypeOkA_sound {C : Context} {rt : RefType}
    (h : checkReftypeOkA C rt = true) : Reftype_okA C rt := by
  cases rt with
  | ref _ ht => exact .mk (checkHeaptypeOkA_sound h)

theorem checkValtypeOkA_sound {C : Context} {t : ValType}
    (h : checkValtypeOkA C t = true) : Valtype_okA C t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref rt => exact .ref (checkReftypeOkA_sound h)
  | bot => exact .bot

theorem checkStoragetypeOkA_sound {C : Context} {zt : StorageType}
    (h : checkStoragetypeOkA C zt = true) : Storagetype_okA C zt := by
  cases zt with
  | val t => exact .val (checkValtypeOkA_sound h)
  | pack _ => exact .pack .mk

theorem checkFieldtypeOkA_sound {C : Context} {ft : FieldType}
    (h : checkFieldtypeOkA C ft = true) : Fieldtype_okA C ft := by
  cases ft with
  | mk _ zt => exact .mk (checkStoragetypeOkA_sound h)

theorem checkComptypeOkA_sound {C : Context} {ct : CompType}
    (h : checkComptypeOkA C ct = true) : Comptype_okA C ct := by
  cases ct with
  | struct fts =>
      exact .struct (fun ft hft =>
        checkFieldtypeOkA_sound (List.all_eq_true.mp h ft hft))
  | array ft => exact .array (checkFieldtypeOkA_sound h)
  | func dom cod =>
      rw [checkComptypeOkA, Bool.and_eq_true] at h
      exact .func
        (.mk (fun t ht => checkValtypeOkA_sound (List.all_eq_true.mp h.1 t ht)))
        (.mk (fun t ht => checkValtypeOkA_sound (List.all_eq_true.mp h.2 t ht)))

theorem checkSubtypeOkA_sound {C : Context} {x : TypeIdx} {st : SubType}
    (h : checkSubtypeOkA C x st = true) : Subtype_okA C st x := by
  cases st with
  | sub fin sups ct =>
      cases sups with
      | nil =>
          exact Subtype_okA.mk (xs := []) (cts' := [])
            (Nat.zero_le 1) rfl
            (by intro n a b ha _; simp only [List.getElem?_nil] at ha; cases ha)
            (checkComptypeOkA_sound h)
            (by intro ct' hct'; nomatch hct')
      | cons tu rest =>
          cases rest with
          | cons _ _ => simp [checkSubtypeOkA] at h
          | nil =>
              cases tu with
              | recu _ | defd _ => simp [checkSubtypeOkA] at h
              | idx y =>
                  simp only [checkSubtypeOkA, Bool.and_eq_true] at h
                  have hyx := h.1.1
                  have hct := h.1.2
                  have htail := h.2
                  split at htail
                  · rename_i dt hdt
                    split at htail
                    · rename_i fin' sups' ct' hu
                      rw [Bool.and_eq_true] at htail
                      have hidxs := htail.1
                      have hsub := htail.2
                      rcases hi : TypeUses.toTypeIdxs sups' with _ | xs'
                      · simp [hi] at hidxs
                      · have hsups := TypeUses.toTypeIdxs_eq hi
                        subst sups'
                        exact Subtype_okA.mk (xs := [y]) (cts' := [ct'])
                          (Nat.le_refl 1) rfl
                          (by
                            intro n a b ha hb
                            cases n with
                            | zero =>
                                simp only [List.getElem?_cons_zero,
                                  Option.some.injEq] at ha hb
                                subst a; subst b
                                exact ⟨of_decide_eq_true hyx, dt, fin', xs', hdt, hu⟩
                            | succ n =>
                                simp only [List.getElem?_cons_succ,
                                  List.getElem?_nil] at ha
                                nomatch ha)
                          (checkComptypeOkA_sound hct)
                          (by
                            intro ct'' hmem
                            simp only [List.mem_singleton] at hmem
                            subst ct''
                            exact decComptypeSubN_sound hsub)
                    · contradiction
                  · contradiction

theorem checkSubtypeOk2A_sound {C : Context} {x : TypeIdx} {i : Nat} {st : SubType}
    (h : checkSubtypeOk2A C x i st = true) : Subtype_ok2A C st x i := by
  cases st with
  | sub fin sups ct =>
      cases sups with
      | nil =>
          exact Subtype_ok2A.mk (cts' := [])
            (Nat.zero_le 1) rfl
            (by intro n a b ha _; exact nomatch ha)
            (by intro tu htu; nomatch htu)
            (checkComptypeOkA_sound h)
            (by intro ct' hct'; nomatch hct')
      | cons tu rest =>
          cases rest with
          | cons _ _ => simp [checkSubtypeOk2A] at h
          | nil =>
              simp only [checkSubtypeOk2A, Bool.and_eq_true] at h
              have hbefore := h.1.1.1
              have htuOk := h.1.1.2
              have hct := h.1.2
              have htail := h.2
              split at htail
              · rename_i fin' sups' ct' hu
                exact Subtype_ok2A.mk (cts' := [ct'])
                  (Nat.le_refl 1) rfl
                  (by
                    intro n a b ha hb
                    cases n with
                    | zero =>
                        simp only [List.getElem?_cons_zero,
                          Option.some.injEq, TypeUses.toList] at ha hb
                        subst a; subst b
                        exact ⟨hbefore, fin', sups', hu⟩
                    | succ n =>
                        simp only [List.getElem?_cons_succ,
                          List.getElem?_nil, TypeUses.toList] at ha
                        nomatch ha)
                  (by
                    intro tu' hmem
                    simp only [TypeUses.toList, List.mem_singleton] at hmem
                    subst tu'
                    have hok := checkHeaptypeOkA_sound htuOk
                    cases hok with
                    | typeuse hok => exact hok)
                  (checkComptypeOkA_sound hct)
                  (by
                    intro ct'' hmem
                    simp only [List.mem_singleton] at hmem
                    subst ct''
                    exact decComptypeSubN_sound htail)
              · contradiction

theorem checkSubtypeListOk2A_sound {C : Context} :
    ∀ {sts : List SubType} {x : TypeIdx} {i : Nat},
      checkSubtypeListOk2A C sts x i = true →
      Rectype_ok2A C (.recr (SubTypes.ofList sts)) x i := by
  intro sts
  induction sts with
  | nil => intro x i _; exact .empty
  | cons st sts ih =>
      intro x i h
      rw [checkSubtypeListOk2A, Bool.and_eq_true] at h
      exact .cons (checkSubtypeOk2A_sound h.1) (ih h.2)

theorem checkRectypeOk2A_sound {C : Context} {qt : RecType} {x : TypeIdx} {i : Nat}
    (h : checkRectypeOk2A C qt x i = true) : Rectype_ok2A C qt x i := by
  cases qt with
  | recr sts =>
      rw [← SubTypes.ofList_toList sts]
      exact checkSubtypeListOk2A_sound h

theorem checkRectypeListA_sound {C : Context} :
    ∀ {sts : List SubType} {x : TypeIdx},
      checkRectypeListA C sts x = true →
      Rectype_okA C (.recr (SubTypes.ofList sts)) x := by
  intro sts
  induction sts with
  | nil => intro x _; exact .empty
  | cons st sts ih =>
      intro x h
      rw [checkRectypeListA, Bool.or_eq_true] at h
      rcases h with hc | hr
      · rw [Bool.and_eq_true] at hc
        exact .cons (checkSubtypeOkA_sound hc.1) (ih hc.2)
      · exact .rec2 (checkSubtypeListOk2A_sound (by simpa using hr))

theorem checkRectypeOkA_sound {C : Context} {qt : RecType} {x : TypeIdx}
    (h : checkRectypeOkA C qt x = true) : Rectype_okA C qt x := by
  cases qt with
  | recr sts =>
      rw [← SubTypes.ofList_toList sts]
      exact checkRectypeListA_sound h

theorem checkTypeOkA_sound {C : Context} {td : TypeDef}
    (h : checkTypeOkA C td = true) :
    Type_okA C td (rollDt (TypeIdx.ofNat C.types.length) td.rectype) := by
  simp only [checkTypeOkA, Bool.and_eq_true, decide_eq_true_eq] at h
  have hrange : TypeGroupRangeOk C td := h.1
  refine .mk hrange ?_ rfl (checkRectypeOkA_sound h.2)
  simp [TypeIdx.ofNat, Nat.mod_eq_of_lt hrange.1]

theorem checkTypesOkA_sound : ∀ (C : Context) (tds : List TypeDef),
    checkTypesOkA C tds = true →
    Types_okA C tds (checkedTypes C tds) := by
  intro C tds
  induction tds generalizing C with
  | nil =>
      intro _
      exact .empty
  | cons td tds ih =>
      intro h
      rw [checkTypesOkA, Bool.and_eq_true] at h
      let dts := rollDt (TypeIdx.ofNat C.types.length) td.rectype
      have htd : Type_okA C td dts := by
        simpa [dts] using checkTypeOkA_sound h.1
      have hrest := ih (Context.append C { types := dts }) h.2
      simpa [checkedTypes, dts] using Types_okA.cons htd hrest

/-! ## Completeness of the syntax-directed validity layer

Subtyping completeness is intentionally not smuggled into these lemmas.  The
only missing implication for recursive type sections is the explicit
`Comptype_subA` decision theorem over a context produced by `Types_okA`. -/

theorem checkHeaptypeOkA_complete {C : Context} {ht : HeapType}
    (hsyn : ht.isSyn = true) (h : Heaptype_okA C ht) :
    checkHeaptypeOkA C ht = true := by
  cases h with
  | abs => rfl
  | typeuse htu =>
      cases htu with
      | typeidx hx => simp [checkHeaptypeOkA, hx]
      | rec_ _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | deftype _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem checkReftypeOkA_complete {C : Context} {rt : RefType}
    (hsyn : rt.isSyn = true) (h : Reftype_okA C rt) :
    checkReftypeOkA C rt = true := by
  cases h with
  | mk hht => exact checkHeaptypeOkA_complete hsyn hht

theorem checkValtypeOkA_complete {C : Context} {t : ValType}
    (hsyn : t.isSyn = true) (h : Valtype_okA C t) :
    checkValtypeOkA C t = true := by
  cases h with
  | num _ => rfl
  | vec _ => rfl
  | ref hrt => exact checkReftypeOkA_complete hsyn hrt
  | bot => simp [ValType.isSyn] at hsyn

theorem checkStoragetypeOkA_complete {C : Context} {zt : StorageType}
    (hsyn : zt.isSyn = true) (h : Storagetype_okA C zt) :
    checkStoragetypeOkA C zt = true := by
  cases h with
  | val ht => exact checkValtypeOkA_complete hsyn ht
  | pack _ => rfl

theorem checkFieldtypeOkA_complete {C : Context} {ft : FieldType}
    (hsyn : ft.isSyn = true) (h : Fieldtype_okA C ft) :
    checkFieldtypeOkA C ft = true := by
  cases h with
  | mk hzt => exact checkStoragetypeOkA_complete hsyn hzt

theorem checkComptypeOkA_complete {C : Context} {ct : CompType}
    (hsyn : ct.isSyn = true) (h : Comptype_okA C ct) :
    checkComptypeOkA C ct = true := by
  cases h with
  | struct hall =>
      exact List.all_eq_true.mpr (fun ft hft =>
        checkFieldtypeOkA_complete
          (List.all_eq_true.mp hsyn ft hft) (hall ft hft))
  | array hft => exact checkFieldtypeOkA_complete hsyn hft
  | func hdom hcod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      rw [checkComptypeOkA, Bool.and_eq_true]
      cases hdom with
      | mk hdom =>
          cases hcod with
          | mk hcod =>
              exact ⟨
                List.all_eq_true.mpr (fun t ht => checkValtypeOkA_complete
                  (List.all_eq_true.mp hsyn.1 t ht) (hdom t ht)),
                List.all_eq_true.mpr (fun t ht => checkValtypeOkA_complete
                  (List.all_eq_true.mp hsyn.2 t ht) (hcod t ht))⟩

/-! ## Exact recursive-subtype residual

The two constructors below are now complete modulo one, and only one,
context-sensitive premise: completeness of the heap-type walk in the context
where the composite subtype is checked.  `Subtype.lean` already propagates
that premise through every outer subtype relation. -/

theorem checkSubtypeOkA_complete_of_heap {C : Context} {x : TypeIdx} {st : SubType}
    (hsyn : st.isSyn = true)
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (h : Subtype_okA C st x) : checkSubtypeOkA C x st = true := by
  cases h with
  | mk hlen hlen₂ hall hok hsub =>
      rename_i fin xs ct cts'
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      cases xs with
      | nil =>
          simpa [checkSubtypeOkA, TypeUses.ofList] using
            checkComptypeOkA_complete hsyn.2 hok
      | cons y ys =>
          cases ys with
          | nil =>
              cases cts' with
              | nil => simp [SeqLen₂] at hlen₂
              | cons ct' rest =>
                  cases rest with
                  | cons _ _ => simp [SeqLen₂] at hlen₂
                  | nil =>
                      have hp := hall 0 y ct' rfl rfl
                      obtain ⟨hlt, dt, fin', xs', hlookup, hunroll⟩ := hp
                      have hs : Comptype_subA C ct ct' := hsub ct' (by simp)
                      simp [checkSubtypeOkA, TypeUses.ofList, hlookup, hunroll,
                        hlt, checkComptypeOkA_complete hsyn.2 hok,
                        TypeUses.toTypeIdxs_ofList_idx,
                        decComptypeSubN_complete_of_heap hheap hs]
          | cons _ _ =>
              simp only [List.length_cons] at hlen
              omega

theorem checkSubtypeOk2A_complete_of_heap {C : Context} {x : TypeIdx} {i : Nat}
    {st : SubType} (hsyn : st.isSyn = true)
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (h : Subtype_ok2A C st x i) : checkSubtypeOk2A C x i st = true := by
  cases h with
  | mk hlen hlen₂ hall htuOk hok hsub =>
      rename_i fin sups ct cts'
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      cases sups with
      | nil =>
          simpa [checkSubtypeOk2A] using checkComptypeOkA_complete hsyn.2 hok
      | cons tu rest =>
          cases rest with
          | nil =>
              cases cts' with
              | nil => simp [SeqLen₂, TypeUses.toList] at hlen₂
              | cons ct' cts =>
                  cases cts with
                  | cons _ _ => simp [SeqLen₂, TypeUses.toList] at hlen₂
                  | nil =>
                      obtain ⟨hbefore, fin', sups', hunroll⟩ := hall 0 tu ct' rfl rfl
                      have hmem : tu ∈ TypeUses.toList (.cons tu .nil) := by
                        change tu ∈ [tu]
                        exact List.mem_cons_self
                      have htu : Typeuse_okA C tu := htuOk tu hmem
                      have htuSyn : TypeUse.isSyn tu = true :=
                        List.all_eq_true.mp hsyn.1 tu hmem
                      have htuCheck : checkHeaptypeOkA C (.use tu) = true :=
                        checkHeaptypeOkA_complete htuSyn (.typeuse htu)
                      have hs : Comptype_subA C ct ct' := hsub ct' (by simp)
                      simp [checkSubtypeOk2A, hbefore, htuCheck, hunroll,
                        checkComptypeOkA_complete hsyn.2 hok,
                        decComptypeSubN_complete_of_heap hheap hs]
          | cons _ _ =>
              simp only [TypeUses.toList, List.length_cons] at hlen
              omega

theorem checkRectypeListOk2A_complete_of_heap {C : Context}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true) :
    ∀ (sts : List SubType) {x : TypeIdx} {i : Nat},
      sts.all SubType.isSyn = true →
      Rectype_ok2A C (.recr (SubTypes.ofList sts)) x i →
      checkSubtypeListOk2A C sts x i = true := by
  intro sts
  induction sts with
  | nil => intro x i _ h; cases h; rfl
  | cons st sts ih =>
      intro x i hsyn h
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      cases h with
      | cons hst htail =>
          rw [checkSubtypeListOk2A, Bool.and_eq_true]
          exact ⟨checkSubtypeOk2A_complete_of_heap hsyn.1 hheap hst,
            ih hsyn.2 htail⟩

theorem checkRectypeOk2A_complete_of_heap {C : Context} {qt : RecType}
    {x : TypeIdx} {i : Nat}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hsyn : qt.isSyn = true) (h : Rectype_ok2A C qt x i) :
    checkRectypeOk2A C qt x i = true := by
  cases qt with
  | recr sts =>
      rw [checkRectypeOk2A]
      have hsyn' : (SubTypes.toList sts).all SubType.isSyn = true := by
        simpa [RecType.isSyn] using hsyn
      have h' : Rectype_ok2A C (.recr (SubTypes.ofList (SubTypes.toList sts))) x i := by
        simpa using h
      exact checkRectypeListOk2A_complete_of_heap hheap _ hsyn' h'

theorem checkRectypeListA_complete_of_heap {C : Context}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hrec : ∀ (sts : List SubType) {h₁ h₂ : HeapType},
      Heaptype_subA (C.withRecs sts) h₁ h₂ →
      decHeaptypeSubN (C.withRecs sts) (C.withRecs sts).subtypeFuel h₁ h₂ = true) :
    ∀ (sts : List SubType) {x : TypeIdx}, sts.all SubType.isSyn = true →
      Rectype_okA C (.recr (SubTypes.ofList sts)) x →
      checkRectypeListA C sts x = true := by
  intro sts
  induction sts with
  | nil => intro x _ _; rfl
  | cons st sts ih =>
      intro x hsyn h
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      rw [checkRectypeListA, Bool.or_eq_true]
      cases h with
      | cons hst htail =>
          apply Or.inl
          rw [Bool.and_eq_true]
          exact ⟨checkSubtypeOkA_complete_of_heap hsyn.1 hheap hst,
            ih hsyn.2 htail⟩
      | rec2 h2 =>
          apply Or.inr
          have h2' : Rectype_ok2A (C.withRecs (st :: sts))
              (.recr (SubTypes.ofList (st :: sts))) x 0 := by
            simpa using h2
          exact checkRectypeListOk2A_complete_of_heap (hrec (st :: sts))
            (st :: sts) (by simpa using hsyn) h2'

theorem checkRectypeOkA_complete_of_heap {C : Context} {qt : RecType} {x : TypeIdx}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hrec : ∀ (sts : List SubType) {h₁ h₂ : HeapType},
      Heaptype_subA (C.withRecs sts) h₁ h₂ →
      decHeaptypeSubN (C.withRecs sts) (C.withRecs sts).subtypeFuel h₁ h₂ = true)
    (hsyn : qt.isSyn = true) (h : Rectype_okA C qt x) :
    checkRectypeOkA C qt x = true := by
  cases qt with
  | recr sts =>
      rw [checkRectypeOkA]
      have hsyn' : (SubTypes.toList sts).all SubType.isSyn = true := by
        simpa [RecType.isSyn] using hsyn
      have h' : Rectype_okA C (.recr (SubTypes.ofList (SubTypes.toList sts))) x := by
        simpa using h
      exact checkRectypeListA_complete_of_heap hheap hrec _ hsyn' h'

end Validate
end WasmGemmGnaf.Wasm.Core
