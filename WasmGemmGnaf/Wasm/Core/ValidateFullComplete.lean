/-
  Completeness of the executable amended-Core validator on grammar modules.

  This file is intentionally downstream of the source type-graph closure and
  heap-subtype normalization proofs.  It contains only converse/reflection
  proofs for the existing checker and the sole `Module_okA` hierarchy.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeComplete
import WasmGemmGnaf.Wasm.Core.ValidateComplete

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

/-! ## Source-graph certificates in module-validation contexts -/

namespace Context

/-- Ranked source-node membership observes only the stored type sequence. -/
theorem SourceTypeNodeA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) {ht : HeapType} {r : Nat}
    (h : SourceTypeNodeA C ht r) : SourceTypeNodeA D ht r := by
  cases h with
  | idx hlookup => exact .idx (by simpa [← htypes] using hlookup)
  | defd hlookup => exact .defd (by simpa [← htypes] using hlookup)

/-- All four structural source-graph certificates transport across contexts
with the same stored type sequence. -/
theorem SourceTypeGraphOkA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (h : SourceTypeGraphOkA C) :
    SourceTypeGraphOkA D := by
  intro ht r hnode g hg
  have hnodeC := hnode.of_types_eq htypes.symm
  have hgC : g ∈ C.heapSupers ht := by
    rwa [heapSupers_eq_of_types_eq htypes]
  obtain ⟨s, hs, htarget⟩ := h hnodeC g hgC
  exact ⟨s, hs, htarget.of_types_eq htypes⟩

theorem SourceTypesConcreteA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (h : SourceTypesConcreteA C) :
    SourceTypesConcreteA D := by
  intro tu r hnode
  obtain ⟨a, ha, hc⟩ := h (hnode.of_types_eq htypes.symm)
  exact ⟨a, by rwa [typeuseShape_eq_of_types_eq htypes] at ha, hc⟩

theorem SourceTypeShapesOkA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (h : SourceTypeShapesOkA C) :
    SourceTypeShapesOkA D := by
  intro tu r a hnode hshape g hg
  have hnodeC := hnode.of_types_eq htypes.symm
  have hshapeC : C.typeuseShape tu = some a := by
    rwa [typeuseShape_eq_of_types_eq htypes]
  have hgC : g ∈ C.heapSupers (.use tu) := by
    rwa [heapSupers_eq_of_types_eq htypes]
  obtain ⟨tu', rfl, htu'⟩ := h hnodeC hshapeC g hgC
  exact ⟨tu', rfl, by rwa [typeuseShape_eq_of_types_eq htypes] at htu'⟩

theorem SourceTypeClosureOkA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (h : SourceTypeClosureOkA C) :
    SourceTypeClosureOkA D := by
  intro i raw d hlookup heq g hg
  have hlookupC : C.types[i]? = some raw := by simpa [htypes] using hlookup
  have heqC : C.heapEq (.use (.defd raw)) (.use (.defd d)) = true := by
    rwa [heapEq_eq_of_types_eq htypes]
  have hgC : g ∈ C.heapSupers (.use (.defd d)) := by
    rwa [heapSupers_eq_of_types_eq htypes]
  obtain ⟨g', hg', hreach⟩ := h hlookupC heqC g hgC
  refine ⟨g', ?_, ?_⟩
  · rwa [heapSupers_eq_of_types_eq htypes] at hg'
  · rw [← reachDef_eq_of_types_eq htypes]
    rw [← resolveIdx_eq_of_types_eq htypes]
    exact hreach

end Context

/-- The source graph certificate depends only on `TYPES`; all other module
context components are irrelevant to the ranked declared-supertype graph. -/
theorem Types_okA.sourceTypeGraphOkA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    (C : Context) (htypes : C.types = dts) :
    Context.SourceTypeGraphOkA C := by
  exact Context.SourceTypeGraphOkA.of_types_eq
    (by simpa using htypes.symm) (hvalid.sourceTypeGraphOkA hsyn)

/-- Concrete source-type shapes likewise ignore every context component except
the stored type sequence. -/
theorem Types_okA.sourceTypesConcreteA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hvalid : Types_okA Context.empty tds dts)
    (C : Context) (htypes : C.types = dts) :
    Context.SourceTypesConcreteA C := by
  exact Context.SourceTypesConcreteA.of_types_eq
    (by simpa using htypes.symm) hvalid.sourceTypesConcreteA

/-- Declared-super shape preservation is invariant under the non-type fields
of a validation context. -/
theorem Types_okA.sourceTypeShapesOkA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    (C : Context) (htypes : C.types = dts) :
    Context.SourceTypeShapesOkA C := by
  exact Context.SourceTypeShapesOkA.of_types_eq
    (by simpa using htypes.symm) (hvalid.sourceTypeShapesOkA hsyn)

/-- Closure equivalence is invariant under the non-type fields of a validation
context. -/
theorem Types_okA.sourceTypeClosureOkA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    (C : Context) (htypes : C.types = dts) :
    Context.SourceTypeClosureOkA C := by
  exact Context.SourceTypeClosureOkA.of_types_eq
    (by simpa using htypes.symm) (hvalid.sourceTypeClosureOkA hsyn)

/-- Source-index heap-subtyping completeness in any module-validation context
with the checked type section. -/
theorem Types_okA.decHeaptypeSubN_complete_of_sourceTypeNodeA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts)
    {root : TypeUse} {r : Nat}
    (hnode : Context.SourceTypeNodeA C (.use root) r)
    {target : HeapType} (hsub : Heaptype_subA C (.use root) target) :
    decHeaptypeSubN C C.subtypeFuel (.use root) target = true := by
  exact Context.decHeaptypeSubN_complete_of_sourceTypeNodeA
    (hvalid.sourceTypeGraphOkA_in_context hsyn C htypes)
    (hvalid.sourceTypesConcreteA_in_context C htypes)
    (hvalid.sourceTypeShapesOkA_in_context hsyn C htypes)
    (hvalid.sourceTypeClosureOkA_in_context hsyn C htypes)
    hnode hsub

/-- Syntactic type uses are source indices, even when the surrounding module
context also contains functions, globals, recursive scratch entries, or other
section components. -/
theorem Types_okA.decHeaptypeSub_complete_of_syn_typeuse_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts)
    {tu : TypeUse} (htuSyn : tu.isSyn = true)
    (htuOk : Typeuse_okA C tu)
    {target : HeapType} (hsub : Heaptype_subA C (.use tu) target) :
    decHeaptypeSubN C C.subtypeFuel (.use tu) target = true := by
  cases tu with
  | idx x =>
      cases htuOk with
      | typeidx hlookup =>
          exact hvalid.decHeaptypeSubN_complete_of_sourceTypeNodeA_in_context
            hsyn htypes (.idx hlookup) hsub
  | recu _ | defd _ => simp [TypeUse.isSyn] at htuSyn

/-! ## Shape normalization for amended semantic heap subtyping -/

/-- A structural certificate assigning a concrete abstract heap shape to a
heap type and to every declared supertype reachable from its unrolling.  This
is proof data for the existing amended relation, not a second validity
relation or validator. -/
inductive GoodHeapShapeA (C : Context) : HeapType → AbsHeapType → Prop where
  | abs (a : AbsHeapType) : GoodHeapShapeA C (.abs a) a
  | use {tu : TypeUse} {fin : Option Final} {sups : TypeUses} {ct : CompType} :
      C.unrollHt (.use tu) = some (.sub fin sups ct) →
      (∀ u ∈ TypeUses.toList sups,
        GoodHeapShapeA C (.use u) ct.absShape) →
      GoodHeapShapeA C (.use tu) ct.absShape

theorem GoodHeapShapeA.unique {C : Context} {ht : HeapType}
    {a b : AbsHeapType} (ha : GoodHeapShapeA C ht a)
    (hb : GoodHeapShapeA C ht b) : a = b := by
  cases ha with
  | abs => cases hb; rfl
  | @use tu fin sups ct hu hs =>
      cases hb with
      | @use _ fin' sups' ct' hu' hs' =>
          rw [hu] at hu'
          injection hu' with h
          cases h
          rfl

theorem GoodHeapShapeA.typeuseShape {C : Context} {tu : TypeUse}
    {a : AbsHeapType} (hnrec : ∀ i : Nat, tu ≠ .recu i)
    (h : GoodHeapShapeA C (.use tu) a) :
    C.typeuseShape tu = some a := by
  cases h with
  | @use _ fin sups ct hu hs =>
      exact Context.typeuseShape_of_unrollHt hu hnrec

/-- Every semantically valid heap type in the context has a structural shape
certificate. -/
def Context.ValidHeapShapesA (C : Context) : Prop :=
  ∀ {ht : HeapType}, Heaptype_okA C ht →
    ∃ a : AbsHeapType, GoodHeapShapeA C ht a

theorem GoodHeapShapeA.of_idx_lookup {C : Context} {x : TypeIdx}
    {dt : DefType} {a : AbsHeapType}
    (hx : C.types[x.val]? = some dt)
    (h : GoodHeapShapeA C (.use (.idx x)) a) :
    GoodHeapShapeA C (.use (.defd dt)) a := by
  cases h with
  | @use _ fin sups ct hu hs =>
      apply GoodHeapShapeA.use (fin := fin) (sups := sups) (ct := ct)
      · simpa [Context.unrollHt, hx] using hu
      · exact hs

theorem GoodHeapShapeA.idx_of_lookup {C : Context} {x : TypeIdx}
    {dt : DefType} {a : AbsHeapType}
    (hx : C.types[x.val]? = some dt)
    (h : GoodHeapShapeA C (.use (.defd dt)) a) :
    GoodHeapShapeA C (.use (.idx x)) a := by
  cases h with
  | @use _ fin sups ct hu hs =>
      apply GoodHeapShapeA.use (fin := fin) (sups := sups) (ct := ct)
      · simpa [Context.unrollHt, hx] using hu
      · exact hs

theorem GoodHeapShapeA.ne_bot_of_use {C : Context} {tu : TypeUse}
    {a : AbsHeapType} (h : GoodHeapShapeA C (.use tu) a) : a ≠ .bot := by
  cases h with
  | @use _ _ _ ct _ _ => cases ct <;> simp [CompType.absShape]

theorem GoodHeapShapeA.eq_abs_bot {C : Context} {ht : HeapType}
    (h : GoodHeapShapeA C ht .bot) : ht = .abs .bot := by
  cases ht with
  | abs a => cases h; rfl
  | use tu => exact False.elim (h.ne_bot_of_use rfl)

/-- The amended semantic heap-subtyping relation preserves the finite abstract
heap lattice whenever its context carries structural shape certificates. -/
theorem Heaptype_subA.goodShape
    {C : Context} {h₁ h₂ : HeapType} (h : Heaptype_subA C h₁ h₂) :
    C.ValidHeapShapesA → ∀ {a b : AbsHeapType},
      GoodHeapShapeA C h₁ a → GoodHeapShapeA C h₂ b →
      decAbsSub a b = true := by
  apply Heaptype_subA.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ => True)
    (motive_14 := fun C h₁ h₂ _ =>
      C.ValidHeapShapesA → ∀ {a b : AbsHeapType},
        GoodHeapShapeA C h₁ a → GoodHeapShapeA C h₂ b →
        decAbsSub a b = true)
    (motive_15 := fun _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ => True)
    (motive_20 := fun _ _ _ _ => True)
    (motive_21 := fun C d₁ d₂ _ =>
      C.ValidHeapShapesA → ∀ {a b : AbsHeapType},
        GoodHeapShapeA C (.use (.defd d₁)) a →
        GoodHeapShapeA C (.use (.defd d₂)) b →
        decAbsSub a b = true)
  all_goals first | (intros <;> trivial) | skip
  case refl =>
      intro D ht henv a b ha hb
      rw [ha.unique hb]
      exact decAbsSub_refl b
  case trans =>
      intro D ht₁ ht₂ mid hok hleft hright ihok ihleft ihrigh
        henv a b ha hb
      obtain ⟨m, hm⟩ := henv hok
      exact decAbsSub_trans
        (ihleft henv ha hm) (ihrigh henv hm hb)
  case eq_any =>
      intro D henv a b ha hb
      cases ha <;> cases hb <;> rfl
  case i31_eq =>
      intro D henv a b ha hb
      cases ha <;> cases hb <;> rfl
  case struct_eq =>
      intro D henv a b ha hb
      cases ha <;> cases hb <;> rfl
  case array_eq =>
      intro D henv a b ha hb
      cases ha <;> cases hb <;> rfl
  case struct =>
      intro D dt fts hexpand henv a b ha hb
      have hs : D.typeuseShape (.defd dt) = some .struct := by
        simpa [Context.typeuseShape] using Context.absShape_eq_of_expand hexpand
      have ha' := ha.typeuseShape (fun i h => by cases h)
      have : a = .struct := Option.some.inj (ha'.symm.trans hs)
      subst a
      cases hb
      rfl
  case array =>
      intro D dt ft hexpand henv a b ha hb
      have hs : D.typeuseShape (.defd dt) = some .array := by
        simpa [Context.typeuseShape] using Context.absShape_eq_of_expand hexpand
      have ha' := ha.typeuseShape (fun i h => by cases h)
      have : a = .array := Option.some.inj (ha'.symm.trans hs)
      subst a
      cases hb
      rfl
  case func =>
      intro D dt dom cod hexpand henv a b ha hb
      have hs : D.typeuseShape (.defd dt) = some .func := by
        simpa [Context.typeuseShape] using Context.absShape_eq_of_expand hexpand
      have ha' := ha.typeuseShape (fun i h => by cases h)
      have : a = .func := Option.some.inj (ha'.symm.trans hs)
      subst a
      cases hb
      rfl
  case def_ =>
      intro D d₁ d₂ hd ihd henv a b ha hb
      exact ihd henv ha hb
  case typeidx_l =>
      intro D x dt ht hx hs ihs henv a b ha hb
      exact ihs henv (ha.of_idx_lookup hx) hb
  case typeidx_r =>
      intro D ht x dt hx hs ihs henv a b ha hb
      exact ihs henv ha (hb.of_idx_lookup hx)
  case rec_ =>
      intro D i j fin sups ct tu hrec hget henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt, hrec] at hu
          have heq : SubType.sub fin sups ct =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with hfin hsups hct
          subst fin' sups' ct'
          have hmember : tu ∈ TypeUses.toList sups := List.mem_of_getElem? hget
          have hab := (hall tu hmember).unique hb
          rw [hab]
          exact decAbsSub_refl b
  case rec_struct =>
      intro D i fin sups fts hrec henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt, hrec] at hu
          have heq : SubType.sub fin sups (.struct fts) =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with _ _ hct
          subst ct'
          cases hb
          rfl
  case rec_array =>
      intro D i fin sups ft hrec henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt, hrec] at hu
          have heq : SubType.sub fin sups (.array ft) =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with _ _ hct
          subst ct'
          cases hb
          rfl
  case rec_func =>
      intro D i fin sups dom cod hrec henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt, hrec] at hu
          have heq : SubType.sub fin sups (.func dom cod) =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with _ _ hct
          subst ct'
          cases hb
          rfl
  case none_ =>
      intro D ht hne hs ihs henv a b ha hb
      have hae : a = .none := ha.unique (GoodHeapShapeA.abs .none)
      subst a
      have hup := ihs henv hb (GoodHeapShapeA.abs .any)
      have hbot : b ≠ .bot := by
        intro he
        subst b
        exact hne hb.eq_abs_bot
      cases b <;> simp_all [decAbsSub]
  case nofunc =>
      intro D ht hne hs ihs henv a b ha hb
      have hae : a = .nofunc := ha.unique (GoodHeapShapeA.abs .nofunc)
      subst a
      have hup := ihs henv hb (GoodHeapShapeA.abs .func)
      have hbot : b ≠ .bot := by
        intro he
        subst b
        exact hne hb.eq_abs_bot
      cases b <;> simp_all [decAbsSub]
  case noexn =>
      intro D ht hne hs ihs henv a b ha hb
      have hae : a = .noexn := ha.unique (GoodHeapShapeA.abs .noexn)
      subst a
      have hup := ihs henv hb (GoodHeapShapeA.abs .exn)
      have hbot : b ≠ .bot := by
        intro he
        subst b
        exact hne hb.eq_abs_bot
      cases b <;> simp_all [decAbsSub]
  case noextern =>
      intro D ht hne hs ihs henv a b ha hb
      have hae : a = .noextern := ha.unique (GoodHeapShapeA.abs .noextern)
      subst a
      have hup := ihs henv hb (GoodHeapShapeA.abs .extern)
      have hbot : b ≠ .bot := by
        intro he
        subst b
        exact hne hb.eq_abs_bot
      cases b <;> simp_all [decAbsSub]
  case bot =>
      intro D ht henv a b ha hb
      have hae : a = .bot := ha.unique (GoodHeapShapeA.abs .bot)
      subst a
      cases b <;> rfl
  case refl =>
      intro D d₁ d₂ heq henv a b ha hb
      have hh : D.heapEq (.use (.defd d₁)) (.use (.defd d₂)) = true := by
        simp [Context.heapEq, Context.normHeapType, heq]
      have hs := Context.typeuseShape_eq_of_heapEq hh
      have ha' := ha.typeuseShape (fun i h => by cases h)
      have hb' := hb.typeuseShape (fun i h => by cases h)
      have hab : a = b := Option.some.inj (ha'.symm.trans (hs.trans hb'))
      subst b
      exact decAbsSub_refl a
  case super =>
      intro D d₁ d₂ fin sups ct i tu hunroll hget htail ihtail
        henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt] at hu
          rw [hunroll] at hu
          have heq : SubType.sub fin sups ct =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with hfin hsups hct
          subst fin' sups' ct'
          have hm : _ ∈ TypeUses.toList sups := List.mem_of_getElem? hget
          exact ihtail henv (hall _ hm) hb

end WasmGemmGnaf.Wasm.Core
