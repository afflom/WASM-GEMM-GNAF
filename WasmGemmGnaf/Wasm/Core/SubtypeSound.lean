/-
  Wasm/Core/SubtypeSound.lean --- facts needed to complete the amended Core
  subtype decision procedure.

  `Subtype.lean` proves every positive answer sound.  This file deliberately
  contains no `HeapComplete` assumption and no conditional completeness result:
  such a hypothesis merely renamed the missing theorem and could not close
  validation.  The executable and declarative sides now both expose the
  corrected bottom hierarchy from `Validation/SubtypingAmended.lean`.

  The remaining completeness argument is context-sensitive.  A type-use walk
  may cross a declared supertype only through a well-formed intermediate in
  `Heaptype_subA/trans`; proving that such a walk preserves its composite-type
  family requires carrying the type-section well-formedness derivation.  That
  certificate must be produced by the full type-section checker and consumed
  by instruction/module completeness.  It is not represented here by an
  assumption.
-/
import WasmGemmGnaf.Wasm.Core.ValidateTypes

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## The finite amended abstract hierarchy -/

/-- The amended abstract hierarchy is reflexive. -/
theorem decAbsSub_refl (a : AbsHeapType) : decAbsSub a a = true := by
  cases a <;> rfl

@[simp] theorem Context.heapEq_refl (C : Context) (ht : HeapType) :
    C.heapEq ht ht = true := by simp [Context.heapEq]

@[simp] theorem Context.reachDef_refl (C : Context) (n : Nat) (ht : HeapType) :
    C.reachDef n ht ht = true := by
  cases n <;> simp [Context.reachDef]

theorem Context.heapEq_symm {C : Context} {h₁ h₂ : HeapType}
    (h : C.heapEq h₁ h₂ = true) : C.heapEq h₂ h₁ = true := by
  unfold Context.heapEq at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  exact h.symm

theorem Context.heapEq_trans {C : Context} {h₁ h₂ h₃ : HeapType}
    (h₁₂ : C.heapEq h₁ h₂ = true)
    (h₂₃ : C.heapEq h₂ h₃ = true) :
    C.heapEq h₁ h₃ = true := by
  unfold Context.heapEq at h₁₂ h₂₃ ⊢
  simp only [decide_eq_true_eq] at h₁₂ h₂₃ ⊢
  exact h₁₂.trans h₂₃

/-- Changing only the target to a `heapEq`-equivalent representative never
changes reachability or consumes additional fuel. -/
theorem Context.reachDef_target_heapEq {C : Context} :
    ∀ (n : Nat) {h h₁ h₂ : HeapType},
      C.reachDef n h h₁ = true → C.heapEq h₁ h₂ = true →
      C.reachDef n h h₂ = true := by
  intro n
  induction n with
  | zero =>
      intro h h₁ h₂ hr he
      rw [Context.reachDef] at hr ⊢
      exact Context.heapEq_trans hr he
  | succ n ih =>
      intro h h₁ h₂ hr he
      rw [Context.reachDef, Bool.or_eq_true] at hr ⊢
      rcases hr with heq | hs
      · exact Or.inl (Context.heapEq_trans heq he)
      · right
        obtain ⟨g, hg, hgr⟩ := List.any_eq_true.mp hs
        exact List.any_eq_true.mpr ⟨g, hg, ih hgr he⟩

/-- The context-bounded heap checker is reflexive.  The only non-immediate
case is an in-range type index: resolving the target exposes the named
`deftype`, and the checker's positive fuel takes the corresponding one-step
edge before closing by `heapEq`. -/
theorem decHeaptypeSub_refl (C : Context) (ht : HeapType) :
    decHeaptypeSubN C C.subtypeFuel ht ht = true := by
  cases ht with
  | abs a => exact decAbsSub_refl a
  | use tu =>
      cases tu with
      | defd dt => simp [decHeaptypeSubN, decHeapSubR, Context.resolveIdx]
      | recu i => simp [decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
          Context.heapEq, Context.normHeapType]
      | idx x =>
          cases hx : C.types[x.val]? with
          | none => simp [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, hx]
          | some dt =>
              simp [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, hx,
                Context.subtypeFuel, Context.reachDef, Context.heapSupers]

theorem decReftypeSub_refl (C : Context) (rt : RefType) :
    decReftypeSubN C C.subtypeFuel rt rt = true := by
  cases rt with
  | ref nul ht =>
      cases nul <;> simp [decReftypeSubN, decHeaptypeSub_refl]

theorem decValtypeSub_refl (C : Context) (t : ValType) :
    decValtypeSubN C C.subtypeFuel t t = true := by
  cases t with
  | num nt => cases nt <;> rfl
  | vec vt => cases vt <;> rfl
  | ref rt => exact decReftypeSub_refl C rt
  | bot => rfl

/-! ## Ranked source type graphs -/

@[simp] theorem SubTypes.length_substSubTypes : (sts : SubTypes) →
    (tvs : List TypeVar) → (tus : List TypeUse) →
    SubTypes.length (substSubTypes sts tvs tus) = SubTypes.length sts
  | .nil, _, _ => rfl
  | .cons _ sts, tvs, tus => by
      simp [substSubTypes, SubTypes.length,
        SubTypes.length_substSubTypes sts tvs tus]

@[simp] theorem SubTypes.toList_length : (sts : SubTypes) →
    (SubTypes.toList sts).length = SubTypes.length sts
  | .nil => rfl
  | .cons _ sts => by
      simp [SubTypes.toList, SubTypes.length, SubTypes.toList_length sts]

@[simp] theorem SubTypes.getElem?_substSubTypes : (sts : SubTypes) →
    (tvs : List TypeVar) → (tus : List TypeUse) → (i : Nat) →
    (SubTypes.toList (substSubTypes sts tvs tus))[i]? =
      (SubTypes.toList sts)[i]?.map (fun st => substSubType st tvs tus)
  | .nil, _, _, _ => by simp [substSubTypes, SubTypes.toList]
  | .cons st sts, tvs, tus, 0 => rfl
  | .cons st sts, tvs, tus, i + 1 => by
      simpa [substSubTypes, SubTypes.toList] using
        SubTypes.getElem?_substSubTypes sts tvs tus i

@[simp] theorem CompType.absShape_substCompType (ct : CompType)
    (tvs : List TypeVar) (tus : List TypeUse) :
    (substCompType ct tvs tus).absShape = ct.absShape := by
  cases ct <;> rfl

/-- Substitution changes references inside a defined type but never the outer
composite family selected by its projection. -/
theorem DefType.absShape_substDefType (dt : DefType)
    (tvs : List TypeVar) (tus : List TypeUse) :
    (substDefType dt tvs tus).absShape = dt.absShape := by
  cases dt with
  | defd qt i =>
      cases qt with
      | recr sts =>
          simp only [DefType.absShape, expandDt, unrollDt, unrollRt,
            substDefType, substRecType]
          simp only [SubTypes.getElem?_substSubTypes]
          cases hst : (SubTypes.toList sts)[i]? with
          | none => simp
          | some st =>
              cases st with
              | sub fin sups ct =>
                  simp [substSubType]

@[simp] theorem DefType.absShape_closDefType (C : Context) (dt : DefType) :
    (C.closDefType dt).absShape = dt.absShape := by
  exact DefType.absShape_substDefType dt _ _

/-- The equivalence test used at the base of a declared-super walk preserves
the concrete composite family. -/
theorem Context.typeuseShape_eq_of_heapEq {C : Context} {tu₁ tu₂ : TypeUse}
    (h : C.heapEq (.use tu₁) (.use tu₂) = true) :
    C.typeuseShape tu₁ = C.typeuseShape tu₂ := by
  unfold Context.heapEq at h
  simp only [decide_eq_true_eq] at h
  cases tu₁ with
  | idx x₁ =>
      cases tu₂ with
      | idx x₂ =>
          simp only [Context.normHeapType, HeapType.use.injEq,
            TypeUse.idx.injEq] at h
          subst x₂
          rfl
      | recu _ | defd _ => simp [Context.normHeapType] at h
  | recu i₁ =>
      cases tu₂ with
      | recu i₂ =>
          simp only [Context.normHeapType, HeapType.use.injEq,
            TypeUse.recu.injEq] at h
          subst i₂
          rfl
      | idx _ | defd _ => simp [Context.normHeapType] at h
  | defd d₁ =>
      cases tu₂ with
      | idx _ | recu _ => simp [Context.normHeapType] at h
      | defd d₂ =>
          simp only [Context.normHeapType, HeapType.use.injEq,
            TypeUse.defd.injEq] at h
          simp only [Context.typeuseShape]
          rw [← DefType.absShape_closDefType C d₁,
            ← DefType.absShape_closDefType C d₂, h]

/-- Amended defined-type validity supplies the expansion shape selected by its
in-range projection. -/
theorem Deftype_okA.expand_exists {C : Context} {dt : DefType}
    (h : Deftype_okA C dt) : ∃ ct : CompType, Expand dt ct := by
  cases h with
  | mk hqt hi =>
      rename_i qt i x
      cases qt with
      | recr sts =>
          unfold RecType.count at hi
          let tvs := (List.range (SubTypes.length sts)).map
            (fun j => TypeVar.recv j)
          let tus := (List.range (SubTypes.length sts)).map
            (fun j => TypeUse.defd (.defd (.recr sts) j))
          let sts' := substSubTypes sts tvs tus
          have hi' : i < (SubTypes.toList sts').length := by
            simpa [sts'] using hi
          let st := (SubTypes.toList sts')[i]
          have hst : (SubTypes.toList sts')[i]? = some st :=
            List.getElem?_eq_getElem hi'
          cases hstEq : st with
          | sub fin sups ct =>
              refine ⟨ct, .mk ?_⟩
              unfold expandDt unrollDt unrollRt
              change (match (SubTypes.toList sts')[i]? with
                | some (.sub _ _ ct') => some ct'
                | none => none) = some ct
              rw [hst]
              rw [hstEq]

namespace Context

/-- A node of the source type graph, with the exact alternating rank used by
`Context.subtypeFuel`.  A source index has odd rank; dereferencing it reaches
the stored defined type at the immediately smaller even rank. -/
inductive SourceTypeNodeA (C : Context) : HeapType → Nat → Prop where
  | idx {x : TypeIdx} {dt : DefType} :
      C.types[x.val]? = some dt →
      SourceTypeNodeA C (.use (.idx x)) (2 * x.val + 1)
  | defd {i : Nat} {dt : DefType} :
      C.types[i]? = some dt →
      SourceTypeNodeA C (.use (.defd dt)) (2 * i)

/-- Every executable declared-super edge out of a source node strictly lowers
its alternating index/defined-type rank.  This is structural graph data, not a
stored subtype-completeness proposition. -/
def SourceTypeGraphOkA (C : Context) : Prop :=
  ∀ {h : HeapType} {r : Nat}, SourceTypeNodeA C h r →
    ∀ g ∈ C.heapSupers h,
      ∃ s : Nat, s < r ∧ SourceTypeNodeA C g s

/-- The three expansion families that a stored source-defined type can have. -/
def ConcreteAbsShapeA (a : AbsHeapType) : Prop :=
  a = .struct ∨ a = .array ∨ a = .func

/-- Every ranked source node expands to one of the concrete composite
families.  This is the exact structural fact consumed by normalization; it
does not assert a checker-completeness theorem or require re-validating a
rolled semantic `deftype` as source syntax. -/
def SourceTypesConcreteA (C : Context) : Prop :=
  ∀ {tu : TypeUse} {r : Nat}, SourceTypeNodeA C (.use tu) r →
    ∃ a : AbsHeapType,
      C.typeuseShape tu = some a ∧ ConcreteAbsShapeA a

/-- Declared-super edges preserve the outer concrete composite family of a
ranked source node. -/
def SourceTypeShapesOkA (C : Context) : Prop :=
  ∀ {tu : TypeUse} {r : Nat} {a : AbsHeapType},
    SourceTypeNodeA C (.use tu) r → C.typeuseShape tu = some a →
    ∀ g ∈ C.heapSupers (.use tu),
      ∃ tu' : TypeUse, g = .use tu' ∧ C.typeuseShape tu' = some a

/-- A declared-super edge exposed by a closure-equivalent literal defined
type re-enters the finite source graph after resolving a possible source
index.  Closing a source supertype turns `_IDX x` into its literal defined
type, so direct `heapEq` is deliberately too strong here; one executable
declared-super step is the exact structural correspondence. -/
def SourceTypeClosureOkA (C : Context) : Prop :=
  ∀ {i : Nat} {raw d : DefType}, C.types[i]? = some raw →
    C.heapEq (.use (.defd raw)) (.use (.defd d)) = true →
    ∀ g ∈ C.heapSupers (.use (.defd d)),
      ∃ g' ∈ C.heapSupers (.use (.defd raw)),
        C.reachDef 1 g' (C.resolveIdx g) = true

theorem absShape_eq_of_expand {dt : DefType} {ct : CompType}
    (h : Expand dt ct) : dt.absShape = some ct.absShape := by
  cases h with
  | mk he => simp [DefType.absShape, he]

/-- Every valid ranked source node has one of the three concrete composite
families used by executable heap subtyping. -/
theorem SourceTypeNodeA.shape_exists {C : Context}
    (hconcrete : SourceTypesConcreteA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) :
    ∃ (tu : TypeUse) (a : AbsHeapType),
      h = .use tu ∧ C.typeuseShape tu = some a := by
  cases hnode with
  | idx hlookup =>
      obtain ⟨a, ha, _⟩ := hconcrete (.idx hlookup)
      exact ⟨_, a, rfl, ha⟩
  | defd hlookup =>
      obtain ⟨a, ha, _⟩ := hconcrete (.defd hlookup)
      exact ⟨_, a, rfl, ha⟩

/-- A ranked declared-super walk stays in the source node's concrete family,
including an endpoint accepted through `heapEq` closure equivalence. -/
theorem reachDef_typeuseShape_of_sourceGraphOkA {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hshapes : SourceTypeShapesOkA C) :
    ∀ (n : Nat) {tu : TypeUse} {r : Nat} {a : AbsHeapType}
      {target : TypeUse},
      SourceTypeNodeA C (.use tu) r →
      C.typeuseShape tu = some a →
      C.reachDef n (.use tu) (.use target) = true →
      C.typeuseShape target = some a := by
  intro n
  induction n with
  | zero =>
      intro tu r a target hnode hshape hreach
      rw [Context.reachDef] at hreach
      rw [← Context.typeuseShape_eq_of_heapEq hreach]
      exact hshape
  | succ n ih =>
      intro tu r a target hnode hshape hreach
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hsupers
      · rw [← Context.typeuseShape_eq_of_heapEq heq]
        exact hshape
      · obtain ⟨g, hg, hgreach⟩ := List.any_eq_true.mp hsupers
        obtain ⟨s, _, hgnode⟩ := hgraph hnode g hg
        obtain ⟨tu', rfl, hgshape⟩ := hshapes hnode hshape g hg
        exact ih hgnode hgshape hgreach

/-- A walk through a ranked graph can follow a declared-super edge exposed by
any closure-equivalent literal representative. -/
theorem reachDef_follow_equiv_super {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hclosure : SourceTypeClosureOkA C) :
    ∀ (n : Nat) {h : HeapType} {r : Nat} {d : DefType} {g : HeapType},
      SourceTypeNodeA C h r →
      C.reachDef n h (.use (.defd d)) = true →
      g ∈ C.heapSupers (.use (.defd d)) →
      C.reachDef (n + 2) h (C.resolveIdx g) = true := by
  intro n
  induction n with
  | zero =>
      intro h r d g hnode hreach hg
      rw [Context.reachDef] at hreach
      cases hnode with
      | idx hlookup =>
          simp [Context.heapEq, Context.normHeapType] at hreach
      | defd hlookup =>
          obtain ⟨g', hg', hgreach⟩ := hclosure hlookup hreach g hg
          rw [Context.reachDef, Bool.or_eq_true]
          right
          exact List.any_eq_true.mpr ⟨g', hg', hgreach⟩
  | succ n ih =>
      intro h r d g hnode hreach hg
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hsupers
      · have hbase : C.reachDef 2 h (C.resolveIdx g) = true := by
          cases hnode with
          | idx hlookup =>
              simp [Context.heapEq, Context.normHeapType] at heq
          | defd hlookup =>
              obtain ⟨g', hg', hgreach⟩ := hclosure hlookup heq g hg
              rw [Context.reachDef, Bool.or_eq_true]
              right
              exact List.any_eq_true.mpr ⟨g', hg', hgreach⟩
        exact reachDef_mono (by omega) hbase
      · obtain ⟨next, hnext, hnextReach⟩ := List.any_eq_true.mp hsupers
        obtain ⟨s, _, hnextNode⟩ := hgraph hnode next hnext
        rw [Context.reachDef, Bool.or_eq_true]
        right
        exact List.any_eq_true.mpr ⟨next, hnext,
          ih hnextNode hnextReach hg⟩

/-- A ranked walk that reaches a source index can take the index-to-stored
defined-type edge.  Unlike the literal-defined-type case above, `heapEq` at
an index is syntactic, so no closure transport is needed. -/
theorem reachDef_follow_idx {C : Context}
    (hgraph : SourceTypeGraphOkA C) :
    ∀ (n : Nat) {h : HeapType} {r : Nat} {x : TypeIdx} {d : DefType},
      SourceTypeNodeA C h r →
      C.reachDef n h (.use (.idx x)) = true →
      C.types[x.val]? = some d →
      C.reachDef (n + 1) h (.use (.defd d)) = true := by
  intro n
  induction n with
  | zero =>
      intro h r x d hnode hreach hx
      rw [Context.reachDef] at hreach
      cases hnode with
      | idx hlookup =>
          simp only [Context.heapEq, decide_eq_true_eq, Context.normHeapType,
            HeapType.use.injEq, TypeUse.idx.injEq] at hreach
          subst x
          have : d = _ := Option.some.inj (hx.symm.trans hlookup)
          subst d
          simp [Context.reachDef, Context.heapSupers, hlookup]
      | defd _ =>
          simp [Context.heapEq, Context.normHeapType] at hreach
  | succ n ih =>
      intro h r x d hnode hreach hx
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hsupers
      · have hbase : C.reachDef 1 h (.use (.defd d)) = true := by
          cases hnode with
          | idx hlookup =>
              simp only [Context.heapEq, decide_eq_true_eq,
                Context.normHeapType, HeapType.use.injEq,
                TypeUse.idx.injEq] at heq
              subst x
              have : d = _ := Option.some.inj (hx.symm.trans hlookup)
              subst d
              simp [Context.reachDef, Context.heapSupers, hlookup]
          | defd _ =>
              simp [Context.heapEq, Context.normHeapType] at heq
        exact reachDef_mono (by omega) hbase
      · obtain ⟨next, hnext, hnextReach⟩ := List.any_eq_true.mp hsupers
        obtain ⟨s, _, hnextNode⟩ := hgraph hnode next hnext
        rw [Context.reachDef, Bool.or_eq_true]
        right
        exact List.any_eq_true.mpr ⟨next, hnext,
          ih hnextNode hnextReach hx⟩

/-- Normalize the target of a ranked walk in exactly the way the executable
heap checker normalizes its right endpoint. -/
theorem reachDef_resolveIdx_of_reach {C : Context}
    (hgraph : SourceTypeGraphOkA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) {target : HeapType} {n : Nat}
    (hreach : C.reachDef n h target = true) :
    ∃ m : Nat, C.reachDef m h (C.resolveIdx target) = true := by
  cases target with
  | abs a => exact ⟨n, hreach⟩
  | use tu =>
      cases tu with
      | defd d => exact ⟨n, hreach⟩
      | recu i => exact ⟨n, hreach⟩
      | idx x =>
          cases hx : C.types[x.val]? with
          | none => exact ⟨n, by simpa [Context.resolveIdx, hx] using hreach⟩
          | some d =>
              exact ⟨n + 1, by
                simpa [Context.resolveIdx, hx] using
                  reachDef_follow_idx hgraph n hnode hreach hx⟩

/-- Pointwise form of the source graph obligation.  The index-to-stored-node
half of the alternating graph is automatic; this predicate records only the
declared supertypes of each stored defined type. -/
def DeclaredTypeSupersRankedA (C : Context) : Prop :=
  ∀ (i : Nat) (dt : DefType), C.types[i]? = some dt →
    ∀ g ∈ C.heapSupers (.use (.defd dt)),
      ∃ s : Nat, s < 2 * i ∧ SourceTypeNodeA C g s

/-- A declared type use denotes an earlier node of the source graph. -/
inductive TypeUse.RankedBeforeA (C : Context) (i : Nat) : TypeUse → Prop where
  | idx {x : TypeIdx} {dt : DefType} : x.val < i →
      C.types[x.val]? = some dt → RankedBeforeA C i (.idx x)
  | defd {j : Nat} {dt : DefType} : j < i →
      C.types[j]? = some dt → RankedBeforeA C i (.defd dt)

/-- Unrolling every stored source type exposes only declared supertypes ranked
strictly before that entry. -/
def StoredTypeSupersRankedA (C : Context) : Prop :=
  ∀ (i : Nat) (dt : DefType), C.types[i]? = some dt →
    ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
      unrollDt dt = some (.sub fin sups ct) →
      SeqAll (TypeUse.RankedBeforeA C i) (TypeUses.toList sups)

theorem TypeUse.RankedBeforeA.sourceNode {C : Context} {i : Nat}
    {tu : TypeUse} (h : TypeUse.RankedBeforeA C i tu) :
    ∃ s : Nat, s < 2 * i ∧ SourceTypeNodeA C (.use tu) s := by
  cases h with
  | idx hlt hlookup => exact ⟨2 * _ + 1, by omega, .idx hlookup⟩
  | defd hlt hlookup => exact ⟨2 * _, by omega, .defd hlookup⟩

theorem declaredTypeSupersRankedA_of_storedTypeSupersRankedA {C : Context}
    (hstored : StoredTypeSupersRankedA C) : DeclaredTypeSupersRankedA C := by
  intro i dt hlookup g hg
  rcases hu : unrollDt dt with _ | st
  · simp only [Context.heapSupers, hu] at hg
    simp at hg
  · cases st with
    | sub fin sups ct =>
        simp only [Context.heapSupers, hu, List.mem_map] at hg
        obtain ⟨tu, htu, rfl⟩ := hg
        exact (hstored i dt hlookup hu tu htu).sourceNode

theorem sourceTypeGraphOkA_of_declaredTypeSupersRankedA {C : Context}
    (hdecl : DeclaredTypeSupersRankedA C) : SourceTypeGraphOkA C := by
  intro h r hnode g hg
  cases hnode with
  | idx hlookup =>
      simp only [Context.heapSupers, hlookup, List.mem_singleton] at hg
      subst g
      exact ⟨2 * _, by omega, .defd hlookup⟩
  | defd hlookup => exact hdecl _ _ hlookup g hg

theorem SourceTypeNodeA.rank_lt_fuel {C : Context} {h : HeapType} {r : Nat}
    (hn : SourceTypeNodeA C h r) : r + 1 ≤ C.subtypeFuel := by
  cases hn with
  | idx hlookup =>
      have hi := (List.getElem?_eq_some_iff.mp hlookup).1
      simp only [Context.subtypeFuel]
      omega
  | defd hlookup =>
      have hi := (List.getElem?_eq_some_iff.mp hlookup).1
      simp only [Context.subtypeFuel]
      omega

/-- A successful unbounded walk from a ranked source node can be replayed in
one more step than its rank. -/
theorem reachDef_bounded_of_sourceTypeGraphOkA {C : Context}
    (hgraph : SourceTypeGraphOkA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) {target : HeapType} {n : Nat}
    (hreach : C.reachDef n h target = true) :
    C.reachDef (r + 1) h target = true := by
  let rec go (h : HeapType) (r : Nat) (hnode : SourceTypeNodeA C h r)
      (n : Nat) (hreach : C.reachDef n h target = true) :
      C.reachDef (r + 1) h target = true := by
    cases n with
    | zero =>
        rw [Context.reachDef] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inl hreach
    | succ n =>
        rw [Context.reachDef, Bool.or_eq_true] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        rcases hreach with heq | hsupers
        · exact Or.inl heq
        · right
          obtain ⟨g, hg, hgreach⟩ := List.any_eq_true.mp hsupers
          obtain ⟨s, hsr, hgnode⟩ := hgraph hnode g hg
          have hbounded := go g s hgnode n hgreach
          exact List.any_eq_true.mpr ⟨g, hg,
            reachDef_mono (by omega) hbounded⟩
  termination_by r
  exact go h r hnode n hreach

/-- The context's sole subtype fuel is a uniform bound for every successful
walk whose left endpoint comes from its source type vector. -/
theorem reachDef_sourceTypeFuel_of_graphOkA {C : Context}
    (hgraph : SourceTypeGraphOkA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) {target : HeapType} {n : Nat}
    (hreach : C.reachDef n h target = true) :
    C.reachDef C.subtypeFuel h target = true := by
  exact reachDef_mono hnode.rank_lt_fuel
    (reachDef_bounded_of_sourceTypeGraphOkA hgraph hnode hreach)

/-- The rank theorem in the exact form consumed by the heap decision
procedure when its resolved target is a defined type. -/
theorem decHeaptypeSubN_source_defd_of_reach {C : Context}
    (hgraph : SourceTypeGraphOkA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) {target : DefType} {n : Nat}
    (hreach : C.reachDef n h (.use (.defd target)) = true) :
    decHeaptypeSubN C C.subtypeFuel h (.use (.defd target)) = true := by
  have hb := reachDef_sourceTypeFuel_of_graphOkA hgraph hnode hreach
  cases hnode <;>
    simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx] using hb

/-- Right-hand type indices are resolved before the same ranked walk. -/
theorem decHeaptypeSubN_source_idx_of_reach {C : Context}
    (hgraph : SourceTypeGraphOkA C) {h : HeapType} {r : Nat}
    (hnode : SourceTypeNodeA C h r) {x : TypeIdx} {target : DefType} {n : Nat}
    (hx : C.types[x.val]? = some target)
    (hreach : C.reachDef n h (.use (.defd target)) = true) :
    decHeaptypeSubN C C.subtypeFuel h (.use (.idx x)) = true := by
  have hb := reachDef_sourceTypeFuel_of_graphOkA hgraph hnode hreach
  cases hnode <;>
    simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, hx] using hb

theorem ConcreteAbsShapeA.not_none {a : AbsHeapType}
    (h : ConcreteAbsShapeA a) : decAbsSub a .none ≠ true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ConcreteAbsShapeA.not_nofunc {a : AbsHeapType}
    (h : ConcreteAbsShapeA a) : decAbsSub a .nofunc ≠ true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ConcreteAbsShapeA.not_noexn {a : AbsHeapType}
    (h : ConcreteAbsShapeA a) : decAbsSub a .noexn ≠ true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ConcreteAbsShapeA.not_noextern {a : AbsHeapType}
    (h : ConcreteAbsShapeA a) : decAbsSub a .noextern ≠ true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ConcreteAbsShapeA.not_bot {a : AbsHeapType}
    (h : ConcreteAbsShapeA a) : decAbsSub a .bot ≠ true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem concreteAbsShapeA_of_compType (ct : CompType) :
    ConcreteAbsShapeA ct.absShape := by
  cases ct <;> simp [ConcreteAbsShapeA, CompType.absShape]

theorem SourceTypeNodeA.concreteShape {C : Context}
    (hconcrete : SourceTypesConcreteA C) {root : TypeUse} {r : Nat}
    (hnode : SourceTypeNodeA C (.use root) r) :
    ∃ a : AbsHeapType,
      C.typeuseShape root = some a ∧ ConcreteAbsShapeA a := by
  exact hconcrete hnode

/-- Normal form of a declarative subtype derivation whose leftmost endpoint
is a ranked source-defined type.  A type-use result is a declared-super walk
to the checker's resolved target; an abstract result is a finite-lattice
answer from the source type's concrete family. -/
inductive SourceSubtypeWitnessA (C : Context) (root : TypeUse)
    (shape : AbsHeapType) : HeapType → Prop where
  | use {tu : TypeUse} :
      (∃ n : Nat,
        C.reachDef n (.use root) (C.resolveIdx (.use tu)) = true) →
      SourceSubtypeWitnessA C root shape (.use tu)
  | abs {a : AbsHeapType} : decAbsSub shape a = true →
      SourceSubtypeWitnessA C root shape (.abs a)

theorem SourceSubtypeWitnessA.initial {C : Context}
    (hgraph : SourceTypeGraphOkA C) {root : TypeUse} {r : Nat}
    (hnode : SourceTypeNodeA C (.use root) r) {shape : AbsHeapType} :
    SourceSubtypeWitnessA C root shape (.use root) := by
  exact SourceSubtypeWitnessA.use
    (reachDef_resolveIdx_of_reach hgraph hnode
      (Context.reachDef_refl C 0 (.use root)))

/-- A source normal form is accepted by the executable heap checker at the
context's sole structural fuel bound. -/
theorem SourceSubtypeWitnessA.decides {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hshapes : SourceTypeShapesOkA C)
    {root : TypeUse} {r : Nat} (hnode : SourceTypeNodeA C (.use root) r)
    {shape : AbsHeapType} (hshape : C.typeuseShape root = some shape)
    {target : HeapType} (h : SourceSubtypeWitnessA C root shape target) :
    decHeaptypeSubN C C.subtypeFuel (.use root) target = true := by
  have hshapeA : C.typeuseShapeA root = some shape := by
    cases hnode <;>
      simpa [Context.typeuseShapeA, Context.typeuseShape] using hshape
  cases h with
  | abs habs =>
      simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, hshapeA]
        using habs
  | use hreach =>
      rename_i tu
      obtain ⟨n, hreach⟩ := hreach
      cases tu with
      | defd d =>
          exact decHeaptypeSubN_source_defd_of_reach hgraph hnode hreach
      | idx x =>
          cases hx : C.types[x.val]? with
          | some d =>
              exact decHeaptypeSubN_source_idx_of_reach hgraph hnode hx
                (by simpa [Context.resolveIdx, hx] using hreach)
          | none =>
              have htshape := reachDef_typeuseShape_of_sourceGraphOkA
                hgraph hshapes n hnode hshape
                (by simpa [Context.resolveIdx, hx] using hreach)
              simp [Context.typeuseShape, hx] at htshape
      | recu i =>
          have htshape := reachDef_typeuseShape_of_sourceGraphOkA
            hgraph hshapes n hnode hshape
            (by simpa [Context.resolveIdx] using hreach)
          simp [Context.typeuseShape] at htshape

end Context

/-- The amended abstract hierarchy is transitive. -/
theorem decAbsSub_trans {a b c : AbsHeapType} (h₁ : decAbsSub a b = true)
    (h₂ : decAbsSub b c = true) : decAbsSub a c = true := by
  cases a <;> cases b <;> cases c <;>
    first
      | rfl
      | exact absurd h₁ (by decide)
      | exact absurd h₂ (by decide)

/-- `BOT` is the only abstract heap type below `BOT` in the executable
hierarchy. -/
theorem isBot_of_decAbsSub_to_bot {a : AbsHeapType}
    (h : decAbsSub a .bot = true) : a = .bot := by
  cases a <;> first | rfl | exact absurd h (by decide)

/-! ## The repaired declarative relation cannot re-enter `BOT` -/

/-- If an amended heap-subtyping derivation ends at `BOT`, it started at
`BOT`.  This is the load-bearing fact the four restored side conditions buy:
the transitivity rule cannot recreate the pinned collapse indirectly. -/
theorem source_bot_of_target_bot {C : Context} {h₁ h₂ : HeapType}
    (h : Heaptype_subA C h₁ h₂) (heq : h₂ = .abs .bot) : h₁ = .abs .bot := by
  let rec go {C : Context} {a b : HeapType} (hs : Heaptype_subA C a b) :
      b = .abs .bot → a = .abs .bot :=
    match hs with
    | .refl => fun he => he
    | .trans _ hs₁ hs₂ => fun he => go hs₁ (go hs₂ he)
    | .eq_any => fun he => nomatch he
    | .i31_eq => fun he => nomatch he
    | .struct_eq => fun he => nomatch he
    | .array_eq => fun he => nomatch he
    | .struct _ => fun he => nomatch he
    | .array _ => fun he => nomatch he
    | .func _ => fun he => nomatch he
    | .def_ _ => fun he => nomatch he
    | .typeidx_l _ hs => fun he => nomatch go hs he
    | .typeidx_r _ _ => fun he => nomatch he
    | .rec_ _ _ => fun he => nomatch he
    | .rec_struct _ => fun he => nomatch he
    | .rec_array _ => fun he => nomatch he
    | .rec_func _ => fun he => nomatch he
    | .none_ hne _ => fun he => absurd he hne
    | .nofunc hne _ => fun he => absurd he hne
    | .noexn hne _ => fun he => absurd he hne
    | .noextern hne _ => fun he => absurd he hne
    | .bot => fun _ => rfl
  exact go h heq

/-- The repaired relation does not derive the first collapsing edge
`NONE <: BOT`. -/
theorem not_none_sub_bot (C : Context) :
    ¬ Heaptype_subA C (.abs .none) (.abs .bot) := by
  intro h
  have heq := source_bot_of_target_bot h rfl
  contradiction

/-- Nor does it derive `NOFUNC <: BOT`. -/
theorem not_nofunc_sub_bot (C : Context) :
    ¬ Heaptype_subA C (.abs .nofunc) (.abs .bot) := by
  intro h
  have heq := source_bot_of_target_bot h rfl
  contradiction

/-- Nor does it derive `NOEXN <: BOT`. -/
theorem not_noexn_sub_bot (C : Context) :
    ¬ Heaptype_subA C (.abs .noexn) (.abs .bot) := by
  intro h
  have heq := source_bot_of_target_bot h rfl
  contradiction

/-- Nor does it derive `NOEXTERN <: BOT`. -/
theorem not_noextern_sub_bot (C : Context) :
    ¬ Heaptype_subA C (.abs .noextern) (.abs .bot) := by
  intro h
  have heq := source_bot_of_target_bot h rfl
  contradiction

/-! ## Admissible transitivity above heap types

The source relation makes heap transitivity explicit, while the outer
relations are syntax-directed.  Their transitivity is nevertheless
admissible when the intermediate type is valid, exactly the premise needed by
the heap rule. -/

theorem Reftype_subA.trans {C : Context} {rt₁ rt₂ rt₃ : RefType}
    (hok : Reftype_okA C rt₂) (h₁₂ : Reftype_subA C rt₁ rt₂)
    (h₂₃ : Reftype_subA C rt₂ rt₃) : Reftype_subA C rt₁ rt₃ := by
  cases hok with
  | mk hht =>
      cases h₁₂ <;> cases h₂₃
      · exact .nonnull (.trans hht (by assumption) (by assumption))
      · exact .null (.trans hht (by assumption) (by assumption))
      · exact .null (.trans hht (by assumption) (by assumption))

theorem Valtype_subA.trans {C : Context} {t₁ t₂ t₃ : ValType}
    (hok : Valtype_okA C t₂) (h₁₂ : Valtype_subA C t₁ t₂)
    (h₂₃ : Valtype_subA C t₂ t₃) : Valtype_subA C t₁ t₃ := by
  cases h₁₂ with
  | bot => exact .bot
  | num h₁₂ =>
      cases h₁₂
      cases h₂₃ with
      | num h₂₃ => cases h₂₃; exact .num .mk
  | vec h₁₂ =>
      cases h₁₂
      cases h₂₃ with
      | vec h₂₃ => cases h₂₃; exact .vec .mk
  | ref h₁₂ =>
      cases hok with
      | ref hok =>
          cases h₂₃ with
          | ref h₂₃ => exact .ref (Reftype_subA.trans hok h₁₂ h₂₃)

theorem Resulttype_subA.trans {C : Context} {ts₁ ts₂ ts₃ : List ValType}
    (hok : Resulttype_okA C ts₂) (h₁₂ : Resulttype_subA C ts₁ ts₂)
    (h₂₃ : Resulttype_subA C ts₂ ts₃) : Resulttype_subA C ts₁ ts₃ := by
  cases h₁₂ with
  | mk hlen₁₂ hall₁₂ =>
      cases h₂₃ with
      | mk hlen₂₃ hall₂₃ =>
          cases hok with
          | mk hok =>
              refine .mk (hlen₁₂.trans hlen₂₃) ?_
              intro i t₁ t₃ ht₁ ht₃
              have hi : i < ts₂.length := by
                have hi₁ := (List.getElem?_eq_some_iff.mp ht₁).1
                simpa [SeqLen₂] using (hlen₁₂.symm ▸ hi₁)
              let t₂ := ts₂[i]
              have ht₂ : ts₂[i]? = some t₂ := List.getElem?_eq_getElem hi
              exact Valtype_subA.trans (hok t₂ (List.getElem_mem hi))
                (hall₁₂ i t₁ t₂ ht₁ ht₂)
                (hall₂₃ i t₂ t₃ ht₂ ht₃)

/-! ## Why endpoint validity is not a completeness certificate

`Deftype_subA/super` validates neither the literal supertype node nor the edge
out of that node.  Consequently a valid node can point to a shape-compatible
but invalid literal node, which can in turn point across families.  The module
validator must therefore retain provenance for every reachable node from its
`Types_okA` derivation; validity of the two heap endpoints alone is too weak. -/

private def endpointCounterStruct : DefType :=
  .defd (.recr (.cons
    (.sub (some .final) .nil (.struct .nil)) .nil)) 0

private def endpointCounterBad : DefType :=
  .defd (.recr (.cons
    (.sub (some .final) (.cons (.defd endpointCounterStruct) .nil)
      (.func .nil .nil)) .nil)) 0

private def endpointCounterFunc : DefType :=
  .defd (.recr (.cons
    (.sub (some .final) (.cons (.defd endpointCounterBad) .nil)
      (.func .nil .nil)) .nil)) 0

private theorem emptyResult_okA (C : Context) : Resulttype_ok C [] :=
  .mk (fun t ht => by simp at ht)

private theorem emptyFunc_okA (C : Context) :
    Comptype_ok C (.func .nil .nil) :=
  .func (emptyResult_okA C) (emptyResult_okA C)

private theorem emptyFunc_subA (C : Context) :
    Comptype_sub C (.func .nil .nil) (.func .nil .nil) :=
  .func (.mk rfl (fun _ _ _ h _ => nomatch h))
    (.mk rfl (fun _ _ _ h _ => nomatch h))

private theorem endpointCounterStruct_expand :
    expandDt endpointCounterStruct = some (.struct .nil) := by decide

private theorem endpointCounterBad_unroll :
    unrollDt endpointCounterBad = some
      (.sub (some .final) (.cons (.defd endpointCounterStruct) .nil)
        (.func .nil .nil)) := by decide

private theorem endpointCounterFunc_unroll :
    unrollDt endpointCounterFunc = some
      (.sub (some .final) (.cons (.defd endpointCounterBad) .nil)
        (.func .nil .nil)) := by decide

private theorem endpointCounterFunc_expand :
    expandDt endpointCounterFunc = some (.func .nil .nil) := by decide

private theorem endpointCounterStruct_ok :
    Deftype_ok Context.empty endpointCounterStruct := by
  apply Deftype_ok.mk (x := TypeIdx.ofNat 0)
  · apply Rectype_ok.cons
    · apply Subtype_ok.mk (xs := []) (cts' := [])
      · simp
      · rfl
      · intro i x ct hx _
        simp at hx
      · exact .struct (fun _ hft => nomatch hft)
      · intro ct hct
        nomatch hct
    · exact .empty
  · decide

private theorem endpointCounterFunc_ok :
    Deftype_ok Context.empty endpointCounterFunc := by
  apply Deftype_ok.mk (x := TypeIdx.ofNat 0)
  · apply Rectype_ok.rec2
    apply Rectype_ok2.cons
    · apply Subtype_ok2.mk (cts' := [.func .nil .nil])
      · decide
      · rfl
      · intro i tu ct htu hct
        have hi : i = 0 := by
          cases i with
          | zero => rfl
          | succ i => simp [TypeUses.toList] at htu
        subst i
        have htu' : tu = .defd endpointCounterBad := by
          exact (Option.some.inj htu).symm
        subst tu
        have hct' : ct = .func .nil .nil := by
          exact (Option.some.inj hct).symm
        subst ct
        exact ⟨rfl, some .final,
          (.cons (.defd endpointCounterStruct) .nil), rfl⟩
      · exact emptyFunc_okA _
      · intro ct hct
        have : ct = .func .nil .nil := by simpa using hct
        subst ct
        exact emptyFunc_subA _
    · exact .empty
  · decide

private theorem endpointCounterFunc_sub_struct :
    Heaptype_sub Context.empty (.use (.defd endpointCounterFunc))
      (.abs .struct) := by
  have hbadStruct : Heaptype_sub Context.empty
      (.use (.defd endpointCounterBad))
      (.use (.defd endpointCounterStruct)) := by
    exact .def_ (@Deftype_sub.super Context.empty endpointCounterBad
      endpointCounterStruct (some .final)
      (.cons (.defd endpointCounterStruct) .nil) (.func .nil .nil) 0
      (.defd endpointCounterStruct) endpointCounterBad_unroll rfl .refl)
  have hfuncStruct : Heaptype_sub Context.empty
      (.use (.defd endpointCounterFunc))
      (.use (.defd endpointCounterStruct)) :=
    .def_ (@Deftype_sub.super Context.empty endpointCounterFunc
      endpointCounterStruct (some .final)
      (.cons (.defd endpointCounterBad) .nil) (.func .nil .nil) 0
      (.defd endpointCounterBad) endpointCounterFunc_unroll rfl hbadStruct)
  exact .trans (.typeuse (.deftype endpointCounterStruct_ok)) hfuncStruct
    (.struct (.mk endpointCounterStruct_expand))

/-- Endpoint well-formedness alone does not make the executable heap walk
complete, even if fuel is existentially unbounded. -/
theorem heapDecision_not_complete_of_endpoint_validity :
    ∃ h₁ h₂ : HeapType,
      Heaptype_ok Context.empty h₁ ∧ Heaptype_ok Context.empty h₂ ∧
      Heaptype_sub Context.empty h₁ h₂ ∧
      ∀ n, decHeaptypeSubN Context.empty n h₁ h₂ = false := by
  exact ⟨.use (.defd endpointCounterFunc), .abs .struct,
    .typeuse (.deftype endpointCounterFunc_ok), .abs,
    endpointCounterFunc_sub_struct, fun n => by
      simp [decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
        Context.typeuseShapeA, DefType.absShape, CompType.absShape,
        decAbsSub, endpointCounterFunc_expand]⟩

/-- The pinned missing-premise hierarchy fails executable completeness even
when both endpoints are grammar-level abstract heap types.  Its literal
function intermediate is valid only because pinned `Subtype_ok2` omits the
declared-supertype `Typeuse_ok` premise; the hidden invalid edge then carries
`NOFUNC` across to `STRUCT` through pinned transitivity.  AMD-013 excludes
exactly that intermediate in `Subtype_ok2A`, while this theorem preserves the
kernel counterexample against the untouched authority transcription. -/
theorem heapDecision_not_complete_on_abstract_endpoints :
    Heaptype_ok Context.empty (.abs .nofunc) ∧
    Heaptype_ok Context.empty (.abs .struct) ∧
    Heaptype_sub Context.empty (.abs .nofunc) (.abs .struct) ∧
    ∀ n, decHeaptypeSubN Context.empty n (.abs .nofunc) (.abs .struct) = false := by
  have hfunc : Heaptype_sub Context.empty
      (.use (.defd endpointCounterFunc)) (.abs .func) :=
    .func (.mk endpointCounterFunc_expand)
  have hbottom : Heaptype_sub Context.empty (.abs .nofunc)
      (.use (.defd endpointCounterFunc)) :=
    .nofunc hfunc
  have hmiddle : Heaptype_ok Context.empty
      (.use (.defd endpointCounterFunc)) :=
    .typeuse (.deftype endpointCounterFunc_ok)
  exact ⟨.abs, .abs, .trans hmiddle hbottom endpointCounterFunc_sub_struct,
    fun _ => rfl⟩

/-! ## Executable regression witnesses -/

private def fuelChainType (super : Option Nat) : TypeDef :=
  ⟨.recr (.cons (.sub (some .final)
    (match super with
     | none => .nil
     | some i => .cons (.idx (TypeIdx.ofNat i)) .nil)
    (.func .nil .nil)) .nil)⟩

private def fuelChainTypes : List TypeDef :=
  [fuelChainType none, fuelChainType (some 0), fuelChainType (some 1)]

private def fuelChainDefTypes : List DefType :=
  Validate.checkedTypes Context.empty fuelChainTypes

private def fuelChainContext : Context :=
  { Context.empty with types := fuelChainDefTypes }

/-- A three-group source-valid chain consumes five alternating walk steps
(`_IDX 2`, `defd 2`, `_IDX 1`, `defd 1`, `_IDX 0`, `defd 0`).  The sole
context fuel formula therefore reserves two steps per source type; the old
`|TYPES| + 1` bound rejected this judgment. -/
theorem threeGroupSubtypeFuel_regression :
    Validate.checkTypesOkA Context.empty fuelChainTypes = true ∧
    fuelChainContext.subtypeFuel = 7 ∧
    decHeaptypeSubN fuelChainContext fuelChainContext.subtypeFuel
      (.use (.idx (TypeIdx.ofNat 2)))
      (.use (.idx (TypeIdx.ofNat 0))) = true := by
  decide

/-- The formerly collapsing abstract pair is rejected by computation. -/
example : decAbsSub .none .func = false := rfl

/-- The mirror cross-family pair is rejected too. -/
example : decAbsSub .nofunc .any = false := rfl

/-- The repaired missing-premise edge is rejected. -/
example : decAbsSub .none .bot = false := rfl

/-- Intended internal-family subtyping remains accepted. -/
example : decAbsSub .none .eq = true := rfl

/-- Intended function-family subtyping remains accepted. -/
example : decAbsSub .nofunc .func = true := rfl

/-- The executable full heap checker does not reintroduce the defect in the
empty context. -/
example : decHeaptypeSub Context.empty (.abs .none) (.abs .func) = false := by
  decide

end WasmGemmGnaf.Wasm.Core
