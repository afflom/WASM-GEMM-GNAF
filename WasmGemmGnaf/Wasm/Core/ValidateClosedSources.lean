import WasmGemmGnaf.Wasm.Core.RuntimeTypeBridge
import WasmGemmGnaf.Wasm.Core.ValidateHeapComplete

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

/-!
## Closed substitution environments

Module validation stores the rolled source type vector in `Context.types`, but
the import projection stores `$clos_externtype`, whose defined-type leaves are
members of `closDefTypes Context.types`.  The lemmas below establish the
structural fact needed to connect those two representations: substituting a
type whose free indices are all in range with an environment containing no
free type indices produces a type with no free type indices.

This is provenance only.  It contains no subtype conclusion or decision
result.
-/

def ClosedUsesA (us : List TypeUse) : Prop :=
  ∀ tu ∈ us, TypesBelow 0 (freeTypeUse tu)

theorem ClosedUsesA.map_defd {dts : List DefType}
    (h : ∀ dt ∈ dts, TypesBelow 0 (freeDefType dt)) :
    ClosedUsesA (dts.map TypeUse.defd) := by
  intro tu htu
  obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp htu
  simpa [freeTypeUse] using h dt hdt

mutual

theorem substTypeUse_typesClosed : ∀ (tu : TypeUse) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeTypeUse tu) →
    TypesBelow 0
      (freeTypeUse (substTypeUse tu (idxVars us.length) us))
  | .idx x, us, hbound, hclosed, hfree => by
      have hx : x.val < us.length :=
        hfree x (by simp [freeTypeUse, Free.ofTypeIdx])
      let replacement := us[x.val]
      have hlookup : us[x.val]? = some replacement :=
        List.getElem?_eq_getElem hx
      have hsubst := substTypeVar_idxVars_get hbound hlookup
      simp only [substTypeUse, hsubst]
      exact hclosed replacement (List.mem_of_getElem? hlookup)
  | .recu i, us, _, _, _ => by
      simp [substTypeUse, substTypeVar_recv_idxVars, freeTypeUse,
        Free.empty, TypesBelow]
  | .defd dt, us, hbound, hclosed, hfree => by
      simpa [substTypeUse, freeTypeUse] using
        substDefType_typesClosed dt us hbound hclosed
          (by simpa [freeTypeUse] using hfree)
termination_by tu us _ _ _ => 2 * wtTypeUse tu
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtTypeUse] at *
  all_goals omega

theorem substDefType_typesClosed : ∀ (dt : DefType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeDefType dt) →
    TypesBelow 0
      (freeDefType (substAllDefType dt us))
  | .defd qt i, us, hbound, hclosed, hfree => by
      simpa [substAllDefType, substDefType, freeDefType] using
        substRecType_typesClosed qt us hbound hclosed
          (by simpa [freeDefType] using hfree)
termination_by dt us _ _ _ => 2 * wtDefType dt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtDefType] at *
  all_goals omega

theorem substRecType_typesClosed : ∀ (qt : RecType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeRecType qt) →
    TypesBelow 0
      (freeRecType (substRecType qt (idxVars us.length) us))
  | .recr sts, us, hbound, hclosed, hfree => by
      simp only [substRecType, minus_idxVars]
      simpa [freeRecType] using substSubTypes_typesClosed sts us hbound
        hclosed (by simpa [freeRecType] using hfree)
termination_by qt us _ _ _ => 2 * wtRecType qt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRecType] at *
  all_goals omega

theorem substSubTypes_typesClosed : ∀ (sts : SubTypes) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeSubTypes sts) →
    TypesBelow 0
      (freeSubTypes (substSubTypes sts (idxVars us.length) us))
  | .nil, _, _, _, _ => by
      simp [substSubTypes, freeSubTypes, Free.empty, TypesBelow]
  | .cons st sts, us, hbound, hclosed, hfree => by
      rw [freeSubTypes, typesBelow_append] at hfree
      simp only [substSubTypes, freeSubTypes, typesBelow_append]
      exact ⟨substSubType_typesClosed st us hbound hclosed hfree.1,
        substSubTypes_typesClosed sts us hbound hclosed hfree.2⟩
termination_by sts us _ _ _ => 2 * wtSubTypes sts + 1
decreasing_by
  all_goals subst_vars
  all_goals have := wtSubType_pos st
  all_goals simp only [wtSubTypes] at *
  all_goals omega

theorem substSubType_typesClosed : ∀ (st : SubType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeSubType st) →
    TypesBelow 0
      (freeSubType (substSubType st (idxVars us.length) us))
  | .sub fin sups ct, us, hbound, hclosed, hfree => by
      rw [freeSubType, typesBelow_append] at hfree
      simp only [substSubType, freeSubType, typesBelow_append]
      exact ⟨substTypeUses_typesClosed sups us hbound hclosed hfree.1,
        substCompType_typesClosed ct us hbound hclosed hfree.2⟩
termination_by st us _ _ _ => 2 * wtSubType st
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtSubType] at *
  all_goals omega

theorem substTypeUses_typesClosed : ∀ (tus : TypeUses) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeTypeUses tus) →
    TypesBelow 0
      (freeTypeUses (substTypeUses tus (idxVars us.length) us))
  | .nil, _, _, _, _ => by
      simp [substTypeUses, freeTypeUses, Free.empty, TypesBelow]
  | .cons tu tus, us, hbound, hclosed, hfree => by
      rw [freeTypeUses, typesBelow_append] at hfree
      simp only [substTypeUses, freeTypeUses, typesBelow_append]
      exact ⟨substTypeUse_typesClosed tu us hbound hclosed hfree.1,
        substTypeUses_typesClosed tus us hbound hclosed hfree.2⟩
termination_by tus us _ _ _ => 2 * wtTypeUses tus + 1
decreasing_by
  all_goals subst_vars
  all_goals have := wtTypeUse_pos tu
  all_goals simp only [wtTypeUses] at *
  all_goals omega

theorem substCompType_typesClosed : ∀ (ct : CompType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeCompType ct) →
    TypesBelow 0
      (freeCompType (substCompType ct (idxVars us.length) us))
  | .struct fts, us, hbound, hclosed, hfree => by
      simpa [substCompType, freeCompType] using
        substFieldTypes_typesClosed fts us hbound hclosed hfree
  | .array ft, us, hbound, hclosed, hfree => by
      simpa [substCompType, freeCompType] using
        substFieldType_typesClosed ft us hbound hclosed hfree
  | .func dom cod, us, hbound, hclosed, hfree => by
      rw [freeCompType, typesBelow_append] at hfree
      simp only [substCompType, freeCompType, typesBelow_append]
      exact ⟨substValTypes_typesClosed dom us hbound hclosed hfree.1,
        substValTypes_typesClosed cod us hbound hclosed hfree.2⟩
termination_by ct us _ _ _ => 2 * wtCompType ct
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtCompType] at *
  all_goals omega

theorem substFieldTypes_typesClosed : ∀ (fts : FieldTypes) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeFieldTypes fts) →
    TypesBelow 0
      (freeFieldTypes (substFieldTypes fts (idxVars us.length) us))
  | .nil, _, _, _, _ => by
      simp [substFieldTypes, freeFieldTypes, Free.empty, TypesBelow]
  | .cons ft fts, us, hbound, hclosed, hfree => by
      rw [freeFieldTypes, typesBelow_append] at hfree
      simp only [substFieldTypes, freeFieldTypes, typesBelow_append]
      exact ⟨substFieldType_typesClosed ft us hbound hclosed hfree.1,
        substFieldTypes_typesClosed fts us hbound hclosed hfree.2⟩
termination_by fts us _ _ _ => 2 * wtFieldTypes fts + 1
decreasing_by
  all_goals subst_vars
  all_goals have := wtFieldType_pos ft
  all_goals simp only [wtFieldTypes] at *
  all_goals omega

theorem substFieldType_typesClosed : ∀ (ft : FieldType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeFieldType ft) →
    TypesBelow 0
      (freeFieldType (substFieldType ft (idxVars us.length) us))
  | .mk mutability zt, us, hbound, hclosed, hfree => by
      simpa [substFieldType, freeFieldType] using
        substStorageType_typesClosed zt us hbound hclosed hfree
termination_by ft us _ _ _ => 2 * wtFieldType ft
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtFieldType] at *
  all_goals omega

theorem substStorageType_typesClosed : ∀ (zt : StorageType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeStorageType zt) →
    TypesBelow 0
      (freeStorageType (substStorageType zt (idxVars us.length) us))
  | .pack pt, _, _, _, _ => by
      simp [substStorageType, freeStorageType, Free.empty, TypesBelow]
  | .val t, us, hbound, hclosed, hfree => by
      simpa [substStorageType, freeStorageType] using
        substValType_typesClosed t us hbound hclosed hfree
termination_by zt us _ _ _ => 2 * wtStorageType zt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtStorageType] at *
  all_goals omega

theorem substValTypes_typesClosed : ∀ (ts : ValTypes) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeValTypes ts) →
    TypesBelow 0
      (freeValTypes (substValTypes ts (idxVars us.length) us))
  | .nil, _, _, _, _ => by
      simp [substValTypes, freeValTypes, Free.empty, TypesBelow]
  | .cons t ts, us, hbound, hclosed, hfree => by
      rw [freeValTypes, typesBelow_append] at hfree
      simp only [substValTypes, freeValTypes, typesBelow_append]
      exact ⟨substValType_typesClosed t us hbound hclosed hfree.1,
        substValTypes_typesClosed ts us hbound hclosed hfree.2⟩
termination_by ts us _ _ _ => 2 * wtValTypes ts + 1
decreasing_by
  all_goals subst_vars
  all_goals have := wtValType_pos t
  all_goals simp only [wtValTypes] at *
  all_goals omega

theorem substValType_typesClosed : ∀ (t : ValType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeValType t) →
    TypesBelow 0
      (freeValType (substValType t (idxVars us.length) us))
  | .num nt, _, _, _, _ => by
      simp [substValType, freeValType, Free.empty, TypesBelow]
  | .vec vt, _, _, _, _ => by
      simp [substValType, freeValType, Free.empty, TypesBelow]
  | .bot, _, _, _, _ => by
      simp [substValType, freeValType, Free.empty, TypesBelow]
  | .ref rt, us, hbound, hclosed, hfree => by
      simpa [substValType, freeValType] using
        substRefType_typesClosed rt us hbound hclosed hfree
termination_by t us _ _ _ => 2 * wtValType t
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtValType] at *
  all_goals omega

theorem substRefType_typesClosed : ∀ (rt : RefType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeRefType rt) →
    TypesBelow 0
      (freeRefType (substRefType rt (idxVars us.length) us))
  | .ref nul ht, us, hbound, hclosed, hfree => by
      simpa [substRefType, freeRefType] using
        substHeapType_typesClosed ht us hbound hclosed hfree
termination_by rt us _ _ _ => 2 * wtRefType rt
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtRefType] at *
  all_goals omega

theorem substHeapType_typesClosed : ∀ (ht : HeapType) (us : List TypeUse),
    us.length ≤ 2 ^ 32 → ClosedUsesA us →
    TypesBelow us.length (freeHeapType ht) →
    TypesBelow 0
      (freeHeapType (substHeapType ht (idxVars us.length) us))
  | .abs a, _, _, _, _ => by
      simp [substHeapType, freeHeapType, Free.empty, TypesBelow]
  | .use tu, us, hbound, hclosed, hfree => by
      simpa [substHeapType, freeHeapType] using
        substTypeUse_typesClosed tu us hbound hclosed hfree
termination_by ht us _ _ _ => 2 * wtHeapType ht
decreasing_by
  all_goals subst_vars
  all_goals simp only [wtHeapType] at *
  all_goals omega

end

/-! ## Closed outputs of the type-section closure

The source-order bound proved by type validation is exactly the induction
invariant of `closDefTypesAux`: the next raw entry only refers to entries in
the already-closed accumulator.  Consequently every member appended by the
closure is free of type indices.
-/

theorem closDefTypesAux_typesClosed :
    ∀ (acc rest : List DefType),
      (∀ dt ∈ acc, TypesBelow 0 (freeDefType dt)) →
      (∀ (k : Nat) (dt : DefType), rest[k]? = some dt →
        TypesBelow (acc.length + k) (freeDefType dt)) →
      acc.length + rest.length ≤ 2 ^ 32 →
      ∀ dt ∈ closDefTypesAux acc rest,
        TypesBelow 0 (freeDefType dt)
  | acc, [], hacc, _, _, dt, hdt => by
      simpa [closDefTypesAux] using hacc dt hdt
  | acc, raw :: rest, hacc, hcausal, hbound, dt, hdt => by
      let closed := substAllDefType raw (acc.map TypeUse.defd)
      have haccBound : acc.length ≤ 2 ^ 32 := by
        simp only [List.length_cons] at hbound
        omega
      have hrawFree : TypesBelow acc.length (freeDefType raw) := by
        simpa using hcausal 0 raw (by simp)
      have hclosed : TypesBelow 0 (freeDefType closed) := by
        exact substDefType_typesClosed raw (acc.map TypeUse.defd)
          (by simpa using haccBound) (ClosedUsesA.map_defd hacc)
          (by simpa using hrawFree)
      have hnextAcc : ∀ d ∈ acc ++ [closed],
          TypesBelow 0 (freeDefType d) := by
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hacc d hd
        · have hdc : d = closed := List.mem_singleton.mp hd
          subst d
          exact hclosed
      have hnextCausal : ∀ (k : Nat) (d : DefType),
          rest[k]? = some d →
            TypesBelow ((acc ++ [closed]).length + k)
              (freeDefType d) := by
        intro k d hk
        have hb := hcausal (k + 1) d (by simpa using hk)
        intro x hx
        have hxlt := hb x hx
        simp only [List.length_append, List.length_singleton]
        omega
      have hnextBound : (acc ++ [closed]).length + rest.length ≤
          2 ^ 32 := by
        simp only [List.length_cons] at hbound
        simp only [List.length_append, List.length_singleton]
        omega
      exact closDefTypesAux_typesClosed (acc ++ [closed]) rest
        hnextAcc hnextCausal hnextBound dt (by
          simpa [closDefTypesAux, closed] using hdt)

theorem Types_okA.closDefTypes_typesClosed {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw) :
    ∀ dt ∈ closDefTypes raw, TypesBelow 0 (freeDefType dt) := by
  intro dt hdt
  exact closDefTypesAux_typesClosed [] raw
    (by intro d hd; simp at hd)
    (by simpa using hvalid.storedFreeBefore hsyn)
    (by simpa using hvalid.outputLength_le) dt
    (by simpa [closDefTypes] using hdt)

/-- A type without free type indices is a fixed point of every all-type
substitution environment. -/
theorem substAllDefType_eq_self_of_typesClosed {dt : DefType}
    (hclosed : TypesBelow 0 (freeDefType dt)) (us : List TypeUse) :
    substAllDefType dt us = dt := by
  have hagree : ClosingEnvsAgree (freeDefType dt) us [] := by
    intro x hx
    have hxlt := hclosed x hx
    omega
  have heq := subst_defType_env dt us [] hagree
  simpa [substAllDefType, idxVars, subst_defType_nil] using heq

/-- Closing an already-closed member of a validated type-section closure does
not alter it, even when the validator context retains the raw source vector. -/
theorem Types_okA.closDefType_closed_member {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw)
    {C : Context} {dt : DefType}
    (hdt : dt ∈ closDefTypes raw) : C.closDefType dt = dt := by
  apply substAllDefType_eq_self_of_typesClosed
  exact hvalid.closDefTypes_typesClosed hsyn dt hdt

/-! ## The closed source graph inside a raw validation context -/

namespace Exec

/-- A closure-equivalent literal exposes only edges that re-enter the closed
source graph.  The returned equality is executable `heapEq`, not a stored
subtyping conclusion. -/
def ClosedTypeClosureOkA (C : Context) (dts : List DefType) : Prop :=
  ∀ (i : Nat) (root : DefType), dts[i]? = some root →
    ∀ (d : DefType),
      C.heapEq (.use (.defd root)) (.use (.defd d)) = true →
      ∀ g ∈ C.heapSupers (.use (.defd d)),
        ∃ g' ∈ C.heapSupers (.use (.defd root)),
          C.heapEq g' (C.resolveIdx g) = true

end Exec

theorem Types_okA.closedTypeGraphOkAt_closure {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw) (C : Context) :
    Exec.ClosedTypeGraphOkAt C (closDefTypes raw) := by
  have hgraph := hvalid.closedTypeGraphOk_allocTypes hsyn
  rw [hvalid.allocTypes_eq_closure hsyn] at hgraph
  intro i dt hdt g hg
  exact hgraph i dt hdt g (by
    simpa [Context.heapSupers] using hg)

theorem Types_okA.closedTypesConcreteA_closure {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw) :
    Exec.ClosedTypesConcreteA (closDefTypes raw) := by
  have hconcrete := Exec.Types_okA.closedTypesConcreteA_allocTypes hsyn hvalid
  rwa [hvalid.allocTypes_eq_closure hsyn] at hconcrete

theorem Types_okA.closedTypeShapesOkA_closure {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw) (C : Context) :
    Exec.ClosedTypeShapesOkA C (closDefTypes raw) := by
  have hshapes := Exec.Types_okA.closedTypeShapesOkA_allocTypes hsyn hvalid
  rw [hvalid.allocTypes_eq_closure hsyn] at hshapes
  intro i dt hdt a hshape g hg
  exact hshapes i dt hdt a hshape g (by
    simpa [Context.heapSupers] using hg)

theorem Types_okA.closedTypeClosureOkA_closure {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw)
    {C : Context} (htypes : C.types = raw) :
    Exec.ClosedTypeClosureOkA C (closDefTypes raw) := by
  let closed := closDefTypes raw
  have hgraph := hvalid.closedTypeGraphOkAt_closure hsyn C
  intro i root hroot d heq g hg
  rw [heapSupers_defd_superUses] at hg
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hg
  have hrootMem : root ∈ closed := by
    exact List.mem_of_getElem? hroot
  have hrootFixed : C.closDefType root = root := by
    exact hvalid.closDefType_closed_member hsyn hrootMem
  have hcloseD : C.closDefType d = root := by
    have hc := heapEq_defd heq
    exact hc.symm.trans hrootFixed
  have htargetClosed : closeUse closed target ∈ superUses root := by
    have hm : closeUse closed target ∈
        superUses (substAllDefType d (closed.map TypeUse.defd)) := by
      rw [superUses_substAll]
      exact List.mem_map.mpr ⟨target, htarget, rfl⟩
    have hsubst : substAllDefType d (closed.map TypeUse.defd) = root := by
      simpa [Context.closDefType, Context.closTypes, htypes, closed] using
        hcloseD
    rwa [hsubst] at hm
  have hgClosed : HeapType.use (closeUse closed target) ∈
      C.heapSupers (.use (.defd root)) := by
    rw [heapSupers_defd_superUses]
    exact List.mem_map.mpr ⟨_, htargetClosed, rfl⟩
  obtain ⟨j, super, _, hsuper, hclosedEq⟩ :=
    hgraph i root hroot (.use (closeUse closed target)) hgClosed
  have hsuperMem : super ∈ closed := List.mem_of_getElem? hsuper
  have hsuperFixed : C.closDefType super = super :=
    hvalid.closDefType_closed_member hsyn hsuperMem
  have hclosedUseEq : closeUse closed target = .defd super :=
    HeapType.use.inj hclosedEq
  refine ⟨.use (closeUse closed target), hgClosed, ?_⟩
  cases target with
  | idx x =>
      cases hx : raw[x.val]? with
      | none =>
          have hclose := closeUse_idx_of_none hvalid.outputLength_le hx
          rw [hclose] at hclosedUseEq
          simp at hclosedUseEq
      | some source =>
          have hclose := closeUse_idx_of_lookup
            (hvalid.storedFreeBefore hsyn) hvalid.outputLength_le hx
          rw [hclose] at hclosedUseEq
          have hsuperEq :
              ({ Context.empty with types := raw } : Context).closDefType source =
                super := TypeUse.defd.inj hclosedUseEq
          have hsourceClose : C.closDefType source = super := by
            simpa [Context.closDefType, Context.closTypes, htypes] using
              hsuperEq
          rw [hclose, hsuperEq]
          simp [Context.heapEq, Context.normHeapType, Context.resolveIdx,
            htypes, hx, hsuperFixed, hsourceClose]
  | recu k =>
      have hclose := closeUse_recu (dts := raw) k
      rw [hclose] at hclosedUseEq
      simp at hclosedUseEq
  | defd source =>
      have hclose := closeUse_defd (dts := raw) source
      rw [hclose] at hclosedUseEq
      have hsuperEq :
          ({ Context.empty with types := raw } : Context).closDefType source =
            super := TypeUse.defd.inj hclosedUseEq
      have hsourceClose : C.closDefType source = super := by
        simpa [Context.closDefType, Context.closTypes, htypes] using hsuperEq
      rw [hclose, hsuperEq]
      simp [Context.heapEq, Context.normHeapType, Context.resolveIdx,
        hsuperFixed, hsourceClose]

namespace Exec

/-- A walk in the closed source graph can follow an edge exposed through any
closure-equivalent literal representative. -/
theorem reachDef_follow_closedTypeClosure {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hclosure : ClosedTypeClosureOkA C dts) :
    ∀ (n : Nat) {i : Nat} {root d : DefType} {g : HeapType},
      dts[i]? = some root →
      C.reachDef n (.use (.defd root)) (.use (.defd d)) = true →
      g ∈ C.heapSupers (.use (.defd d)) →
      C.reachDef (n + 1) (.use (.defd root)) (C.resolveIdx g) = true := by
  intro n
  induction n with
  | zero =>
      intro i root d g hroot hreach hg
      rw [Context.reachDef] at hreach
      obtain ⟨g', hg', heq⟩ := hclosure i root hroot d hreach g hg
      rw [Context.reachDef, Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨g', hg', by
        simpa [Context.reachDef] using heq⟩)
  | succ n ih =>
      intro i root d g hroot hreach hg
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hnext
      · obtain ⟨g', hg', hgeq⟩ := hclosure i root hroot d heq g hg
        have hbase : C.reachDef 1 (.use (.defd root))
            (C.resolveIdx g) = true := by
          rw [Context.reachDef, Bool.or_eq_true]
          exact Or.inr (List.any_eq_true.mpr ⟨g', hg', by
            simpa [Context.reachDef] using hgeq⟩)
        exact reachDef_mono (n := 1) (by omega) hbase
      · obtain ⟨next, hnextMem, hnextReach⟩ :=
          List.any_eq_true.mp hnext
        obtain ⟨j, nextDt, _, hnextLookup, hnextEq⟩ :=
          hgraph i root hroot next hnextMem
        subst next
        have htail := ih hnextLookup hnextReach hg
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr
          ⟨.use (.defd nextDt), hnextMem, htail⟩)

/-- Concrete shape is preserved along a walk whose nodes remain in the
validated closed graph, including a closure-equivalent endpoint. -/
theorem reachDef_typeuseShape_of_closedTypeGraph {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts) :
    ∀ (n : Nat) {i : Nat} {root : DefType} {target : TypeUse}
      {a : AbsHeapType},
      dts[i]? = some root → root.absShape = some a →
      C.reachDef n (.use (.defd root)) (.use target) = true →
      C.typeuseShape target = some a := by
  intro n
  induction n with
  | zero =>
      intro i root target a hroot hshape hreach
      rw [Context.reachDef] at hreach
      rw [← Context.typeuseShape_eq_of_heapEq hreach]
      simpa [Context.typeuseShape] using hshape
  | succ n ih =>
      intro i root target a hroot hshape hreach
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hnext
      · rw [← Context.typeuseShape_eq_of_heapEq heq]
        simpa [Context.typeuseShape] using hshape
      · obtain ⟨next, hnextMem, hnextReach⟩ :=
          List.any_eq_true.mp hnext
        obtain ⟨j, nextDt, hnextLookup, hnextEq, hnextShape⟩ :=
          hshapes i root hroot a hshape next hnextMem
        subst next
        exact ih hnextLookup hnextShape hnextReach

/-- The closure index bounds every successful walk starting at that closed
member; no exactness assumption for arbitrary literal endpoints is needed. -/
theorem reachDef_bounded_of_closedTypeGraphOkAt {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    {i : Nat} {root : DefType} (hroot : dts[i]? = some root)
    {target : HeapType} {n : Nat}
    (hreach : C.reachDef n (.use (.defd root)) target = true) :
    C.reachDef (i + 1) (.use (.defd root)) target = true := by
  let rec go (i : Nat) (root : DefType) (hroot : dts[i]? = some root)
      (n : Nat)
      (hreach : C.reachDef n (.use (.defd root)) target = true) :
      C.reachDef (i + 1) (.use (.defd root)) target = true := by
    cases n with
    | zero =>
        rw [Context.reachDef] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inl hreach
    | succ n =>
        rw [Context.reachDef, Bool.or_eq_true] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        rcases hreach with heq | hnext
        · exact Or.inl heq
        · right
          obtain ⟨next, hnextMem, hnextReach⟩ :=
            List.any_eq_true.mp hnext
          obtain ⟨j, nextDt, hji, hnextLookup, hnextEq⟩ :=
            hgraph i root hroot next hnextMem
          subst next
          have hbounded := go j nextDt hnextLookup n hnextReach
          exact List.any_eq_true.mpr ⟨.use (.defd nextDt), hnextMem,
            reachDef_mono (by omega) hbounded⟩
  termination_by i
  exact go i root hroot n hreach

/-- Every member of the decreasing closed graph has the recursive structural
shape certificate consumed by the abstract-left heap checker. -/
theorem goodHeapShape_of_closedTypeGraphOkAt {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts) :
    ∀ (i : Nat) (root : DefType), dts[i]? = some root →
      ∀ (a : AbsHeapType), root.absShape = some a →
        GoodHeapShapeA C (.use (.defd root)) a := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
      intro root hroot a hshape
      cases hu : unrollDt root with
      | none =>
          simp [DefType.absShape, expandDt, hu] at hshape
      | some st =>
          cases st with
          | sub fin sups ct =>
              have hctShape : ct.absShape = a := by
                have hsome : some ct.absShape = some a := by
                  simpa [DefType.absShape, expandDt, hu] using hshape
                exact Option.some.inj hsome
              subst a
              apply GoodHeapShapeA.use (fin := fin) (sups := sups)
                (ct := ct)
              · simpa [Context.unrollHt] using hu
              · intro tu htu
                have hg : .use tu ∈
                    C.heapSupers (.use (.defd root)) := by
                  simp [Context.heapSupers, hu, htu]
                obtain ⟨j, super, hji, hsuper, htuEq⟩ :=
                  hgraph i root hroot (.use tu) hg
                have hsuperShape : super.absShape = some ct.absShape := by
                  obtain ⟨_, super', hsuper', heq, hs⟩ :=
                    hshapes i root hroot ct.absShape hshape (.use tu) hg
                  have hsuperEq : super = super' := by
                    have htuEq' : tu = .defd super := HeapType.use.inj htuEq
                    have heq' : tu = .defd super' := HeapType.use.inj heq
                    exact TypeUse.defd.inj (htuEq'.symm.trans heq')
                  subst super'
                  exact hs
                have hgood := ih j hji super hsuper ct.absShape hsuperShape
                have htuDef : tu = .defd super := HeapType.use.inj htuEq
                simpa [htuDef] using hgood

mutual

/-- Normalization for a declarative derivation starting at a member of the
validated closed source vector while decisions still run in the raw context. -/
theorem ClosedSubtypeWitnessA.of_heaptype_subA_closedSource
    {dts : List DefType} {C : Context}
    (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (hclosure : ClosedTypeClosureOkA C dts) (hrecs : C.recs = [])
    {root : DefType} {i : Nat} (hroot : dts[i]? = some root)
    {shape : AbsHeapType} (hshape : root.absShape = some shape)
    (hconcrete : Context.ConcreteAbsShapeA shape) {h₁ h₂ : HeapType} :
    Heaptype_subA C h₁ h₂ →
      ClosedSubtypeWitnessA C (.defd root) shape h₁ →
      ClosedSubtypeWitnessA C (.defd root) shape h₂
  | .refl, hw => hw
  | .trans _ hs₁ hs₂, hw =>
      ClosedSubtypeWitnessA.of_heaptype_subA_closedSource hgraph hshapes
        hclosure hrecs hroot hshape hconcrete hs₂
        (ClosedSubtypeWitnessA.of_heaptype_subA_closedSource hgraph hshapes
          hclosure hrecs hroot hshape hconcrete hs₁ hw)
  | .eq_any, .abs h => .abs (decAbsSub_trans h (by decide))
  | .i31_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .array_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct hexpand, .use hreach => by
      rename_i dt fts
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_closedTypeGraph hgraph
        hshapes n hroot hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.struct) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .struct := by
        have htarget' : dt.absShape = some shape := by
          simpa [Context.typeuseShape] using htarget
        exact Option.some.inj (htarget'.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .array hexpand, .use hreach => by
      rename_i dt ft
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_closedTypeGraph hgraph
        hshapes n hroot hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.array) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .array := by
        have htarget' : dt.absShape = some shape := by
          simpa [Context.typeuseShape] using htarget
        exact Option.some.inj (htarget'.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .func hexpand, .use hreach => by
      rename_i dt dom cod
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_closedTypeGraph hgraph
        hshapes n hroot hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.func) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .func := by
        have htarget' : dt.absShape = some shape := by
          simpa [Context.typeuseShape] using htarget
        exact Option.some.inj (htarget'.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .def_ hs, hw =>
      ClosedSubtypeWitnessA.of_deftype_subA_closedSource hgraph hshapes
        hclosure hrecs hroot hshape hconcrete hs hw
  | .typeidx_l hx hs, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      apply ClosedSubtypeWitnessA.of_heaptype_subA_closedSource hgraph
        hshapes hclosure hrecs hroot hshape hconcrete hs
      exact .use ⟨n, by simpa [Context.resolveIdx, hx] using hreach⟩
  | .typeidx_r hx hs, hw => by
      have hw' := ClosedSubtypeWitnessA.of_heaptype_subA_closedSource
        hgraph hshapes hclosure hrecs hroot hshape hconcrete hs hw
      cases hw' with
      | use hreach =>
          obtain ⟨n, hreach⟩ := hreach
          exact .use ⟨n, by simpa [Context.resolveIdx, hx] using hreach⟩
  | .rec_ hx _, _ => by rw [hrecs] at hx; simp at hx
  | .rec_struct hx, _ => by rw [hrecs] at hx; simp at hx
  | .rec_array hx, _ => by rw [hrecs] at hx; simp at hx
  | .rec_func hx, _ => by rw [hrecs] at hx; simp at hx
  | .none_ _ _, .abs h => False.elim (hconcrete.not_none h)
  | .nofunc _ _, .abs h => False.elim (hconcrete.not_nofunc h)
  | .noexn _ _, .abs h => False.elim (hconcrete.not_noexn h)
  | .noextern _ _, .abs h => False.elim (hconcrete.not_noextern h)
  | .bot, .abs h => False.elim (hconcrete.not_bot h)
termination_by structural hsub _ => hsub

theorem ClosedSubtypeWitnessA.of_deftype_subA_closedSource
    {dts : List DefType} {C : Context}
    (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (hclosure : ClosedTypeClosureOkA C dts) (hrecs : C.recs = [])
    {root : DefType} {i : Nat} (hroot : dts[i]? = some root)
    {shape : AbsHeapType} (hshape : root.absShape = some shape)
    (hconcrete : Context.ConcreteAbsShapeA shape) {d₁ d₂ : DefType} :
    Deftype_subA C d₁ d₂ →
      ClosedSubtypeWitnessA C (.defd root) shape (.use (.defd d₁)) →
      ClosedSubtypeWitnessA C (.defd root) shape (.use (.defd d₂))
  | .refl heq, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      apply ClosedSubtypeWitnessA.use
      refine ⟨n, Context.reachDef_target_heapEq n hreach ?_⟩
      simp [Context.resolveIdx, Context.heapEq, Context.normHeapType, heq]
  | .super hunroll hget htail, .use hreach => by
      rename_i fin sups ct j tu
      obtain ⟨n, hreach⟩ := hreach
      have hmem : .use tu ∈ C.heapSupers (.use (.defd d₁)) := by
        simp only [Context.heapSupers, hunroll, List.mem_map]
        exact ⟨tu, List.mem_of_getElem? hget, rfl⟩
      have hfollow := reachDef_follow_closedTypeClosure hgraph hclosure n
        hroot (by simpa [Context.resolveIdx] using hreach) hmem
      exact ClosedSubtypeWitnessA.of_heaptype_subA_closedSource hgraph
        hshapes hclosure hrecs hroot hshape hconcrete htail
          (.use ⟨n + 1, hfollow⟩)
termination_by structural hsub _ => hsub

end

/-- A normalized closed-source witness is accepted at the raw context's
structural fuel bound. -/
theorem ClosedSubtypeWitnessA.decides_closedSource {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    {root : DefType} {i : Nat} (hroot : dts[i]? = some root)
    {shape : AbsHeapType} (hshape : root.absShape = some shape)
    (hfuel : i + 1 ≤ C.subtypeFuel) {target : HeapType}
    (hw : ClosedSubtypeWitnessA C (.defd root) shape target) :
    decHeaptypeSubN C C.subtypeFuel (.use (.defd root)) target = true := by
  have hshapeA : C.typeuseShapeA (.defd root) = some shape := by
    simpa [Context.typeuseShapeA] using hshape
  cases hw with
  | abs habs =>
      simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
        hshapeA] using habs
  | use hreach =>
      rename_i targetUse
      obtain ⟨n, hreach⟩ := hreach
      cases targetUse with
      | defd targetDt =>
          have hbounded := reachDef_bounded_of_closedTypeGraphOkAt hgraph
            hroot (by simpa [Context.resolveIdx] using hreach)
          have hfull := reachDef_mono hfuel hbounded
          simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx] using hfull
      | idx x =>
          cases hx : C.types[x.val]? with
          | some targetDt =>
              have hbounded := reachDef_bounded_of_closedTypeGraphOkAt hgraph
                hroot (by simpa [Context.resolveIdx, hx] using hreach)
              have hfull := reachDef_mono hfuel hbounded
              simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, hx]
                using hfull
          | none =>
              have htarget := reachDef_typeuseShape_of_closedTypeGraph hgraph
                hshapes n hroot hshape (by
                  simpa [Context.resolveIdx, hx] using hreach)
              simp [Context.typeuseShape, hx] at htarget
      | recu j =>
          have htarget := reachDef_typeuseShape_of_closedTypeGraph hgraph
            hshapes n hroot hshape (by
              simpa [Context.resolveIdx] using hreach)
          simp [Context.typeuseShape] at htarget

end Exec

/-- Exact amended heap-decision completeness for a literal member of the
closure computed from a validated source type section.  The decision still
runs in the raw validation context; no unrestricted literal endpoint is
admitted. -/
theorem Types_okA.decHeaptypeSubN_complete_of_closed_member
    {types : List TypeDef} {raw : List DefType}
    (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw)
    {C : Context} (htypes : C.types = raw) (hrecs : C.recs = [])
    {i : Nat} {root : DefType}
    (hroot : (closDefTypes raw)[i]? = some root)
    {target : HeapType}
    (hsub : Heaptype_subA C (.use (.defd root)) target) :
    decHeaptypeSubN C C.subtypeFuel (.use (.defd root)) target = true := by
  have hgraph := hvalid.closedTypeGraphOkAt_closure hsyn C
  have hshapes := hvalid.closedTypeShapesOkA_closure hsyn C
  have hclosure := hvalid.closedTypeClosureOkA_closure hsyn htypes
  have hconcrete := hvalid.closedTypesConcreteA_closure hsyn
  obtain ⟨shape, hshape, hshapeConcrete⟩ := hconcrete i root hroot
  have hw := Exec.ClosedSubtypeWitnessA.of_heaptype_subA_closedSource
    hgraph hshapes hclosure hrecs hroot hshape hshapeConcrete hsub
      (Exec.ClosedSubtypeWitnessA.initialDefd
        (C := C) (root := root) (shape := shape))
  have hclosedLength : (closDefTypes raw).length = raw.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] raw
  have hiClosed : i < (closDefTypes raw).length :=
    (List.getElem?_eq_some_iff.mp hroot).1
  have hiRaw : i < raw.length := by simpa [hclosedLength] using hiClosed
  have hfuel : i + 1 ≤ C.subtypeFuel := by
    simp only [Context.subtypeFuel, htypes]
    omega
  exact hw.decides_closedSource hgraph hshapes hroot hshape hfuel

end WasmGemmGnaf.Wasm.Core
