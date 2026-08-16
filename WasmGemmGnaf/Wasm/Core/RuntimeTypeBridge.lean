/-
  Runtime allocation closes the validated source type vector.  This file
  proves that the executable allocator's left fold is exactly the authority
  closure operation, so runtime types retain the causal source graph proved
  by validation.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeComplete
import WasmGemmGnaf.Wasm.Core.InstantiationAmended

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core

private theorem closingEnvsAgree_prefix_runtime {f : Free}
    {pre suffix : List DefType}
    (hbound : pre.length + suffix.length ≤ 2 ^ 32)
    (hfree : TypesBelow pre.length f) :
    ClosingEnvsAgree f (pre.map TypeUse.defd)
      ((pre ++ suffix).map TypeUse.defd) := by
  intro x hx
  have hxlt := hfree x hx
  simpa [List.map_append] using
    (substTypeVar_idxVars_prefix
      (pre := pre.map TypeUse.defd)
      (suffix := suffix.map TypeUse.defd)
      (x := x) (by simpa using hbound) (by simpa using hxlt))

private theorem substAllDefTypes_eq_of_prefix {pre suffix group : List DefType}
    (hbound : pre.length + suffix.length ≤ 2 ^ 32)
    (hfree : ∀ dt ∈ group, TypesBelow pre.length (freeDefType dt)) :
    substAllDefTypes group ((pre ++ suffix).map TypeUse.defd) =
      substAllDefTypes group (pre.map TypeUse.defd) := by
  unfold substAllDefTypes
  apply List.map_congr_left
  intro dt hdt
  exact (subst_defType_env dt _ _
    (closingEnvsAgree_prefix_runtime hbound (hfree dt hdt))).symm

private theorem closDefTypesAux_group_eq
    (pre group : List DefType)
    (hbound : pre.length + group.length ≤ 2 ^ 32)
    (hfree : ∀ dt ∈ group, TypesBelow pre.length (freeDefType dt)) :
    closDefTypesAux pre group =
      pre ++ substAllDefTypes group (pre.map TypeUse.defd) := by
  induction group generalizing pre with
  | nil => simp [closDefTypesAux, substAllDefTypes]
  | cons head tail ih =>
      let closed := substAllDefType head (pre.map TypeUse.defd)
      rw [closDefTypesAux]
      have htailBound : (pre ++ [closed]).length + tail.length ≤
          2 ^ 32 := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢
        omega
      have htailFree : ∀ dt ∈ tail,
          TypesBelow (pre ++ [closed]).length (freeDefType dt) := by
        intro dt hdt x hx
        have hlt := hfree dt (by simp [hdt]) x hx
        simp only [List.length_append, List.length_singleton]
        omega
      rw [ih (pre ++ [closed]) htailBound htailFree]
      have hprefixBound : pre.length + 1 ≤ 2 ^ 32 := by
        simp only [List.length_cons] at hbound
        omega
      have hsubst : substAllDefTypes tail
          ((pre ++ [closed]).map TypeUse.defd) =
          substAllDefTypes tail (pre.map TypeUse.defd) := by
        apply substAllDefTypes_eq_of_prefix
          (pre := pre) (suffix := [closed]) hprefixBound
        intro dt hdt
        exact hfree dt (by simp [hdt])
      rw [hsubst]
      simp [substAllDefTypes, closed, List.append_assoc]

private theorem closDefTypesAux_append (acc left right : List DefType) :
    closDefTypesAux acc (left ++ right) =
      closDefTypesAux (closDefTypesAux acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons head tail ih =>
      rw [List.cons_append]
      simp only [closDefTypesAux]
      exact ih _

private theorem closDefTypes_append (left right : List DefType) :
    closDefTypes (left ++ right) =
      closDefTypesAux (closDefTypes left) right := by
  unfold closDefTypes
  exact closDefTypesAux_append [] left right

private def allocTypesFrom (allocated : List DefType)
    (types : List TypeDef) : List DefType :=
  types.foldl
    (fun dts type =>
      dts ++ substAllDefTypes
        (rollDt (TypeIdx.ofNat dts.length) type.rectype)
        (dts.map TypeUse.defd)) allocated

@[simp] private theorem allocTypesFrom_nil (allocated : List DefType) :
    allocTypesFrom allocated [] = allocated := rfl

@[simp] private theorem allocTypesFrom_cons (allocated : List DefType)
    (type : TypeDef) (types : List TypeDef) :
    allocTypesFrom allocated (type :: types) =
      allocTypesFrom
        (allocated ++ substAllDefTypes
          (rollDt (TypeIdx.ofNat allocated.length) type.rectype)
          (allocated.map TypeUse.defd)) types := rfl

private theorem allocTypesFrom_empty (types : List TypeDef) :
    allocTypesFrom [] types = Exec.allocTypes types := rfl

private theorem Types_okA.allocTypes_eq_closDefTypes {C : Context}
    {types : List TypeDef} {raw : List DefType}
    (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA C types raw) :
    allocTypesFrom (closDefTypes C.types) types =
      closDefTypes (C.types ++ raw) := by
  induction hvalid with
  | empty => simp
  | @cons C type types head tail hhead htail ih =>
      have hsynParts : type.isSyn = true ∧
          types.all TypeDef.isSyn = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsyn
      rw [allocTypesFrom_cons]
      have hprefixLength : (closDefTypes C.types).length = C.types.length := by
        simpa [closDefTypes] using closDefTypesAux_length [] C.types
      obtain ⟨hrange, hbase, hgroup, hrect⟩ := hhead
      rename_i x
      have hbaseLt : C.types.length < 2 ^ 32 := hrange.1
      have hidx : TypeIdx.ofNat (closDefTypes C.types).length =
          TypeIdx.ofNat C.types.length := by rw [hprefixLength]
      have hidxBase : TypeIdx.ofNat C.types.length =
          TypeIdx.ofNat x.val := by rw [hbase]
      have hidxX : TypeIdx.ofNat x.val = x := by
        apply Subtype.ext
        exact TypeIdx.ofNat_val_of_lt x.val (by omega)
      rw [hidx, hidxBase, hidxX, ← hgroup]
      have hgroupBound : (closDefTypes C.types).length + head.length ≤
          2 ^ 32 := by
        rw [hprefixLength]
        exact Type_okA.groupEnd_le (.mk hrange hbase hgroup hrect)
      have hgroupFree : ∀ dt ∈ head,
          TypesBelow (closDefTypes C.types).length (freeDefType dt) := by
        intro dt hdt
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hdt
        rw [hprefixLength]
        exact Type_okA.groupFreeBefore hsynParts.1
          (.mk hrange hbase hgroup hrect) k dt hk
      rw [← closDefTypesAux_group_eq _ _ hgroupBound hgroupFree]
      rw [← closDefTypes_append]
      have ih' := ih hsynParts.2
      simpa only [Context.append, List.append_assoc] using ih'

theorem Types_okA.allocTypes_eq_closure {types : List TypeDef}
    {raw : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types raw) :
    Exec.allocTypes types = closDefTypes raw := by
  have h := hvalid.allocTypes_eq_closDefTypes hsyn
  simpa [allocTypesFrom_empty, Context.empty] using h

/-- Closing a validated source type section preserves its strictly decreasing
declared-super graph.  This is the runtime graph certificate consumed by the
finite subtype walk; it is derived from validation and stores no decision
result. -/
theorem Types_okA.closedTypeGraphOk_allocTypes {types : List TypeDef}
    {rawTypes : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types rawTypes) :
    Exec.ClosedTypeGraphOk (Exec.allocTypes types) := by
  rw [hvalid.allocTypes_eq_closure hsyn]
  intro i closed hclosed g hg
  have hcausal := hvalid.storedFreeBefore hsyn
  have hbound := hvalid.outputLength_le
  have hlength : (closDefTypes rawTypes).length = rawTypes.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] rawTypes
  have hiClosed : i < (closDefTypes rawTypes).length :=
    (List.getElem?_eq_some_iff.mp hclosed).1
  have hiRaw : i < rawTypes.length := by simpa [hlength] using hiClosed
  let raw := rawTypes[i]
  have hraw : rawTypes[i]? = some raw := List.getElem?_eq_getElem hiRaw
  have hclosedRaw := closDefTypes_get_full hcausal hbound hraw
  have hclosedEq : closed =
      substAllDefType raw ((closDefTypes rawTypes).map TypeUse.defd) := by
    exact Option.some.inj (hclosed.symm.trans hclosedRaw)
  subst closed
  rw [heapSupers_defd_superUses, superUses_substAll] at hg
  obtain ⟨closedSuper, hclosedSuper, rfl⟩ := List.mem_map.mp hg
  obtain ⟨sourceSuper, hsourceSuper, rfl⟩ :=
    List.mem_map.mp hclosedSuper
  have hranked := rankedBefore_of_superUse
    (hvalid.storedTypeSupersRankedA hsyn) hraw hsourceSuper
  cases hranked with
  | @idx x source hxi hsource =>
      let super :=
        ({ Context.empty with types := rawTypes } : Context).closDefType source
      refine ⟨x.val, super, hxi, ?_, ?_⟩
      · exact closDefTypes_lookup_clos hcausal hbound hsource
      · rw [closeUse_idx_of_lookup hcausal hbound hsource]
  | @defd j source hji hsource =>
      let super :=
        ({ Context.empty with types := rawTypes } : Context).closDefType source
      refine ⟨j, super, hji, ?_, ?_⟩
      · exact closDefTypes_lookup_clos hcausal hbound hsource
      · rw [closeUse_defd]

namespace Exec

def ClosedTypesConcreteA (dts : List DefType) : Prop :=
  ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
    ∃ a : AbsHeapType,
      dt.absShape = some a ∧ Context.ConcreteAbsShapeA a

def ClosedTypeGraphOkAt (C : Context) (dts : List DefType) : Prop :=
  ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
    ∀ g ∈ C.heapSupers (.use (.defd dt)),
      ∃ (j : Nat) (super : DefType),
        j < i ∧ dts[j]? = some super ∧ g = .use (.defd super)

def ClosedTypeShapesOkA (C : Context) (dts : List DefType) : Prop :=
  ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
    ∀ (a : AbsHeapType), dt.absShape = some a →
      ∀ g ∈ C.heapSupers (.use (.defd dt)),
        ∃ (j : Nat) (super : DefType),
          dts[j]? = some super ∧ g = .use (.defd super) ∧
            super.absShape = some a

private theorem empty_heapEq_defd_iff (left right : DefType) :
    Context.empty.heapEq (.use (.defd left)) (.use (.defd right)) = true ↔
      left = right := by
  simp [Context.heapEq, Context.normHeapType, Context.empty,
    Context.closDefType, Context.closTypes, closDefTypes,
    closDefTypesAux, substAllDefType, idxVars, subst_defType_nil]

theorem reachDef_follow_closedTypeGraphOk {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right) :
    ∀ (n : Nat) {i : Nat} {root target : DefType} {g : HeapType},
      dts[i]? = some root →
      C.reachDef n (.use (.defd root))
        (.use (.defd target)) = true →
      g ∈ C.heapSupers (.use (.defd target)) →
      ∃ (j : Nat) (super : DefType),
        dts[j]? = some super ∧ g = .use (.defd super) ∧
          C.reachDef (n + 1) (.use (.defd root)) g = true := by
  intro n
  induction n with
  | zero =>
      intro i root target g hroot hreach hg
      rw [Context.reachDef] at hreach
      have heq : root = target := heqExact root target hreach
      subst target
      obtain ⟨j, super, _, hsuper, rfl⟩ := hgraph i root hroot g hg
      refine ⟨j, super, hsuper, rfl, ?_⟩
      rw [Context.reachDef, Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr
        ⟨_, hg, by simp [Context.reachDef]⟩)
  | succ n ih =>
      intro i root target g hroot hreach hg
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hnext
      · have hrootTarget : root = target := heqExact root target heq
        subst target
        obtain ⟨j, super, _, hsuper, rfl⟩ := hgraph i root hroot g hg
        refine ⟨j, super, hsuper, rfl, ?_⟩
        apply reachDef_mono (n := 1) (by omega)
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr
          ⟨_, hg, by simp [Context.reachDef]⟩)
      · obtain ⟨next, hnextMem, hnextReach⟩ := List.any_eq_true.mp hnext
        obtain ⟨j, nextDt, _, hnextLookup, hnextEq⟩ :=
          hgraph i root hroot next hnextMem
        subst next
        obtain ⟨k, super, hsuper, rfl, htail⟩ :=
          ih hnextLookup hnextReach hg
        refine ⟨k, super, hsuper, rfl, ?_⟩
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr ⟨_, hnextMem, htail⟩)

theorem reachDef_target_defd_of_closedTypeGraphOk {dts : List DefType}
    (hgraph : ClosedTypeGraphOkAt Context.empty dts) :
    ∀ (n : Nat) {i : Nat} {root : DefType} {target : HeapType},
      dts[i]? = some root →
      Context.empty.reachDef n (.use (.defd root)) target = true →
      ∃ targetDt : DefType, target = .use (.defd targetDt) := by
  intro n
  induction n with
  | zero =>
      intro i root target hroot hreach
      rw [Context.reachDef] at hreach
      cases target with
      | abs a =>
          simp [Context.heapEq, Context.normHeapType, Context.empty] at hreach
      | use tu =>
          cases tu with
          | idx x =>
              simp [Context.heapEq, Context.normHeapType, Context.empty] at hreach
          | recu j =>
              simp [Context.heapEq, Context.normHeapType, Context.empty] at hreach
          | defd dt => exact ⟨dt, rfl⟩
  | succ n ih =>
      intro i root target hroot hreach
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hnext
      · cases target with
        | abs a =>
            simp [Context.heapEq, Context.normHeapType, Context.empty] at heq
        | use tu =>
            cases tu with
            | idx x =>
                simp [Context.heapEq, Context.normHeapType, Context.empty] at heq
            | recu j =>
                simp [Context.heapEq, Context.normHeapType, Context.empty] at heq
            | defd dt => exact ⟨dt, rfl⟩
      · obtain ⟨next, hnextMem, hnextReach⟩ := List.any_eq_true.mp hnext
        obtain ⟨j, nextDt, _, hnextLookup, hnextEq⟩ :=
          hgraph i root hroot next hnextMem
        subst next
        exact ih hnextLookup hnextReach

theorem reachDef_shape_of_closedTypeGraphOk {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right) :
    ∀ (n : Nat) {i : Nat} {root target : DefType} {a : AbsHeapType},
      dts[i]? = some root → root.absShape = some a →
      C.reachDef n (.use (.defd root))
        (.use (.defd target)) = true →
      target.absShape = some a := by
  intro n
  induction n with
  | zero =>
      intro i root target a hroot hshape hreach
      have heq : root = target :=
        heqExact root target (by
          simpa [Context.reachDef] using hreach)
      subst target
      exact hshape
  | succ n ih =>
      intro i root target a hroot hshape hreach
      rw [Context.reachDef, Bool.or_eq_true] at hreach
      rcases hreach with heq | hnext
      · have hrootTarget : root = target := heqExact root target heq
        subst target
        exact hshape
      · obtain ⟨next, hnextMem, hnextReach⟩ := List.any_eq_true.mp hnext
        obtain ⟨j, nextDt, hnextLookup, hnextEq, hnextShape⟩ :=
          hshapes i root hroot a hshape next hnextMem
        subst next
        exact ih hnextLookup hnextShape hnextReach

/-- A literal node whose defined type comes from the closed allocation
vector.  The type-use index remains generic in theorem signatures, matching
the declarative mutual recursion without storing a subtype conclusion. -/
inductive ClosedTypeNodeA (dts : List DefType) : HeapType → Nat → Prop where
  | defd {i : Nat} {dt : DefType} : dts[i]? = some dt →
      ClosedTypeNodeA dts (.use (.defd dt)) i

theorem reachDef_shape_of_closedTypeNodeA {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right)
    {root : TypeUse} {target : DefType} {r : Nat} {a : AbsHeapType}
    (hnode : ClosedTypeNodeA dts (.use root) r)
    (hshape : C.typeuseShape root = some a) {n : Nat}
    (hreach : C.reachDef n (.use root) (.use (.defd target)) = true) :
    target.absShape = some a := by
  cases hnode with
  | @defd i rootDt hroot =>
      exact reachDef_shape_of_closedTypeGraphOk hgraph hshapes
        heqExact n hroot (by
          simpa [Context.typeuseShape] using hshape) hreach

theorem reachDef_follow_closedTypeNodeA {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right)
    {root : TypeUse} {r : Nat} (hnode : ClosedTypeNodeA dts (.use root) r)
    {target : DefType} {g : HeapType} {n : Nat}
    (hreach : C.reachDef n (.use root) (.use (.defd target)) = true)
    (hg : g ∈ C.heapSupers (.use (.defd target))) :
    ∃ (j : Nat) (super : DefType),
      dts[j]? = some super ∧ g = .use (.defd super) ∧
        C.reachDef (n + 1) (.use root) g = true := by
  cases hnode with
  | defd hroot =>
      exact reachDef_follow_closedTypeGraphOk hgraph heqExact n hroot
        hreach hg

inductive ClosedSubtypeWitnessA (C : Context) (root : TypeUse)
    (shape : AbsHeapType) : HeapType → Prop where
  | use {target : TypeUse} :
      (∃ n : Nat, C.reachDef n (.use root)
        (C.resolveIdx (.use target)) = true) →
      ClosedSubtypeWitnessA C root shape (.use target)
  | abs {a : AbsHeapType} : decAbsSub shape a = true →
      ClosedSubtypeWitnessA C root shape (.abs a)

theorem ClosedSubtypeWitnessA.initialDefd {C : Context}
    {root : DefType} {shape : AbsHeapType} :
    ClosedSubtypeWitnessA C (.defd root) shape (.use (.defd root)) :=
  .use ⟨0, by simp [Context.reachDef, Context.resolveIdx]⟩

mutual

theorem ClosedSubtypeWitnessA.of_heaptype_subA {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right)
    (htypes : C.types = []) (hrecs : C.recs = [])
    {rootUse : TypeUse} {r : Nat}
    (hnode : ClosedTypeNodeA dts (.use rootUse) r)
    {shape : AbsHeapType} (hshape : C.typeuseShape rootUse = some shape)
    (hconcrete : Context.ConcreteAbsShapeA shape) {h₁ h₂ : HeapType} :
    Heaptype_subA C h₁ h₂ →
      ClosedSubtypeWitnessA C rootUse shape h₁ →
      ClosedSubtypeWitnessA C rootUse shape h₂
  | .refl, hw => hw
  | .trans _ hs₁ hs₂, hw =>
      ClosedSubtypeWitnessA.of_heaptype_subA (C := C) hgraph hshapes heqExact htypes hrecs
        hnode hshape
        hconcrete hs₂
        (ClosedSubtypeWitnessA.of_heaptype_subA (C := C) hgraph hshapes heqExact
          htypes hrecs hnode hshape hconcrete hs₁ hw)
  | .eq_any, .abs h => .abs (decAbsSub_trans h (by decide))
  | .i31_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .array_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct hexpand, .use hreach => by
      rename_i dt fts
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_shape_of_closedTypeNodeA hgraph hshapes
        heqExact hnode hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.struct) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .struct :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .array hexpand, .use hreach => by
      rename_i dt ft
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_shape_of_closedTypeNodeA hgraph hshapes
        heqExact hnode hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.array) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .array :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .func hexpand, .use hreach => by
      rename_i dt dom cod
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_shape_of_closedTypeNodeA hgraph hshapes
        heqExact hnode hshape (by
          simpa [Context.resolveIdx] using hreach)
      have hexpandShape : dt.absShape = some (.func) := by
        simpa using Context.absShape_eq_of_expand hexpand
      have hs : shape = .func :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .def_ hs, hw =>
      ClosedSubtypeWitnessA.of_deftype_subA (C := C) hgraph hshapes heqExact htypes
        hrecs hnode hshape hconcrete hs hw
  | .typeidx_l hx _, _ => by rw [htypes] at hx; simp at hx
  | .typeidx_r hx _, _ => by rw [htypes] at hx; simp at hx
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

theorem ClosedSubtypeWitnessA.of_deftype_subA {dts : List DefType}
    {C : Context} (hgraph : ClosedTypeGraphOkAt C dts)
    (hshapes : ClosedTypeShapesOkA C dts)
    (heqExact : ∀ left right : DefType,
      C.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right)
    (htypes : C.types = []) (hrecs : C.recs = [])
    {rootUse : TypeUse} {r : Nat}
    (hnode : ClosedTypeNodeA dts (.use rootUse) r)
    {shape : AbsHeapType} (hshape : C.typeuseShape rootUse = some shape)
    (hconcrete : Context.ConcreteAbsShapeA shape) {d₁ d₂ : DefType} :
    Deftype_subA C d₁ d₂ →
      ClosedSubtypeWitnessA C rootUse shape (.use (.defd d₁)) →
      ClosedSubtypeWitnessA C rootUse shape (.use (.defd d₂))
  | .refl heq, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      apply ClosedSubtypeWitnessA.use
      refine ⟨n, Context.reachDef_target_heapEq n hreach ?_⟩
      simp [Context.resolveIdx, Context.heapEq, Context.normHeapType, heq]
  | .super hunroll hget htail, .use hreach => by
      rename_i fin sups ct j tu
      obtain ⟨n, hreach⟩ := hreach
      have hmem : .use tu ∈
          C.heapSupers (.use (.defd d₁)) := by
        simp only [Context.heapSupers, hunroll, List.mem_map]
        exact ⟨tu, List.mem_of_getElem? hget, rfl⟩
      obtain ⟨k, super, hsuper, htu, hfollow⟩ :=
        reachDef_follow_closedTypeNodeA hgraph heqExact hnode (by
          simpa [Context.resolveIdx] using hreach) hmem
      have htu' : tu = .defd super := by injection htu
      have hresolve : C.resolveIdx (.use tu) = .use tu := by
        rw [htu']
        simp [Context.resolveIdx]
      exact ClosedSubtypeWitnessA.of_heaptype_subA (C := C) hgraph hshapes heqExact
        htypes hrecs hnode hshape hconcrete htail
          (.use ⟨n + 1, by
            rw [hresolve]
            exact hfollow⟩)
termination_by structural hsub _ => hsub

end

theorem decHeaptypeSubN_complete_of_closedTypes {dts : List DefType}
    (hgraph : ClosedTypeGraphOk dts)
    (hconcrete : ClosedTypesConcreteA dts)
    (hshapes : ClosedTypeShapesOkA Context.empty dts)
    {root : DefType} {i : Nat} (hroot : dts[i]? = some root)
    {target : HeapType}
    (hsub : Heaptype_subA Context.empty (.use (.defd root)) target) :
    decHeaptypeSubN Context.empty dts.length (.use (.defd root)) target =
      true := by
  have hgraphAt : ClosedTypeGraphOkAt Context.empty dts := hgraph
  have heqExact : ∀ left right : DefType,
      Context.empty.heapEq (.use (.defd left)) (.use (.defd right)) = true →
        left = right := fun left right h =>
    (empty_heapEq_defd_iff left right).mp h
  obtain ⟨shape, hshape, hshapeConcrete⟩ := hconcrete i root hroot
  have hnode : ClosedTypeNodeA dts (.use (.defd root)) i := .defd hroot
  have hshape' : Context.empty.typeuseShape (.defd root) = some shape := by
    simpa [Context.typeuseShape] using hshape
  have hshapeA : Context.empty.typeuseShapeA (.defd root) = some shape := by
    simpa [Context.typeuseShapeA] using hshape
  have hw := ClosedSubtypeWitnessA.of_heaptype_subA hgraphAt hshapes heqExact
    rfl rfl hnode hshape' hshapeConcrete hsub
    (ClosedSubtypeWitnessA.initialDefd (C := Context.empty)
      (shape := shape))
  cases hw with
  | abs habs =>
      simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
        hshapeA] using habs
  | use hreach =>
      rename_i targetUse
      obtain ⟨n, hreach⟩ := hreach
      obtain ⟨targetDt, htarget⟩ :=
        reachDef_target_defd_of_closedTypeGraphOk hgraphAt n hroot hreach
      cases targetUse with
      | idx x => simp [Context.resolveIdx, Context.empty] at htarget
      | recu j => simp [Context.resolveIdx, Context.empty] at htarget
      | defd dt =>
          have hdt : dt = targetDt := by
            simpa [Context.resolveIdx] using htarget
          subst targetDt
          have hbounded := reachDef_closedTypeFuel_of_graphOk hgraph hroot hreach
          simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx] using hbounded

theorem Types_okA.closedTypesConcreteA_allocTypes {types : List TypeDef}
    {rawTypes : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types rawTypes) :
    ClosedTypesConcreteA (allocTypes types) := by
  rw [hvalid.allocTypes_eq_closure hsyn]
  intro i closed hclosed
  have hcausal := hvalid.storedFreeBefore hsyn
  have hbound := hvalid.outputLength_le
  have hlength : (closDefTypes rawTypes).length = rawTypes.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] rawTypes
  have hiClosed : i < (closDefTypes rawTypes).length :=
    (List.getElem?_eq_some_iff.mp hclosed).1
  have hiRaw : i < rawTypes.length := by simpa [hlength] using hiClosed
  let raw := rawTypes[i]
  have hraw : rawTypes[i]? = some raw := List.getElem?_eq_getElem hiRaw
  have hclosedRaw := closDefTypes_get_full hcausal hbound hraw
  have hclosedEq : closed =
      substAllDefType raw ((closDefTypes rawTypes).map TypeUse.defd) :=
    Option.some.inj (hclosed.symm.trans hclosedRaw)
  obtain ⟨a, hrawShape, hconcrete⟩ :=
    hvalid.sourceTypesConcreteA (Context.SourceTypeNodeA.defd hraw)
  refine ⟨a, ?_, hconcrete⟩
  rw [hclosedEq]
  simp only [substAllDefType, DefType.absShape_substDefType]
  simpa [Context.typeuseShape] using hrawShape

theorem Types_okA.closedTypeShapesOkA_allocTypes {types : List TypeDef}
    {rawTypes : List DefType} (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types rawTypes) :
    ClosedTypeShapesOkA Context.empty (allocTypes types) := by
  rw [hvalid.allocTypes_eq_closure hsyn]
  intro i closed hclosed a hclosedShape g hg
  have hcausal := hvalid.storedFreeBefore hsyn
  have hbound := hvalid.outputLength_le
  have hlength : (closDefTypes rawTypes).length = rawTypes.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] rawTypes
  have hiClosed : i < (closDefTypes rawTypes).length :=
    (List.getElem?_eq_some_iff.mp hclosed).1
  have hiRaw : i < rawTypes.length := by simpa [hlength] using hiClosed
  let raw := rawTypes[i]
  have hraw : rawTypes[i]? = some raw := List.getElem?_eq_getElem hiRaw
  have hclosedRaw := closDefTypes_get_full hcausal hbound hraw
  have hclosedEq : closed =
      substAllDefType raw ((closDefTypes rawTypes).map TypeUse.defd) :=
    Option.some.inj (hclosed.symm.trans hclosedRaw)
  have hrawShape : raw.absShape = some a := by
    rw [hclosedEq] at hclosedShape
    simpa only [substAllDefType, DefType.absShape_substDefType] using
      hclosedShape
  rw [hclosedEq, heapSupers_defd_superUses, superUses_substAll] at hg
  obtain ⟨closedSuper, hclosedSuper, rfl⟩ := List.mem_map.mp hg
  obtain ⟨sourceSuper, hsourceSuper, rfl⟩ :=
    List.mem_map.mp hclosedSuper
  let sourceContext : Context := { Context.empty with types := rawTypes }
  have hsourceNode : Context.SourceTypeNodeA sourceContext
      (.use (.defd raw)) (2 * i) := by
    exact .defd hraw
  have hsourceParentShape : sourceContext.typeuseShape (.defd raw) =
      some a := by
    simpa [sourceContext, Context.typeuseShape] using hrawShape
  have hsourceEdge : .use sourceSuper ∈
      sourceContext.heapSupers (.use (.defd raw)) := by
    rw [heapSupers_defd_superUses]
    exact List.mem_map.mpr ⟨sourceSuper, hsourceSuper, rfl⟩
  obtain ⟨sourceSuper', hsourceEq, hsourceShape'⟩ :=
    hvalid.sourceTypeShapesOkA hsyn hsourceNode hsourceParentShape
      (.use sourceSuper) hsourceEdge
  have hsourceUseEq : sourceSuper = sourceSuper' := by
    injection hsourceEq
  subst sourceSuper'
  have hranked := rankedBefore_of_superUse
    (hvalid.storedTypeSupersRankedA hsyn) hraw hsourceSuper
  cases hranked with
  | @idx x source hxi hsource =>
      let super := sourceContext.closDefType source
      refine ⟨x.val, super, closDefTypes_lookup_clos hcausal hbound hsource,
        ?_, ?_⟩
      · rw [closeUse_idx_of_lookup hcausal hbound hsource]
      · have hsourceAbs : source.absShape = some a := by
          simpa [sourceContext, Context.typeuseShape, hsource] using
            hsourceShape'
        simpa [super] using hsourceAbs
  | @defd j source hji hsource =>
      let super := sourceContext.closDefType source
      refine ⟨j, super, closDefTypes_lookup_clos hcausal hbound hsource,
        ?_, ?_⟩
      · rw [closeUse_defd]
      · have hsourceAbs : source.absShape = some a := by
          simpa [sourceContext, Context.typeuseShape] using hsourceShape'
        simpa [super] using hsourceAbs

/-- Exact runtime heap-subtype decision completeness for a literal defined
type allocated from a validated source module. -/
theorem Types_okA.decHeaptypeSubN_complete_of_allocated
    {types : List TypeDef} {rawTypes : List DefType}
    (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types rawTypes)
    {i : Nat} {root : DefType}
    (hroot : (allocTypes types)[i]? = some root)
    {target : HeapType}
    (hsub : Heaptype_subA Context.empty (.use (.defd root)) target) :
    decHeaptypeSubN Context.empty (allocTypes types).length
      (.use (.defd root)) target = true := by
  exact decHeaptypeSubN_complete_of_closedTypes
    (hvalid.closedTypeGraphOk_allocTypes hsyn)
    (Types_okA.closedTypesConcreteA_allocTypes hsyn hvalid)
    (Types_okA.closedTypeShapesOkA_allocTypes hsyn hvalid)
    hroot hsub

end Exec

end WasmGemmGnaf.Wasm.Core
