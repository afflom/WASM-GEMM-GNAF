/-
  Wasm/Core/SubtypeComplete.lean --- completeness of the amended executable
  heap subtype decision on ranked source type graphs.

  The declarative heap/deftype relations are mutually inductive.  Their
  normalization proof therefore follows their generated mutual structural
  recursion directly; keeping it downstream of `SubtypeSound` leaves the
  source-graph certificate interface independently buildable.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeSound

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

theorem Comptype_subA.absShape_eq {C : Context} {ct₁ ct₂ : CompType}
    (h : Comptype_subA C ct₁ ct₂) : ct₁.absShape = ct₂.absShape := by
  cases h <;> rfl

namespace Context

theorem typeuseShape_of_unrollHt {C : Context} {tu : TypeUse}
    {fin : Option Final} {sups : TypeUses} {ct : CompType}
    (h : C.unrollHt (.use tu) = some (.sub fin sups ct))
    (hnrec : ∀ i : Nat, tu ≠ .recu i) :
    C.typeuseShape tu = some ct.absShape := by
  cases tu with
  | idx x =>
      cases hx : C.types[x.val]? with
      | none => simp [Context.unrollHt, hx] at h
      | some d =>
          simp only [Context.unrollHt, hx] at h
          simp [Context.typeuseShape, hx, DefType.absShape, expandDt, h]
  | defd d =>
      simp only [Context.unrollHt] at h
      simp [Context.typeuseShape, DefType.absShape, expandDt, h]
  | recu i => exact absurd rfl (hnrec i)

mutual

/-- Every amended heap-subtyping derivation starting from a source normal
form stays in that normal form. -/
theorem SourceSubtypeWitnessA.of_heaptype_subA {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hshapes : SourceTypeShapesOkA C)
    (hclosure : SourceTypeClosureOkA C) {root : TypeUse} {r : Nat}
    (hnode : SourceTypeNodeA C (.use root) r) {shape : AbsHeapType}
    (hshape : C.typeuseShape root = some shape)
    (hconcrete : ConcreteAbsShapeA shape) {h₁ h₂ : HeapType} :
    Heaptype_subA C h₁ h₂ → SourceSubtypeWitnessA C root shape h₁ →
      SourceSubtypeWitnessA C root shape h₂
  | .refl, hw => hw
  | .trans _ hs₁ hs₂, hw =>
      SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure hnode
        hshape hconcrete hs₂
        (SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure hnode
          hshape hconcrete hs₁ hw)
  | .eq_any, .abs h => .abs (decAbsSub_trans h (by decide))
  | .i31_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .array_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct hexpand, .use hreach => by
      rename_i dt fts
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      have hexpandShape :
          C.typeuseShape (.defd dt) = some (.struct) := by
        simpa [Context.typeuseShape] using absShape_eq_of_expand hexpand
      have hs : shape = .struct :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .array hexpand, .use hreach => by
      rename_i dt ft
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      have hexpandShape :
          C.typeuseShape (.defd dt) = some (.array) := by
        simpa [Context.typeuseShape] using absShape_eq_of_expand hexpand
      have hs : shape = .array :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .func hexpand, .use hreach => by
      rename_i dt dom cod
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      have hexpandShape :
          C.typeuseShape (.defd dt) = some (.func) := by
        simpa [Context.typeuseShape] using absShape_eq_of_expand hexpand
      have hs : shape = .func :=
        Option.some.inj (htarget.symm.trans hexpandShape)
      subst shape
      exact .abs (by decide)
  | .def_ hs, hw =>
      SourceSubtypeWitnessA.of_deftype_subA hgraph hshapes hclosure hnode
        hshape hconcrete hs hw
  | .typeidx_l hx hs, .use hreach => by
      apply SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure
        hnode hshape hconcrete hs
      apply SourceSubtypeWitnessA.use
      simpa [Context.resolveIdx, hx] using hreach
  | .typeidx_r hx hs, hw => by
      have hw' := SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes
        hclosure hnode hshape hconcrete hs hw
      cases hw' with
      | use hreach =>
          apply SourceSubtypeWitnessA.use
          simpa [Context.resolveIdx, hx] using hreach
  | .rec_ _ _, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      simp [Context.typeuseShape] at htarget
  | .none_ _ _, .abs h => False.elim (hconcrete.not_none h)
  | .nofunc _ _, .abs h => False.elim (hconcrete.not_nofunc h)
  | .noexn _ _, .abs h => False.elim (hconcrete.not_noexn h)
  | .noextern _ _, .abs h => False.elim (hconcrete.not_noextern h)
  | .bot, .abs h => False.elim (hconcrete.not_bot h)

/-- Defined-type subtyping is the declared-super walk component of the same
normalization. -/
theorem SourceSubtypeWitnessA.of_deftype_subA {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hshapes : SourceTypeShapesOkA C)
    (hclosure : SourceTypeClosureOkA C) {root : TypeUse} {r : Nat}
    (hnode : SourceTypeNodeA C (.use root) r) {shape : AbsHeapType}
    (hshape : C.typeuseShape root = some shape)
    (hconcrete : ConcreteAbsShapeA shape) {d₁ d₂ : DefType} :
    Deftype_subA C d₁ d₂ →
      SourceSubtypeWitnessA C root shape (.use (.defd d₁)) →
      SourceSubtypeWitnessA C root shape (.use (.defd d₂))
  | .refl heq, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      apply SourceSubtypeWitnessA.use
      refine ⟨n, reachDef_target_heapEq n hreach ?_⟩
      simp [Context.resolveIdx, Context.heapEq, Context.normHeapType, heq]
  | .super hunroll hget htail, .use hreach => by
      rename_i fin sups ct i tu
      obtain ⟨n, hreach⟩ := hreach
      have hmem : .use tu ∈ C.heapSupers (.use (.defd d₁)) := by
        simp only [Context.heapSupers, hunroll, List.mem_map]
        exact ⟨tu, List.mem_of_getElem? hget, rfl⟩
      have hfollow := reachDef_follow_equiv_super hgraph hclosure n
        hnode (by simpa [Context.resolveIdx] using hreach) hmem
      obtain ⟨m, hresolved⟩ :=
        reachDef_resolveIdx_of_reach hgraph hnode hfollow
      exact SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure
        hnode hshape hconcrete htail
        (SourceSubtypeWitnessA.use ⟨m, hresolved⟩)

end

/-- Exact amended heap-decision completeness for a ranked source-defined
left endpoint. -/
theorem decHeaptypeSubN_complete_of_sourceTypeNodeA {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hvalid : SourceTypesValidA C)
    (hshapes : SourceTypeShapesOkA C) (hclosure : SourceTypeClosureOkA C)
    {root : TypeUse} {r : Nat} (hnode : SourceTypeNodeA C (.use root) r)
    {target : HeapType} (hsub : Heaptype_subA C (.use root) target) :
    decHeaptypeSubN C C.subtypeFuel (.use root) target = true := by
  obtain ⟨shape, hshape, hconcrete⟩ := hnode.concreteShape hvalid
  exact (SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure hnode
    hshape hconcrete hsub
    (SourceSubtypeWitnessA.initial hgraph hnode)).decides
      hgraph hshapes hnode hshape

end Context
end WasmGemmGnaf.Wasm.Core
