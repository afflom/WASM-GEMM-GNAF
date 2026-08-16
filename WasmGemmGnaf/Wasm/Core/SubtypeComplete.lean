/-
  Wasm/Core/SubtypeComplete.lean --- completeness of the amended executable
  heap subtype decision on ranked source type graphs.

  The declarative heap/deftype relations are mutually inductive.  Their
  normalization proof therefore follows their generated mutual structural
  recursion directly; keeping it downstream of `SubtypeSound` leaves the
  source-graph certificate interface independently buildable.
-/
import WasmGemmGnaf.Wasm.Core.TypeGraphClosure

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

theorem Comptype_subA.absShape_eq {C : Context} {ct₁ ct₂ : CompType}
    (h : Comptype_subA C ct₁ ct₂) : ct₁.absShape = ct₂.absShape := by
  cases h <;> rfl

namespace Context

/-- The outer abstract family observed by the heap decision. -/
def heapShapeA (C : Context) : HeapType → Option AbsHeapType
  | .abs a => some a
  | .use tu => C.typeuseShape tu

/-- In a source type-section context (whose recursive-group scratch space is
empty), every valid heap type has a concrete outer family.  Source indices use
the checked graph certificate; literal semantic defined types use their own
amended validity derivation. -/
theorem Heaptype_okA.heapShapeA_exists {C : Context}
    (hconcrete : SourceTypesConcreteA C) (hrecs : C.recs = [])
    {ht : HeapType} (h : Heaptype_okA C ht) :
    ∃ a : AbsHeapType, C.heapShapeA ht = some a := by
  cases h with
  | abs => exact ⟨_, rfl⟩
  | typeuse htu =>
      cases htu with
      | typeidx hlookup =>
          obtain ⟨a, ha, _⟩ := hconcrete (.idx hlookup)
          exact ⟨a, ha⟩
      | rec_ hlookup => simp [hrecs] at hlookup
      | deftype hdt =>
          obtain ⟨ct, hexpand⟩ := hdt.expand_exists
          exact ⟨ct.absShape, by
            simpa [heapShapeA, typeuseShape] using
              absShape_eq_of_expand hexpand⟩

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
  | .rec_struct _, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      simp [Context.typeuseShape] at htarget
  | .rec_array _, .use hreach => by
      obtain ⟨n, hreach⟩ := hreach
      have htarget := reachDef_typeuseShape_of_sourceGraphOkA
        hgraph hshapes n hnode hshape
        (by simpa [Context.resolveIdx] using hreach)
      simp [Context.typeuseShape] at htarget
  | .rec_func _, .use hreach => by
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
      exact SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure
        hnode hshape hconcrete htail
        (SourceSubtypeWitnessA.use ⟨n + 2, hfollow⟩)

end

/-- Exact amended heap-decision completeness for a ranked source-defined
left endpoint. -/
theorem decHeaptypeSubN_complete_of_sourceTypeNodeA {C : Context}
    (hgraph : SourceTypeGraphOkA C) (hconcrete : SourceTypesConcreteA C)
    (hshapes : SourceTypeShapesOkA C) (hclosure : SourceTypeClosureOkA C)
    {root : TypeUse} {r : Nat} (hnode : SourceTypeNodeA C (.use root) r)
    {target : HeapType} (hsub : Heaptype_subA C (.use root) target) :
    decHeaptypeSubN C C.subtypeFuel (.use root) target = true := by
  obtain ⟨shape, hshape, hshapeConcrete⟩ := hnode.concreteShape hconcrete
  exact (SourceSubtypeWitnessA.of_heaptype_subA hgraph hshapes hclosure hnode
    hshape hshapeConcrete hsub
    (SourceSubtypeWitnessA.initial hgraph hnode)).decides
      hgraph hshapes hnode hshape

end Context

/-- The full checked type section supplies every structural certificate needed
by the executable heap-subtype converse for a source-ranked left endpoint. -/
theorem Types_okA.decHeaptypeSubN_complete_of_sourceTypeNodeA
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    {root : TypeUse} {r : Nat}
    (hnode : Context.SourceTypeNodeA
      { Context.empty with types := dts } (.use root) r)
    {target : HeapType}
    (hsub : Heaptype_subA { Context.empty with types := dts }
      (.use root) target) :
    decHeaptypeSubN { Context.empty with types := dts }
      ({ Context.empty with types := dts } : Context).subtypeFuel
      (.use root) target = true := by
  exact Context.decHeaptypeSubN_complete_of_sourceTypeNodeA
    (hvalid.sourceTypeGraphOkA hsyn)
    hvalid.sourceTypesConcreteA
    (hvalid.sourceTypeShapesOkA hsyn)
    (hvalid.sourceTypeClosureOkA hsyn)
    hnode hsub

/-- The same source-ranked converse at the public context-selected decision
entry point. -/
theorem Types_okA.decHeaptypeSub_complete_of_sourceTypeNodeA
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    {root : TypeUse} {r : Nat}
    (hnode : Context.SourceTypeNodeA
      { Context.empty with types := dts } (.use root) r)
    {target : HeapType}
    (hsub : Heaptype_subA { Context.empty with types := dts }
      (.use root) target) :
    decHeaptypeSub { Context.empty with types := dts }
      (.use root) target = true := by
  exact hvalid.decHeaptypeSubN_complete_of_sourceTypeNodeA hsyn hnode hsub

/-- Every syntactic type-use is a ranked source index, so checked type-section
provenance discharges the executable subtype converse directly. -/
theorem Types_okA.decHeaptypeSub_complete_of_syn_typeuse
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    {tu : TypeUse} (htuSyn : tu.isSyn = true)
    (htuOk : Typeuse_okA { Context.empty with types := dts } tu)
    {target : HeapType}
    (hsub : Heaptype_subA { Context.empty with types := dts }
      (.use tu) target) :
    decHeaptypeSub { Context.empty with types := dts }
      (.use tu) target = true := by
  cases tu with
  | idx x =>
      cases htuOk with
      | typeidx hlookup =>
          exact hvalid.decHeaptypeSub_complete_of_sourceTypeNodeA hsyn
            (.idx hlookup) hsub
  | recu _ | defd _ => simp [TypeUse.isSyn] at htuSyn

end WasmGemmGnaf.Wasm.Core
