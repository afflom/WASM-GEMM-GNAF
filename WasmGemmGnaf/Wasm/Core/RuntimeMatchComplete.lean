import WasmGemmGnaf.Wasm.Core.RuntimeTypeBridge
import WasmGemmGnaf.Wasm.Core.RuntimeDecision

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

inductive RuntimeAbsRootA : AbsHeapType → Prop where
  | i31 : RuntimeAbsRootA .i31
  | exn : RuntimeAbsRootA .exn
  | any : RuntimeAbsRootA .any
  | extern : RuntimeAbsRootA .extern

inductive RuntimeAbsSubtypeWitnessA (root : AbsHeapType) : HeapType → Prop where
  | abs {target : AbsHeapType} : decAbsSub root target = true →
      RuntimeAbsSubtypeWitnessA root (.abs target)

theorem RuntimeAbsSubtypeWitnessA.of_heaptype_subA
    {root : AbsHeapType} (hroot : RuntimeAbsRootA root)
    {C : Context} {h₁ h₂ : HeapType} : Heaptype_subA C h₁ h₂ →
    RuntimeAbsSubtypeWitnessA root h₁ →
    RuntimeAbsSubtypeWitnessA root h₂
  | .refl, hw => hw
  | .trans _ hleft hright, hw =>
      RuntimeAbsSubtypeWitnessA.of_heaptype_subA hroot hright
        (RuntimeAbsSubtypeWitnessA.of_heaptype_subA hroot hleft hw)
  | .eq_any, .abs h => .abs (decAbsSub_trans h (by decide))
  | .i31_eq, .abs h => .abs (decAbsSub_trans h (by decide))
  | .struct_eq, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .array_eq, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .struct _, hw => by cases hw
  | .array _, hw => by cases hw
  | .func _, hw => by cases hw
  | .def_ _, hw => by cases hw
  | .typeidx_l _ _, hw => by cases hw
  | .typeidx_r _ htail, hw => by
      have hbad := RuntimeAbsSubtypeWitnessA.of_heaptype_subA hroot htail hw
      cases hbad
  | .rec_ _ _, hw => by cases hw
  | .none_ _ _, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .nofunc _ _, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .noexn _ _, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .noextern _ _, .abs h => by cases hroot <;> simp [decAbsSub] at h
  | .bot, .abs h => by cases hroot <;> simp [decAbsSub] at h
termination_by structural hsub _ => hsub

theorem RuntimeAbsSubtypeWitnessA.decides
    {root : AbsHeapType} {target : HeapType}
    (hw : RuntimeAbsSubtypeWitnessA root target) (fuel : Nat) :
    decHeaptypeSubN Context.empty fuel (.abs root) target = true := by
  cases hw with
  | abs h => simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx] using h

theorem ClosedSubtypeWitnessA.decides_of_graph
    {dts : List DefType} (hgraph : ClosedTypeGraphOk dts)
    {root : DefType} {i : Nat} (hroot : dts[i]? = some root)
    {shape : AbsHeapType}
    (hshape : Context.empty.typeuseShape (.defd root) = some shape)
    {target : HeapType}
    (hw : ClosedSubtypeWitnessA Context.empty (.defd root) shape target) :
    decHeaptypeSubN Context.empty dts.length
      (.use (.defd root)) target = true := by
  have hshapeA : Context.empty.typeuseShapeA (.defd root) = some shape := by
    simpa [Context.typeuseShapeA] using hshape
  cases hw with
  | abs habs =>
      simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
        hshapeA] using habs
  | use hreach =>
      rename_i targetUse
      obtain ⟨n, hreach⟩ := hreach
      have hgraphAt : ClosedTypeGraphOkAt Context.empty dts := hgraph
      obtain ⟨targetDt, htarget⟩ :=
        reachDef_target_defd_of_closedTypeGraphOk hgraphAt n hroot hreach
      cases targetUse with
      | idx x => simp [Context.resolveIdx, Context.empty] at htarget
      | recu j => simp [Context.resolveIdx] at htarget
      | defd dt =>
          have hdt : dt = targetDt := by
            simpa [Context.resolveIdx] using htarget
          subst targetDt
          have hbounded := reachDef_closedTypeFuel_of_graphOk hgraph hroot hreach
          simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx] using hbounded

def StoreTypeOriginsA (s : Store) (dts : List DefType) : Prop :=
  (∀ {si : StructInst}, si ∈ s.structs →
    ∃ i : Nat, dts[i]? = some si.type) ∧
  (∀ {ai : ArrayInst}, ai ∈ s.arrays →
    ∃ i : Nat, dts[i]? = some ai.type) ∧
  (∀ {fi : FuncInst}, fi ∈ s.funcs →
    (∃ i : Nat, dts[i]? = some fi.type) ∧ fi.mod.types = dts)

inductive RuntimeHeapWitnessA (dts : List DefType) :
    HeapType → HeapType → Prop where
  | bot {target : HeapType} :
      RuntimeHeapWitnessA dts (.abs .bot) target
  | abs {root : AbsHeapType} {target : HeapType} :
      RuntimeAbsRootA root → RuntimeAbsSubtypeWitnessA root target →
      RuntimeHeapWitnessA dts (.abs root) target
  | allocated {i : Nat} {root : DefType} {shape : AbsHeapType}
      {target : HeapType} :
      dts[i]? = some root →
      Context.empty.typeuseShape (.defd root) = some shape →
      Context.ConcreteAbsShapeA shape →
      ClosedSubtypeWitnessA Context.empty (.defd root) shape target →
      RuntimeHeapWitnessA dts (.use (.defd root)) target

theorem RuntimeHeapWitnessA.of_heaptype_subA
    {dts : List DefType}
    (hgraph : ClosedTypeGraphOk dts)
    (hshapes : ClosedTypeShapesOkA Context.empty dts)
    {h₁ middle h₂ : HeapType}
    (hsub : Heaptype_subA Context.empty middle h₂)
    (hw : RuntimeHeapWitnessA dts h₁ middle) :
    RuntimeHeapWitnessA dts h₁ h₂ := by
  cases hw with
  | bot => exact .bot
  | abs hroot hw =>
      exact .abs hroot (hw.of_heaptype_subA hroot hsub)
  | @allocated i root shape target hlookup hshape hconcrete hw =>
      have hgraphAt : ClosedTypeGraphOkAt Context.empty dts := hgraph
      have heqExact : ∀ left right : DefType,
          Context.empty.heapEq (.use (.defd left)) (.use (.defd right)) = true →
            left = right := by
        intro left right h
        simpa [Context.heapEq, Context.normHeapType, Context.empty,
          Context.closDefType, Context.closTypes, closDefTypes,
          closDefTypesAux, substAllDefType, idxVars, subst_defType_nil] using h
      have hnode : ClosedTypeNodeA dts (.use (.defd root)) i := .defd hlookup
      exact .allocated hlookup hshape hconcrete
        (hw.of_heaptype_subA hgraphAt hshapes heqExact rfl rfl
          hnode hshape hconcrete hsub)

theorem RuntimeHeapWitnessA.decides
    {dts : List DefType} (hgraph : ClosedTypeGraphOk dts)
    {source target : HeapType} (hw : RuntimeHeapWitnessA dts source target) :
    decHeaptypeSubN Context.empty dts.length source target = true := by
  cases hw with
  | bot =>
      cases target with
      | abs a => rfl
      | use u => cases u <;> simp [decHeaptypeSubN, decHeapSubR,
          Context.resolveIdx, Context.empty]
  | abs hroot hw => exact hw.decides dts.length
  | allocated hlookup hshape hconcrete hw =>
      exact hw.decides_of_graph hgraph hlookup hshape

inductive RuntimeRefWitnessA (dts : List DefType) : RefType → RefType → Prop where
  | mk {sourceNull targetNull : Option Null} {sourceHeap targetHeap : HeapType} :
      (targetNull.isSome || !sourceNull.isSome) = true →
      RuntimeHeapWitnessA dts sourceHeap targetHeap →
      RuntimeRefWitnessA dts (.ref sourceNull sourceHeap)
        (.ref targetNull targetHeap)

theorem RuntimeRefWitnessA.of_reftype_subA
    {dts : List DefType}
    (hgraph : ClosedTypeGraphOk dts)
    (hshapes : ClosedTypeShapesOkA Context.empty dts)
    {principal middle target : RefType}
    (hw : RuntimeRefWitnessA dts principal middle)
    (hsub : Reftype_subA Context.empty middle target) :
    RuntimeRefWitnessA dts principal target := by
  cases hw with
  | @mk sourceNull middleNull sourceHeap middleHeap hnull hheap =>
      cases hsub with
      | nonnull hsub =>
          exact .mk (by simpa using hnull)
            (hheap.of_heaptype_subA hgraph hshapes hsub)
      | @null _ targetNull _ targetHeap hsub =>
          exact .mk (by simp) (hheap.of_heaptype_subA hgraph hshapes hsub)

theorem RuntimeRefWitnessA.decides
    {dts : List DefType} (hgraph : ClosedTypeGraphOk dts)
    {principal target : RefType} (hw : RuntimeRefWitnessA dts principal target) :
    decReftypeSubN Context.empty dts.length principal target = true := by
  cases hw with
  | mk hnull hheap =>
      simp only [decReftypeSubN, Bool.and_eq_true]
      exact ⟨hnull, hheap.decides hgraph⟩

theorem principalRefTypeN_witness_of_ref_ok
    {dts : List DefType} {s : Store}
    (hgraph : ClosedTypeGraphOk dts)
    (hconcrete : ClosedTypesConcreteA dts)
    (hshapes : ClosedTypeShapesOkA Context.empty dts)
    (horigin : StoreTypeOriginsA s dts)
    {r : Ref} {target : RefType} (href : Ref_okA s r target) :
    ∃ principal : RefType,
      principalRefTypeN dts.length s r = some principal ∧
      RuntimeRefWitnessA dts principal target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction href with
  | null hsub =>
      exact ⟨.ref (some .null) (.abs .bot), rfl,
        .mk (by decide) .bot⟩
  | i31 =>
      exact ⟨.ref none (.abs .i31), rfl,
        .mk (by decide) (.abs .i31 (.abs (by decide)))⟩
  | @struct address si type hlookup htype =>
      subst type
      obtain ⟨i, horigin⟩ := horigin.1 (List.mem_of_getElem? hlookup)
      obtain ⟨shape, hshape, hshapeConcrete⟩ := hconcrete i si.type horigin
      have hshape' : Context.empty.typeuseShape (.defd si.type) =
          some shape := by simpa [Context.typeuseShape] using hshape
      exact ⟨.ref none (.use (.defd si.type)), by
          simp [principalRefTypeN, principalAddrRefTypeN, hlookup],
        .mk (by decide) (.allocated horigin hshape' hshapeConcrete
          (ClosedSubtypeWitnessA.initialDefd (C := Context.empty)
            (shape := shape)))⟩
  | @array address ai type hlookup htype =>
      subst type
      obtain ⟨i, horigin⟩ := horigin.2.1 (List.mem_of_getElem? hlookup)
      obtain ⟨shape, hshape, hshapeConcrete⟩ := hconcrete i ai.type horigin
      have hshape' : Context.empty.typeuseShape (.defd ai.type) =
          some shape := by simpa [Context.typeuseShape] using hshape
      exact ⟨.ref none (.use (.defd ai.type)), by
          simp [principalRefTypeN, principalAddrRefTypeN, hlookup],
        .mk (by decide) (.allocated horigin hshape' hshapeConcrete
          (ClosedSubtypeWitnessA.initialDefd (C := Context.empty)
            (shape := shape)))⟩
  | @func address fi type hlookup htype =>
      subst type
      obtain ⟨⟨i, horigin⟩, _⟩ :=
        horigin.2.2 (List.mem_of_getElem? hlookup)
      obtain ⟨shape, hshape, hshapeConcrete⟩ := hconcrete i fi.type horigin
      have hshape' : Context.empty.typeuseShape (.defd fi.type) =
          some shape := by simpa [Context.typeuseShape] using hshape
      exact ⟨.ref none (.use (.defd fi.type)), by
          simp [principalRefTypeN, principalAddrRefTypeN, hlookup],
        .mk (by decide) (.allocated horigin hshape' hshapeConcrete
          (ClosedSubtypeWitnessA.initialDefd (C := Context.empty)
            (shape := shape)))⟩
  | exn hlookup =>
      exact ⟨.ref none (.abs .exn), by
          simp [principalRefTypeN, principalAddrRefTypeN, hlookup],
        .mk (by decide) (.abs .exn (.abs (by decide)))⟩
  | host =>
      exact ⟨.ref none (.abs .any), rfl,
        .mk (by decide) (.abs .any (.abs (by decide)))⟩
  | @extern underlying href ih =>
      obtain ⟨principal, hp, hw⟩ := ih
      have hdec : decReftypeSubN Context.empty dts.length principal
          (.ref none (.abs .any)) = true := hw.decides hgraph
      have hpAddr : principalAddrRefTypeN dts.length s underlying =
          some principal := by simpa [principalRefTypeN] using hp
      have hpExtern : principalAddrRefTypeN dts.length s (.extern underlying) =
          some (.ref none (.abs .extern)) := by
        rw [principalAddrRefTypeN, hpAddr]
        change (if decReftypeSubN Context.empty dts.length principal
            (.ref none (.abs .any)) then
              some (RefType.ref none (.abs .extern))
          else none) = some (RefType.ref none (.abs .extern))
        rw [hdec]
        simp
      exact ⟨.ref none (.abs .extern), by
          simpa [principalRefTypeN] using hpExtern,
        .mk (by decide) (.abs .extern (.abs (by decide)))⟩
  | sub href hsub ih =>
      obtain ⟨principal, hp, hw⟩ := ih
      exact ⟨principal, hp, hw.of_reftype_subA hgraph hshapes hsub⟩

theorem refMatchesN_complete_of_allocated
    {types : List TypeDef} {rawTypes : List DefType} {s : Store}
    (hsyn : types.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty types rawTypes)
    (horigin : StoreTypeOriginsA s (allocTypes types))
    {r : Ref} {target : RefType}
    (href : ∃ rt : RefType, Ref_okA s r rt ∧
      Reftype_subA Context.empty rt target) :
    refMatchesN (allocTypes types).length s r target = true := by
  obtain ⟨rt, href, hsub⟩ := href
  have hgraph := hvalid.closedTypeGraphOk_allocTypes hsyn
  have hconcrete := Types_okA.closedTypesConcreteA_allocTypes hsyn hvalid
  have hshapes := Types_okA.closedTypeShapesOkA_allocTypes hsyn hvalid
  obtain ⟨principal, hp, hw⟩ :=
    principalRefTypeN_witness_of_ref_ok hgraph hconcrete hshapes horigin href
  have hw' := hw.of_reftype_subA hgraph hshapes hsub
  simp [refMatchesN, hp, hw'.decides hgraph]

end WasmGemmGnaf.Wasm.Core.Exec
