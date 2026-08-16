import WasmGemmGnaf.Wasm.Core.ValidateHeapFlow

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

theorem Heaptype_subA.decHeaptypeSubN_complete_of_abs_abs
    {C : Context} {n : Nat} {a b : AbsHeapType}
    (h : Heaptype_subA C (.abs a) (.abs b))
    (henv : C.ValidHeapShapesA) :
    decHeaptypeSubN C n (.abs a) (.abs b) = true := by
  have hab := h.goodShape henv (GoodHeapShapeA.abs a)
    (GoodHeapShapeA.abs b)
  simpa [decHeaptypeSubN, Context.resolveIdx, decHeapSubR] using hab

theorem Heaptype_subA.decHeaptypeSubN_complete_of_abs_nonrec_use
    {C : Context} {n : Nat} {a b : AbsHeapType} {tu : TypeUse}
    (h : Heaptype_subA C (.abs a) (.use tu))
    (henv : C.ValidHeapShapesA) (hgood : GoodHeapShapeA C (.use tu) b)
    (hnrec : ∀ i : Nat, tu ≠ .recu i) :
    decHeaptypeSubN C n (.abs a) (.use tu) = true := by
  have hclass := h.absUseClass henv rfl rfl hgood
  have hshape := hgood.typeuseShape hnrec
  cases tu with
  | recu i => exact absurd rfl (hnrec i)
  | defd dt =>
      have hshape' : dt.absShape = some b := by
        simpa [Context.typeuseShape] using hshape
      rcases hclass with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst a
        simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR]
      · subst a
        rcases hb with hb | hb <;> subst b <;>
          simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR,
            Context.typeuseShapeA, hshape']
      · subst a
        subst b
        simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR,
          Context.typeuseShapeA, hshape']
  | idx x =>
      cases hx : C.types[x.val]? with
      | none => simp [Context.typeuseShape, hx] at hshape
      | some dt =>
          have hshape' : C.typeuseShape (.defd dt) = some b := by
            simpa [Context.typeuseShape, hx] using hshape
          have hshapeDt : dt.absShape = some b := by
            simpa [Context.typeuseShape] using hshape'
          rcases hclass with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · subst a
            simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR, hx]
          · subst a
            rcases hb with hb | hb <;> subst b <;>
              simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR, hx,
                Context.typeuseShapeA, hshapeDt]
          · subst a
            subst b
            simp [decHeaptypeSubN, Context.resolveIdx, decHeapSubR, hx,
              Context.typeuseShapeA, hshapeDt]

/-- Heap subtyping is decidable-complete at grammar heap-type endpoints in
any ordinary module-validation context backed by a checked type section.
Recursive scratch references and literal defined types are deliberately not
grammar heap types; the former are handled while checking recursive groups,
and the latter are the normalized representation stored in `C.types`. -/
theorem Types_okA.decHeaptypeSubN_complete_of_syn
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (hrecs : C.recs = [])
    {left right : HeapType}
    (hleftSyn : left.isSyn = true) (hleftOk : Heaptype_okA C left)
    (hrightSyn : right.isSyn = true) (hrightOk : Heaptype_okA C right)
    (hsub : Heaptype_subA C left right) :
    decHeaptypeSubN C C.subtypeFuel left right = true := by
  have henv : C.ValidHeapShapesA :=
    htypesOk.validHeapShapesA_in_context htds C htypes hrecs
  cases left with
  | abs a =>
      cases right with
      | abs b =>
          exact hsub.decHeaptypeSubN_complete_of_abs_abs henv
      | use tu =>
          obtain ⟨b, hgood⟩ := henv hrightOk
          apply hsub.decHeaptypeSubN_complete_of_abs_nonrec_use henv hgood
          intro i hi
          subst tu
          simp [HeapType.isSyn, TypeUse.isSyn] at hrightSyn
  | use tu =>
      cases hleftOk with
      | typeuse htuOk =>
          exact htypesOk.decHeaptypeSub_complete_of_syn_typeuse_in_context
            htds htypes hleftSyn htuOk hsub

end WasmGemmGnaf.Wasm.Core
