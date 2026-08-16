import WasmGemmGnaf.Wasm.Core.ValidateContextSources

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

def Instr.directSourceSpecialA : Instr → Bool
  | .unreachable | .drop | .select none | .br _ | .brTable _ _
  | .brOnNull _ | .brOnNonNull _ | .brOnCast _ _ _
  | .brOnCastFail _ _ _ | .ret | .returnCall _ | .returnCallRef _
  | .returnCallIndirect _ _ | .throw _ | .throwRef | .refIsNull
  | .refAsNonNull | .refTest _ | .refCast _ | .externConvertAny
  | .anyConvertExtern | .block _ _ | .loop _ _ | .ifElse _ _ _
  | .tryTable _ _ _ => true
  | _ => false

private theorem all_hasDefault_of_defaultable_source {ts : List ValType}
    (h : SeqAll Defaultable ts) : ts.all ValType.hasDefault = true := by
  rw [List.all_eq_true]
  intro t ht
  cases h t ht with
  | mk hd => exact hd

/-- Completeness of the fixed-type instruction dispatcher at checked source
endpoints.  The six subtype decisions in the dispatcher are fed only by
syntax or by source-provenant context components. -/
theorem instrDispatch_complete_of_source {C : Context} {i : Instr}
    {it : InstrType} (htypes : SourceTypeCompleteA C) (hC : C.SourceA)
    (hsyn : Instr.isSyn i = true)
    (hspecial : Instr.directSourceSpecialA i = false)
    (h : Instr_okA C i it) :
    (match instrTypeA C i with
      | some it => some it
      | none => instrType C i) = some it := by
  have hwf : Instr.wf i = true := h.wf_of
  cases h <;> simp_all only [Instr.directSourceSpecialA]
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Defaultable _›
  all_goals try cases ‹Option LoadOp›
  all_goals try cases ‹Option StoreOp›
  all_goals try cases ‹FieldType›
  case call_indirect =>
    have hleft := hC.tables (by assumption)
    have hright : RefType.funcref.SourceA C := trivial
    have hdecRef := htypes.reftypeComplete hleft hright (by assumption)
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case array_new_elem =>
    rename_i x y dt m rt rt' hx helem hsub hexpand
    have hleft : rt'.SourceA C := hC.elems helem
    have hcomp := htypes.compSource hx (Expand.mk hexpand)
    have hright : rt.SourceA C := hcomp
    have hdecRef := htypes.reftypeComplete hleft hright hsub
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case array_copy =>
    rename_i x₁ x₂ dt₁ dt₂ zt₁ zt₂ m hx₁ hx₂ hsub hexpand₂ hexpand₁
    have hcomp₁ := htypes.compSource hx₁ (Expand.mk hexpand₁)
    have hcomp₂ := htypes.compSource hx₂ (Expand.mk hexpand₂)
    have hleft : zt₂.SourceA C := hcomp₂
    have hright : zt₁.SourceA C := hcomp₁
    have hdecStorage := htypes.storageComplete hleft hright hsub
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case array_init_elem =>
    rename_i x y dt zt rt hx helem hsub hexpand
    have href : rt.SourceA C := hC.elems helem
    have hleft : (StorageType.val (.ref rt)).SourceA C := href
    have hcomp := htypes.compSource hx (Expand.mk hexpand)
    have hright : zt.SourceA C := hcomp
    have hdecStorage := htypes.storageComplete hleft hright hsub
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case table_copy =>
    rename_i x₁ x₂ tt₁ tt₂ hx₁ hx₂ hsub
    have hleft : tt₂.elem.SourceA C := hC.tables hx₂
    have hright : tt₁.elem.SourceA C := hC.tables hx₁
    have hdecRef := htypes.reftypeComplete hleft hright hsub
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case table_init =>
    have hleft := hC.elems (by assumption)
    have hright := hC.tables (by assumption)
    have hdecRef := htypes.reftypeComplete hleft hright (by assumption)
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  all_goals try
    have hcheckVal := checkValtypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)
  all_goals try
    have hcheckHeap := checkHeaptypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)
  all_goals try
    have hdefaults := all_hasDefault_of_defaultable_source (by assumption)
  all_goals try
    rw [checkValtypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)]
  all_goals try
    rw [checkHeaptypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)]
  all_goals
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, StorageType.isUnpacked, ValType.hasDefault, VecType.size]
  case select_expl =>
    have hc : checkValtypeOkA C _ = true :=
      checkValtypeOkA_complete
        (by simpa [Instr.isSyn] using hsyn) (by assumption)
    simp [hc]
  case ref_null =>
    have hc : checkHeaptypeOkA C _ = true :=
      checkHeaptypeOkA_complete
        (by simpa [Instr.isSyn] using hsyn) (by assumption)
    simp [hc]
  case struct_get.mk.mk =>
    simp [FieldType.storage]

private theorem checkInstrA_eq_source_dispatch {C : Context} {st : St}
    {i : Instr} (h : Instr.directSourceSpecialA i = false) :
    checkInstrA C st i =
      (match instrTypeA C i with
       | some it => (applyTypeA C st it).map (it.locals, ·)
       | none => match instrType C i with
         | some it => (applyTypeA C st it).map (it.locals, ·)
         | none => none) := by
  cases i <;> try rfl
  case select ts =>
    cases ts with
    | none => simp [Instr.directSourceSpecialA] at h
    | some _ => rfl
  all_goals simp [Instr.directSourceSpecialA] at h

/-- Frame-preserving completeness for every fixed-type opcode, using only the
checked source graph and source-provenant context lookups. -/
theorem instrDefault_complete_of_source {C : Context} {i : Instr}
    {it : InstrType} (htypes : SourceTypeCompleteA C) (hC : C.SourceA)
    (hsyn : Instr.isSyn i = true)
    (hspecial : Instr.directSourceSpecialA i = false)
    (hok : Instr_okA C i it) {frame : List ValType} {st : St}
    (hsat : St.SatA C st (frame ++ it.dom)) :
    ∃ st', checkInstrA C st i = some (it.locals, st') ∧
      St.SatA C st' (frame ++ it.cod) := by
  have htype := instrDispatch_complete_of_source htypes hC hsyn hspecial hok
  obtain ⟨st', happly, hout⟩ := applyTypeA_complete_frame hsat
  refine ⟨st', ?_, hout⟩
  rw [checkInstrA_eq_source_dispatch hspecial]
  cases ha : instrTypeA C i with
  | some jt =>
      simp only [ha, Option.some.injEq] at htype
      subst jt
      simp [happly]
  | none =>
      simp only [ha] at htype ⊢
      cases hl : instrType C i with
      | none => simp only [hl] at htype; contradiction
      | some jt =>
          simp only [hl, Option.some.injEq] at htype
          subst jt
          simp [happly]

/-- The fixed dispatcher can only expose operand/result heap leaves carried
by syntax or by a source-provenant context lookup.  Free stack-polymorphic
types occur only in the direct-special arms excluded by this theorem. -/
theorem instrDispatch_result_source {C : Context} {i : Instr}
    {it : InstrType} (htypes : SourceTypeCompleteA C) (hC : C.SourceA)
    (hsyn : Instr.isSyn i = true)
    (hspecial : Instr.directSourceSpecialA i = false)
    (h : Instr_okA C i it) :
    ResultSourceA C it.dom ∧ ResultSourceA C it.cod := by
  cases h <;> simp_all only [Instr.directSourceSpecialA]
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Defaultable _›
  all_goals try cases ‹Option LoadOp›
  all_goals try cases ‹Option StoreOp›
  all_goals try cases ‹FieldType›
  case select_expl =>
    have ht := Valtype_okA.sourceA_of_syn
      (by simpa [Instr.isSyn] using hsyn) (by assumption)
    simp_all [ResultSourceA, ValType.i32, ValType.SourceA]
  case br_if =>
    have hs := hC.labels (by assumption)
    exact ⟨ResultSourceA.append hs
      (by simp [ResultSourceA, ValType.i32, ValType.SourceA]), hs⟩
  case call.mk =>
    have hc := hC.funcs (by assumption) (Expand.mk (by assumption))
    simpa [ResultSourceA, CompType.SourceA] using hc
  case call_ref.mk =>
    have hc := hC.types (by assumption) (Expand.mk (by assumption))
    have hi := htypes.idxSource (by assumption)
    exact ⟨ResultSourceA.append hc.1 (ResultSourceA.singleton hi), hc.2⟩
  case call_indirect.mk =>
    have hc := hC.types (by assumption) (Expand.mk (by assumption))
    exact ⟨ResultSourceA.append hc.1
      (by simp [ResultSourceA, AddrType.toValType, AddrType.toNumType,
        ValType.SourceA]), hc.2⟩
  case ref_null =>
    have hh := Heaptype_okA.sourceA_of_syn
      (by simpa [Instr.isSyn] using hsyn) (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case ref_func =>
    have hh := hC.funcHeap (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case ref_eq =>
    simp [ResultSourceA, RefType.eqref, ValType.SourceA,
      RefType.SourceA, HeapType.SourceA]
  case i31_get =>
    simp [ResultSourceA, RefType.i31ref, ValType.SourceA,
      RefType.SourceA, HeapType.SourceA]
  case struct_new.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    have hi := htypes.idxSource (by assumption)
    refine ⟨FieldTypes.sourceA_unpacked hc, ?_⟩
    simpa [ResultSourceA, ValType.SourceA, RefType.SourceA] using hi
  case struct_new_default.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case struct_get.mk.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    have hf := hc _ (List.mem_of_getElem? (by assumption))
    have hi := htypes.idxSource (by assumption)
    have hu := hf.unpack
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case struct_set.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    have hf := hc _ (List.mem_of_getElem? (by assumption))
    have hi := htypes.idxSource (by assumption)
    have hu := hf.unpack
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case array_new.mk.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    simp only [CompType.SourceA, FieldType.SourceA] at hc
    have hu := hc.unpack
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case array_new_default.mk.mk.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case array_new_fixed.mk.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    simp only [CompType.SourceA, FieldType.SourceA] at hc
    have hu := hc.unpack
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case array_new_elem.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_new_data.mk.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_get.mk.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    simp only [CompType.SourceA, FieldType.SourceA] at hc
    have hu := hc.unpack
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
      FieldType.storage]
  case array_set.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    simp only [CompType.SourceA, FieldType.SourceA] at hc
    have hu := hc.unpack
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_len =>
    simp [ResultSourceA, RefType.arrayref, ValType.SourceA,
      RefType.SourceA, HeapType.SourceA]
  case array_fill.mk =>
    have hc := htypes.compSource (by assumption) (Expand.mk (by assumption))
    simp only [CompType.SourceA, FieldType.SourceA] at hc
    have hu := hc.unpack
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_copy.mk.mk =>
    rename_i x₁ x₂ dt₁ dt₂ zt₁ zt₂ m hx₁ hx₂ hsub hexpand₂ hexpand₁
    have hi₁ := htypes.idxSource hx₁
    have hi₂ := htypes.idxSource hx₂
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_init_elem.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case array_init_data.mk =>
    have hi := htypes.idxSource (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA]
  case local_get =>
    have ht := hC.locals (by assumption)
    simp_all [ResultSourceA]
  case local_set =>
    have ht := hC.locals (by assumption)
    simp_all [ResultSourceA]
  case local_tee =>
    have ht := hC.locals (by assumption)
    simp_all [ResultSourceA]
  case global_get =>
    have ht := hC.globals (by assumption)
    simp_all [ResultSourceA]
  case global_set =>
    have ht := hC.globals (by assumption)
    simp_all [ResultSourceA]
  case table_get =>
    have ht := hC.tables (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, AddrType.toValType,
      AddrType.toNumType]
  case table_set =>
    have ht := hC.tables (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, AddrType.toValType,
      AddrType.toNumType]
  case table_grow =>
    have ht := hC.tables (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, AddrType.toValType,
      AddrType.toNumType]
  case table_fill =>
    have ht := hC.tables (by assumption)
    simp_all [ResultSourceA, ValType.SourceA, AddrType.toValType,
      AddrType.toNumType]
  all_goals simp_all [ResultSourceA, ValType.SourceA, RefType.SourceA,
    HeapType.SourceA, StorageType.SourceA, FieldType.SourceA,
    AddrType.toValType, AddrType.toNumType]

/-- Fixed-dispatch completeness together with preservation of source-ranked
operand-stack provenance. -/
theorem instrDefault_complete_source_state {C : Context} {i : Instr}
    {it : InstrType} (htypes : SourceTypeCompleteA C) (hC : C.SourceA)
    (hsyn : Instr.isSyn i = true)
    (hspecial : Instr.directSourceSpecialA i = false)
    (hok : Instr_okA C i it) {frame : List ValType} {st : St}
    (hstSource : St.SourceA C st)
    (hsat : St.SatA C st (frame ++ it.dom)) :
    ∃ st', checkInstrA C st i = some (it.locals, st') ∧
      St.SatA C st' (frame ++ it.cod) ∧ St.SourceA C st' := by
  have htype := instrDispatch_complete_of_source htypes hC hsyn hspecial hok
  have hsource := instrDispatch_result_source htypes hC hsyn hspecial hok
  obtain ⟨st', happly, hout⟩ := applyTypeA_complete_frame hsat
  have houtSource := hstSource.of_applyTypeA hsource.2 happly
  refine ⟨st', ?_, hout, houtSource⟩
  rw [checkInstrA_eq_source_dispatch hspecial]
  cases ha : instrTypeA C i with
  | some jt =>
      simp only [ha, Option.some.injEq] at htype
      subst jt
      simp [happly]
  | none =>
      simp only [ha] at htype ⊢
      cases hl : instrType C i with
      | none => simp only [hl] at htype; contradiction
      | some jt =>
          simp only [hl, Option.some.injEq] at htype
          subst jt
          simp [happly]

end Validate
end WasmGemmGnaf.Wasm.Core
