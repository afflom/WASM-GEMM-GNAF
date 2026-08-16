/-
  Full module-level reflection for the amended Core validator.

  This layer uses the source-restricted `checkSeqA` completeness theorem.  It
  deliberately leaves the legacy fragment checker in `Validate.lean` intact;
  the public facade selects the full checker once both directions below are
  established.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeTransport
import WasmGemmGnaf.Wasm.Core.ValidateModuleSources
import WasmGemmGnaf.Wasm.Core.ValidateSeqCompleteClosure
import WasmGemmGnaf.Wasm.Core.ValidateStoredCompOk
import WasmGemmGnaf.Wasm.Core.ValidateTypesFullComplete

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## Source provenance to semantic context validity -/

/-- The stored raw/closed type invariant is stable when only non-type context
components change. -/
theorem _root_.WasmGemmGnaf.Wasm.Core.Context.StoredDeftypesOkA.transport
    {C D : Context} (hCD : SameTypeEnv C D)
    (h : C.StoredDeftypesOkA) : D.StoredDeftypesOkA := by
  constructor
  · intro i dt hlookup
    exact Deftype_okA.transport hCD.1 hCD.2
      (h.1 (by simpa [hCD.1] using hlookup))
  · intro i dt hlookup
    exact Deftype_okA.transport hCD.1 hCD.2
      (h.2 (by simpa [hCD.1] using hlookup))

/-- Checked-source provenance plus semantic validity of every stored raw and
closed defined type reconstructs the validator's exact semantic context
invariant. -/
theorem _root_.WasmGemmGnaf.Wasm.Core.Context.SourceA.validA_of_stored
    {C : Context} (hsource : C.SourceA)
    (hstored : C.StoredDeftypesOkA) : Context.ValidA C := by
  constructor
  · intro D hD x dt ct hlookup hexpand
    exact Comptype_okA.transport hD.1 hD.2
      ((hsource.types hlookup hexpand).ok_of_stored hstored)
  · intro D hD x dt ct hlookup hexpand
    exact Comptype_okA.transport hD.1 hD.2
      ((hsource.funcs hlookup hexpand).ok_of_stored hstored)
  · intro D hD x dt hlookup
    exact Heaptype_okA.transport hD.1 hD.2
      ((hsource.funcHeap hlookup).ok_of_stored hstored)
  · intro D hD x jt dt dom hlookup hasDef hexpand
    apply Resulttype_okA.transport hD.1 hD.2
    exact .mk (fun t ht =>
      (hsource.tags hlookup hasDef hexpand t ht).ok_of_stored hstored)
  · intro D hD x gt hlookup
    exact Valtype_okA.transport hD.1 hD.2
      ((hsource.globals hlookup).ok_of_stored hstored)
  · intro D hD x tt hlookup
    exact Reftype_okA.transport hD.1 hD.2
      ((hsource.tables hlookup).ok_of_stored hstored)
  · intro D hD x rt hlookup
    exact Reftype_okA.transport hD.1 hD.2
      ((hsource.elems hlookup).ok_of_stored hstored)
  · intro D hD x lt hlookup
    exact Valtype_okA.transport hD.1 hD.2
      ((hsource.locals hlookup).ok_of_stored hstored)
  · intro D hD x ts hlookup
    apply Resulttype_okA.transport hD.1 hD.2
    exact .mk (fun t ht =>
      (hsource.labels hlookup t ht).ok_of_stored hstored)
  · intro D hD ts hret
    apply Resulttype_okA.transport hD.1 hD.2
    exact .mk (fun t ht =>
      (hsource.ret hret t ht).ok_of_stored hstored)

/-- Constructor-shaped form of `Module_okA.stageSource`.  The existential
public helper intentionally hides the judgment's staged contexts; module
completeness needs the same proof before that information is erased. -/
private theorem stageSourceExactA
    {m : Module} {C C' : Context} {dts' : List DefType}
    {xtsI : List ExternType} {jts : List TagType}
    {gts : List GlobalType} {mts : List MemType} {tts : List TableType}
    {dts : List DefType} {oks : List DataType} {rts : List ElemType}
    {jtsI : List TagType} {gtsI : List GlobalType}
    {mtsI : List MemType} {ttsI : List TableType}
    {dtsI : List DefType} {xs : List FuncIdx}
    (hsyn : m.isSyn = true)
    (htypes : Types_okA Context.empty m.types dts')
    (himpLen : SeqLen₂ m.imports xtsI)
    (himp : SeqAll₂ (Import_okA { Context.empty with types := dts' })
      m.imports xtsI)
    (htagLen : SeqLen₂ m.tags jts)
    (htags : SeqAll₂ (Tag_okA C') m.tags jts)
    (hglobals : Globals_okA C' m.globals gts)
    (htableLen : SeqLen₂ m.tables tts)
    (htables : SeqAll₂ (Table_okA C') m.tables tts)
    (hfuncLen : SeqLen₂ m.funcs dts)
    (hfuncs : SeqAll₂ (Func_okA C) m.funcs dts)
    (helemLen : SeqLen₂ m.elems rts)
    (helems : SeqAll₂ (Elem_okA C) m.elems rts)
    (hC : C = Context.append C'
      { tags := jtsI ++ jts, globals := gts, mems := mtsI ++ mts,
        tables := ttsI ++ tts, datas := oks, elems := rts })
    (hC' : C' =
      { types := dts', globals := gtsI, funcs := dtsI ++ dts, refs := xs })
    (hjtsI : jtsI = ExternType.tags xtsI)
    (hgtsI : gtsI = ExternType.globals xtsI)
    (httsI : ttsI = ExternType.tables xtsI)
    (hdtsI : funcsXt xtsI = some dtsI) :
    C.SourceA ∧ C'.SourceA := by
  simp only [Module.isSyn, Bool.and_eq_true] at hsyn
  rcases hsyn with
    ⟨⟨⟨⟨⟨⟨⟨htypesSyn, himportsSyn⟩, htagsSyn⟩,
      hglobalsSyn⟩, htablesSyn⟩, hfuncsSyn⟩, hdatasSyn⟩,
      helemsSyn⟩
  let B : Context := { Context.empty with types := dts' }
  have htypesB : SourceTypeCompleteA B := {
    tds := m.types
    dts := dts'
    syn := htypesSyn
    typesOk := htypes
    types := rfl
    recs := rfl
  }
  have hC'types : C'.types = dts' := by
    rw [hC']
  have hC'recs : C'.recs = [] := by
    rw [hC']
  have hCtypes : C.types = dts' := by
    rw [hC, hC']
    simp [Context.append]
  have hCrecs : C.recs = [] := by
    rw [hC, hC']
    simp [Context.append]
  have htypesC' : SourceTypeCompleteA C' := {
    tds := m.types
    dts := dts'
    syn := htypesSyn
    typesOk := htypes
    types := hC'types
    recs := hC'recs
  }
  have htypesC : SourceTypeCompleteA C := {
    tds := m.types
    dts := dts'
    syn := htypesSyn
    typesOk := htypes
    types := hCtypes
    recs := hCrecs
  }
  have hBC' : SameTypeEnv B C' := by
    constructor
    · simpa [B] using hC'types.symm
    · change [] = C'.recs
      exact hC'recs.symm
  have hCC' : SameTypeEnv C C' :=
    ⟨hCtypes.trans hC'types.symm, hCrecs.trans hC'recs.symm⟩
  have hBC : SameTypeEnv B C :=
    ⟨by simpa [B] using hCtypes.symm,
      by change [] = C.recs; exact hCrecs.symm⟩
  have hC'C : SameTypeEnv C' C := hCC'.symm
  have himpOk :
      SeqAll (fun i : Import => Externtype_okA B i.externtype)
        m.imports :=
    imports_extern_ok himpLen himp
  have hxtsEq :
      xtsI = m.imports.map (fun i => B.closExternType i.externtype) :=
    imports_types_eq_of_isSyn m.imports xtsI himpLen himp
  have hdtsIClosed : funcsXt
      (m.imports.map (fun i => B.closExternType i.externtype)) =
        some dtsI := by
    rw [← hxtsEq]
    exact hdtsI
  have himpGlobalsB : ∀ gt ∈ gtsI, gt.valtype.SourceA B := by
    rw [hgtsI, hxtsEq]
    exact globals_closExternType_source htypesB m.imports
      himportsSyn himpOk
  have himpTagsB :
      ∀ jt ∈ jtsI, (HeapType.use jt).SourceA B := by
    rw [hjtsI, hxtsEq]
    exact tags_closExternType_source htypesB m.imports
      himportsSyn himpOk
  have himpTablesB : ∀ tt ∈ ttsI, tt.elem.SourceA B := by
    rw [httsI, hxtsEq]
    exact tables_closExternType_source htypesB m.imports
      himportsSyn himpOk
  have hdefTagsC' : ∀ jt ∈ jts, (HeapType.use jt).SourceA C' :=
    tags_source htypesC' htagsSyn htagLen htags
  have hdefGlobalsC' : ∀ gt ∈ gts, gt.valtype.SourceA C' :=
    Globals_okA.source htypesC' hglobalsSyn hglobals
  have hdefTablesC' : ∀ tt ∈ tts, tt.elem.SourceA C' :=
    tables_source htablesSyn htableLen htables
  have hElemsC : ∀ rt ∈ rts, rt.SourceA C :=
    elems_source helemsSyn helemLen helems
  have hC'Funcs : C'.funcs = dtsI ++ dts := by
    rw [hC']
  have hC'Globals : C'.globals = gtsI := by
    rw [hC']
  have hC'Source : C'.SourceA := by
    constructor
    · intro x dt ct hx he
      exact htypesC'.compSource hx he
    · intro x dt ct hx he
      have hmem : dt ∈ dtsI ++ dts := by
        rw [hC'Funcs] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact (htypesB.funcsXtCompSource himportsSyn hdtsIClosed
            himp he).of_types_eq hBC'.1 hBC'.2
      · exact CompType.SourceA.of_types_eq hCC'.1 hCC'.2
          ((funcs_source htypesC hfuncLen hfuncs hdef).2 he)
    · intro x dt hx
      have hmem : dt ∈ dtsI ++ dts := by
        rw [hC'Funcs] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact (HeapType.sourceA_of_funcsXt_closExternType
            htypesB.recs himportsSyn hdtsIClosed himp).of_types_eq
          hBC'.1 hBC'.2
      · exact HeapType.SourceA.of_types_eq hCC'.1 hCC'.2
          (funcs_source htypesC hfuncLen hfuncs hdef).1
    · intro x jt dt dom hx hj he
      rw [hC'] at hx
      simp at hx
    · intro x gt hx
      have hmem : gt ∈ gtsI := by
        rw [hC'Globals] at hx
        exact List.mem_of_getElem? hx
      exact (himpGlobalsB gt hmem).of_types_eq hBC'.1 hBC'.2
    · intro x tt hx
      rw [hC'] at hx
      simp at hx
    · intro x rt hx
      rw [hC'] at hx
      simp at hx
    · intro x lt hx
      rw [hC'] at hx
      simp at hx
    · intro x ts hx
      rw [hC'] at hx
      simp at hx
    · intro ts hx
      rw [hC'] at hx
      simp at hx
  have hCFuncs : C.funcs = dtsI ++ dts := by
    rw [hC, hC']
    simp [Context.append]
  have hCTags : C.tags = jtsI ++ jts := by
    rw [hC, hC']
    simp [Context.append]
  have hCGlobals : C.globals = gtsI ++ gts := by
    rw [hC, hC']
    simp [Context.append]
  have hCTables : C.tables = ttsI ++ tts := by
    rw [hC, hC']
    simp [Context.append]
  have hCElems : C.elems = rts := by
    rw [hC, hC']
    simp [Context.append]
  have hCSource : C.SourceA := by
    constructor
    · intro x dt ct hx he
      exact htypesC.compSource hx he
    · intro x dt ct hx he
      have hmem : dt ∈ dtsI ++ dts := by
        rw [hCFuncs] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact CompType.SourceA.of_types_eq hBC.1 hBC.2
          (htypesB.funcsXtCompSource himportsSyn hdtsIClosed himp he)
      · exact (funcs_source htypesC hfuncLen hfuncs hdef).2 he
    · intro x dt hx
      have hmem : dt ∈ dtsI ++ dts := by
        rw [hCFuncs] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact HeapType.SourceA.of_types_eq hBC.1 hBC.2
          (HeapType.sourceA_of_funcsXt_closExternType
            htypesB.recs himportsSyn hdtsIClosed himp)
      · exact (funcs_source htypesC hfuncLen hfuncs hdef).1
    · intro x jt dt dom hx hj he
      have hmem : jt ∈ jtsI ++ jts := by
        rw [hCTags] at hx
        exact List.mem_of_getElem? hx
      have hsource : (HeapType.use jt).SourceA C := by
        rcases List.mem_append.mp hmem with himp | hdef
        · exact HeapType.SourceA.of_types_eq hBC.1 hBC.2
            (himpTagsB jt himp)
        · exact HeapType.SourceA.of_types_eq hC'C.1 hC'C.2
            (hdefTagsC' jt hdef)
      exact htypesC.tagDomSource hsource hj he
    · intro x gt hx
      have hmem : gt ∈ gtsI ++ gts := by
        rw [hCGlobals] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact ValType.SourceA.of_types_eq hBC.1 hBC.2
          (himpGlobalsB gt himp)
      · exact ValType.SourceA.of_types_eq hC'C.1 hC'C.2
          (hdefGlobalsC' gt hdef)
    · intro x tt hx
      have hmem : tt ∈ ttsI ++ tts := by
        rw [hCTables] at hx
        exact List.mem_of_getElem? hx
      rcases List.mem_append.mp hmem with himp | hdef
      · exact RefType.SourceA.of_types_eq hBC.1 hBC.2
          (himpTablesB tt himp)
      · exact RefType.SourceA.of_types_eq hC'C.1 hC'C.2
          (hdefTablesC' tt hdef)
    · intro x rt hx
      have hmem : rt ∈ rts := by
        rw [hCElems] at hx
        exact List.mem_of_getElem? hx
      exact hElemsC rt hmem
    · intro x lt hx
      rw [hC, hC'] at hx
      simp [Context.append] at hx
    · intro x ts hx
      rw [hC, hC'] at hx
      simp [Context.append] at hx
    · intro ts hx
      rw [hC, hC'] at hx
      simp [Context.append] at hx
  exact ⟨hCSource, hC'Source⟩

/-! ## Full expression and constant-expression checks -/

/-- The amended expression checker is complete on a source sequence once the
checked module context supplies semantic validity and source provenance. -/
theorem checkExprA_complete_full {C : Context} {e : Expr}
    {ts : List ValType} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hsyn : InstrSeq.isSyn e = true)
    (h : Expr_okA C e ts) : checkExprA C e ts = true := by
  cases h with
  | mk hseq =>
      obtain ⟨xs, st, hrun, hsat, _⟩ :=
        checkSeqA_complete_full e C ⟨[], [], ts⟩ hC hheap hsyn hseq
          [] (St.mk false []) (St.ValidA.empty C false)
          (St.SourceA.empty C false) ⟨St.mk false [], rfl, rfl⟩
      unfold checkExprA
      rw [hrun]
      exact St.finishA_iff_satA.mpr (by simpa using hsat)

/-- `Instr.isConst` is the executable reading of every constructor of the
declarative constant-instruction judgment. -/
theorem Instr.isConst_completeA {C : Context} {i : Instr}
    (h : Instr_const C i) : Instr.isConst C i = true := by
  cases h with
  | const hwf => simpa [Instr.isConst] using hwf
  | global_get hlookup => simp [Instr.isConst, hlookup]
  | @binop n _ hop =>
      cases n <;> rcases hop with rfl | rfl | rfl <;>
        simp [Instr.isConst, Inn.toNumType]
  | _ => rfl

/-- The full constant-expression check: amended expression typing plus the
independent constant-instruction predicate. -/
def checkConstExprFullA (C : Context) (e : Expr) (t : ValType) : Bool :=
  checkValtypeOkA C t && checkExprA C e [t] &&
    (InstrSeq.toList e).all (Instr.isConst C)

theorem checkConstExprFullA_sound {C : Context} {e : Expr} {t : ValType}
    (hC : Context.ValidA C) (h : checkConstExprFullA C e t = true) :
    Expr_ok_constA C e t := by
  simp only [checkConstExprFullA, Bool.and_eq_true] at h
  exact .mk (checkExprA_sound hC
      (ResultValidA.singleton (valValidA_of_check h.1.1)) h.1.2)
    (.mk (fun i hi => Instr.isConst_sound
      (List.all_eq_true.mp h.2 i hi)))

theorem checkConstExprFullA_complete {C : Context} {e : Expr} {t : ValType}
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (htsyn : t.isSyn = true) (ht : Valtype_okA C t)
    (hsyn : InstrSeq.isSyn e = true) (h : Expr_ok_constA C e t) :
    checkConstExprFullA C e t = true := by
  cases h with
  | mk hexpr hconst =>
      simp only [checkConstExprFullA, Bool.and_eq_true]
      refine ⟨⟨checkValtypeOkA_complete htsyn ht,
        checkExprA_complete_full hC hheap hsyn hexpr⟩, ?_⟩
      cases hconst with
      | mk hall =>
          rw [List.all_eq_true]
          intro i hi
          exact Instr.isConst_completeA (hall i hi)

/-! ## Full module-section checks -/

/-- The local state assigned by the appendix algorithm: defaultable locals are
initialized, while non-nullable reference locals start uninitialized. -/
def checkedLocalTypeA (l : Local) : LocalType :=
  if l.valtype.hasDefault then ⟨.set, l.valtype⟩
  else ⟨.unset, l.valtype⟩

@[simp] theorem checkedLocalTypeA_valtype (l : Local) :
    (checkedLocalTypeA l).valtype = l.valtype := by
  unfold checkedLocalTypeA
  split <;> rfl

def checkLocalA (C : Context) (l : Local) : Bool :=
  l.valtype.isSyn && checkValtypeOkA C l.valtype

theorem checkLocalA_sound {C : Context} {l : Local}
    (h : checkLocalA C l = true) :
    Local_okA C l (checkedLocalTypeA l) := by
  rw [checkLocalA, Bool.and_eq_true] at h
  have hvalid := checkValtypeOkA_sound h.2
  unfold checkedLocalTypeA
  split
  · exact .set hvalid (.mk (by assumption))
  · rename_i hdefault
    apply Local_okA.unset hvalid
    apply Nondefaultable.mk
    cases ht : l.valtype with
    | num _ | vec _ => simp [ht, ValType.hasDefault] at hdefault
    | bot => simp [ht, ValType.isSyn] at h
    | ref rt =>
        cases rt with
        | ref nul ht' =>
            cases nul <;> simp_all [ValType.hasDefault, ValType.noDefault]

theorem checkLocalA_complete {C : Context} {l : Local} {lt : LocalType}
    (hsyn : l.valtype.isSyn = true) (h : Local_okA C l lt) :
    checkedLocalTypeA l = lt ∧ checkLocalA C l = true := by
  cases h with
  | set hvalid hdefault =>
      cases hdefault with
      | mk hd =>
          exact ⟨by simp [checkedLocalTypeA, hd], by
            simp [checkLocalA, hsyn,
              checkValtypeOkA_complete hsyn hvalid]⟩
  | unset hvalid hnodefault =>
      cases hnodefault with
      | mk hn =>
          have hnotDefault : l.valtype.hasDefault = false := by
            cases ht : l.valtype with
            | num _ | vec _ | bot =>
                simp [ht, ValType.noDefault] at hn
            | ref rt =>
                cases rt with
                | ref nul heap =>
                    cases nul <;>
                      simp_all [ht, ValType.hasDefault, ValType.noDefault]
          exact ⟨by simp [checkedLocalTypeA, hnotDefault],
            by simp [checkLocalA, hsyn,
              checkValtypeOkA_complete hsyn hvalid]⟩

/-! ## Staged global-context closure -/

/-- Adding one semantically valid global preserves the validation invariant.
This is the exact context extension used by `Globals_okA/cons`. -/
theorem _root_.WasmGemmGnaf.Wasm.Core.Context.ValidA.appendGlobal
    {C : Context} {gt : GlobalType}
    (hC : Context.ValidA C) (hgt : ValValidA C gt.valtype) :
    Context.ValidA (Context.append C { globals := [gt] }) := by
  let E := Context.append C { globals := [gt] }
  have hCE : SameTypeEnv C E := by
    simp [E, SameTypeEnv, Context.append]
  constructor
  · intro D hD x dt ct hx he
    exact hC.types (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx) he
  · intro D hD x dt ct hx he
    exact hC.funcs (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx) he
  · intro D hD x dt hx
    exact hC.funcHeap (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx)
  · intro D hD x jt dt dom hx hj he
    exact hC.tags (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx) hj he
  · intro D hD x actual hx
    have hCD : SameTypeEnv C D := SameTypeEnv.trans hCE hD
    by_cases hold : x.val < C.globals.length
    · apply hC.globals hCD
      rw [show E.globals = C.globals ++ [gt] by rfl] at hx
      simpa [List.getElem?_append_left hold] using hx
    · have hbound : x.val < C.globals.length + 1 := by
        have := (List.getElem?_eq_some_iff.mp hx).1
        simpa [E, Context.append] using this
      have heq : x.val = C.globals.length := by omega
      have hactual : actual = gt := by
        rw [show E.globals = C.globals ++ [gt] by rfl] at hx
        rw [heq] at hx
        have hx' : some gt = some actual := by simpa using hx
        exact (Option.some.inj hx').symm
      subst actual
      exact hgt D hCD
  · intro D hD x tt hx
    exact hC.tables (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx)
  · intro D hD x rt hx
    exact hC.elems (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx)
  · intro D hD x lt hx
    exact hC.locals (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx)
  · intro D hD x ts hx
    exact hC.labels (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [E, Context.append] using hx)
  · intro D hD ts hx
    apply hC.ret (D := D) (SameTypeEnv.trans hCE hD)
    cases hr : C.ret <;> simp [E, Context.append, hr] at hx ⊢
    exact hx

/-- Source provenance is likewise stable under the staged global extension. -/
theorem _root_.WasmGemmGnaf.Wasm.Core.Context.SourceA.appendGlobal
    {C : Context} {gt : GlobalType}
    (hC : C.SourceA) (hgt : gt.valtype.SourceA C) :
    (Context.append C { globals := [gt] }).SourceA := by
  let E := Context.append C { globals := [gt] }
  have hCE : SameTypeEnv C E := by
    simp [E, SameTypeEnv, Context.append]
  constructor
  · intro x dt ct hx he
    exact (hC.types (by simpa [E, Context.append] using hx) he).of_types_eq
      hCE.1 hCE.2
  · intro x dt ct hx he
    exact (hC.funcs (by simpa [E, Context.append] using hx) he).of_types_eq
      hCE.1 hCE.2
  · intro x dt hx
    exact (hC.funcHeap (by simpa [E, Context.append] using hx)).of_types_eq
      hCE.1 hCE.2
  · intro x jt dt dom hx hj he
    exact (hC.tags (by simpa [E, Context.append] using hx) hj he).transport hCE
  · intro x actual hx
    by_cases hold : x.val < C.globals.length
    · exact (hC.globals (by
          rw [show E.globals = C.globals ++ [gt] by rfl] at hx
          simpa [List.getElem?_append_left hold] using hx)).of_types_eq
        hCE.1 hCE.2
    · have hbound : x.val < C.globals.length + 1 := by
        have := (List.getElem?_eq_some_iff.mp hx).1
        simpa [E, Context.append] using this
      have heq : x.val = C.globals.length := by omega
      have hactual : actual = gt := by
        rw [show E.globals = C.globals ++ [gt] by rfl] at hx
        rw [heq] at hx
        have hx' : some gt = some actual := by simpa using hx
        exact (Option.some.inj hx').symm
      subst actual
      exact hgt.of_types_eq hCE.1 hCE.2
  · intro x tt hx
    exact (hC.tables (by simpa [E, Context.append] using hx)).of_types_eq
      hCE.1 hCE.2
  · intro x rt hx
    exact (hC.elems (by simpa [E, Context.append] using hx)).of_types_eq
      hCE.1 hCE.2
  · intro x lt hx
    exact (hC.locals (by simpa [E, Context.append] using hx)).of_types_eq
      hCE.1 hCE.2
  · intro x ts hx
    exact (hC.labels (by simpa [E, Context.append] using hx)).transport hCE
  · intro ts hx
    apply ResultSourceA.transport hCE
    apply hC.ret
    cases hr : C.ret <;> simp [E, Context.append, hr] at hx ⊢
    exact hx

def HeapSubCompleteA.appendGlobal {C : Context} {gt : GlobalType}
    (h : HeapSubCompleteA C) (hgt : gt.valtype.SourceA C) :
    HeapSubCompleteA (Context.append C { globals := [gt] }) := by
  have hsame : SameTypeEnv C (Context.append C { globals := [gt] }) := by
    simp [SameTypeEnv, Context.append]
  exact ⟨h.types.transport hsame, h.context.appendGlobal hgt⟩

/-! ## Full external-type and tag checks -/

def checkExternTypeFullA (C : Context) : ExternType → Bool
  | .tag jt => checkFuncTypeUse C jt
  | .global gt => checkValtypeOkA C gt.valtype
  | .mem mt => checkLimits mt.lim (2 ^ 16)
  | .table tt =>
      checkLimits tt.lim (2 ^ 32 - 1) && checkReftypeOkA C tt.elem
  | .func tu => checkFuncTypeUse C tu

def checkTagFullA (C : Context) (tg : Tag) : Bool :=
  checkFuncTypeUse C tg.tagtype

theorem checkExternTypeFullA_sound {C : Context} {xt : ExternType}
    (h : checkExternTypeFullA C xt = true) : Externtype_okA C xt := by
  cases xt with
  | tag jt =>
      obtain ⟨htu, dom, cod, he⟩ := checkFuncTypeUse_sound h
      exact .tag (.mk htu he)
  | func tu =>
      obtain ⟨htu, dom, cod, he⟩ := checkFuncTypeUse_sound h
      exact .func htu he
  | global gt => exact .global (.mk (checkValtypeOkA_sound h))
  | mem mt => exact .mem (.mk (checkLimits_sound h))
  | table tt =>
      rw [checkExternTypeFullA, Bool.and_eq_true] at h
      exact .table (.mk (checkLimits_sound h.1)
        (checkReftypeOkA_sound h.2))

theorem checkExternTypeFullA_complete {C : Context} {xt : ExternType}
    (hsyn : xt.isSyn = true) (h : Externtype_okA C xt) :
    checkExternTypeFullA C xt = true := by
  cases h with
  | tag hjt =>
      cases hjt with
      | mk htu he =>
          cases htu with
          | typeidx _ => exact checkFuncTypeUse_complete he
          | rec_ _ | deftype _ => simp [ExternType.isSyn, TypeUse.isSyn] at hsyn
  | func htu he =>
      cases htu with
      | typeidx _ => exact checkFuncTypeUse_complete he
      | rec_ _ | deftype _ => simp [ExternType.isSyn, TypeUse.isSyn] at hsyn
  | global hgt =>
      cases hgt with
      | mk ht =>
          exact checkValtypeOkA_complete
            (by simpa [ExternType.isSyn, GlobalType.isSyn] using hsyn) ht
  | mem hmt => cases hmt with | mk hlim => exact checkLimits_complete hlim
  | table htt =>
      cases htt with
      | mk hlim href =>
          simp only [checkExternTypeFullA, Bool.and_eq_true]
          exact ⟨checkLimits_complete hlim,
            checkReftypeOkA_complete
              (by simpa [ExternType.isSyn, TableType.isSyn] using hsyn) href⟩

theorem checkTagFullA_sound {C : Context} {tg : Tag}
    (h : checkTagFullA C tg = true) :
    Tag_okA C tg (C.closTagType tg.tagtype) := by
  obtain ⟨htu, dom, cod, he⟩ := checkFuncTypeUse_sound h
  exact .mk (.mk htu he)

theorem checkTagFullA_complete {C : Context} {tg : Tag} {jt : TagType}
    (hsyn : tg.isSyn = true) (h : Tag_okA C tg jt) :
    jt = C.closTagType tg.tagtype ∧ checkTagFullA C tg = true := by
  cases tg with
  | mk tu =>
      cases tu with
      | idx x =>
          cases h with
          | mk hjt =>
              cases hjt with
              | mk htu he =>
                  exact ⟨rfl, checkFuncTypeUse_complete he⟩
      | recu i | defd dt => simp [Tag.isSyn, TypeUse.isSyn] at hsyn

/-- The full external-type checker determines the closed import sequence. -/
theorem importsFullA_ok {C : Context} (is : List Import)
    (h : is.all (fun i => checkExternTypeFullA C i.externtype) = true) :
    SeqAll₂ (Import_okA C) is
      (is.map (fun i => C.closExternType i.externtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst b
  exact .mk (checkExternTypeFullA_sound
    (List.all_eq_true.mp h a (List.mem_of_getElem? ha)))

/-- The full tag checker determines the closed tag-type sequence. -/
theorem tagsFullA_ok {C : Context} (tgs : List Tag)
    (h : tgs.all (checkTagFullA C) = true) :
    SeqAll₂ (Tag_okA C) tgs
      (tgs.map (fun tg => C.closTagType tg.tagtype)) := by
  intro i a b ha hb
  rw [List.getElem?_map, ha] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst b
  exact checkTagFullA_sound
    (List.all_eq_true.mp h a (List.mem_of_getElem? ha))

/-- Lockstep completeness of the full import checker. -/
theorem importsFullA_complete {C : Context} :
    ∀ (is : List Import) (xts : List ExternType),
      is.all Import.isSyn = true → is.length = xts.length →
      SeqAll₂ (Import_okA C) is xts →
      xts = is.map (fun i => C.closExternType i.externtype) ∧
        is.all (fun i => checkExternTypeFullA C i.externtype) = true := by
  intro is
  induction is with
  | nil =>
      intro xts hsyn hlen hall
      cases xts with
      | nil => exact ⟨rfl, rfl⟩
      | cons xt xts => simp at hlen
  | cons i is ih =>
      intro xts hsyn hlen hall
      cases xts with
      | nil => simp at hlen
      | cons xt xts =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 i xt rfl rfl
          obtain ⟨htail, htailCheck⟩ := ih xts hsyn.2
            (by simpa using hlen)
            (fun j a b ha hb => hall (j + 1) a b
              (by simpa using ha) (by simpa using hb))
          cases hhead with
          | mk hext =>
              refine ⟨by simp [htail], ?_⟩
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨checkExternTypeFullA_complete hsyn.1 hext, htailCheck⟩

/-- Lockstep completeness of the full tag checker. -/
theorem tagsFullA_complete {C : Context} :
    ∀ (tgs : List Tag) (jts : List TagType),
      tgs.all Tag.isSyn = true → tgs.length = jts.length →
      SeqAll₂ (Tag_okA C) tgs jts →
      jts = tgs.map (fun tg => C.closTagType tg.tagtype) ∧
        tgs.all (checkTagFullA C) = true := by
  intro tgs
  induction tgs with
  | nil =>
      intro jts hsyn hlen hall
      cases jts with
      | nil => exact ⟨rfl, rfl⟩
      | cons jt jts => simp at hlen
  | cons tg tgs ih =>
      intro jts hsyn hlen hall
      cases jts with
      | nil => simp at hlen
      | cons jt jts =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 tg jt rfl rfl
          obtain ⟨htail, htailCheck⟩ := ih jts hsyn.2
            (by simpa using hlen)
            (fun j a b ha hb => hall (j + 1) a b
              (by simpa using ha) (by simpa using hb))
          have hjt : jt = C.closTagType tg.tagtype := by
            cases hhead
            rfl
          refine ⟨by simp [hjt, htail], ?_⟩
          simp only [List.all_cons, Bool.and_eq_true]
          exact ⟨(checkTagFullA_complete hsyn.1 hhead).2, htailCheck⟩

/-! ## Staged globals -/

def checkGlobalsFullA : Context → List Global → Option (List GlobalType)
  | _, [] => some []
  | C, g :: gs =>
      if checkValtypeOkA C g.globaltype.valtype &&
          checkConstExprFullA C g.init g.globaltype.valtype then
        match checkGlobalsFullA
            (Context.append C { globals := [g.globaltype] }) gs with
        | some gts => some (g.globaltype :: gts)
        | none => none
      else none

theorem checkGlobalsFullA_sound : ∀ {C : Context} {gs : List Global}
    {gts : List GlobalType}, Context.ValidA C →
    gs.all Global.isSyn = true →
    checkGlobalsFullA C gs = some gts → Globals_okA C gs gts := by
  intro C gs
  induction gs generalizing C with
  | nil =>
      intro gts hC hsyn hcheck
      simp only [checkGlobalsFullA, Option.some.injEq] at hcheck
      subst gts
      exact .empty
  | cons g gs ih =>
      intro gts hC hsyn hcheck
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      rw [checkGlobalsFullA] at hcheck
      split at hcheck
      · rename_i hhead
        rw [Bool.and_eq_true] at hhead
        cases htail : checkGlobalsFullA
            (Context.append C { globals := [g.globaltype] }) gs with
        | none => simp only [htail] at hcheck; contradiction
        | some tail =>
            simp only [htail, Option.some.injEq, List.cons.injEq] at hcheck
            obtain ⟨rfl, rfl⟩ := hcheck
            have hgt : Valtype_okA C g.globaltype.valtype :=
              checkValtypeOkA_sound hhead.1
            have hgtValid : ValValidA C g.globaltype.valtype := by
              intro D hD
              exact Valtype_okA.transport hD.1 hD.2 hgt
            exact .cons
              (.mk (.mk hgt) (checkConstExprFullA_sound hC hhead.2))
              (ih (WasmGemmGnaf.Wasm.Core.Context.ValidA.appendGlobal
                hC hgtValid) hsyn.2 htail)
      · contradiction

theorem checkGlobalsFullA_complete : ∀ {C : Context} {gs : List Global}
    {gts : List GlobalType}, Context.ValidA C → HeapSubCompleteA C →
    gs.all Global.isSyn = true → Globals_okA C gs gts →
    checkGlobalsFullA C gs = some gts := by
  intro C gs
  induction gs generalizing C with
  | nil =>
      intro gts hC hheap hsyn hvalid
      cases hvalid
      rfl
  | cons g gs ih =>
      intro gts hC hheap hsyn hvalid
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      cases hvalid with
      | cons hglobal htail =>
          cases hglobal with
          | mk hgt hconst =>
              cases hgt with
              | mk hval =>
                  have hgsyn : g.globaltype.isSyn = true ∧
                      g.init.isSyn = true := by
                    simpa [Global.isSyn] using hsyn.1
                  have hvalCheck := checkValtypeOkA_complete
                    (by simpa [GlobalType.isSyn] using hgsyn.1)
                    hval
                  have hconstCheck := checkConstExprFullA_complete hC hheap
                    (by simpa [GlobalType.isSyn] using hgsyn.1)
                    hval hgsyn.2 hconst
                  have hvalValid : ValValidA C g.globaltype.valtype := by
                    intro D hD
                    exact Valtype_okA.transport hD.1 hD.2 hval
                  have hvalSource : g.globaltype.valtype.SourceA C :=
                    hval.sourceA_of_syn
                      (by simpa [GlobalType.isSyn] using hgsyn.1)
                  have htailCheck := ih
                    (WasmGemmGnaf.Wasm.Core.Context.ValidA.appendGlobal
                      hC hvalValid)
                    (hheap.appendGlobal hvalSource) hsyn.2 htail
                  simp [checkGlobalsFullA, hvalCheck, hconstCheck, htailCheck]

/-- The staged global fold exposes heap-source provenance before expression
soundness needs the semantic context invariant. -/
theorem checkGlobalsFullA_sources : ∀ {C : Context} {gs : List Global}
    {gts : List GlobalType}, gs.all Global.isSyn = true →
    checkGlobalsFullA C gs = some gts →
    ∀ gt ∈ gts, gt.valtype.SourceA C := by
  intro C gs
  induction gs generalizing C with
  | nil =>
      intro gts hsyn hcheck gt hgt
      simp [checkGlobalsFullA] at hcheck
      subst gts
      simp at hgt
  | cons g gs ih =>
      intro gts hsyn hcheck gt hgt
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      rw [checkGlobalsFullA] at hcheck
      split at hcheck
      · rename_i hhead
        rw [Bool.and_eq_true] at hhead
        cases htail : checkGlobalsFullA
            (Context.append C { globals := [g.globaltype] }) gs with
        | none => simp [htail] at hcheck
        | some tail =>
            simp only [htail, Option.some.injEq, List.cons.injEq] at hcheck
            obtain ⟨rfl, rfl⟩ := hcheck
            rcases List.mem_cons.mp hgt with rfl | hgt
            · have hval := checkValtypeOkA_sound hhead.1
              have hgSyn := hsyn.1
              simp only [Global.isSyn, Bool.and_eq_true] at hgSyn
              have hvalSyn : g.globaltype.valtype.isSyn = true := by
                simpa [GlobalType.isSyn] using hgSyn.1
              exact hval.sourceA_of_syn hvalSyn
            · have hsource := ih hsyn.2 htail gt hgt
              exact ValType.SourceA.of_types_eq
                (C := Context.append C { globals := [g.globaltype] })
                (D := C) (by simp [Context.append])
                (by simp [Context.append]) hsource
      · contradiction

/-! ## Function body contexts -/

def functionBodyContextA (C : Context) (dom cod : List ValType)
    (locals : List LocalType) : Context :=
  Context.append C
    { locals := dom.map (fun t => ⟨Init.set, t⟩) ++ locals,
      labels := [cod], ret := some cod }

theorem functionBodyContextA_eq {C : Context} {dom cod : List ValType}
    {locals : List LocalType}
    (hlocals : C.locals = []) (hlabels : C.labels = [])
    (hret : C.ret = none) :
    functionBodyContextA C dom cod locals =
      { C with
        locals := dom.map (fun t => ⟨Init.set, t⟩) ++ locals,
        labels := [cod], ret := some cod } := by
  cases C
  simp_all [functionBodyContextA, Context.append]

theorem _root_.WasmGemmGnaf.Wasm.Core.Context.ValidA.functionBody
    {C : Context} {dom cod : List ValType} {locals : List LocalType}
    (hC : Context.ValidA C) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.ret = none)
    (hdom : ResultValidA C dom) (hcod : ResultValidA C cod)
    (hlocal : ∀ lt ∈ locals, ValValidA C lt.valtype) :
    Context.ValidA (functionBodyContextA C dom cod locals) := by
  let E := functionBodyContextA C dom cod locals
  have hCE : SameTypeEnv C E := by
    simp [E, functionBodyContextA, SameTypeEnv, Context.append]
  have hshape := functionBodyContextA_eq
    (dom := dom) (cod := cod) (locals := locals) hlocals hlabels hret
  constructor
  · intro D hD x dt ct hx he
    exact hC.types (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx) he
  · intro D hD x dt ct hx he
    exact hC.funcs (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx) he
  · intro D hD x dt hx
    exact hC.funcHeap (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx)
  · intro D hD x jt dt ds hx hj he
    exact hC.tags (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx) hj he
  · intro D hD x gt hx
    exact hC.globals (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx)
  · intro D hD x tt hx
    exact hC.tables (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx)
  · intro D hD x rt hx
    exact hC.elems (D := D) (SameTypeEnv.trans hCE hD)
      (by simpa [hshape] using hx)
  · intro D hD x lt hx
    have hmem : lt ∈ dom.map (fun t => ⟨Init.set, t⟩) ++ locals := by
      rw [hshape] at hx
      exact List.mem_of_getElem? hx
    have hCD : SameTypeEnv C D := SameTypeEnv.trans hCE hD
    rcases List.mem_append.mp hmem with hparam | hdecl
    · obtain ⟨t, ht, heq⟩ := List.mem_map.mp hparam
      rw [← heq]
      cases hdom D hCD with
      | mk hall => exact hall t ht
    · exact hlocal lt hdecl D hCD
  · intro D hD x ts hx
    have hmem : ts ∈ [cod] := by
      rw [hshape] at hx
      exact List.mem_of_getElem? hx
    have heq : ts = cod := by simpa using hmem
    subst ts
    exact hcod D (SameTypeEnv.trans hCE hD)
  · intro D hD ts hx
    have heq : ts = cod := by
      rw [hshape] at hx
      exact (Option.some.inj hx).symm
    subst ts
    exact hcod D (SameTypeEnv.trans hCE hD)

theorem _root_.WasmGemmGnaf.Wasm.Core.Context.SourceA.functionBody
    {C : Context} {dom cod : List ValType} {locals : List LocalType}
    (hC : C.SourceA) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.ret = none)
    (hdom : ResultSourceA C dom) (hcod : ResultSourceA C cod)
    (hlocal : ∀ lt ∈ locals, lt.valtype.SourceA C) :
    (functionBodyContextA C dom cod locals).SourceA := by
  let E := functionBodyContextA C dom cod locals
  have hCE : SameTypeEnv C E := by
    simp [E, functionBodyContextA, SameTypeEnv, Context.append]
  have hshape := functionBodyContextA_eq
    (dom := dom) (cod := cod) (locals := locals) hlocals hlabels hret
  constructor
  · intro x dt ct hx he
    exact (hC.types (by simpa [hshape] using hx) he).of_types_eq hCE.1 hCE.2
  · intro x dt ct hx he
    exact (hC.funcs (by simpa [hshape] using hx) he).of_types_eq hCE.1 hCE.2
  · intro x dt hx
    exact (hC.funcHeap (by simpa [hshape] using hx)).of_types_eq hCE.1 hCE.2
  · intro x jt dt ds hx hj he
    exact (hC.tags (by simpa [hshape] using hx) hj he).transport hCE
  · intro x gt hx
    exact (hC.globals (by simpa [hshape] using hx)).of_types_eq hCE.1 hCE.2
  · intro x tt hx
    exact (hC.tables (by simpa [hshape] using hx)).of_types_eq hCE.1 hCE.2
  · intro x rt hx
    exact (hC.elems (by simpa [hshape] using hx)).of_types_eq hCE.1 hCE.2
  · intro x lt hx
    have hmem : lt ∈ dom.map (fun t => ⟨Init.set, t⟩) ++ locals := by
      rw [hshape] at hx
      exact List.mem_of_getElem? hx
    rcases List.mem_append.mp hmem with hparam | hdecl
    · obtain ⟨t, ht, heq⟩ := List.mem_map.mp hparam
      rw [← heq]
      exact (hdom t ht).of_types_eq hCE.1 hCE.2
    · exact (hlocal lt hdecl).of_types_eq hCE.1 hCE.2
  · intro x ts hx
    have hmem : ts ∈ [cod] := by
      rw [hshape] at hx
      exact List.mem_of_getElem? hx
    have heq : ts = cod := by simpa using hmem
    subst ts
    exact hcod.transport hCE
  · intro ts hx
    have heq : ts = cod := by
      rw [hshape] at hx
      exact (Option.some.inj hx).symm
    subst ts
    exact hcod.transport hCE

def HeapSubCompleteA.functionBody {C : Context}
    {dom cod : List ValType} {locals : List LocalType}
    (h : HeapSubCompleteA C) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.ret = none)
    (hdom : ResultSourceA C dom) (hcod : ResultSourceA C cod)
    (hlocal : ∀ lt ∈ locals, lt.valtype.SourceA C) :
    HeapSubCompleteA (functionBodyContextA C dom cod locals) := by
  have hsame : SameTypeEnv C (functionBodyContextA C dom cod locals) := by
    simp [SameTypeEnv, functionBodyContextA, Context.append]
  exact ⟨h.types.transport hsame,
    WasmGemmGnaf.Wasm.Core.Context.SourceA.functionBody h.context
      hlocals hlabels hret hdom hcod hlocal⟩

def checkedLocalsA (locals : List Local) : List LocalType :=
  locals.map checkedLocalTypeA

theorem checkLocalsA_complete {C : Context} :
    ∀ {locals : List Local} {lts : List LocalType},
      locals.all (fun l => l.valtype.isSyn) = true →
      SeqLen₂ locals lts → SeqAll₂ (Local_okA C) locals lts →
      lts = checkedLocalsA locals ∧
        locals.all (checkLocalA C) = true := by
  intro locals
  induction locals with
  | nil =>
      intro lts hsyn hlen hall
      cases lts with
      | nil => exact ⟨rfl, rfl⟩
      | cons lt rest => simp [SeqLen₂] at hlen
  | cons l locals ih =>
      intro lts hsyn hlen hall
      cases lts with
      | nil => simp [SeqLen₂] at hlen
      | cons lt lts =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 l lt rfl rfl
          obtain ⟨heq, hcheck⟩ := checkLocalA_complete hsyn.1 hhead
          obtain ⟨htail, htailCheck⟩ := ih hsyn.2
            (by simpa [SeqLen₂] using Nat.succ.inj hlen)
            (fun i a b ha hb => hall (i + 1) a b
              (by simpa using ha) (by simpa using hb))
          subst lt
          exact ⟨by simp [checkedLocalsA, htail], by
            simp [hcheck, htailCheck]⟩

def checkFuncFullA (C : Context) (f : Func) : Bool :=
  match C.types[f.typeidx.val]? with
  | none => false
  | some dt =>
      match funcTypeOfA dt with
      | none => false
      | some (dom, cod) =>
          f.locals.all (checkLocalA C) &&
          checkExprA
            (functionBodyContextA C dom cod (checkedLocalsA f.locals))
            f.body cod

theorem checkFuncFullA_sound {C : Context} {f : Func}
    (hC : Context.ValidA C) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.ret = none)
    (hsyn : f.isSyn = true) (h : checkFuncFullA C f = true) :
    ∃ dt : DefType, C.types[f.typeidx.val]? = some dt ∧ Func_okA C f dt := by
  unfold checkFuncFullA at h
  cases hlookup : C.types[f.typeidx.val]? with
  | none => simp only [hlookup] at h; contradiction
  | some dt =>
      simp only [hlookup] at h
      cases hft : funcTypeOfA dt with
      | none => simp only [hft] at h; contradiction
      | some p =>
          obtain ⟨dom, cod⟩ := p
          simp only [hft, Bool.and_eq_true] at h
          obtain ⟨ds, cs, rfl, rfl, hexpand⟩ := funcTypeOfA_sound hft
          have hdom := hC.typeFuncDom hlookup hexpand
          have hcod := hC.typeFuncCod hlookup hexpand
          have hlocalValid : ∀ lt ∈ checkedLocalsA f.locals,
              ValValidA C lt.valtype := by
            intro lt hlt
            obtain ⟨l, hl, heq⟩ := List.mem_map.mp hlt
            have hc := List.all_eq_true.mp h.1 l hl
            have hv := (checkLocalA_sound hc).valtype_ok
            intro D hD
            rw [← heq]
            simpa only [checkedLocalTypeA_valtype] using
              Valtype_okA.transport hD.1 hD.2 hv
          have hbodyC :=
            WasmGemmGnaf.Wasm.Core.Context.ValidA.functionBody hC
              hlocals hlabels hret hdom hcod hlocalValid
          refine ⟨dt, rfl, .mk (lcts := checkedLocalsA f.locals)
            hlookup hexpand (by simp [SeqLen₂, checkedLocalsA]) ?_ ?_⟩
          · intro i l lt hl hlt
            rw [checkedLocalsA, List.getElem?_map, hl] at hlt
            simp only [Option.map_some, Option.some.injEq] at hlt
            subst lt
            exact checkLocalA_sound
              (List.all_eq_true.mp h.1 l (List.mem_of_getElem? hl))
          · exact checkExprA_sound hbodyC
              (ResultValidA.transport (by
                simp [SameTypeEnv, functionBodyContextA, Context.append]) hcod)
              h.2

theorem checkFuncFullA_complete {C : Context} {f : Func} {dt : DefType}
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (hlocals : C.locals = []) (hlabels : C.labels = [])
    (hret : C.ret = none) (hsyn : f.isSyn = true)
    (h : Func_okA C f dt) : checkFuncFullA C f = true := by
  simp only [Func.isSyn, Bool.and_eq_true] at hsyn
  cases h with
  | @mk dom cod lcts hlookup hexpand hlen hall hbody =>
      obtain ⟨hlcts, hlocalsCheck⟩ :=
        checkLocalsA_complete hsyn.1 hlen hall
      subst lcts
      cases hexpand with
      | mk hexpand =>
          have hft : funcTypeOfA dt =
              some (ValTypes.toList dom, ValTypes.toList cod) := by
            simp [funcTypeOfA, hexpand]
          have htypeSource := hheap.context.types hlookup (Expand.mk hexpand)
          have hlocalValid : ∀ lt ∈ checkedLocalsA f.locals,
              ValValidA C lt.valtype := by
            intro lt hlt
            obtain ⟨l, hl, heq⟩ := List.mem_map.mp hlt
            have hc := List.all_eq_true.mp hlocalsCheck l hl
            have hv := (checkLocalA_sound hc).valtype_ok
            intro D hD
            rw [← heq]
            simpa only [checkedLocalTypeA_valtype] using
              Valtype_okA.transport hD.1 hD.2 hv
          have hlocalSource : ∀ lt ∈ checkedLocalsA f.locals,
              lt.valtype.SourceA C := by
            intro lt hlt
            obtain ⟨l, hl, heq⟩ := List.mem_map.mp hlt
            have hlSyn := List.all_eq_true.mp hsyn.1 l hl
            have hc := List.all_eq_true.mp hlocalsCheck l hl
            rw [← heq]
            simpa only [checkedLocalTypeA_valtype] using
              (checkLocalA_sound hc).valtype_ok.sourceA_of_syn hlSyn
          have hdomValid := hC.typeFuncDom hlookup (Expand.mk hexpand)
          have hcodValid := hC.typeFuncCod hlookup (Expand.mk hexpand)
          have hbodyC :=
            WasmGemmGnaf.Wasm.Core.Context.ValidA.functionBody hC
              hlocals hlabels hret hdomValid hcodValid hlocalValid
          have hbodyHeap := hheap.functionBody hlocals hlabels hret
            htypeSource.1 htypeSource.2 hlocalSource
          have hbodyCheck := checkExprA_complete_full hbodyC hbodyHeap
            hsyn.2 hbody
          simp [checkFuncFullA, hlookup, hft, hlocalsCheck, hbodyCheck]

/-! ## Tables, data segments, and element segments -/

def checkTableFullA (C : Context) (t : Table) : Bool :=
  checkLimits t.tabletype.lim (2 ^ 32 - 1) &&
  checkReftypeOkA C t.tabletype.elem &&
  checkConstExprFullA C t.init (.ref t.tabletype.elem)

def checkDataFullA (C : Context) (d : Data) : Bool :=
  match d.mode with
  | .passive => true
  | .active x e =>
      match C.mems[x.val]? with
      | none => false
      | some mt => checkConstExprFullA C e mt.addr.toValType

def checkElemModeFullA (C : Context) (rt : RefType) : ElemMode → Bool
  | .passive => true
  | .declare => true
  | .active x e =>
      match C.tables[x.val]? with
      | none => false
      | some tt =>
          decReftypeSubN C C.subtypeFuel rt tt.elem &&
          checkConstExprFullA C e tt.addr.toValType

def checkElemFullA (C : Context) (e : Elem) : Bool :=
  checkReftypeOkA C e.reftype &&
  e.init.all (fun ex => checkConstExprFullA C ex (.ref e.reftype)) &&
  checkElemModeFullA C e.reftype e.mode

theorem checkTableFullA_sound {C : Context} {t : Table}
    (hC : Context.ValidA C) (h : checkTableFullA C t = true) :
    Table_okA C t t.tabletype := by
  simp only [checkTableFullA, Bool.and_eq_true] at h
  exact .mk (.mk (checkLimits_sound h.1.1)
      (checkReftypeOkA_sound h.1.2))
    (checkConstExprFullA_sound hC h.2)

theorem checkTableFullA_complete {C : Context} {t : Table}
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (hsyn : t.isSyn = true) (h : Table_okA C t t.tabletype) :
    checkTableFullA C t = true := by
  simp only [Table.isSyn, Bool.and_eq_true] at hsyn
  cases h with
  | mk htt hconst =>
      cases htt with
      | mk hlim href =>
          have hrefCheck := checkReftypeOkA_complete
            (by simpa [TableType.isSyn] using hsyn.1) href
          have hconstCheck := checkConstExprFullA_complete hC hheap
            (by simpa [ValType.isSyn, TableType.isSyn] using hsyn.1)
            (.ref href) hsyn.2 hconst
          simp [checkTableFullA, checkLimits_complete hlim,
            hrefCheck, hconstCheck]

theorem checkDataFullA_sound {C : Context} {d : Data}
    (hC : Context.ValidA C) (h : checkDataFullA C d = true) :
    Data_okA C d .ok := by
  cases d with
  | mk bytes mode =>
      apply Data_okA.mk
      cases mode with
      | passive => exact .passive
      | active x e =>
          simp only [checkDataFullA] at h
          cases hlookup : C.mems[x.val]? with
          | none => simp only [hlookup] at h; contradiction
          | some mt =>
              simp only [hlookup] at h
              exact .active hlookup (checkConstExprFullA_sound hC h)

theorem checkDataFullA_complete {C : Context} {d : Data}
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (hsyn : d.isSyn = true) (h : Data_okA C d .ok) :
    checkDataFullA C d = true := by
  cases d with
  | mk bytes mode =>
      cases mode with
      | passive => rfl
      | active x e =>
          cases h with
          | mk hmode =>
              cases hmode with
              | active hlookup hconst =>
                  rename_i mt
                  have hval : Valtype_okA C mt.addr.toValType := by
                    cases mt.addr <;> exact .num .mk
                  have hconstCheck := checkConstExprFullA_complete hC hheap
                    (by cases mt.addr <;> rfl) hval
                    (by simpa [Data.isSyn, DataMode.isSyn] using hsyn) hconst
                  simp [checkDataFullA, hlookup, hconstCheck]

theorem checkElemModeFullA_sound {C : Context} {rt : RefType}
    {mode : ElemMode} (hC : Context.ValidA C)
    (h : checkElemModeFullA C rt mode = true) :
    Elemmode_okA C mode rt := by
  cases mode with
  | passive => exact .passive
  | declare => exact .declare
  | active x e =>
      cases hlookup : C.tables[x.val]? with
      | none => rw [checkElemModeFullA, hlookup] at h; contradiction
      | some tt =>
          rw [checkElemModeFullA, hlookup, Bool.and_eq_true] at h
          exact .active hlookup (decReftypeSubN_sound h.1)
            (checkConstExprFullA_sound hC h.2)

theorem checkElemModeFullA_complete {C : Context} {rt : RefType}
    {mode : ElemMode} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hrtSyn : rt.isSyn = true)
    (hmodeSyn : mode.isSyn = true) (hrt : Reftype_okA C rt)
    (h : Elemmode_okA C mode rt) : checkElemModeFullA C rt mode = true := by
  cases h with
  | passive => rfl
  | declare => rfl
  | active hlookup hsub hconst =>
      rename_i x e tt
      have hleft := hrt.sourceA_of_syn hrtSyn
      have hright := hheap.context.tables hlookup
      have hsubCheck := hheap.types.reftypeComplete hleft hright hsub
      have hval : Valtype_okA C tt.addr.toValType := by
        cases tt.addr <;> exact .num .mk
      have hconstCheck := checkConstExprFullA_complete hC hheap
        (by cases tt.addr <;> rfl) hval
        (by simpa [ElemMode.isSyn] using hmodeSyn) hconst
      simp [checkElemModeFullA, hlookup, hsubCheck, hconstCheck]

theorem checkElemFullA_sound {C : Context} {e : Elem}
    (hC : Context.ValidA C) (h : checkElemFullA C e = true) :
    Elem_okA C e e.reftype := by
  simp only [checkElemFullA, Bool.and_eq_true] at h
  exact .mk (checkReftypeOkA_sound h.1.1) (fun ex hex =>
      checkConstExprFullA_sound hC
        (List.all_eq_true.mp h.1.2 ex hex))
    (checkElemModeFullA_sound hC h.2)

theorem checkElemFullA_complete {C : Context} {e : Elem}
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (hsyn : e.isSyn = true) (h : Elem_okA C e e.reftype) :
    checkElemFullA C e = true := by
  simp only [Elem.isSyn, Bool.and_eq_true] at hsyn
  cases h with
  | mk href hinits hmode =>
      have hrefCheck := checkReftypeOkA_complete hsyn.1.1 href
      have hinitsCheck : e.init.all
          (fun ex => checkConstExprFullA C ex (.ref e.reftype)) = true := by
        rw [List.all_eq_true]
        intro ex hex
        exact checkConstExprFullA_complete hC hheap
          (by simpa [ValType.isSyn] using hsyn.1.1) (.ref href)
          (List.all_eq_true.mp hsyn.1.2 ex hex) (hinits ex hex)
      have hmodeCheck := checkElemModeFullA_complete hC hheap
        hsyn.1.1 hsyn.2 href hmode
      simp [checkElemFullA, hrefCheck, hinitsCheck, hmodeCheck]

theorem tablesFullA_complete {C : Context} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) :
    ∀ (tables : List Table) (tts : List TableType),
      tables.all Table.isSyn = true → tables.length = tts.length →
      SeqAll₂ (Table_okA C) tables tts →
      tts = tables.map Table.tabletype ∧
        tables.all (checkTableFullA C) = true := by
  intro tables
  induction tables with
  | nil =>
      intro tts hsyn hlen hall
      cases tts with
      | nil => exact ⟨rfl, rfl⟩
      | cons tt tts => simp at hlen
  | cons table tables ih =>
      intro tts hsyn hlen hall
      cases tts with
      | nil => simp at hlen
      | cons tt tts =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 table tt rfl rfl
          obtain ⟨htail, htailCheck⟩ := ih tts hsyn.2
            (by simpa using hlen)
            (fun i a b ha hb => hall (i + 1) a b
              (by simpa using ha) (by simpa using hb))
          cases hhead with
          | mk htt hconst =>
              have hcheck := checkTableFullA_complete hC hheap hsyn.1
                (Table_okA.mk htt hconst)
              exact ⟨by simp [htail], by simp [hcheck, htailCheck]⟩

theorem datasFullA_complete {C : Context} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) :
    ∀ (datas : List Data) (oks : List DataType),
      datas.all Data.isSyn = true → datas.length = oks.length →
      SeqAll₂ (Data_okA C) datas oks →
      oks = datas.map (fun _ => DataType.ok) ∧
        datas.all (checkDataFullA C) = true := by
  intro datas
  induction datas with
  | nil =>
      intro oks hsyn hlen hall
      cases oks with
      | nil => exact ⟨rfl, rfl⟩
      | cons result oks => simp at hlen
  | cons data datas ih =>
      intro oks hsyn hlen hall
      cases oks with
      | nil => simp at hlen
      | cons result oks =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 data result rfl rfl
          obtain ⟨htail, htailCheck⟩ := ih oks hsyn.2
            (by simpa using hlen)
            (fun i a b ha hb => hall (i + 1) a b
              (by simpa using ha) (by simpa using hb))
          cases hhead with
          | mk hmode =>
              have hcheck := checkDataFullA_complete hC hheap hsyn.1
                (Data_okA.mk hmode)
              exact ⟨by simp [htail], by simp [hcheck, htailCheck]⟩

theorem elemsFullA_complete {C : Context} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) :
    ∀ (elems : List Elem) (rts : List ElemType),
      elems.all Elem.isSyn = true → elems.length = rts.length →
      SeqAll₂ (Elem_okA C) elems rts →
      rts = elems.map Elem.reftype ∧
        elems.all (checkElemFullA C) = true := by
  intro elems
  induction elems with
  | nil =>
      intro rts hsyn hlen hall
      cases rts with
      | nil => exact ⟨rfl, rfl⟩
      | cons rt rts => simp at hlen
  | cons elem elems ih =>
      intro rts hsyn hlen hall
      cases rts with
      | nil => simp at hlen
      | cons rt rts =>
          simp only [List.all_cons, Bool.and_eq_true] at hsyn
          have hhead := hall 0 elem rt rfl rfl
          obtain ⟨htail, htailCheck⟩ := ih rts hsyn.2
            (by simpa using hlen)
            (fun i a b ha hb => hall (i + 1) a b
              (by simpa using ha) (by simpa using hb))
          cases hhead with
          | mk href hinits hmode =>
              have hcheck := checkElemFullA_complete hC hheap hsyn.1
                (Elem_okA.mk href hinits hmode)
              exact ⟨by simp [htail], by simp [hcheck, htailCheck]⟩

theorem funcsFullA_complete {C : Context} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.ret = none)
    {funcs : List Func} {dts : List DefType}
    (hsyn : funcs.all Func.isSyn = true) (hlen : funcs.length = dts.length)
    (hall : SeqAll₂ (Func_okA C) funcs dts) :
    funcs.all (checkFuncFullA C) = true := by
  rw [List.all_eq_true]
  intro f hf
  obtain ⟨i, hi, hfi⟩ := List.mem_iff_getElem.mp hf
  have hi' : i < dts.length := by simpa [hlen] using hi
  exact checkFuncFullA_complete hC hheap hlocals hlabels hret
    (List.all_eq_true.mp hsyn f hf)
    (hall i f dts[i] (by rw [List.getElem?_eq_getElem hi, hfi])
      (List.getElem?_eq_getElem hi'))

/-! ## Full staged module checker -/

/-- The two exact `Module_okA` contexts, using the full amended global checker
instead of the legacy fragment checker. -/
def Module.contextsFullA (m : Module) : Option (Context × Context) :=
  match funcsXt (Module.importTypes m) with
  | none => none
  | some dtsI =>
      match m.funcs.mapM (fun f => (rollTypes [] m.types)[f.typeidx.val]?) with
      | none => none
      | some fdts =>
          let C' : Context :=
            { types := rollTypes [] m.types,
              globals := ExternType.globals (Module.importTypes m),
              funcs := dtsI ++ fdts,
              refs := funcidxNonfuncs' m.globals m.mems m.tables m.elems }
          match checkGlobalsFullA C' m.globals with
          | none => none
          | some gts =>
              some (C',
                Context.append C'
                  { tags := ExternType.tags (Module.importTypes m) ++
                            m.tags.map (fun tg => C'.closTagType tg.tagtype),
                    globals := gts,
                    mems := ExternType.mems (Module.importTypes m) ++
                            m.mems.map Mem.memtype,
                    tables := ExternType.tables (Module.importTypes m) ++
                              m.tables.map Table.tabletype,
                    datas := m.datas.map (fun _ => DataType.ok),
                    elems := m.elems.map Elem.reftype })

/-- The production amended-Core module checker.  Every syntax-bearing section
uses the full grammar checker; no legacy fragment predicate occurs. -/
def validateFullA (m : Module) : Bool :=
  Module.wf m &&
  checkTypesOkA Context.empty m.types &&
  (match Module.contextsFullA m with
   | none => false
   | some (C', C) =>
       m.imports.all (fun i =>
         checkExternTypeFullA (Module.typeContext m) i.externtype) &&
       m.tags.all (checkTagFullA C') &&
       m.mems.all (fun mem => checkLimits mem.memtype.lim (2 ^ 16)) &&
       m.tables.all (checkTableFullA C') &&
       m.funcs.all (checkFuncFullA C) &&
       m.datas.all (checkDataFullA C) &&
       m.elems.all (checkElemFullA C) &&
       (match m.start with
        | none => true
        | some s => checkStart C s) &&
       m.exports.all (fun e => checkExternIdx C e.externidx) &&
       disjoint (m.exports.map Export.name))

/-- Full module-checker soundness once the checked type section supplies
semantic validity for its raw and causally closed stored defined types.  The
source package for the staged contexts is reconstructed directly from the
successful checks, before semantic expression soundness is invoked. -/
theorem validateFullA_sound_of_stored {m : Module}
    (hstored : ∀ {dts : List DefType},
      Types_okA Context.empty m.types dts →
      ({ Context.empty with types := dts } : Context).StoredDeftypesOkA)
    (h : validateFullA m = true) :
    ∃ mt : ModuleType, Module_okA m mt := by
  simp only [validateFullA, Bool.and_eq_true] at h
  obtain ⟨⟨hwf, htypes⟩, hrest⟩ := h
  have hsyn : m.isSyn = true := by
    simp only [Module.wf, Bool.and_eq_true] at hwf
    exact hwf.2
  have hsynParts := hsyn
  simp only [Module.isSyn, Bool.and_eq_true] at hsynParts
  rcases hsynParts with
    ⟨⟨⟨⟨⟨⟨⟨htypesSyn, himportsSyn⟩, htagsSyn⟩,
      hglobalsSyn⟩, htablesSyn⟩, hfuncsSyn⟩, hdatasSyn⟩,
      helemsSyn⟩
  cases hctx : Module.contextsFullA m with
  | none => simp only [hctx] at hrest; contradiction
  | some p =>
      obtain ⟨C', C⟩ := p
      simp only [hctx, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨himp, htags⟩, hmem⟩, htables⟩, hfuncs⟩,
        hdatas⟩, helems⟩, hstart⟩, hexports⟩, hdisj⟩ := hrest
      unfold Module.contextsFullA at hctx
      cases hfx : funcsXt (Module.importTypes m) with
      | none => simp only [hfx] at hctx; contradiction
      | some dtsI =>
          simp only [hfx] at hctx
          cases hmap : m.funcs.mapM
              (fun f => (rollTypes [] m.types)[f.typeidx.val]?) with
          | none => simp only [hmap] at hctx; contradiction
          | some fdts =>
              simp only [hmap] at hctx
              let P : Context :=
                { types := rollTypes [] m.types,
                  globals := ExternType.globals (Module.importTypes m),
                  funcs := dtsI ++ fdts,
                  refs := funcidxNonfuncs' m.globals m.mems m.tables m.elems }
              cases hgl : checkGlobalsFullA P m.globals with
              | none => simp only [P, hgl] at hctx; contradiction
              | some gts =>
                  simp only [P, hgl, Option.some.injEq, Prod.mk.injEq] at hctx
                  obtain ⟨hC', hC⟩ := hctx
                  symm at hC' hC
                  let ds := checkedTypes Context.empty m.types
                  have htyok : Types_okA Context.empty m.types ds :=
                    checkTypesOkA_sound Context.empty m.types htypes
                  have hdts : rollTypes [] m.types = ds := by
                    simpa [ds] using
                      rollTypes_eq_append_checkedTypes Context.empty m.types
                  let B : Context := { Context.empty with types := ds }
                  have htc : Module.typeContext m = B := by
                    rw [Module.typeContext, hdts]
                    rfl
                  have himportTypes : Module.importTypes m =
                      m.imports.map (fun i => B.closExternType i.externtype) := by
                    rw [Module.importTypes, htc]
                  have hC'types : C'.types = ds := by
                    rw [hC', hdts]
                  have hC'recs : C'.recs = [] := by
                    rw [hC']
                  have hCtypes : C.types = ds := by
                    rw [hC, hdts]
                    simp [Context.append]
                  have hCrecs : C.recs = [] := by
                    rw [hC]
                    simp [Context.append]
                  have htypesB : SourceTypeCompleteA B := {
                    tds := m.types
                    dts := ds
                    syn := htypesSyn
                    typesOk := htyok
                    types := rfl
                    recs := rfl
                  }
                  have htypesC' : SourceTypeCompleteA C' := {
                    tds := m.types
                    dts := ds
                    syn := htypesSyn
                    typesOk := htyok
                    types := hC'types
                    recs := hC'recs
                  }
                  have htypesC : SourceTypeCompleteA C := {
                    tds := m.types
                    dts := ds
                    syn := htypesSyn
                    typesOk := htyok
                    types := hCtypes
                    recs := hCrecs
                  }
                  have hBC' : SameTypeEnv B C' := by
                    exact ⟨by simpa [B] using hC'types.symm,
                      by change [] = C'.recs; exact hC'recs.symm⟩
                  have hBC : SameTypeEnv B C := by
                    exact ⟨by simpa [B] using hCtypes.symm,
                      by change [] = C.recs; exact hCrecs.symm⟩
                  have hCC' : SameTypeEnv C C' :=
                    ⟨hCtypes.trans hC'types.symm,
                      hCrecs.trans hC'recs.symm⟩
                  have hC'C : SameTypeEnv C' C := hCC'.symm
                  have himpB : m.imports.all
                      (fun i => checkExternTypeFullA B i.externtype) = true := by
                    simpa [htc] using himp
                  have himpRel : SeqAll₂ (Import_okA B) m.imports
                      (Module.importTypes m) := by
                    rw [himportTypes]
                    exact importsFullA_ok m.imports himpB
                  have himpOk : SeqAll
                      (fun i : Import => Externtype_okA B i.externtype)
                      m.imports :=
                    imports_extern_ok
                      (by simp [SeqLen₂, Module.importTypes]) himpRel
                  have hdtsIClosed : funcsXt
                      (m.imports.map
                        (fun i => B.closExternType i.externtype)) =
                        some dtsI := by
                    rw [← himportTypes]
                    exact hfx
                  have himpGlobalsB : ∀ gt ∈
                      ExternType.globals (Module.importTypes m),
                      gt.valtype.SourceA B := by
                    rw [himportTypes]
                    exact globals_closExternType_source htypesB m.imports
                      himportsSyn himpOk
                  have himpTagsB : ∀ jt ∈
                      ExternType.tags (Module.importTypes m),
                      (HeapType.use jt).SourceA B := by
                    rw [himportTypes]
                    exact tags_closExternType_source htypesB m.imports
                      himportsSyn himpOk
                  have himpTablesB : ∀ tt ∈
                      ExternType.tables (Module.importTypes m),
                      tt.elem.SourceA B := by
                    rw [himportTypes]
                    exact tables_closExternType_source htypesB m.imports
                      himportsSyn himpOk
                  obtain ⟨hfdtsLen, hfdtsAll⟩ := mapM_getElem hmap
                  have hfdtsLookup : ∀ dt ∈ fdts,
                      ∃ x : TypeIdx, C'.types[x.val]? = some dt := by
                    intro dt hdt
                    obtain ⟨f, hf, hsel⟩ :=
                      seqAll₂_right_mem hfdtsLen hfdtsAll hdt
                    refine ⟨f.typeidx, ?_⟩
                    rw [hC'types, ← hdts]
                    exact hsel
                  have htagRel : SeqAll₂ (Tag_okA C') m.tags
                      (m.tags.map (fun tg => C'.closTagType tg.tagtype)) :=
                    tagsFullA_ok m.tags htags
                  have hdefTagsC' : ∀ jt ∈
                      m.tags.map (fun tg => C'.closTagType tg.tagtype),
                      (HeapType.use jt).SourceA C' :=
                    tags_source htypesC' htagsSyn
                      (by simp [SeqLen₂]) htagRel
                  have hdefGlobalsC' : ∀ gt ∈ gts,
                      gt.valtype.SourceA C' :=
                    checkGlobalsFullA_sources hglobalsSyn (by
                      rw [hC']
                      simpa [P] using hgl)
                  have hdefTablesC' : ∀ tt ∈
                      m.tables.map Table.tabletype, tt.elem.SourceA C' := by
                    intro tt htt
                    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htt
                    have hcheck := List.all_eq_true.mp htables t ht
                    simp only [checkTableFullA, Bool.and_eq_true] at hcheck
                    have hs := List.all_eq_true.mp htablesSyn t ht
                    simp only [Table.isSyn, Bool.and_eq_true] at hs
                    exact (checkReftypeOkA_sound hcheck.1.2).sourceA_of_syn
                      (by simpa [TableType.isSyn] using hs.1)
                  have hElemsC : ∀ rt ∈ m.elems.map Elem.reftype,
                      rt.SourceA C := by
                    intro rt hrt
                    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hrt
                    have hcheck := List.all_eq_true.mp helems e he
                    simp only [checkElemFullA, Bool.and_eq_true] at hcheck
                    have hs := List.all_eq_true.mp helemsSyn e he
                    simp only [Elem.isSyn, Bool.and_eq_true] at hs
                    exact (checkReftypeOkA_sound hcheck.1.1).sourceA_of_syn
                      hs.1.1
                  have hC'Funcs : C'.funcs = dtsI ++ fdts := by
                    rw [hC']
                  have hC'Globals : C'.globals =
                      ExternType.globals (Module.importTypes m) := by
                    rw [hC']
                  have hC'Source : C'.SourceA := by
                    constructor
                    · intro x dt ct hx he
                      exact htypesC'.compSource hx he
                    · intro x dt ct hx he
                      have hmem : dt ∈ dtsI ++ fdts := by
                        rw [hC'Funcs] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpDt | hdefDt
                      · exact (htypesB.funcsXtCompSource himportsSyn
                            hdtsIClosed himpDt he).of_types_eq hBC'.1 hBC'.2
                      · obtain ⟨x, hx⟩ := hfdtsLookup dt hdefDt
                        exact htypesC'.compSource hx he
                    · intro x dt hx
                      have hmem : dt ∈ dtsI ++ fdts := by
                        rw [hC'Funcs] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpDt | hdefDt
                      · exact (HeapType.sourceA_of_funcsXt_closExternType
                            htypesB.recs himportsSyn hdtsIClosed himpDt).of_types_eq
                            hBC'.1 hBC'.2
                      · obtain ⟨x, hx⟩ := hfdtsLookup dt hdefDt
                        exact htypesC'.defdSource hx
                    · intro x jt dt dom hx hj he
                      rw [hC'] at hx
                      simp at hx
                    · intro x gt hx
                      have hmem : gt ∈
                          ExternType.globals (Module.importTypes m) := by
                        rw [hC'Globals] at hx
                        exact List.mem_of_getElem? hx
                      exact (himpGlobalsB gt hmem).of_types_eq hBC'.1 hBC'.2
                    · intro x tt hx
                      rw [hC'] at hx
                      simp at hx
                    · intro x rt hx
                      rw [hC'] at hx
                      simp at hx
                    · intro x lt hx
                      rw [hC'] at hx
                      simp at hx
                    · intro x ts hx
                      rw [hC'] at hx
                      simp at hx
                    · intro ts hx
                      rw [hC'] at hx
                      simp at hx
                  have hCFuncs : C.funcs = dtsI ++ fdts := by
                    rw [hC]
                    simp [Context.append]
                  have hCTags : C.tags =
                      ExternType.tags (Module.importTypes m) ++
                        m.tags.map (fun tg => C'.closTagType tg.tagtype) := by
                    rw [hC, hC']
                    simp [Context.append]
                  have hCGlobals : C.globals =
                      ExternType.globals (Module.importTypes m) ++ gts := by
                    rw [hC]
                    simp [Context.append]
                  have hCTables : C.tables =
                      ExternType.tables (Module.importTypes m) ++
                        m.tables.map Table.tabletype := by
                    rw [hC]
                    simp [Context.append]
                  have hCElems : C.elems = m.elems.map Elem.reftype := by
                    rw [hC]
                    simp [Context.append]
                  have hCSource : C.SourceA := by
                    constructor
                    · intro x dt ct hx he
                      exact htypesC.compSource hx he
                    · intro x dt ct hx he
                      have hmem : dt ∈ dtsI ++ fdts := by
                        rw [hCFuncs] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpDt | hdefDt
                      · exact (htypesB.funcsXtCompSource himportsSyn
                            hdtsIClosed himpDt he).of_types_eq hBC.1 hBC.2
                      · obtain ⟨x, hx⟩ := hfdtsLookup dt hdefDt
                        exact (htypesC'.compSource hx he).of_types_eq
                          hC'C.1 hC'C.2
                    · intro x dt hx
                      have hmem : dt ∈ dtsI ++ fdts := by
                        rw [hCFuncs] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpDt | hdefDt
                      · exact (HeapType.sourceA_of_funcsXt_closExternType
                            htypesB.recs himportsSyn hdtsIClosed himpDt).of_types_eq
                            hBC.1 hBC.2
                      · obtain ⟨x, hx⟩ := hfdtsLookup dt hdefDt
                        exact (htypesC'.defdSource hx).of_types_eq hC'C.1 hC'C.2
                    · intro x jt dt dom hx hj he
                      have hmem : jt ∈
                          ExternType.tags (Module.importTypes m) ++
                            m.tags.map (fun tg => C'.closTagType tg.tagtype) := by
                        rw [hCTags] at hx
                        exact List.mem_of_getElem? hx
                      have hsource : (HeapType.use jt).SourceA C := by
                        rcases List.mem_append.mp hmem with himpJt | hdefJt
                        · exact (himpTagsB jt himpJt).of_types_eq hBC.1 hBC.2
                        · exact (hdefTagsC' jt hdefJt).of_types_eq
                            hC'C.1 hC'C.2
                      exact htypesC.tagDomSource hsource hj he
                    · intro x gt hx
                      have hmem : gt ∈
                          ExternType.globals (Module.importTypes m) ++ gts := by
                        rw [hCGlobals] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpGt | hdefGt
                      · exact (himpGlobalsB gt himpGt).of_types_eq hBC.1 hBC.2
                      · exact (hdefGlobalsC' gt hdefGt).of_types_eq
                          hC'C.1 hC'C.2
                    · intro x tt hx
                      have hmem : tt ∈
                          ExternType.tables (Module.importTypes m) ++
                            m.tables.map Table.tabletype := by
                        rw [hCTables] at hx
                        exact List.mem_of_getElem? hx
                      rcases List.mem_append.mp hmem with himpTt | hdefTt
                      · exact (himpTablesB tt himpTt).of_types_eq hBC.1 hBC.2
                      · exact (hdefTablesC' tt hdefTt).of_types_eq
                          hC'C.1 hC'C.2
                    · intro x rt hx
                      have hmem : rt ∈ m.elems.map Elem.reftype := by
                        rw [hCElems] at hx
                        exact List.mem_of_getElem? hx
                      exact hElemsC rt hmem
                    · intro x lt hx
                      rw [hC] at hx
                      simp [Context.append] at hx
                    · intro x ts hx
                      rw [hC] at hx
                      simp [Context.append] at hx
                    · intro ts hx
                      rw [hC] at hx
                      simp [Context.append] at hx
                  have hstoredB : B.StoredDeftypesOkA := by
                    simpa [B] using hstored htyok
                  have hvalidC' : Context.ValidA C' :=
                    hC'Source.validA_of_stored (hstoredB.transport hBC')
                  have hvalidC : Context.ValidA C :=
                    hCSource.validA_of_stored (hstoredB.transport hBC)
                  obtain ⟨xts, hxlen, hxall⟩ :=
                    exports_ok m.exports C hexports
                  refine ⟨_, Module_okA.mk (C := C) (C' := C') (dts' := ds)
                    (xtsI := Module.importTypes m) (xtsE := xts)
                    (jts := m.tags.map (fun tg => C'.closTagType tg.tagtype))
                    (gts := gts) (mts := m.mems.map Mem.memtype)
                    (tts := m.tables.map Table.tabletype) (dts := fdts)
                    (oks := m.datas.map (fun _ => DataType.ok))
                    (rts := m.elems.map Elem.reftype)
                    (nms := m.exports.map Export.name)
                    (jtsI := ExternType.tags (Module.importTypes m))
                    (gtsI := ExternType.globals (Module.importTypes m))
                    (mtsI := ExternType.mems (Module.importTypes m))
                    (ttsI := ExternType.tables (Module.importTypes m))
                    (dtsI := dtsI)
                    (xs := funcidxNonfuncs' m.globals m.mems m.tables m.elems)
                    htyok (by simp [SeqLen₂, Module.importTypes]) himpRel
                    (by simp [SeqLen₂]) htagRel
                    (checkGlobalsFullA_sound hvalidC' hglobalsSyn
                      (by rw [hC']; simpa [P] using hgl))
                    (by simp [SeqLen₂]) ?_ (by simp [SeqLen₂]) ?_
                    hfdtsLen ?_ (by simp [SeqLen₂]) ?_
                    (by simp [SeqLen₂]) ?_ ?_ hxlen hxall hdisj
                    ?_ ?_ rfl rfl rfl rfl rfl hfx⟩
                  · intro i mem mt hmemAt hmtAt
                    rw [List.getElem?_map, hmemAt] at hmtAt
                    simp only [Option.map_some, Option.some.injEq] at hmtAt
                    subst mt
                    exact .mk (.mk (checkLimits_sound
                      (List.all_eq_true.mp hmem mem
                        (List.mem_of_getElem? hmemAt))))
                  · intro i t tt htAt httAt
                    rw [List.getElem?_map, htAt] at httAt
                    simp only [Option.map_some, Option.some.injEq] at httAt
                    subst tt
                    exact checkTableFullA_sound hvalidC'
                      (List.all_eq_true.mp htables t
                        (List.mem_of_getElem? htAt))
                  · intro i f dt hfAt hdtAt
                    obtain ⟨actual, hlookup, hok⟩ :=
                      checkFuncFullA_sound hvalidC
                        (by rw [hC]; simp [Context.append])
                        (by rw [hC]; simp [Context.append])
                        (by rw [hC]; simp [Context.append])
                        (List.all_eq_true.mp hfuncsSyn f
                          (List.mem_of_getElem? hfAt))
                        (List.all_eq_true.mp hfuncs f
                          (List.mem_of_getElem? hfAt))
                    have hselected := hfdtsAll i f dt hfAt hdtAt
                    rw [hdts, ← hCtypes, hlookup] at hselected
                    injection hselected with hselected
                    exact hselected ▸ hok
                  · intro i d out hdAt houtAt
                    cases out
                    exact checkDataFullA_sound hvalidC
                      (List.all_eq_true.mp hdatas d
                        (List.mem_of_getElem? hdAt))
                  · intro i e rt heAt hrtAt
                    rw [List.getElem?_map, heAt] at hrtAt
                    simp only [Option.map_some, Option.some.injEq] at hrtAt
                    subst rt
                    exact checkElemFullA_sound hvalidC
                      (List.all_eq_true.mp helems e
                        (List.mem_of_getElem? heAt))
                  · intro s hs
                    simp only [hs] at hstart
                    exact checkStart_sound hstart
                  · simpa [hC'] using hC
                  · simpa [hdts] using hC'

/-- Full module-checker completeness once the type section supplies semantic
validity for every raw and causally closed stored defined type.  The standalone
type-section theorem discharges this explicit induction boundary below. -/
theorem validateFullA_complete_of_stored {m : Module} {mt : ModuleType}
    (hwf : Module.wf m = true) (hmod : Module_okA m mt)
    (hstored : ∀ {dts : List DefType},
      Types_okA Context.empty m.types dts →
      ({ Context.empty with types := dts } : Context).StoredDeftypesOkA) :
    validateFullA m = true := by
  have hsyn : m.isSyn = true := by
    simp only [Module.wf, Bool.and_eq_true] at hwf
    exact hwf.2
  have hsynParts := hsyn
  simp only [Module.isSyn, Bool.and_eq_true] at hsynParts
  rcases hsynParts with
    ⟨⟨⟨⟨⟨⟨⟨htypesSyn, himportsSyn⟩, htagsSyn⟩,
      hglobalsSyn⟩, htablesSyn⟩, hfuncsSyn⟩, hdatasSyn⟩,
      helemsSyn⟩
  cases hmod with
  | @mk C C' dts' xtsI xtsE jts gts mts tts dts oks rts nms
      jtsI gtsI mtsI ttsI dtsI xs hty hli hi hlj hj hg hlm hm hlt ht
      hlf hf hld hd hle he hs hlx hx hdis hC hC' hxs hjI hgI hmI htI hdI =>
      obtain ⟨hsourceC, hsourceC'⟩ :=
        stageSourceExactA hsyn hty hli hi hlj hj hg hlt ht hlf hf hle he
          hC hC' hjI hgI htI hdI
      have hCtypes : C.types = dts' := by
        rw [hC, hC']
        simp [Context.append]
      have hCrecs : C.recs = [] := by
        rw [hC, hC']
        simp [Context.append]
      have hC'types : C'.types = dts' := by
        rw [hC']
      have hC'recs : C'.recs = [] := by
        rw [hC']
      have htypesC : SourceTypeCompleteA C := {
        tds := m.types
        dts := dts'
        syn := htypesSyn
        typesOk := hty
        types := hCtypes
        recs := hCrecs
      }
      have htypesC' : SourceTypeCompleteA C' := {
        tds := m.types
        dts := dts'
        syn := htypesSyn
        typesOk := hty
        types := hC'types
        recs := hC'recs
      }
      let B : Context := { Context.empty with types := dts' }
      have hBC : SameTypeEnv B C := by
        constructor
        · simpa [B] using hCtypes.symm
        · change [] = C.recs
          exact hCrecs.symm
      have hBC' : SameTypeEnv B C' := by
        constructor
        · simpa [B] using hC'types.symm
        · change [] = C'.recs
          exact hC'recs.symm
      have hstoredB : B.StoredDeftypesOkA := by
        simpa [B] using hstored hty
      have hstoredC := hstoredB.transport hBC
      have hstoredC' := hstoredB.transport hBC'
      have hvalidC : Context.ValidA C :=
        hsourceC.validA_of_stored hstoredC
      have hvalidC' : Context.ValidA C' :=
        hsourceC'.validA_of_stored hstoredC'
      have hheapC : HeapSubCompleteA C := ⟨htypesC, hsourceC⟩
      have hheapC' : HeapSubCompleteA C' := ⟨htypesC', hsourceC'⟩
      have hdts' : rollTypes [] m.types = dts' := by
        simpa using types_ok_roll hty
      have htc : Module.typeContext m = B := by
        rw [Module.typeContext, hdts']
        simp [B, Context.empty]
      obtain ⟨hxtsEq, himpck⟩ :=
        importsFullA_complete m.imports xtsI himportsSyn hli hi
      have hxtsI : Module.importTypes m = xtsI := by
        rw [Module.importTypes, htc]
        simpa [B] using hxtsEq.symm
      obtain ⟨hjtsEq, htagck⟩ :=
        tagsFullA_complete m.tags jts htagsSyn hlj hj
      have hgl : checkGlobalsFullA C' m.globals = some gts :=
        checkGlobalsFullA_complete hvalidC' hheapC' hglobalsSyn hg
      obtain ⟨hmtsEq, hmemck⟩ := mems_complete m.mems mts hlm hm
      obtain ⟨httsEq, htableck⟩ :=
        tablesFullA_complete hvalidC' hheapC' m.tables tts
          htablesSyn hlt ht
      have hClocals : C.locals = [] := by
        rw [hC, hC']
        simp [Context.append]
      have hClabels : C.labels = [] := by
        rw [hC, hC']
        simp [Context.append]
      have hCret : C.ret = none := by
        rw [hC, hC']
        simp [Context.append]
      have hfuncck : m.funcs.all (checkFuncFullA C) = true :=
        funcsFullA_complete hvalidC hheapC hClocals hClabels hCret
          hfuncsSyn hlf hf
      obtain ⟨hoksEq, hdatack⟩ :=
        datasFullA_complete hvalidC hheapC m.datas oks
          hdatasSyn hld hd
      obtain ⟨hrtsEq, helemck⟩ :=
        elemsFullA_complete hvalidC hheapC m.elems rts
          helemsSyn hle he
      obtain ⟨hnmsEq, hexpck⟩ :=
        exports_complete m.exports nms xtsE hlx.1 hlx.2 hx
      have hmapM :
          m.funcs.mapM
            (fun f => (rollTypes [] m.types)[f.typeidx.val]?) = some dts := by
        refine mapM_of_getElem hlf ?_
        intro i f dt hfi hdti
        rw [hdts']
        have hlookup := funcs_type_lookup hf i f dt hfi hdti
        rwa [hCtypes] at hlookup
      have hC'eq : C' =
          { types := rollTypes [] m.types,
            globals := ExternType.globals xtsI,
            funcs := dtsI ++ dts,
            refs := funcidxNonfuncs' m.globals m.mems m.tables m.elems } := by
        rw [hC', hdts', ← hgI, hxs]
      have hctx : Module.contextsFullA m = some (C', C) := by
        simp only [Module.contextsFullA, hxtsI, hdI, hmapM]
        rw [← hC'eq, hgl, hC, hjI, hmI, htI, hjtsEq, hmtsEq,
          httsEq, hoksEq, hrtsEq]
      have hstart : (match m.start with
          | none => true
          | some s => checkStart C s) = true := by
        cases hst : m.start with
        | none => rfl
        | some s => exact checkStart_complete (hs s hst)
      have htypesck : checkTypesOkA Context.empty m.types = true :=
        checkTypesOkA_complete htypesSyn hty
      have himpck' : m.imports.all (fun i =>
          checkExternTypeFullA (Module.typeContext m) i.externtype) = true := by
        rw [htc]
        exact himpck
      have hdis' : disjoint (m.exports.map Export.name) = true := by
        rw [← hnmsEq]
        exact hdis
      simp only [validateFullA, hwf, htypesck, Bool.true_and, hctx,
        himpck', htagck, hmemck, htableck, hfuncck, hdatack, helemck,
        hstart, hexpck, hdis']

end Validate
end WasmGemmGnaf.Wasm.Core
