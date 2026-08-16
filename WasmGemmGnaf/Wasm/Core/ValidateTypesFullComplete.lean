import WasmGemmGnaf.Wasm.Core.ValidateRolledSources

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-- Every composite normal form reached through the stored type vector has
source provenance in the context where the executable subtype check runs. -/
private def StoredCompSourcesA (C : Context) : Prop :=
  ∀ {i : Nat} {dt : DefType} {fin : Option Final} {sups : TypeUses}
      {ct : CompType},
    C.types[i]? = some dt →
    unrollDt dt = some (.sub fin sups ct) → ct.SourceA C

private theorem checkSubtypeOkA_complete_of_sources
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)
    (hstored : StoredCompSourcesA C)
    {x : TypeIdx} {st : SubType} (hsyn : st.isSyn = true)
    (h : Subtype_okA C st x) : checkSubtypeOkA C x st = true := by
  cases h with
  | mk hlen hlen₂ hall hok hsub =>
      rename_i fin xs ct cts'
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      cases xs with
      | nil =>
          simpa [checkSubtypeOkA, TypeUses.ofList] using
            checkComptypeOkA_complete hsyn.2 hok
      | cons y ys =>
          cases ys with
          | nil =>
              cases cts' with
              | nil => simp [SeqLen₂] at hlen₂
              | cons ct' rest =>
                  cases rest with
                  | cons _ _ => simp [SeqLen₂] at hlen₂
                  | nil =>
                      have hp := hall 0 y ct' rfl rfl
                      obtain ⟨hlt, dt, fin', xs', hlookup, hunroll⟩ := hp
                      have hs : Comptype_subA C ct ct' := hsub ct' (by simp)
                      have hleft : ct.SourceA C :=
                        hok.sourceA_of_syn hsyn.2
                      have hright : ct'.SourceA C := hstored hlookup hunroll
                      simp [checkSubtypeOkA, TypeUses.ofList, hlookup, hunroll,
                        hlt, checkComptypeOkA_complete hsyn.2 hok,
                        TypeUses.toTypeIdxs_ofList_idx,
                        hs.decComptypeSubN_complete_of_sourceA htds htypesOk
                          htypes henv hleft hright]
          | cons _ _ =>
              simp only [List.length_cons] at hlen
              omega

private theorem checkSubtypeOk2A_complete_of_sources
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)
    (hstored : StoredCompSourcesA C)
    {x : TypeIdx} {i : Nat} {st : SubType} (hsyn : st.isSyn = true)
    (h : Subtype_ok2A C st x i) : checkSubtypeOk2A C x i st = true := by
  cases h with
  | mk hlen hlen₂ hall htuOk hok hsub =>
      rename_i fin sups ct cts'
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      cases sups with
      | nil =>
          simpa [checkSubtypeOk2A] using checkComptypeOkA_complete hsyn.2 hok
      | cons tu rest =>
          cases rest with
          | nil =>
              cases cts' with
              | nil => simp [SeqLen₂, TypeUses.toList] at hlen₂
              | cons ct' cts =>
                  cases cts with
                  | cons _ _ => simp [SeqLen₂, TypeUses.toList] at hlen₂
                  | nil =>
                      obtain ⟨hbefore, fin', sups', hunroll⟩ :=
                        hall 0 tu ct' rfl rfl
                      have hmem : tu ∈ TypeUses.toList (.cons tu .nil) := by
                        change tu ∈ [tu]
                        exact List.mem_cons_self
                      have htu : Typeuse_okA C tu := htuOk tu hmem
                      have htuSyn : TypeUse.isSyn tu = true :=
                        List.all_eq_true.mp hsyn.1 tu hmem
                      have htuCheck : checkHeaptypeOkA C (.use tu) = true :=
                        checkHeaptypeOkA_complete htuSyn (.typeuse htu)
                      have hs : Comptype_subA C ct ct' := hsub ct' (by simp)
                      have hleft : ct.SourceA C :=
                        hok.sourceA_of_syn hsyn.2
                      have hright : ct'.SourceA C := by
                        cases tu with
                        | recu _ | defd _ =>
                            simp [TypeUse.isSyn] at htuSyn
                        | idx y =>
                            cases htu with
                            | typeidx hlookup =>
                                rename_i dt
                                have hunroll' : unrollDt dt =
                                    some (.sub fin' sups' ct') := by
                                  simpa [Context.unrollHt, hlookup] using hunroll
                                exact hstored hlookup hunroll'
                      simp [checkSubtypeOk2A, hbefore, htuCheck, hunroll,
                        checkComptypeOkA_complete hsyn.2 hok,
                        hs.decComptypeSubN_complete_of_sourceA htds htypesOk
                          htypes henv hleft hright]
          | cons _ _ =>
              simp only [TypeUses.toList, List.length_cons] at hlen
              omega

private theorem checkRectypeListOk2A_complete_of_sources
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)
    (hstored : StoredCompSourcesA C) :
    ∀ (sts : List SubType) {x : TypeIdx} {i : Nat},
      sts.all SubType.isSyn = true →
      Rectype_ok2A C (.recr (SubTypes.ofList sts)) x i →
      checkSubtypeListOk2A C sts x i = true := by
  intro sts
  induction sts with
  | nil => intro x i _ h; cases h; rfl
  | cons st sts ih =>
      intro x i hsyn h
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      cases h with
      | cons hst htail =>
          rw [checkSubtypeListOk2A, Bool.and_eq_true]
          exact ⟨checkSubtypeOk2A_complete_of_sources htds htypesOk
              htypes henv hstored hsyn.1 hst,
            ih hsyn.2 htail⟩

private theorem checkRectypeListA_complete_of_sources
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)
    (hstored : StoredCompSourcesA C) :
    ∀ (sts : List SubType) {x : TypeIdx},
      sts.all SubType.isSyn = true →
      Rectype_okA C (.recr (SubTypes.ofList sts)) x →
      checkRectypeListA C sts x = true := by
  intro sts
  induction sts with
  | nil => intro x _ _; rfl
  | cons st sts ih =>
      intro x hsyn h
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      rw [checkRectypeListA, Bool.or_eq_true]
      cases h with
      | cons hst hscope htail =>
          apply Or.inl
          simp only [Bool.and_eq_true]
          exact ⟨⟨checkSubtypeOkA_complete_of_sources htds htypesOk
              htypes henv hstored hsyn.1 hst, hscope⟩,
            ih hsyn.2 htail⟩
      | rec2 h2 =>
          apply Or.inr
          have h2' : Rectype_ok2A (C.withRecs (st :: sts))
              (.recr (SubTypes.ofList (st :: sts))) x 0 := by
            simpa using h2
          have htypesRec : (C.withRecs (st :: sts)).types = dts := by
            simpa [Context.withRecs] using htypes
          have henvRec : (C.withRecs (st :: sts)).ValidHeapShapesA :=
            Context.validHeapShapesA_of_rectype_ok2A
              (htypesOk.sourceTypeGraphOkA_in_context htds _ htypesRec)
              (htypesOk.sourceTypesConcreteA_in_context _ htypesRec)
              (htypesOk.sourceTypeShapesOkA_in_context htds _ htypesRec)
              (by simpa [RecType.isSyn] using hsyn) h2'
              (by simp [Context.withRecs])
          have hstoredRec : StoredCompSourcesA (C.withRecs (st :: sts)) := by
            intro i dt fin sups ct hlookup hunroll
            have hlookupDts : dts[i]? = some dt := by
              simpa [htypesRec] using hlookup
            exact htypesOk.storedCompSourceA_in_context htds
              (B := C.withRecs (st :: sts))
              (by simpa [Context.empty] using htypesRec)
              i dt hlookupDts hunroll
          exact checkRectypeListOk2A_complete_of_sources htds htypesOk
            htypesRec henvRec hstoredRec (st :: sts)
            (by simpa using hsyn) h2'

private theorem checkRectypeOkA_complete_of_sources
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (hrecs : C.recs = [])
    (hstored : StoredCompSourcesA C)
    {qt : RecType} {x : TypeIdx} (hsyn : qt.isSyn = true)
    (h : Rectype_okA C qt x) : checkRectypeOkA C qt x = true := by
  have henv : C.ValidHeapShapesA :=
    htypesOk.validHeapShapesA_in_context htds C htypes hrecs
  cases qt with
  | recr sts =>
      rw [checkRectypeOkA]
      have hsyn' : (SubTypes.toList sts).all SubType.isSyn = true := by
        simpa [RecType.isSyn] using hsyn
      have h' : Rectype_okA C
          (.recr (SubTypes.ofList (SubTypes.toList sts))) x := by
        simpa using h
      exact checkRectypeListA_complete_of_sources htds htypesOk htypes
        henv hstored _ hsyn' h'

private theorem Type_okA.output_eq_checked {C : Context} {td : TypeDef}
    {dts : List DefType} (h : Type_okA C td dts) :
    dts = rollDt (TypeIdx.ofNat C.types.length) td.rectype := by
  cases h with
  | @mk x hrange hbase hresult _ =>
      have hx : TypeIdx.ofNat C.types.length = x := by
        apply Subtype.ext
        rw [TypeIdx.ofNat_val_of_lt]
        · exact hbase.symm
        · omega
      simpa [hx] using hresult

/-- Appending one validated group to a validated type-section prefix preserves
the staged `Types_okA` derivation and its exact output concatenation. -/
private theorem Types_okA.snoc
    {C : Context} {tds : List TypeDef} {dts : List DefType}
    (hvalid : Types_okA C tds dts)
    {td : TypeDef} {group : List DefType}
    (htd : Type_okA (Context.append C { types := dts }) td group) :
    Types_okA C (tds ++ [td]) (dts ++ group) := by
  induction hvalid with
  | @empty C' =>
      have hzero : Context.append C' { types := [] } = C' := by
        cases C' with
        | mk types recs tags globals mems tables funcs datas elems locals
            labels ret refs =>
            cases ret <;> simp [Context.append]
      rw [hzero] at htd
      simpa using Types_okA.cons htd (Types_okA.empty (C :=
        Context.append C' { types := group }))
  | @cons C' head rest first tail hhead htail ih =>
      have htd' : Type_okA
          (Context.append (Context.append C' { types := first })
            { types := tail }) td group := by
        cases hret : C'.ret <;>
          simpa [Context.append, List.append_assoc, hret] using htd
      simpa [List.append_assoc] using Types_okA.cons hhead (ih htd')

private theorem checkTypeOkA_complete_from_prefix
    {prefixTds : List TypeDef} {prefixDts : List DefType}
    (hprefixSyn : prefixTds.all TypeDef.isSyn = true)
    (hprefixOk : Types_okA Context.empty prefixTds prefixDts)
    {td : TypeDef} {group : List DefType} (htdSyn : td.isSyn = true)
    (htd : Type_okA { Context.empty with types := prefixDts } td group) :
    checkTypeOkA { Context.empty with types := prefixDts } td = true := by
  have htdAtEnd : Type_okA
      (Context.append Context.empty { types := prefixDts }) td group := by
    simpa [Context.append] using htd
  have hfull : Types_okA Context.empty (prefixTds ++ [td])
      (prefixDts ++ group) := Types_okA.snoc hprefixOk htdAtEnd
  have hfullSyn : (prefixTds ++ [td]).all TypeDef.isSyn = true := by
    simp [hprefixSyn, htdSyn]
  cases htd with
  | @mk x hrange hbase hgroup hrect =>
      have hx : TypeIdx.ofNat prefixDts.length = x := by
        apply Subtype.ext
        have hlt : prefixDts.length < 2 ^ 32 := by
          simpa [Context.empty] using hrange.1
        rw [TypeIdx.ofNat_val_of_lt _ hlt]
        simpa [Context.empty] using hbase.symm
      subst x
      subst group
      simp only [checkTypeOkA, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hrange, ?_⟩
      let B := Context.append { Context.empty with types := prefixDts }
        { types := rollDt (TypeIdx.ofNat prefixDts.length) td.rectype }
      have hBtypes : B.types = prefixDts ++
          rollDt (TypeIdx.ofNat prefixDts.length) td.rectype := by
        simp [B, Context.append]
      have hBrecs : B.recs = [] := by
        simp [B, Context.append, Context.empty]
      have hstored : StoredCompSourcesA B := by
        intro i dt fin sups ct hlookup hunroll
        exact hfull.storedCompSourceA_in_context hfullSyn
          (B := B) (by simpa [Context.empty] using hBtypes)
          i dt (by simpa [B, Context.append] using hlookup) hunroll
      have hcomplete := checkRectypeOkA_complete_of_sources hfullSyn hfull
        hBtypes hBrecs hstored htdSyn hrect
      simpa [B] using hcomplete

private theorem checkTypesOkA_complete_from_prefix :
    ∀ (prefixTds : List TypeDef) (prefixDts : List DefType)
      (tds : List TypeDef) (dts : List DefType),
      prefixTds.all TypeDef.isSyn = true →
      Types_okA Context.empty prefixTds prefixDts →
      tds.all TypeDef.isSyn = true →
      Types_okA { Context.empty with types := prefixDts } tds dts →
      checkTypesOkA { Context.empty with types := prefixDts } tds = true := by
  intro prefixTds prefixDts tds
  induction tds generalizing prefixTds prefixDts with
  | nil =>
      intro dts _ _ _ hvalid
      cases hvalid
      rfl
  | cons td rest ih =>
      intro dts hprefixSyn hprefixOk hsyn hvalid
      simp only [List.all_cons, Bool.and_eq_true] at hsyn
      cases hvalid with
      | @cons _ _ _ group tail htd htail =>
          have hgroup := Type_okA.output_eq_checked htd
          subst group
          rw [checkTypesOkA, Bool.and_eq_true]
          refine ⟨checkTypeOkA_complete_from_prefix hprefixSyn hprefixOk
              hsyn.1 htd, ?_⟩
          let nextGroup := rollDt
            (TypeIdx.ofNat prefixDts.length) td.rectype
          have htdAtEnd : Type_okA
              (Context.append Context.empty { types := prefixDts }) td
              nextGroup := by
            simpa [Context.append, nextGroup] using htd
          have hprefixNext : Types_okA Context.empty
              (prefixTds ++ [td]) (prefixDts ++ nextGroup) :=
            Types_okA.snoc hprefixOk htdAtEnd
          have hprefixNextSyn : (prefixTds ++ [td]).all
              TypeDef.isSyn = true := by
            simp [hprefixSyn, hsyn.1]
          have htail' : Types_okA
              { Context.empty with types := prefixDts ++ nextGroup }
              rest tail := by
            simpa [Context.append, nextGroup] using htail
          simpa [nextGroup, Context.append] using
            ih (prefixTds ++ [td]) (prefixDts ++ nextGroup) tail
              hprefixNextSyn hprefixNext hsyn.2 htail'

/-- Full grammar-level completeness of the production amended-Core type
section checker, with no heap-decision callback and no fragment premise. -/
theorem checkTypesOkA_complete {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts) :
    checkTypesOkA Context.empty tds = true := by
  have hempty : Types_okA Context.empty [] [] := .empty
  simpa [Context.empty] using
    checkTypesOkA_complete_from_prefix [] [] tds dts rfl hempty hsyn hvalid

end Validate
end WasmGemmGnaf.Wasm.Core
