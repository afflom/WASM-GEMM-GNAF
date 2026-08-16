/-
  Source provenance for the heap leaves that occur in grammar composite types
  and in the rolled/unrolled normal forms stored by a checked type section.
-/
import WasmGemmGnaf.Wasm.Core.ValidateClosedSources

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

/-- A heap leaf is either abstract, a ranked node of the checked source type
vector, or a literal member of that vector's computed closed form. -/
def HeapType.SourceA (C : Context) : HeapType → Prop
  | .abs _ => True
  | .use tu =>
      (∃ r : Nat, C.SourceTypeNodeA (.use tu) r) ∨
      (∃ i : Nat, ∃ dt : DefType,
        tu = .defd dt ∧ (closDefTypes C.types)[i]? = some dt ∧
          C.recs = [])

def RefType.SourceA (C : Context) : RefType → Prop
  | .ref _ ht => ht.SourceA C

theorem RefType.SourceA.diff_left {C : Context} {left right : RefType}
    (h : left.SourceA C) : (RefType.diff left right).SourceA C := by
  cases left with
  | ref nul₁ ht₁ =>
      cases right with
      | ref nul₂ ht₂ =>
          cases nul₂ <;> exact h

def ValType.SourceA (C : Context) : ValType → Prop
  | .ref rt => rt.SourceA C
  | _ => True

def StorageType.SourceA (C : Context) : StorageType → Prop
  | .val t => t.SourceA C
  | .pack _ => True

def FieldType.SourceA (C : Context) : FieldType → Prop
  | .mk _ zt => zt.SourceA C

def CompType.SourceA (C : Context) : CompType → Prop
  | .struct fts => ∀ ft ∈ FieldTypes.toList fts, ft.SourceA C
  | .array ft => ft.SourceA C
  | .func dom cod =>
      (∀ t ∈ ValTypes.toList dom, t.SourceA C) ∧
      (∀ t ∈ ValTypes.toList cod, t.SourceA C)

theorem StorageType.SourceA.unpack {C : Context} {zt : StorageType}
    (h : zt.SourceA C) : zt.unpack.SourceA C := by
  cases zt with
  | val t => exact h
  | pack _ => trivial

theorem FieldType.SourceA.unpack {C : Context} {ft : FieldType}
    (h : ft.SourceA C) : ft.storage.unpack.SourceA C := by
  cases ft with
  | mk m zt => exact StorageType.SourceA.unpack h

theorem FieldTypes.sourceA_unpacked {C : Context} {fts : FieldTypes}
    (h : ∀ ft ∈ FieldTypes.toList fts, ft.SourceA C) :
    ∀ t ∈ fts.unpacked, t.SourceA C := by
  intro t ht
  obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp ht
  exact (h ft hft).unpack

theorem HeapType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {ht : HeapType} (h : ht.SourceA C) : ht.SourceA D := by
  cases ht with
  | abs _ => trivial
  | use tu =>
      rcases h with hraw | hclosed
      · obtain ⟨r, hnode⟩ := hraw
        exact Or.inl ⟨r, hnode.of_types_eq htypes⟩
      · obtain ⟨i, dt, htu, hlookup, hempty⟩ := hclosed
        exact Or.inr ⟨i, dt, htu, by simpa [htypes] using hlookup,
          by simpa [hrecs] using hempty⟩

theorem RefType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {rt : RefType} (h : rt.SourceA C) : rt.SourceA D := by
  cases rt with
  | ref _ ht => exact HeapType.SourceA.of_types_eq htypes hrecs h

theorem ValType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {t : ValType} (h : t.SourceA C) : t.SourceA D := by
  cases t with
  | ref rt => exact RefType.SourceA.of_types_eq htypes hrecs h
  | num _ | vec _ | bot => trivial

theorem StorageType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {zt : StorageType}
    (h : zt.SourceA C) : zt.SourceA D := by
  cases zt with
  | val t => exact ValType.SourceA.of_types_eq htypes hrecs h
  | pack _ => trivial

theorem FieldType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {ft : FieldType}
    (h : ft.SourceA C) : ft.SourceA D := by
  cases ft with
  | mk _ zt => exact StorageType.SourceA.of_types_eq htypes hrecs h

theorem CompType.SourceA.of_types_eq {C D : Context}
    (htypes : C.types = D.types) (hrecs : C.recs = D.recs)
    {ct : CompType}
    (h : ct.SourceA C) : ct.SourceA D := by
  cases ct with
  | struct fts =>
      intro ft hft
      exact FieldType.SourceA.of_types_eq htypes hrecs (h ft hft)
  | array ft => exact FieldType.SourceA.of_types_eq htypes hrecs h
  | func dom cod =>
      exact ⟨fun t ht => ValType.SourceA.of_types_eq htypes hrecs (h.1 t ht),
        fun t ht => ValType.SourceA.of_types_eq htypes hrecs (h.2 t ht)⟩

theorem Heaptype_okA.sourceA_of_syn {C : Context} {ht : HeapType}
    (hsyn : ht.isSyn = true) (hok : Heaptype_okA C ht) : ht.SourceA C := by
  cases hok with
  | abs => trivial
  | typeuse htu =>
      cases htu with
      | @typeidx _ x _ hlookup =>
          exact Or.inl ⟨2 * x.val + 1, .idx hlookup⟩
      | rec_ _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | deftype _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem Reftype_okA.sourceA_of_syn {C : Context} {rt : RefType}
    (hsyn : rt.isSyn = true) (hok : Reftype_okA C rt) : rt.SourceA C := by
  cases hok with
  | mk hht => exact hht.sourceA_of_syn hsyn

theorem Valtype_okA.sourceA_of_syn {C : Context} {t : ValType}
    (hsyn : t.isSyn = true) (hok : Valtype_okA C t) : t.SourceA C := by
  cases hok with
  | num _ | vec _ => trivial
  | ref hrt => exact hrt.sourceA_of_syn hsyn
  | bot => simp [ValType.isSyn] at hsyn

theorem Storagetype_okA.sourceA_of_syn {C : Context} {zt : StorageType}
    (hsyn : zt.isSyn = true) (hok : Storagetype_okA C zt) : zt.SourceA C := by
  cases hok with
  | val ht => exact ht.sourceA_of_syn hsyn
  | pack _ => trivial

theorem Fieldtype_okA.sourceA_of_syn {C : Context} {ft : FieldType}
    (hsyn : ft.isSyn = true) (hok : Fieldtype_okA C ft) : ft.SourceA C := by
  cases hok with
  | mk hzt => exact hzt.sourceA_of_syn hsyn

theorem Comptype_okA.sourceA_of_syn {C : Context} {ct : CompType}
    (hsyn : ct.isSyn = true) (hok : Comptype_okA C ct) : ct.SourceA C := by
  cases hok with
  | struct hall =>
      intro ft hft
      exact (hall ft hft).sourceA_of_syn
        (List.all_eq_true.mp hsyn ft hft)
  | array hft => exact hft.sourceA_of_syn hsyn
  | func hdom hcod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      constructor
      · intro t ht
        cases hdom with
        | mk hall =>
            have htSyn := List.all_eq_true.mp hsyn.1 t ht
            exact (hall t ht).sourceA_of_syn htSyn
      · intro t ht
        cases hcod with
        | mk hall =>
            have htSyn := List.all_eq_true.mp hsyn.2 t ht
            exact (hall t ht).sourceA_of_syn htSyn

/-! ## Recursive scratch-space shapes -/

private theorem rectype_ok2A_subtype_mem_aux :
    ∀ n : Nat, ∀ {C : Context} {sts : SubTypes} {x : TypeIdx} {i : Nat},
      SubTypes.length sts = n →
      Rectype_ok2A C (.recr sts) x i →
      ∀ {st : SubType}, st ∈ SubTypes.toList sts →
        ∃ (y : TypeIdx) (j : Nat), Subtype_ok2A C st y j := by
  intro n
  induction n with
  | zero =>
      intro C sts x i hlen hrec st hmem
      cases sts with
      | nil => simp [SubTypes.toList] at hmem
      | cons head tail => simp [SubTypes.length] at hlen
  | succ n ih =>
      intro C sts x i hlen hrec st hmem
      cases sts with
      | nil => simp [SubTypes.length] at hlen
      | cons head tail =>
          cases hrec with
          | cons hhead htail =>
              simp only [SubTypes.toList, List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨_, _, hhead⟩
              · apply ih (C := C) (sts := tail) (x := _) (i := _) ?_ htail hmem
                simpa [SubTypes.length] using Nat.succ.inj hlen

theorem Rectype_ok2A.subtype_mem {C : Context} {sts : SubTypes}
    {x : TypeIdx} {i : Nat}
    (h : Rectype_ok2A C (.recr sts) x i) {st : SubType}
    (hst : st ∈ SubTypes.toList sts) :
    ∃ (y : TypeIdx) (j : Nat), Subtype_ok2A C st y j :=
  rectype_ok2A_subtype_mem_aux (SubTypes.length sts) rfl h hst

theorem Subtype_ok2A.goodHeapShape_recu
    {C : Context} (hgraph : C.SourceTypeGraphOkA)
    (hconcrete : C.SourceTypesConcreteA)
    (hshapes : C.SourceTypeShapesOkA)
    {st : SubType} {x : TypeIdx} {i k : Nat}
    (hsyn : st.isSyn = true) (hrecu : C.recs[k]? = some st)
    (h : Subtype_ok2A C st x i) :
    ∃ a : AbsHeapType, GoodHeapShapeA C (.use (.recu k)) a := by
  cases h with
  | @mk _ fin sups ct _ _ cts hlen hlen₂ hall htuOk hctOk hsub =>
      refine ⟨ct.absShape,
        GoodHeapShapeA.use (fin := fin) (sups := sups) (ct := ct) ?_ ?_⟩
      · simpa [Context.unrollHt, hrecu]
      · intro tu htu
        obtain ⟨j, hj⟩ := List.getElem?_of_mem htu
        have hjlt : j < cts.length := by
          have hjlt' := (List.getElem?_eq_some_iff.mp hj).1
          simpa [SeqLen₂] using (hlen₂ ▸ hjlt')
        let ct' := cts[j]
        have hp := hall j tu ct' hj (List.getElem?_eq_getElem hjlt)
        obtain ⟨_, fin', sups', hunroll⟩ := hp
        have htuSyn : tu.isSyn = true := by
          rw [SubType.isSyn, Bool.and_eq_true] at hsyn
          exact List.all_eq_true.mp hsyn.1 tu htu
        have htuValid : Typeuse_okA C tu := htuOk tu htu
        cases tu with
        | defd _ => simp [TypeUse.isSyn] at htuSyn
        | recu _ => simp [TypeUse.isSyn] at htuSyn
        | idx y =>
            cases htuValid with
            | typeidx hlookup =>
                obtain ⟨a, ha, _⟩ := hconcrete (.idx hlookup)
                have hgood := Context.SourceTypeNodeA.goodHeapShape
                  hgraph hshapes (.idx hlookup) ha
                have hshape : C.typeuseShape (.idx y) = some ct'.absShape :=
                  Context.typeuseShape_of_unrollHt hunroll
                    (fun q hq => by cases hq)
                have haEq : a = ct'.absShape :=
                  Option.some.inj (ha.symm.trans hshape)
                subst a
                have hctShape : ct.absShape = ct'.absShape :=
                  (hsub ct' (List.mem_of_getElem?
                    (List.getElem?_eq_getElem hjlt))).absShape_eq
                simpa [hctShape] using hgood

/-- A syntactic recursive group validated by the amended `rec2` rule equips
its temporary `REC` entries, as well as ordinary source and literal heap
types, with structural shape certificates. -/
theorem Context.validHeapShapesA_of_rectype_ok2A
    {C : Context} (hgraph : C.SourceTypeGraphOkA)
    (hconcrete : C.SourceTypesConcreteA)
    (hshapes : C.SourceTypeShapesOkA)
    {sts : SubTypes} {x : TypeIdx} {i : Nat}
    (hsyn : (RecType.recr sts).isSyn = true)
    (hrec : Rectype_ok2A C (.recr sts) x i)
    (hrecs : C.recs = SubTypes.toList sts) : C.ValidHeapShapesA := by
  intro ht hok
  cases hok with
  | abs => exact ⟨_, .abs _⟩
  | typeuse htu =>
      cases htu with
      | typeidx hlookup =>
          obtain ⟨a, ha, _⟩ := hconcrete (.idx hlookup)
          exact ⟨a, Context.SourceTypeNodeA.goodHeapShape
            hgraph hshapes (.idx hlookup) ha⟩
      | deftype hdt =>
          exact hdt.goodHeapShape_of_source rfl hgraph hshapes
      | @rec_ _ k st hlookup =>
          have hmem : st ∈ SubTypes.toList sts := by
            rw [hrecs] at hlookup
            exact List.mem_of_getElem? hlookup
          obtain ⟨y, j, hst⟩ := hrec.subtype_mem hmem
          have hstSyn : st.isSyn = true := by
            simpa [RecType.isSyn] using
              (List.all_eq_true.mp (by simpa [RecType.isSyn] using hsyn) st hmem)
          exact hst.goodHeapShape_recu hgraph hconcrete hshapes hstSyn
            hlookup

theorem HeapType.SourceA.not_recu {C : Context} {tu : TypeUse}
    (h : (HeapType.use tu).SourceA C) : ∀ i : Nat, tu ≠ .recu i := by
  intro i hi
  subst tu
  rcases h with hraw | hclosed
  · obtain ⟨_, hnode⟩ := hraw
    cases hnode
  · obtain ⟨_, dt, heq, _, _⟩ := hclosed
    cases heq

/-- Completeness of the existing heap decision when both endpoints carry the
source provenance induced by a checked type section.  Unlike `/syn`, this also
covers the literal `deftype` normal forms created by rolling a recursive group.
The shape environment may include live `REC` scratch entries. -/
theorem Types_okA.decHeaptypeSubN_complete_of_sourceA
    {tds : List TypeDef} {dts : List DefType}
    (htds : tds.all TypeDef.isSyn = true)
    (htypesOk : Types_okA Context.empty tds dts)
    {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)
    {left right : HeapType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Heaptype_subA C left right) :
    decHeaptypeSubN C C.subtypeFuel left right = true := by
  cases left with
  | abs a =>
      cases right with
      | abs b => exact hsub.decHeaptypeSubN_complete_of_abs_abs henv
      | use tu =>
          rcases hright with hraw | hclosed
          · obtain ⟨r, hnode⟩ := hraw
            obtain ⟨b, hshape, _⟩ :=
              htypesOk.sourceTypesConcreteA_in_context C htypes hnode
            have hgood := Context.SourceTypeNodeA.goodHeapShape
              (htypesOk.sourceTypeGraphOkA_in_context htds C htypes)
              (htypesOk.sourceTypeShapesOkA_in_context htds C htypes)
              hnode hshape
            apply hsub.decHeaptypeSubN_complete_of_abs_nonrec_use henv hgood
            intro i hi
            subst tu
            cases hnode
          · obtain ⟨i, dt, htu, hlookup, hrecs⟩ := hclosed
            subst tu
            have hlookup' : (closDefTypes dts)[i]? = some dt := by
              simpa [htypes] using hlookup
            obtain ⟨b, hshape, _⟩ :=
              htypesOk.closedTypesConcreteA_closure htds i dt hlookup'
            have hgood := Exec.goodHeapShape_of_closedTypeGraphOkAt
              (htypesOk.closedTypeGraphOkAt_closure htds C)
              (htypesOk.closedTypeShapesOkA_closure htds C)
              i dt hlookup' b hshape
            exact hsub.decHeaptypeSubN_complete_of_abs_nonrec_use henv hgood
              (HeapType.SourceA.not_recu (Or.inr
                ⟨i, dt, rfl, hlookup, hrecs⟩))
  | use tu =>
      rcases hleft with hraw | hclosed
      · obtain ⟨r, hnode⟩ := hraw
        exact htypesOk.decHeaptypeSubN_complete_of_sourceTypeNodeA_in_context
          htds htypes hnode hsub
      · obtain ⟨i, dt, htu, hlookup, hrecs⟩ := hclosed
        subst tu
        have hlookup' : (closDefTypes dts)[i]? = some dt := by
          simpa [htypes] using hlookup
        exact htypesOk.decHeaptypeSubN_complete_of_closed_member htds
          htypes hrecs hlookup' hsub

/-! ## Source-provenance lifting through composite subtyping -/

section SourceUpperCompleteness

variable {tds : List TypeDef} {dts : List DefType}
  (htds : tds.all TypeDef.isSyn = true)
  (htypesOk : Types_okA Context.empty tds dts)
  {C : Context} (htypes : C.types = dts) (henv : C.ValidHeapShapesA)

include htds htypesOk htypes henv

theorem Reftype_subA.decReftypeSubN_complete_of_sourceA
    {left right : RefType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Reftype_subA C left right) :
    decReftypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | nonnull hs =>
      simp [decReftypeSubN,
        Types_okA.decHeaptypeSubN_complete_of_sourceA htds htypesOk
          htypes henv hleft hright hs]
  | null hs =>
      simp [decReftypeSubN,
        Types_okA.decHeaptypeSubN_complete_of_sourceA htds htypesOk
          htypes henv hleft hright hs]

theorem Valtype_subA.decValtypeSubN_complete_of_sourceA
    {left right : ValType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Valtype_subA C left right) :
    decValtypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | num hs => exact decNumtypeSub_complete hs
  | vec hs => exact decVectypeSub_complete hs
  | ref hs =>
      exact hs.decReftypeSubN_complete_of_sourceA htds htypesOk htypes
        henv hleft hright
  | bot => rfl

theorem Storagetype_subA.decStoragetypeSubN_complete_of_sourceA
    {left right : StorageType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Storagetype_subA C left right) :
    decStoragetypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | val hs =>
      exact hs.decValtypeSubN_complete_of_sourceA htds htypesOk htypes
        henv hleft hright
  | pack hs => exact decPacktypeSub_complete hs

theorem Fieldtype_subA.decFieldtypeSubN_complete_of_sourceA
    {left right : FieldType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Fieldtype_subA C left right) :
    decFieldtypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | const hs =>
      exact hs.decStoragetypeSubN_complete_of_sourceA htds htypesOk
        htypes henv hleft hright
  | var hs₁ hs₂ =>
      rw [decFieldtypeSubN, Bool.and_eq_true]
      exact ⟨hs₁.decStoragetypeSubN_complete_of_sourceA htds
          htypesOk htypes henv hleft hright,
        hs₂.decStoragetypeSubN_complete_of_sourceA htds
          htypesOk htypes henv hright hleft⟩

theorem Resulttype_subA.decResulttypeSubN_complete_of_sourceA
    {left right : List ValType}
    (hleft : ∀ t ∈ left, t.SourceA C)
    (hright : ∀ t ∈ right, t.SourceA C)
    (hsub : Resulttype_subA C left right) :
    decResulttypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | mk hlen hall =>
      apply decSeq₂_complete (R := fun a b =>
        a.SourceA C ∧ b.SourceA C ∧ Valtype_subA C a b)
        (fun a b h => h.2.2.decValtypeSubN_complete_of_sourceA
          htds htypesOk htypes henv h.1 h.2.1)
        left right hlen
      intro i a b ha hb
      exact ⟨hleft a (List.mem_of_getElem? ha),
        hright b (List.mem_of_getElem? hb), hall i a b ha hb⟩

theorem Comptype_subA.decComptypeSubN_complete_of_sourceA
    {left right : CompType} (hleft : left.SourceA C)
    (hright : right.SourceA C)
    (hsub : Comptype_subA C left right) :
    decComptypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | struct hlen hall =>
      rename_i fts₁ extra fts₂
      simp only [decComptypeSubN, FieldTypes.toList_ofList,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by simp [List.length_append]; omega, ?_⟩
      have htake : (fts₁ ++ extra).take fts₂.length = fts₁ := by
        rw [← hlen, List.take_left]
      rw [htake]
      apply decSeq₂_complete (R := fun a b =>
        a.SourceA C ∧ b.SourceA C ∧ Fieldtype_subA C a b)
        (fun a b h => h.2.2.decFieldtypeSubN_complete_of_sourceA
          htds htypesOk htypes henv h.1 h.2.1)
        fts₁ fts₂ hlen
      intro i a b ha hb
      exact ⟨hleft a (by
          simp only [FieldTypes.toList_ofList]
          apply List.mem_append_left extra
          exact List.mem_of_getElem? ha),
        hright b (by simpa only [FieldTypes.toList_ofList] using
          List.mem_of_getElem? hb), hall i a b ha hb⟩
  | array hs =>
      exact hs.decFieldtypeSubN_complete_of_sourceA htds htypesOk
        htypes henv hleft hright
  | func hdom hcod =>
      rw [decComptypeSubN, Bool.and_eq_true]
      exact ⟨hdom.decResulttypeSubN_complete_of_sourceA htds
          htypesOk htypes henv hright.1 hleft.1,
        hcod.decResulttypeSubN_complete_of_sourceA htds
          htypesOk htypes henv hleft.2 hright.2⟩

end SourceUpperCompleteness

end WasmGemmGnaf.Wasm.Core
