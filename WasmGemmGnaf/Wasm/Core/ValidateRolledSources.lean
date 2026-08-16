/-
  Source provenance of heap leaves in rolled/unrolled checked type entries.
-/
import WasmGemmGnaf.Wasm.Core.ValidateTypeSources

set_option autoImplicit false
set_option maxRecDepth 16000

namespace WasmGemmGnaf.Wasm.Core

private theorem rollUnrollTypeUse_idx_source (base y : TypeIdx)
    (qt : RecType) (n : Nat) (hbound : base.val + n ≤ 2 ^ 32) :
    substTypeUse
        (substTypeUse (.idx y)
          ((List.range n).map
            (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
          ((List.range n).map TypeUse.recu))
        ((List.range n).map TypeVar.recv)
        ((List.range n).map
          (fun j => TypeUse.defd (.defd qt j))) =
      if base.val ≤ y.val ∧ y.val < base.val + n then
        .defd (.defd qt (y.val - base.val))
      else
        .idx y := by
  simp only [substTypeUse]
  rw [substTypeVar_rollVars base y n hbound]
  split
  · rename_i hrange
    simp only [substTypeUse]
    rw [substTypeVar_unrollRecVars]
    simp [show y.val - base.val < n by omega]
  · simp only [substTypeUse]
    exact substTypeVar_unrollIdxVars y n qt

private theorem HeapType.SourceA.rollUnroll
    {pre group tail : List DefType} {base : TypeIdx} {qt : RecType}
    {n : Nat} (hbase : base.val = pre.length)
    (hgroup : group = rollDt base qt) (hgroupLen : group.length = n)
    (hbound : base.val + n ≤ 2 ^ 32)
    {E B : Context} (hE : E.types = pre ++ group)
    (hB : B.types = pre ++ group ++ tail)
    {ht : HeapType} (hsyn : ht.isSyn = true) (hsource : ht.SourceA E) :
    (substHeapType
      (substHeapType ht
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base qt) j)))).SourceA B := by
  cases ht with
  | abs a => trivial
  | use tu =>
      cases tu with
      | defd _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | recu _ => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | idx y =>
          have hsourceRaw :
              ∃ r : Nat, E.SourceTypeNodeA (.use (.idx y)) r := by
            rcases hsource with hraw | hclosed
            · exact hraw
            · obtain ⟨_, dt, heq, _⟩ := hclosed
              cases heq
          obtain ⟨r, hnode⟩ := hsourceRaw
          cases hnode with
          | @idx _ dt hlookup =>
              simp only [substHeapType]
              rw [rollUnrollTypeUse_idx_source base y (rollRt base qt) n hbound]
              split
              · rename_i hins
                have hk : y.val - base.val < n := by omega
                have hcanonical : group[y.val - base.val]? = some
                    (.defd (rollRt base qt) (y.val - base.val)) := by
                  subst group
                  cases qt with
                  | recr sts =>
                      have hn : SubTypes.length sts = n := by
                        simpa [rollDt, rollRt, SubTypes.length_substSubTypes]
                          using hgroupLen
                      simp [rollDt, rollRt, SubTypes.length_substSubTypes,
                        hn, hk]
                have hpos : pre.length + (y.val - base.val) <
                    (pre ++ group).length := by
                  simp [hgroupLen]
                  omega
                have hlookupB :
                    (pre ++ group ++ tail)[pre.length +
                      (y.val - base.val)]? =
                      some (.defd (rollRt base qt) (y.val - base.val)) := by
                  rw [List.getElem?_append_left (by
                    simpa [List.length_append] using hpos)]
                  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
                  simpa using hcanonical
                refine Or.inl ⟨2 * (pre.length + (y.val - base.val)),
                  Context.SourceTypeNodeA.defd ?_⟩
                simpa [hB] using hlookupB
              · rename_i hout
                have hy : y.val < (pre ++ group).length := by
                  rw [hE] at hlookup
                  exact (List.getElem?_eq_some_iff.mp hlookup).1
                have hlookupB : (pre ++ group ++ tail)[y.val]? = some dt := by
                  rw [List.getElem?_append_left (by
                    simpa [List.length_append] using hy)]
                  simpa [hE] using hlookup
                exact Or.inl
                  ⟨2 * y.val + 1, .idx (by simpa [hB] using hlookupB)⟩

section StructuralRollUnroll

variable {pre group tail : List DefType} {base : TypeIdx} {qt : RecType}
  {n : Nat} (hbase : base.val = pre.length)
  (hgroup : group = rollDt base qt) (hgroupLen : group.length = n)
  (hbound : base.val + n ≤ 2 ^ 32)
  {E B : Context} (hE : E.types = pre ++ group)
  (hB : B.types = pre ++ group ++ tail)

include hbase hgroup hgroupLen hbound hE hB

private theorem ValType.SourceA.rollUnroll {t : ValType}
    (hsyn : t.isSyn = true) (hsource : t.SourceA E) :
    (substValType
      (substValType t
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base qt) j)))).SourceA B := by
  cases t with
  | num _ | vec _ => trivial
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      cases rt with
      | ref nul ht =>
          exact HeapType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
            hE hB hsyn hsource

private theorem StorageType.SourceA.rollUnroll {zt : StorageType}
    (hsyn : zt.isSyn = true) (hsource : zt.SourceA E) :
    (substStorageType
      (substStorageType zt
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base qt) j)))).SourceA B := by
  cases zt with
  | pack _ => trivial
  | val t =>
      exact ValType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
        hE hB hsyn hsource

private theorem FieldType.SourceA.rollUnroll {ft : FieldType}
    (hsyn : ft.isSyn = true) (hsource : ft.SourceA E) :
    (substFieldType
      (substFieldType ft
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base qt) j)))).SourceA B := by
  cases ft with
  | mk _ zt =>
      exact StorageType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
        hE hB hsyn hsource

private theorem FieldTypes.sourceA_rollUnroll : ∀ (fts : FieldTypes),
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    (∀ ft ∈ FieldTypes.toList fts, ft.SourceA E) →
    ∀ ft ∈ FieldTypes.toList
      (substFieldTypes
        (substFieldTypes fts
          ((List.range n).map
            (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
          ((List.range n).map TypeUse.recu))
        ((List.range n).map TypeVar.recv)
        ((List.range n).map
          (fun j => TypeUse.defd (.defd (rollRt base qt) j)))),
      ft.SourceA B := by
  intro fts
  cases fts with
  | nil => simp [FieldTypes.toList, substFieldTypes]
  | cons ft rest =>
      intro hsyn hsource out hout
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substFieldTypes, FieldTypes.toList, List.mem_cons] at hout
      rcases hout with rfl | hout
      · exact FieldType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
          hE hB hsyn.1 (hsource ft (by simp [FieldTypes.toList]))
      · exact FieldTypes.sourceA_rollUnroll rest hsyn.2
          (fun candidate hc => hsource candidate (by
            simp [FieldTypes.toList, hc])) out hout

private theorem ValTypes.sourceA_rollUnroll : ∀ (ts : ValTypes),
    (ValTypes.toList ts).all ValType.isSyn = true →
    (∀ t ∈ ValTypes.toList ts, t.SourceA E) →
    ∀ t ∈ ValTypes.toList
      (substValTypes
        (substValTypes ts
          ((List.range n).map
            (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
          ((List.range n).map TypeUse.recu))
        ((List.range n).map TypeVar.recv)
        ((List.range n).map
          (fun j => TypeUse.defd (.defd (rollRt base qt) j)))),
      t.SourceA B := by
  intro ts
  cases ts with
  | nil => simp [ValTypes.toList, substValTypes]
  | cons t rest =>
      intro hsyn hsource out hout
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substValTypes, ValTypes.toList, List.mem_cons] at hout
      rcases hout with rfl | hout
      · exact ValType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
          hE hB hsyn.1 (hsource t (by simp [ValTypes.toList]))
      · exact ValTypes.sourceA_rollUnroll rest hsyn.2
          (fun candidate hc => hsource candidate (by
            simp [ValTypes.toList, hc])) out hout

theorem CompType.SourceA.rollUnroll {ct : CompType}
    (hsyn : ct.isSyn = true) (hsource : ct.SourceA E) :
    (substCompType
      (substCompType ct
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base qt) j)))).SourceA B := by
  cases ct with
  | struct fts =>
      exact FieldTypes.sourceA_rollUnroll hbase hgroup hgroupLen hbound
        hE hB fts hsyn hsource
  | array ft =>
      exact FieldType.SourceA.rollUnroll hbase hgroup hgroupLen hbound
        hE hB hsyn hsource
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      exact ⟨ValTypes.sourceA_rollUnroll hbase hgroup hgroupLen hbound
          hE hB dom hsyn.1 hsource.1,
        ValTypes.sourceA_rollUnroll hbase hgroup hgroupLen hbound
          hE hB cod hsyn.2 hsource.2⟩

end StructuralRollUnroll

private theorem unrollDt_roll_entry_source (base : TypeIdx) (sts : SubTypes)
    (k : Nat) :
    unrollDt (.defd (rollRt base (.recr sts)) k) =
      ((SubTypes.toList sts)[k]?).map (fun st =>
        substSubType
          (substSubType st
            ((List.range (SubTypes.length sts)).map
              (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
            ((List.range (SubTypes.length sts)).map TypeUse.recu))
          ((List.range (SubTypes.length sts)).map TypeVar.recv)
          ((List.range (SubTypes.length sts)).map (fun j =>
            TypeUse.defd (.defd (rollRt base (.recr sts)) j)))) := by
  simp only [rollRt, unrollDt, unrollRt]
  simp only [SubTypes.length_substSubTypes]
  rw [SubTypes.getElem?_substSubTypes]
  rw [SubTypes.getElem?_substSubTypes]
  rw [Option.map_map]
  congr

private theorem rectype_okA_comp_source_mem_aux :
    ∀ n : Nat, ∀ {E : Context} {sts : SubTypes} {x : TypeIdx},
      SubTypes.length sts = n →
      (RecType.recr sts).isSyn = true →
      Rectype_okA E (.recr sts) x →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        (.sub fin sups ct) ∈ SubTypes.toList sts →
        ∃ D : Context, D.types = E.types ∧ ct.SourceA D := by
  intro n
  induction n with
  | zero =>
      intro E sts x hlen hsyn hrec fin sups ct hmem
      cases sts with
      | nil => simp [SubTypes.toList] at hmem
      | cons head tail => simp [SubTypes.length] at hlen
  | succ n ih =>
      intro E sts x hlen hsyn hrec fin sups ct hmem
      cases sts with
      | nil => simp [SubTypes.length] at hlen
      | cons head tail =>
          have hsynList : (head :: SubTypes.toList tail).all
              SubType.isSyn = true := by
            simpa [RecType.isSyn, SubTypes.toList] using hsyn
          rw [List.all_cons, Bool.and_eq_true] at hsynList
          cases hrec with
          | cons hhead hscope htail =>
              simp only [SubTypes.toList, List.mem_cons] at hmem
              rcases hmem with heq | hmem
              · subst head
                cases hhead with
                | mk _ _ _ hok _ =>
                    have hheadSyn := hsynList.1
                    rw [SubType.isSyn, Bool.and_eq_true] at hheadSyn
                    have hctSyn : ct.isSyn = true := hheadSyn.2
                    exact ⟨E, rfl, hok.sourceA_of_syn hctSyn⟩
              · apply ih (E := E) (sts := tail) (x := _) ?_
                  (by simpa [RecType.isSyn] using hsynList.2) htail hmem
                simpa [SubTypes.length] using Nat.succ.inj hlen
          | rec2 hgroup =>
              have hmem' : (.sub fin sups ct) ∈
                  SubTypes.toList (.cons head tail) := by
                simpa [SubTypes.toList] using hmem
              obtain ⟨y, j, hst⟩ := hgroup.subtype_mem hmem'
              cases hst with
              | mk _ _ _ _ hok _ =>
                  have hstSyn : (SubType.sub fin sups ct).isSyn = true :=
                    List.all_eq_true.mp
                      (by simpa [RecType.isSyn] using hsyn)
                      (SubType.sub fin sups ct) hmem'
                  rw [SubType.isSyn, Bool.and_eq_true] at hstSyn
                  exact ⟨E.withRecs (SubTypes.toList (.cons head tail)),
                    by simp [Context.withRecs],
                    hok.sourceA_of_syn hstSyn.2⟩

theorem Rectype_okA.compSourceA_of_mem {E : Context} {sts : SubTypes}
    {x : TypeIdx} (hsyn : (RecType.recr sts).isSyn = true)
    (h : Rectype_okA E (.recr sts) x)
    {fin : Option Final} {sups : TypeUses} {ct : CompType}
    (hmem : (.sub fin sups ct) ∈ SubTypes.toList sts) :
    ∃ D : Context, D.types = E.types ∧ ct.SourceA D :=
  rectype_okA_comp_source_mem_aux (SubTypes.length sts) rfl hsyn h hmem

/-- Every composite normal form obtained by unrolling a stored entry of one
checked grammar group has source provenance for all of its heap leaves in the
final type vector. -/
theorem Type_okA.groupStoredCompSourceA {C : Context} {td : TypeDef}
    {group : List DefType} (htdSyn : td.isSyn = true)
    (hvalid : Type_okA C td group) (tail : List DefType)
    {B : Context} (hB : B.types = C.types ++ group ++ tail) :
  ∀ (k : Nat) (dt : DefType), group[k]? = some dt →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        unrollDt dt = some (.sub fin sups ct) →
        ct.SourceA B := by
  cases hvalid with
  | @mk base hrange hbase hgroup hrect =>
      cases td with
      | mk qt =>
          cases qt with
          | recr sts =>
              subst group
              intro k dt hlookup fin sups ct hunroll
              let n := SubTypes.length sts
              have hgroupLen : (rollDt base (.recr sts)).length = n := by
                simp [n, rollDt, rollRt, SubTypes.length_substSubTypes]
              have hk : k < n := by
                have hk' := (List.getElem?_eq_some_iff.mp hlookup).1
                simpa [hgroupLen] using hk'
              have hcanonical : (rollDt base (.recr sts))[k]? = some
                  (.defd (rollRt base (.recr sts)) k) := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes, n, hk]
              have hdt : dt = .defd (rollRt base (.recr sts)) k :=
                Option.some.inj (hlookup.symm.trans hcanonical)
              subst dt
              have hkList : k < (SubTypes.toList sts).length := by
                simpa [n] using hk
              cases hsource : (SubTypes.toList sts)[k]'hkList with
              | sub rawFin rawSups rawCt =>
                  have hsourceGet' : (SubTypes.toList sts)[k]? =
                      some (.sub rawFin rawSups rawCt) := by
                    have hget := List.getElem?_eq_getElem hkList
                    rw [hsource] at hget
                    exact hget
                  have hmem : (.sub rawFin rawSups rawCt) ∈
                      SubTypes.toList sts := List.mem_of_getElem? hsourceGet'
                  have hqtSyn : (RecType.recr sts).isSyn = true := by
                    simpa [TypeDef.isSyn] using htdSyn
                  obtain ⟨D, hDtypes, hrawSource⟩ :=
                    hrect.compSourceA_of_mem hqtSyn hmem
                  have hrawSyn : rawCt.isSyn = true := by
                    have hstSyn := List.all_eq_true.mp
                      (by simpa [RecType.isSyn] using hqtSyn)
                      (SubType.sub rawFin rawSups rawCt) hmem
                    rw [SubType.isSyn, Bool.and_eq_true] at hstSyn
                    exact hstSyn.2
                  have hu := unrollDt_roll_entry_source base sts k
                  rw [hsourceGet'] at hu
                  simp only [Option.map_some] at hu
                  have hout : (.sub fin sups ct) =
                      substSubType
                        (substSubType (.sub rawFin rawSups rawCt)
                          ((List.range n).map (fun j =>
                            TypeVar.idx (TypeIdx.ofNat (base.val + j))))
                          ((List.range n).map TypeUse.recu))
                        ((List.range n).map TypeVar.recv)
                        ((List.range n).map (fun j => TypeUse.defd
                          (.defd (rollRt base (.recr sts)) j))) := by
                    exact Option.some.inj (hunroll.symm.trans (by simpa [n] using hu))
                  have hbound : base.val + n ≤ 2 ^ 32 := by
                    unfold TypeGroupRangeOk at hrange
                    simpa [RecType.count, n, hbase] using hrange.2
                  have hrolled := CompType.SourceA.rollUnroll
                    (pre := C.types) (group := rollDt base (.recr sts))
                    (tail := tail) (base := base) (qt := .recr sts) (n := n)
                    hbase rfl hgroupLen hbound
                    (E := D)
                    (B := B)
                    (by simpa [Context.append, hDtypes])
                    (by simpa using hB)
                    hrawSyn hrawSource
                  injection hout with _ _ hct
                  simpa [hct] using hrolled

/-- Every stored entry of a checked grammar type section exposes a composite
normal form whose heap leaves are ranked nodes in any context carrying the
same final source vector.  The target may have live recursive scratch entries
because this construction uses only ranked source nodes. -/
theorem Types_okA.storedCompSourceA_in_context {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true) (hvalid : Types_okA C tds dts)
    {B : Context} (hB : B.types = C.types ++ dts) :
    ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        unrollDt dt = some (.sub fin sups ct) →
        ct.SourceA B := by
  induction hvalid with
  | empty =>
      intro i dt hlookup
      simp at hlookup
  | @cons C' td rest group tail htd htail ih =>
      have hsynParts : td.isSyn = true ∧
          rest.all TypeDef.isSyn = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsyn
      intro i dt hlookup fin sups ct hunroll
      by_cases hi : i < group.length
      · have hlookupGroup : group[i]? = some dt := by
          rw [List.getElem?_append_left hi] at hlookup
          exact hlookup
        exact htd.groupStoredCompSourceA hsynParts.1 tail
          (B := B) (by simpa only [List.append_assoc] using hB)
          i dt hlookupGroup hunroll
      · have hlookupTail : tail[i - group.length]? = some dt := by
          rw [List.getElem?_append_right (Nat.le_of_not_gt hi)] at hlookup
          exact hlookup
        apply ih hsynParts.2 ?_ (i - group.length) dt
          hlookupTail hunroll
        cases hret : C'.ret <;>
          simpa [Context.append, List.append_assoc, hret] using hB

/-- The final-vector specialization used by contexts whose remaining fields
come from the type-section base context. -/
theorem Types_okA.storedCompSourceA {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true) (hvalid : Types_okA C tds dts) :
    ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        unrollDt dt = some (.sub fin sups ct) →
        ct.SourceA { C with types := C.types ++ dts } :=
  hvalid.storedCompSourceA_in_context hsyn rfl

end WasmGemmGnaf.Wasm.Core
