/-
  Wasm/Core/TypeGraphOrigin.lean --- structural type-graph certificates
  extracted from an amended Core type-section validity derivation.

  These results retain only source syntax, ranks, shapes, and allocation
  provenance.  They do not assume or store completeness of executable
  subtyping.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeSound
import WasmGemmGnaf.Wasm.Core.RuntimeTypeOrigin
import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

private theorem rollUnrollTypeUse_idx (base y : TypeIdx) (qt : RecType)
    (n : Nat) (hbound : base.val + n ≤ 2 ^ 32) :
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

private theorem unrollDt_roll_entry (base : TypeIdx) (sts : SubTypes)
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

@[simp] private theorem TypeUses.toList_substTypeUses :
    ∀ (sups : TypeUses) (tvs : List TypeVar) (tus : List TypeUse),
      TypeUses.toList (substTypeUses sups tvs tus) =
        (TypeUses.toList sups).map (fun tu => substTypeUse tu tvs tus)
  | .nil, _, _ => rfl
  | .cons tu sups, tvs, tus => by
      simp [substTypeUses, TypeUses.toList,
        TypeUses.toList_substTypeUses sups tvs tus]

private theorem comptypeSubA_absShape_eq {C : Context} {ct₁ ct₂ : CompType}
    (h : Comptype_subA C ct₁ ct₂) : ct₁.absShape = ct₂.absShape := by
  cases h <;> rfl

private def SourceSupersBeforeA (C : Context) (limit : Nat) :
    SubType → Prop
  | .sub _ sups ct =>
      ∀ tu ∈ TypeUses.toList sups,
        ∃ (y : TypeIdx) (dt : DefType),
          tu = .idx y ∧ y.val < limit ∧ C.types[y.val]? = some dt ∧
            dt.absShape = some ct.absShape

private theorem Subtype_okA.sourceSupersBeforeA {C : Context}
    {st : SubType} {x : TypeIdx} (h : Subtype_okA C st x) :
    SourceSupersBeforeA C x.val st := by
  cases h with
  | @mk C' fin xs ct x' cts' hlen hlen₂ hall hok hsub =>
      intro tu htu
      simp only [TypeUses.toList_ofList] at htu
      obtain ⟨y, hyxs, rfl⟩ := List.mem_map.mp htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hyxs
      have hjlt : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
      have hjctlt : j < cts'.length := by
        simpa [SeqLen₂] using (hlen₂ ▸ hjlt)
      let ct' := cts'[j]
      have hp := hall j y ct' hj (List.getElem?_eq_getElem hjctlt)
      obtain ⟨hy, dt, _, _, hlookup, hunroll⟩ := hp
      have hctsub : Comptype_subA C ct ct' :=
        hsub ct' (List.mem_of_getElem? (List.getElem?_eq_getElem hjctlt))
      have hshape : dt.absShape = some ct.absShape := by
        rw [DefType.absShape, expandDt, hunroll]
        simp [comptypeSubA_absShape_eq hctsub]
      exact ⟨y, dt, rfl, hy, hlookup, hshape⟩

private theorem Subtype_ok2A.sourceSupersBeforeA {C : Context}
    {st : SubType} {x : TypeIdx} {i : Nat}
    (hsyn : st.isSyn = true) (h : Subtype_ok2A C st x i) :
    SourceSupersBeforeA C x.val st := by
  cases h with
  | @mk C' fin sups ct x' i' cts' hlen hlen₂ hall hvalid hok hsub =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      intro tu htu
      have htuSyn : tu.isSyn = true :=
        List.all_eq_true.mp hsyn.1 tu htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp htu
      have hjlt : j < (TypeUses.toList sups).length :=
        (List.getElem?_eq_some_iff.mp hj).1
      have hjctlt : j < cts'.length := by
        simpa [SeqLen₂] using (hlen₂ ▸ hjlt)
      let ct' := cts'[j]
      have hp := hall j tu ct' hj (List.getElem?_eq_getElem hjctlt)
      obtain ⟨hbef, fin', sups', hunrollHt⟩ := hp
      have hok := hvalid tu htu
      have hctsub : Comptype_subA C ct ct' :=
        hsub ct' (List.mem_of_getElem? (List.getElem?_eq_getElem hjctlt))
      cases tu with
      | defd _ | recu _ => simp [TypeUse.isSyn] at htuSyn
      | idx y =>
          cases hok with
          | typeidx hlookup =>
              let dt := C.types[y.val]'(List.getElem?_eq_some_iff.mp hlookup).1
              have hdt : C.types[y.val]? = some dt :=
                List.getElem?_eq_getElem _
              have hunroll : unrollDt dt = some (.sub fin' sups' ct') := by
                simpa [Context.unrollHt, hdt] using hunrollHt
              have hshape : dt.absShape = some ct.absShape := by
                rw [DefType.absShape, expandDt, hunroll]
                simp [comptypeSubA_absShape_eq hctsub]
              exact ⟨y, dt, rfl, by simpa [before] using hbef, hdt, hshape⟩

private theorem Rectype_ok2A.sourceSupersBeforeAt {C : Context}
    {sts : SubTypes} {x : TypeIdx} {i : Nat}
    (hrange : x.val + SubTypes.length sts ≤ 2 ^ 32)
    (hsyn : (RecType.recr sts).isSyn = true)
    (h : Rectype_ok2A C (.recr sts) x i) :
    ∀ {k : Nat} {st : SubType},
      (SubTypes.toList sts)[k]? = some st →
      SourceSupersBeforeA C (x.val + k) st := by
  cases h with
  | empty =>
      intro k st hget
      simp [SubTypes.toList] at hget
  | @cons C' head tail x i hst htail =>
      rw [RecType.isSyn, SubTypes.toList, List.all_cons,
        Bool.and_eq_true] at hsyn
      intro k candidate hget
      cases k with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero] at hget
          have hc : head = candidate := Option.some.inj hget
          subst candidate
          simpa using hst.sourceSupersBeforeA hsyn.1
      | succ k =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hget
          have hlen : k < (SubTypes.toList tail).length :=
            (List.getElem?_eq_some_iff.mp hget).1
          have hpositive : 0 < SubTypes.length tail := by
            rw [← SubTypes.toList_length]
            omega
          change x.val + (SubTypes.length tail + 1) ≤ 2 ^ 32 at hrange
          have hxlt : x.val + 1 < 2 ^ 32 := by omega
          have hxval : (TypeIdx.ofNat (x.val + 1)).val = x.val + 1 :=
            TypeIdx.ofNat_val_of_lt _ hxlt
          have htailRange :
              (TypeIdx.ofNat (x.val + 1)).val + SubTypes.length tail ≤
                2 ^ 32 := by
            rw [hxval]
            omega
          have hresult := Rectype_ok2A.sourceSupersBeforeAt
            htailRange hsyn.2 htail hget
          rw [hxval] at hresult
          rw [show x.val + 1 + k = x.val + (k + 1) by omega] at hresult
          exact hresult
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

private theorem Rectype_okA.sourceSupersBeforeAt {C : Context}
    {sts : SubTypes} {x : TypeIdx}
    (hrange : x.val + SubTypes.length sts ≤ 2 ^ 32)
    (hsyn : (RecType.recr sts).isSyn = true)
    (h : Rectype_okA C (.recr sts) x) :
    ∀ {k : Nat} {st : SubType},
      (SubTypes.toList sts)[k]? = some st →
      SourceSupersBeforeA C (x.val + k) st := by
  cases h with
  | empty =>
      intro k st hget
      simp [SubTypes.toList] at hget
  | @cons C' head tail x hst _ htail =>
      rw [RecType.isSyn, SubTypes.toList, List.all_cons,
        Bool.and_eq_true] at hsyn
      intro k candidate hget
      cases k with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero] at hget
          have hc : head = candidate := Option.some.inj hget
          subst candidate
          simpa using hst.sourceSupersBeforeA
      | succ k =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hget
          have hlen : k < (SubTypes.toList tail).length :=
            (List.getElem?_eq_some_iff.mp hget).1
          have hpositive : 0 < SubTypes.length tail := by
            rw [← SubTypes.toList_length]
            omega
          change x.val + (SubTypes.length tail + 1) ≤ 2 ^ 32 at hrange
          have hxlt : x.val + 1 < 2 ^ 32 := by omega
          have hxval : (TypeIdx.ofNat (x.val + 1)).val = x.val + 1 :=
            TypeIdx.ofNat_val_of_lt _ hxlt
          have htailRange :
              (TypeIdx.ofNat (x.val + 1)).val + SubTypes.length tail ≤
                2 ^ 32 := by
            rw [hxval]
            omega
          have hresult := Rectype_okA.sourceSupersBeforeAt
            htailRange hsyn.2 htail hget
          rw [hxval] at hresult
          rw [show x.val + 1 + k = x.val + (k + 1) by omega] at hresult
          exact hresult
  | @rec2 C' all x hrec =>
      intro k st hget
      have hh := Rectype_ok2A.sourceSupersBeforeAt hrange hsyn hrec hget
      simpa [SourceSupersBeforeA, Context.withRecs] using hh
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

private theorem rolledSubtype_supersRankedA {C : Context}
    {base : TypeIdx} {sts : SubTypes} {k : Nat} {st : SubType}
    (hbase : base.val = C.types.length)
    (hrange : base.val + SubTypes.length sts ≤ 2 ^ 32)
    (hbefore : SourceSupersBeforeA
      (Context.append C { types := rollDt base (.recr sts) })
      (base.val + k) st)
    (tail : List DefType) :
    let rolled := rollRt base (.recr sts)
    let n := SubTypes.length sts
    let st' := substSubType
      (substSubType st
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd rolled j)))
    SeqAll
      (Context.TypeUse.RankedBeforeA
        { C with types := C.types ++ rollDt base (.recr sts) ++ tail }
        (C.types.length + k))
      (match st' with | .sub _ sups _ => TypeUses.toList sups) := by
  dsimp only
  cases st with
  | sub fin sups ct =>
      simp only [substSubType, TypeUses.toList_substTypeUses, List.map_map]
      intro candidate hcand
      obtain ⟨tu, htu, rfl⟩ := List.mem_map.mp hcand
      obtain ⟨y, dt, rfl, hy, hlookup, _⟩ := hbefore tu htu
      simp only [Function.comp_apply]
      rw [rollUnrollTypeUse_idx base y (rollRt base (.recr sts))
        (SubTypes.length sts) hrange]
      split
      · rename_i hinside
        apply Context.TypeUse.RankedBeforeA.defd (j := C.types.length +
          (y.val - base.val))
        · omega
        · have hj : y.val - base.val < SubTypes.length sts := by omega
          have hgroup :
              (rollDt base (.recr sts))[y.val - base.val]? =
                some (.defd (rollRt base (.recr sts))
                  (y.val - base.val)) := by
            simp [rollDt, rollRt, SubTypes.length_substSubTypes, hj]
          have hgroupLen : (rollDt base (.recr sts)).length =
              SubTypes.length sts := by
            simp [rollDt, rollRt, SubTypes.length_substSubTypes]
          change (C.types ++ rollDt base (.recr sts) ++ tail)[
              C.types.length + (y.val - base.val)]? = _
          rw [List.getElem?_append_left (by
            simp only [List.length_append, hgroupLen]
            omega)]
          rw [List.getElem?_append_right (Nat.le_add_right _ _)]
          simpa using hgroup
      · rename_i houtside
        apply Context.TypeUse.RankedBeforeA.idx (dt := dt)
        · simpa [hbase] using hy
        · have hylen : y.val <
              (C.types ++ rollDt base (.recr sts)).length :=
              (List.getElem?_eq_some_iff.mp hlookup).1
          change (C.types ++ rollDt base (.recr sts) ++ tail)[y.val]? =
            some dt
          rw [List.getElem?_append_left hylen]
          exact hlookup

private theorem Type_okA.groupStoredTypeSupersRankedA {C : Context}
    {td : TypeDef} {group : List DefType}
    (hsyn : td.isSyn = true) (h : Type_okA C td group)
    (tail : List DefType) :
    ∀ (k : Nat) (dt : DefType), group[k]? = some dt →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        unrollDt dt = some (.sub fin sups ct) →
        SeqAll
          (Context.TypeUse.RankedBeforeA
            { C with types := C.types ++ group ++ tail }
            (C.types.length + k))
          (TypeUses.toList sups) := by
  cases h with
  | mk hrange hbase hgroup hrect =>
      rename_i base
      cases td with
      | mk qt =>
          cases qt with
          | recr sts =>
              subst group
              have hsynQt : (RecType.recr sts).isSyn = true := by
                simpa [TypeDef.isSyn] using hsyn
              have hbound : base.val + SubTypes.length sts ≤ 2 ^ 32 := by
                unfold TypeGroupRangeOk at hrange
                simpa [RecType.count, hbase] using hrange.2
              intro k dt hdt fin sups ct hunroll
              have hgroupLen : (rollDt base (.recr sts)).length =
                  SubTypes.length sts := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes]
              have hk : k < SubTypes.length sts := by
                have hk0 := (List.getElem?_eq_some_iff.mp hdt).1
                rw [hgroupLen] at hk0
                exact hk0
              have hcanonical : (rollDt base (.recr sts))[k]? = some
                  (.defd (rollRt base (.recr sts)) k) := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes, hk]
              have hdtEq : dt = .defd (rollRt base (.recr sts)) k :=
                Option.some.inj (hdt.symm.trans hcanonical)
              subst dt
              have hkList : k < (SubTypes.toList sts).length := by
                simpa only [SubTypes.toList_length] using hk
              obtain ⟨source, hsource⟩ : ∃ source,
                  (SubTypes.toList sts)[k]? = some source :=
                ⟨(SubTypes.toList sts)[k]'hkList,
                  List.getElem?_eq_getElem hkList⟩
              have hbefore := Rectype_okA.sourceSupersBeforeAt
                hbound hsynQt hrect hsource
              have hu := unrollDt_roll_entry base sts k
              rw [hsource] at hu
              simp only [Option.map_some] at hu
              have hout : (.sub fin sups ct) =
                  substSubType
                    (substSubType source
                      ((List.range (SubTypes.length sts)).map
                        (fun j => TypeVar.idx
                          (TypeIdx.ofNat (base.val + j))))
                      ((List.range (SubTypes.length sts)).map TypeUse.recu))
                    ((List.range (SubTypes.length sts)).map TypeVar.recv)
                    ((List.range (SubTypes.length sts)).map (fun j =>
                      TypeUse.defd (.defd (rollRt base (.recr sts)) j))) :=
                Option.some.inj (hunroll.symm.trans hu)
              have hranked := rolledSubtype_supersRankedA hbase hbound
                hbefore tail
              dsimp only at hranked
              rw [← hout] at hranked
              exact hranked

private theorem Types_okA.storedTypeSupersRankedA_interval {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true) (h : Types_okA C tds dts)
    (tail : List DefType) :
    ∀ (i : Nat) (dt : DefType),
      (C.types ++ dts ++ tail)[i]? = some dt →
      C.types.length ≤ i → i < C.types.length + dts.length →
      ∀ {fin : Option Final} {sups : TypeUses} {ct : CompType},
        unrollDt dt = some (.sub fin sups ct) →
        SeqAll
          (Context.TypeUse.RankedBeforeA
            { C with types := C.types ++ dts ++ tail } i)
          (TypeUses.toList sups) := by
  induction h with
  | empty =>
      intro i dt _ _ hi
      simp at hi
      omega
  | @cons C td tds dts₁ dts htd htail ih =>
      have hsynParts : td.isSyn = true ∧
          tds.all TypeDef.isSyn = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsyn
      have hsynHead : td.isSyn = true := by
        exact hsynParts.1
      have hsynTail : tds.all TypeDef.isSyn = true := by
        exact hsynParts.2
      intro i dt hlookup hlo hhi fin sups ct hunroll
      by_cases hgroup : i < C.types.length + dts₁.length
      · have hk : i - C.types.length < dts₁.length := by omega
        have hlookupGroup : dts₁[i - C.types.length]? = some dt := by
          have hlookup' := hlookup
          simp only [List.append_assoc] at hlookup'
          rw [List.getElem?_append_right hlo] at hlookup'
          rw [List.getElem?_append_left hk] at hlookup'
          exact hlookup'
        have hranked := htd.groupStoredTypeSupersRankedA hsynHead
          (dts ++ tail) (i - C.types.length) dt hlookupGroup hunroll
        have hiEq : C.types.length + (i - C.types.length) = i := by omega
        simpa only [List.append_assoc, hiEq] using hranked
      · have hloTail :
            (Context.append C {types := dts₁}).types.length ≤ i := by
          simp only [Context.append, List.length_append]
          omega
        have hhiTail : i <
            (Context.append C {types := dts₁}).types.length + dts.length := by
          simp only [Context.append, List.length_append]
          simpa only [List.length_append, Nat.add_assoc] using hhi
        have hlookupTail :
            ((Context.append C {types := dts₁}).types ++ dts ++ tail)[i]? =
              some dt := by
          simpa only [Context.append, List.append_assoc] using hlookup
        have hranked := ih hsynTail i dt hlookupTail hloTail hhiTail hunroll
        cases hret : C.ret <;>
          simpa [Context.append, List.append_assoc, hret] using hranked

theorem Types_okA.storedTypeSupersRankedA {tds : List TypeDef}
    {dts : List DefType} (hsyn : tds.all TypeDef.isSyn = true)
    (h : Types_okA Context.empty tds dts) :
    Context.StoredTypeSupersRankedA
      { Context.empty with types := dts } := by
  intro i dt hlookup fin sups ct hunroll
  have hi : i < dts.length := (List.getElem?_eq_some_iff.mp hlookup).1
  have hranked := h.storedTypeSupersRankedA_interval hsyn [] i dt
    (by simpa [Context.empty] using hlookup) (by simp [Context.empty])
    (by simpa [Context.empty] using hi) hunroll
  simpa [Context.empty] using hranked

/-- Every declared-super edge of a checked source type section strictly lowers
the alternating source-node rank used by the executable subtype walk. -/
theorem Types_okA.sourceTypeGraphOkA {tds : List TypeDef}
    {dts : List DefType} (hsyn : tds.all TypeDef.isSyn = true)
    (h : Types_okA Context.empty tds dts) :
    Context.SourceTypeGraphOkA
      { Context.empty with types := dts } :=
  Context.sourceTypeGraphOkA_of_declaredTypeSupersRankedA
    (Context.declaredTypeSupersRankedA_of_storedTypeSupersRankedA
      (h.storedTypeSupersRankedA hsyn))

private theorem Type_okA.groupConcreteA {C : Context} {td : TypeDef}
    {group : List DefType} (h : Type_okA C td group) :
    ∀ (k : Nat) (dt : DefType), group[k]? = some dt →
      ∃ a : AbsHeapType,
        dt.absShape = some a ∧ Context.ConcreteAbsShapeA a := by
  cases h with
  | mk hrange hbase hgroup hrect =>
      rename_i base
      cases td with
      | mk qt =>
          cases qt with
          | recr sts =>
              subst group
              intro k dt hdt
              have hgroupLen : (rollDt base (.recr sts)).length =
                  SubTypes.length sts := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes]
              have hk : k < SubTypes.length sts := by
                have hk' := (List.getElem?_eq_some_iff.mp hdt).1
                simpa only [hgroupLen] using hk'
              have hcanonical : (rollDt base (.recr sts))[k]? = some
                  (.defd (rollRt base (.recr sts)) k) := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes, hk]
              have hdtEq : dt = .defd (rollRt base (.recr sts)) k :=
                Option.some.inj (hdt.symm.trans hcanonical)
              subst dt
              have hkList : k < (SubTypes.toList sts).length := by
                simpa only [SubTypes.toList_length] using hk
              obtain ⟨source, hsource⟩ : ∃ source,
                  (SubTypes.toList sts)[k]? = some source :=
                ⟨(SubTypes.toList sts)[k]'hkList,
                  List.getElem?_eq_getElem hkList⟩
              have hu := unrollDt_roll_entry base sts k
              rw [hsource] at hu
              simp only [Option.map_some] at hu
              cases source with
              | sub fin sups ct =>
                  let ct' := substCompType
                    (substCompType ct
                      ((List.range (SubTypes.length sts)).map
                        (fun j => TypeVar.idx
                          (TypeIdx.ofNat (base.val + j))))
                      ((List.range (SubTypes.length sts)).map TypeUse.recu))
                    ((List.range (SubTypes.length sts)).map TypeVar.recv)
                    ((List.range (SubTypes.length sts)).map (fun j =>
                      TypeUse.defd (.defd (rollRt base (.recr sts)) j)))
                  have huexp : unrollDt (.defd (rollRt base (.recr sts)) k) =
                      some (.sub fin
                        (substTypeUses
                          (substTypeUses sups
                            ((List.range (SubTypes.length sts)).map
                              (fun j => TypeVar.idx
                                (TypeIdx.ofNat (base.val + j))))
                            ((List.range (SubTypes.length sts)).map TypeUse.recu))
                          ((List.range (SubTypes.length sts)).map TypeVar.recv)
                          ((List.range (SubTypes.length sts)).map (fun j =>
                            TypeUse.defd (.defd (rollRt base (.recr sts)) j))))
                        ct') := by
                    simpa [substSubType, ct'] using hu
                  refine ⟨ct'.absShape, ?_,
                    Context.concreteAbsShapeA_of_compType ct'⟩
                  simp [DefType.absShape, expandDt, huexp]

private theorem Types_okA.sourceConcrete_interval {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (h : Types_okA C tds dts) :
    ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
      ∃ a : AbsHeapType,
        dt.absShape = some a ∧ Context.ConcreteAbsShapeA a := by
  induction h with
  | empty =>
      intro i dt hlookup
      simp at hlookup
  | @cons C td tds dts₁ dts htd htail ih =>
      intro i dt hlookup
      by_cases hhead : i < dts₁.length
      · have hlookupHead : dts₁[i]? = some dt := by
          rw [List.getElem?_append_left hhead] at hlookup
          exact hlookup
        exact htd.groupConcreteA i dt hlookupHead
      · have hlookupTail : dts[i - dts₁.length]? = some dt := by
          rw [List.getElem?_append_right (Nat.le_of_not_gt hhead)] at hlookup
          exact hlookup
        exact ih _ _ hlookupTail

/-- Every source type produced by a checked type section has a concrete
function, structure, or array expansion. -/
theorem Types_okA.sourceTypesConcreteA {tds : List TypeDef}
    {dts : List DefType} (h : Types_okA Context.empty tds dts) :
    Context.SourceTypesConcreteA
      { Context.empty with types := dts } := by
  intro tu r hnode
  cases hnode with
  | idx hlookup =>
      obtain ⟨a, ha, hc⟩ := h.sourceConcrete_interval _ _ hlookup
      exact ⟨a, by simpa [Context.typeuseShape, hlookup] using ha, hc⟩
  | defd hlookup =>
      obtain ⟨a, ha, hc⟩ := h.sourceConcrete_interval _ _ hlookup
      exact ⟨a, by simpa [Context.typeuseShape] using ha, hc⟩

private theorem rolledTypeUse_shapeA {C : Context} {base y : TypeIdx}
    {sts : SubTypes} {k : Nat} {dt : DefType} {a : AbsHeapType}
    (hbase : base.val = C.types.length)
    (hrange : base.val + SubTypes.length sts ≤ 2 ^ 32)
    (hk : k < SubTypes.length sts)
    (hy : y.val < base.val + k)
    (hlookup : (Context.append C
      { types := rollDt base (.recr sts) }).types[y.val]? = some dt)
    (hshape : dt.absShape = some a) (tail : List DefType) :
    let n := SubTypes.length sts
    let tu := substTypeUse
      (substTypeUse (.idx y)
        ((List.range n).map
          (fun j => TypeVar.idx (TypeIdx.ofNat (base.val + j))))
        ((List.range n).map TypeUse.recu))
      ((List.range n).map TypeVar.recv)
      ((List.range n).map
        (fun j => TypeUse.defd (.defd (rollRt base (.recr sts)) j)))
    ({ C with types := C.types ++ rollDt base (.recr sts) ++ tail } :
      Context).typeuseShape tu = some a := by
  dsimp only
  rw [rollUnrollTypeUse_idx base y (rollRt base (.recr sts))
    (SubTypes.length sts) hrange]
  split
  · rename_i hinside
    have hoff : y.val - base.val < SubTypes.length sts := by omega
    have hgroup : (rollDt base (.recr sts))[y.val - base.val]? =
        some dt := by
      have hfull : (C.types ++ rollDt base (.recr sts))[y.val]? = some dt := by
        simpa only [Context.append] using hlookup
      rw [List.getElem?_append_right (by omega)] at hfull
      simpa only [hbase] using hfull
    have hcanonical : (rollDt base (.recr sts))[y.val - base.val]? =
        some (.defd (rollRt base (.recr sts)) (y.val - base.val)) := by
      simp [rollDt, rollRt, SubTypes.length_substSubTypes, hoff]
    have hdt : dt =
        .defd (rollRt base (.recr sts)) (y.val - base.val) :=
      Option.some.inj (hgroup.symm.trans hcanonical)
    subst dt
    simpa [Context.typeuseShape] using hshape
  · rename_i houtside
    have hyPrefix : y.val < C.types.length := by
      rw [← hbase]
      omega
    have hprefix : C.types[y.val]? = some dt := by
      have hfull : (C.types ++ rollDt base (.recr sts))[y.val]? = some dt := by
        simpa only [Context.append] using hlookup
      rw [List.getElem?_append_left hyPrefix] at hfull
      exact hfull
    have hfinal : (C.types ++ rollDt base (.recr sts) ++ tail)[y.val]? =
        some dt := by
      rw [List.getElem?_append_left]
      · rw [List.getElem?_append_left hyPrefix]
        exact hprefix
      · simp only [List.length_append]
        omega
    have hfinal' : (C.types ++ (rollDt base (.recr sts) ++ tail))[y.val]? =
        some dt := by simpa only [List.append_assoc] using hfinal
    simp [Context.typeuseShape, hfinal', hshape]

private theorem Type_okA.groupShapesOkA {C : Context} {td : TypeDef}
    {group : List DefType} (hsyn : td.isSyn = true)
    (h : Type_okA C td group) (tail : List DefType) :
    ∀ (k : Nat) (dt : DefType), group[k]? = some dt →
      ∀ (a : AbsHeapType), dt.absShape = some a →
        ∀ g ∈ ({ C with types := C.types ++ group ++ tail } :
          Context).heapSupers (.use (.defd dt)),
          ∃ tu' : TypeUse, g = .use tu' ∧
            ({ C with types := C.types ++ group ++ tail } :
              Context).typeuseShape tu' = some a := by
  cases h with
  | mk hrange hbase hgroup hrect =>
      rename_i base
      cases td with
      | mk qt =>
          cases qt with
          | recr sts =>
              subst group
              have hsynQt : (RecType.recr sts).isSyn = true := by
                simpa [TypeDef.isSyn] using hsyn
              have hbound : base.val + SubTypes.length sts ≤ 2 ^ 32 := by
                unfold TypeGroupRangeOk at hrange
                simpa [RecType.count, hbase] using hrange.2
              intro k dt hdt a hdtShape g hg
              have hk : k < SubTypes.length sts := by
                have hk' := (List.getElem?_eq_some_iff.mp hdt).1
                simpa [rollDt, rollRt, SubTypes.length_substSubTypes] using hk'
              have hcanonical : (rollDt base (.recr sts))[k]? = some
                  (.defd (rollRt base (.recr sts)) k) := by
                simp [rollDt, rollRt, SubTypes.length_substSubTypes, hk]
              have hdtEq : dt = .defd (rollRt base (.recr sts)) k :=
                Option.some.inj (hdt.symm.trans hcanonical)
              subst dt
              have hkList : k < (SubTypes.toList sts).length := by
                simpa only [SubTypes.toList_length] using hk
              obtain ⟨source, hsource⟩ : ∃ source,
                  (SubTypes.toList sts)[k]? = some source :=
                ⟨(SubTypes.toList sts)[k]'hkList,
                  List.getElem?_eq_getElem hkList⟩
              have hbefore := Rectype_okA.sourceSupersBeforeAt
                hbound hsynQt hrect hsource
              have hu := unrollDt_roll_entry base sts k
              rw [hsource] at hu
              simp only [Option.map_some] at hu
              cases source with
              | sub fin sups ct =>
                  simp only [Context.heapSupers, hu, substSubType,
                    TypeUses.toList_substTypeUses, List.map_map] at hg
                  obtain ⟨tu, htu, hgeq⟩ := List.mem_map.mp hg
                  subst g
                  obtain ⟨y, target, rfl, hy, hlookup, htargetShape⟩ :=
                    hbefore tu htu
                  have hu' := hu
                  simp only [substSubType] at hu'
                  have hparentShape :
                      (DefType.defd (rollRt base (.recr sts)) k).absShape =
                        some ct.absShape := by
                    rw [DefType.absShape]
                    unfold expandDt
                    rw [hu']
                    simp
                  have ha : a = ct.absShape :=
                    Option.some.inj (hdtShape.symm.trans hparentShape)
                  subst a
                  refine ⟨_, rfl, ?_⟩
                  exact rolledTypeUse_shapeA hbase hbound hk hy hlookup
                    htargetShape tail

private theorem Types_okA.sourceShapes_interval {C : Context}
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true) (h : Types_okA C tds dts)
    (tail : List DefType) :
    ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
      ∀ (a : AbsHeapType), dt.absShape = some a →
        ∀ g ∈ ({ C with types := C.types ++ dts ++ tail } :
          Context).heapSupers (.use (.defd dt)),
          ∃ tu' : TypeUse, g = .use tu' ∧
            ({ C with types := C.types ++ dts ++ tail } :
              Context).typeuseShape tu' = some a := by
  induction h generalizing tail with
  | empty =>
      intro i dt hlookup
      simp at hlookup
  | @cons C td tds dts₁ dts htd htail ih =>
      have hsynParts : td.isSyn = true ∧ tds.all TypeDef.isSyn = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hsyn
      intro i dt hlookup a hshape g hg
      by_cases hhead : i < dts₁.length
      · have hlookupHead : dts₁[i]? = some dt := by
          rw [List.getElem?_append_left hhead] at hlookup
          exact hlookup
        have hh := htd.groupShapesOkA hsynParts.1 (dts ++ tail)
          i dt hlookupHead a hshape g
        simpa only [List.append_assoc] using
          hh (by simpa only [List.append_assoc] using hg)
      · have hlookupTail : dts[i - dts₁.length]? = some dt := by
          rw [List.getElem?_append_right (Nat.le_of_not_gt hhead)] at hlookup
          exact hlookup
        have hh := ih hsynParts.2 tail (i - dts₁.length) dt
          hlookupTail a hshape g
        simpa only [Context.append, List.append_assoc] using
          hh (by simpa only [Context.append, List.append_assoc] using hg)

/-- Every declared-super edge of a checked source type section preserves the
source entry's concrete composite family. -/
theorem Types_okA.sourceTypeShapesOkA {tds : List TypeDef}
    {dts : List DefType} (hsyn : tds.all TypeDef.isSyn = true)
    (h : Types_okA Context.empty tds dts) :
    Context.SourceTypeShapesOkA
      { Context.empty with types := dts } := by
  intro tu r a hnode hshape g hg
  cases hnode with
  | idx hlookup =>
      simp only [Context.heapSupers, hlookup, List.mem_singleton] at hg
      subst g
      exact ⟨_, rfl, by
        simpa [Context.typeuseShape, hlookup] using hshape⟩
  | defd hlookup =>
      rename_i i dt
      have hi : i < dts.length := (List.getElem?_eq_some_iff.mp hlookup).1
      have hh := h.sourceShapes_interval hsyn [] i dt hlookup a
        (by simpa [Context.typeuseShape] using hshape) g
      simpa [Context.empty] using hh (by simpa [Context.empty] using hg)

end WasmGemmGnaf.Wasm.Core
