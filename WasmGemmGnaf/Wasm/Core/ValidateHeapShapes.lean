import WasmGemmGnaf.Wasm.Core.ValidateFullComplete

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

def rawSupers : SubType → List TypeUse
  | .sub _ sups _ => TypeUses.toList sups

theorem TypeUses.noRebasedRecSupers_iff : ∀ {sups : TypeUses},
    sups.noRebasedRecSupers = true ↔
      ∀ tu ∈ TypeUses.toList sups, ∀ j, tu ≠ .recu j
  | .nil => by simp [TypeUses.noRebasedRecSupers, TypeUses.toList]
  | .cons tu rest => by
      cases tu with
      | recu j => simp [TypeUses.noRebasedRecSupers, TypeUses.toList]
      | idx x | defd x =>
          simpa [TypeUses.noRebasedRecSupers, TypeUses.toList] using
            (TypeUses.noRebasedRecSupers_iff (sups := rest))

theorem SubTypes.noRebasedRecSupers_of_mem {sts : SubTypes}
    (h : sts.noRebasedRecSupers = true) {st : SubType}
    (hst : st ∈ SubTypes.toList sts) {tu : TypeUse}
    (htu : tu ∈ rawSupers st) (j : Nat) : tu ≠ .recu j := by
  cases sts with
  | nil => simp [SubTypes.toList] at hst
  | cons head tail =>
      cases head with
      | sub fin sups ct =>
          simp only [SubTypes.noRebasedRecSupers, Bool.and_eq_true] at h
          simp only [SubTypes.toList, List.mem_cons] at hst
          rcases hst with rfl | hst
          · exact TypeUses.noRebasedRecSupers_iff.mp h.1 tu htu j
          · exact SubTypes.noRebasedRecSupers_of_mem h.2 hst htu j
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

inductive RawSuperOriginA (C : Context) (i : Nat) : TypeUse → Prop where
  | idx {x : TypeIdx} {dt : DefType} : C.types[x.val]? = some dt →
      RawSuperOriginA C i (.idx x)
  | recu {j : Nat} : j < i → RawSuperOriginA C i (.recu j)
  | defd {D : Context} {d : DefType} : D.types = C.types →
      Deftype_okA D d → RawSuperOriginA C i (.defd d)

theorem Subtype_okA.rawSupers_empty {C : Context} (htypes : C.types = [])
    {st : SubType} {x : TypeIdx} (h : Subtype_okA C st x) :
    rawSupers st = [] := by
  cases h with
  | @mk C fin xs ct x cts hlen hlen₂ hall hok hsub =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          cases cts with
          | nil => simp [SeqLen₂] at hlen₂
          | cons ct' cts =>
              have hp := hall 0 y ct' rfl rfl
              obtain ⟨_, dt, _, _, hlookup, _⟩ := hp
              simpa [htypes] using hlookup

theorem Subtype_okA.rawSuperOrigin {C : Context}
    {st : SubType} {x : TypeIdx} (h : Subtype_okA C st x) :
    ∀ tu ∈ rawSupers st, RawSuperOriginA C 0 tu := by
  cases h with
  | @mk C fin xs ct x cts hlen hlen₂ hall hok hsub =>
      intro tu htu
      simp only [rawSupers, TypeUses.toList_ofList] at htu
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
      have hjct : j < cts.length := by
        have hj' := (List.getElem?_eq_some_iff.mp hj).1
        simpa [SeqLen₂] using (hlen₂ ▸ hj')
      obtain ⟨_, dt, _, _, hlookup, _⟩ :=
        hall j y cts[j] hj (List.getElem?_eq_getElem hjct)
      exact .idx hlookup

theorem Subtype_ok2A.rawSuperOrigin {C : Context}
    {st : SubType} {x : TypeIdx} {i : Nat} (h : Subtype_ok2A C st x i) :
    ∀ tu ∈ rawSupers st, RawSuperOriginA C i tu := by
  cases h with
  | @mk C fin sups ct x i cts hlen hlen₂ hall hvalid hok hsub =>
      intro tu htu
      have htuOk := hvalid tu htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp htu
      have hjct : j < cts.length := by
        have hj' := (List.getElem?_eq_some_iff.mp hj).1
        simpa [SeqLen₂] using (hlen₂ ▸ hj')
      have hp := hall j tu cts[j] hj (List.getElem?_eq_getElem hjct)
      have hbefore := hp.1
      cases tu with
      | idx y =>
          cases htuOk with
          | typeidx hlookup => exact .idx hlookup
      | recu k =>
          exact .recu (by simpa [before] using hbefore)
      | defd d =>
          cases htuOk with
          | deftype hd => exact .defd rfl hd

theorem Rectype_ok2A.rawSuperOriginAt {C : Context} {sts : SubTypes}
    {x : TypeIdx} {offset : Nat} (h : Rectype_ok2A C (.recr sts) x offset) :
    ∀ {i : Nat} {st : SubType}, (SubTypes.toList sts)[i]? = some st →
      ∀ tu ∈ rawSupers st, RawSuperOriginA C (offset + i) tu := by
  cases h with
  | empty => intro i st hget; simp [SubTypes.toList] at hget
  | @cons C head tail x offset hhead htail =>
      intro i st hget tu htu
      cases i with
      | zero =>
          have heq : head = st := by
            simpa [SubTypes.toList] using Option.some.inj hget
          subst st
          simpa using hhead.rawSuperOrigin tu htu
      | succ i =>
          have hget' : (SubTypes.toList tail)[i]? = some st := by
            simpa [SubTypes.toList] using hget
          have horigin := htail.rawSuperOriginAt hget' tu htu
          rw [show offset + 1 + i = offset + (i + 1) by omega] at horigin
          exact horigin
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

theorem Rectype_okA.rawSuperOriginAt {C : Context}
    {sts : SubTypes} {x : TypeIdx} (h : Rectype_okA C (.recr sts) x) :
    ∀ {i : Nat} {st : SubType}, (SubTypes.toList sts)[i]? = some st →
      ∀ tu ∈ rawSupers st, RawSuperOriginA C i tu := by
  cases h with
  | empty => intro i st hget; simp [SubTypes.toList] at hget
  | @cons C head tail x hhead hscope htail =>
      intro i st hget tu htu
      cases i with
      | zero =>
          have heq : head = st := by
            simpa [SubTypes.toList] using Option.some.inj hget
          subst st
          simpa using hhead.rawSuperOrigin tu htu
      | succ i =>
          have hget' : (SubTypes.toList tail)[i]? = some st := by
            simpa [SubTypes.toList] using hget
          have horigin := htail.rawSuperOriginAt hget' tu htu
          cases horigin with
          | idx hlookup => exact .idx hlookup
          | recu hj =>
              have hmem : st ∈ SubTypes.toList tail :=
                List.mem_of_getElem? hget'
              exact False.elim
                (SubTypes.noRebasedRecSupers_of_mem hscope hmem htu _ rfl)
          | defd htypes' hd => exact .defd htypes' hd
  | @rec2 C sts x hrec =>
      intro i st hget tu htu
      have horigin := hrec.rawSuperOriginAt hget tu htu
      cases horigin with
      | idx hlookup => exact .idx (by simpa [Context.withRecs] using hlookup)
      | recu hj => exact .recu (by simpa using hj)
      | @defd D d hDC hd =>
          exact .defd (hDC.trans (by simpa [Context.withRecs])) hd
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

theorem wtTypeUse_le_wtTypeUses_of_mem {tu : TypeUse} {sups : TypeUses}
    (h : tu ∈ TypeUses.toList sups) : wtTypeUse tu ≤ wtTypeUses sups := by
  cases sups with
  | nil => simp [TypeUses.toList] at h
  | cons head tail =>
      simp only [TypeUses.toList, List.mem_cons] at h
      simp only [wtTypeUses]
      rcases h with rfl | h
      · omega
      · have := wtTypeUse_le_wtTypeUses_of_mem h
        omega
termination_by TypeUses.length sups
decreasing_by simp_all [TypeUses.length]

theorem wtSubType_le_wtSubTypes_of_mem {st : SubType} {sts : SubTypes}
    (h : st ∈ SubTypes.toList sts) : wtSubType st ≤ wtSubTypes sts := by
  cases sts with
  | nil => simp [SubTypes.toList] at h
  | cons head tail =>
      simp only [SubTypes.toList, List.mem_cons] at h
      simp only [wtSubTypes]
      rcases h with rfl | h
      · omega
      · have := wtSubType_le_wtSubTypes_of_mem h
        omega
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

theorem wtDefType_lt_of_defd_rawSuper {sts : SubTypes} {i : Nat}
    {st : SubType} (hst : st ∈ SubTypes.toList sts) {d : DefType}
    (hd : .defd d ∈ rawSupers st) :
    wtDefType d < wtDefType (.defd (.recr sts) i) := by
  cases st with
  | sub fin sups ct =>
      have htu := wtTypeUse_le_wtTypeUses_of_mem hd
      have hstwt := wtSubType_le_wtSubTypes_of_mem hst
      simp only [wtTypeUse, wtSubType, wtDefType, wtRecType] at htu hstwt ⊢
      omega

inductive RawSuperShapeA (C : Context) (group : SubTypes) (i : Nat)
    (shape : AbsHeapType) : TypeUse → Prop where
  | idx {x : TypeIdx} {stored : DefType} :
      C.types[x.val]? = some stored → stored.absShape = some shape →
      RawSuperShapeA C group i shape (.idx x)
  | recu {j : Nat} {fin : Option Final} {sups : TypeUses} {ct : CompType} :
      j < i → (SubTypes.toList group)[j]? = some (.sub fin sups ct) →
      ct.absShape = shape → RawSuperShapeA C group i shape (.recu j)
  | defd {d : DefType} : d.absShape = some shape →
      RawSuperShapeA C group i shape (.defd d)

theorem Subtype_okA.rawSuperShape {C : Context} {group : SubTypes}
    {st : SubType} {x : TypeIdx} (h : Subtype_okA C st x) :
    ∀ tu ∈ rawSupers st,
      RawSuperShapeA C group 0
        (match st with | .sub _ _ ct => ct.absShape) tu := by
  cases h with
  | @mk C fin xs ct x cts hlen hlen₂ hall hok hsub =>
      intro tu htu
      simp only [rawSupers, TypeUses.toList_ofList] at htu
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
      have hjct : j < cts.length := by
        have hj' := (List.getElem?_eq_some_iff.mp hj).1
        simpa [SeqLen₂] using (hlen₂ ▸ hj')
      obtain ⟨_, stored, fin', xs', hlookup, hunroll⟩ :=
        hall j y cts[j] hj (List.getElem?_eq_getElem hjct)
      have hshape : cts[j].absShape = ct.absShape :=
        (hsub cts[j] (List.getElem_mem hjct)).absShape_eq.symm
      apply RawSuperShapeA.idx (stored := stored) hlookup
      simp [DefType.absShape, expandDt, hunroll, hshape]

theorem Subtype_ok2A.rawSuperShape {C : Context}
    {group : SubTypes} (hrecs : C.recs = SubTypes.toList group)
    {st : SubType} {x : TypeIdx} {i : Nat} (h : Subtype_ok2A C st x i) :
    ∀ tu ∈ rawSupers st,
      RawSuperShapeA C group i
        (match st with | .sub _ _ ct => ct.absShape) tu := by
  cases h with
  | @mk C fin sups ct x i cts hlen hlen₂ hall hvalid hok hsub =>
      intro tu htu
      have htuOk := hvalid tu htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp htu
      have hjct : j < cts.length := by
        have hj' := (List.getElem?_eq_some_iff.mp hj).1
        simpa [SeqLen₂] using (hlen₂ ▸ hj')
      have hctmem : cts[j] ∈ cts := List.getElem_mem hjct
      have hshape : cts[j].absShape = ct.absShape :=
        (hsub cts[j] hctmem).absShape_eq.symm
      obtain ⟨hbefore, fin', sups', hunroll⟩ :=
        hall j tu cts[j] hj (List.getElem?_eq_getElem hjct)
      cases tu with
      | idx y =>
          cases htuOk with
          | typeidx hlookup =>
              rename_i stored
              have hdunroll : unrollDt stored = some (.sub fin' sups' cts[j]) := by
                simpa [Context.unrollHt, hlookup] using hunroll
              apply RawSuperShapeA.idx (stored := stored) hlookup
              simp [DefType.absShape, expandDt, hdunroll, hshape]
      | recu k =>
          cases htuOk with
          | @rec_ _ _ target hlookup =>
              rw [hrecs] at hlookup
              cases target with
              | sub targetFin targetSups targetCt =>
                  have hunroll' : (SubTypes.toList group)[k]? =
                      some (.sub fin' sups' cts[j]) := by
                    simpa [Context.unrollHt, hrecs] using hunroll
                  have heq : SubType.sub targetFin targetSups targetCt =
                      .sub fin' sups' cts[j] := by
                    exact Option.some.inj (hlookup.symm.trans hunroll')
                  injection heq with hfin hsups hct
                  subst targetCt
                  exact .recu (by simpa [before] using hbefore) hlookup hshape
      | defd d =>
          have hdunroll : unrollDt d = some (.sub fin' sups' cts[j]) := by
            simpa [Context.unrollHt] using hunroll
          apply RawSuperShapeA.defd
          simp [DefType.absShape, expandDt, hdunroll, hshape]

theorem Rectype_ok2A.rawSuperShapeAt {C : Context}
    {group remaining : SubTypes} (hrecs : C.recs = SubTypes.toList group)
    {x : TypeIdx} {offset : Nat}
    (h : Rectype_ok2A C (.recr remaining) x offset) :
    ∀ {i : Nat} {st : SubType},
      (SubTypes.toList remaining)[i]? = some st →
      ∀ tu ∈ rawSupers st,
        RawSuperShapeA C group (offset + i)
          (match st with | .sub _ _ ct => ct.absShape) tu := by
  cases h with
  | empty => intro i st hget; simp [SubTypes.toList] at hget
  | @cons C head tail x offset hhead htail =>
      intro i st hget tu htu
      cases i with
      | zero =>
          have heq : head = st := by
            simpa [SubTypes.toList] using Option.some.inj hget
          subst st
          cases head
          simpa using hhead.rawSuperShape hrecs tu htu
      | succ i =>
          have hget' : (SubTypes.toList tail)[i]? = some st := by
            simpa [SubTypes.toList] using hget
          have hs := htail.rawSuperShapeAt hrecs hget' tu htu
          rw [show offset + 1 + i = offset + (i + 1) by omega] at hs
          exact hs
termination_by SubTypes.length remaining
decreasing_by simp_all [SubTypes.length]

theorem Rectype_okA.rawSuperShapeAt {C : Context}
    {sts : SubTypes} {x : TypeIdx} (h : Rectype_okA C (.recr sts) x) :
    ∀ {i : Nat} {st : SubType}, (SubTypes.toList sts)[i]? = some st →
      ∀ tu ∈ rawSupers st,
        RawSuperShapeA C sts i
          (match st with | .sub _ _ ct => ct.absShape) tu := by
  cases h with
  | empty => intro i st hget; simp [SubTypes.toList] at hget
  | @cons C head tail x hhead hscope htail =>
      intro i st hget tu htu
      cases i with
      | zero =>
          have heq : head = st := by
            simpa [SubTypes.toList] using Option.some.inj hget
          subst st
          let full : SubTypes := .cons head tail
          have hs := hhead.rawSuperShape (group := full) tu htu
          cases head
          simpa [full] using hs
      | succ i =>
          have hget' : (SubTypes.toList tail)[i]? = some st := by
            simpa [SubTypes.toList] using hget
          have hs := htail.rawSuperShapeAt hget' tu htu
          cases hs with
          | idx hlookup hshape => exact .idx hlookup hshape
          | recu hj hlookup hshape =>
              exact False.elim
                (SubTypes.noRebasedRecSupers_of_mem hscope
                  (List.mem_of_getElem? hget') htu _ rfl)
          | defd hshape => exact .defd hshape
  | @rec2 C sts x hrec =>
      intro i st hget tu htu
      have hs := hrec.rawSuperShapeAt
        (group := sts) (by simp [Context.withRecs]) hget tu htu
      cases hs with
      | idx hlookup hshape =>
          exact .idx (by simpa [Context.withRecs] using hlookup) hshape
      | recu hj hlookup hshape => exact .recu (by simpa using hj) hlookup hshape
      | defd hshape => exact .defd hshape
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

inductive ActualSuperOriginA (C : Context) (dt : DefType) : TypeUse → Prop where
  | source {x : TypeIdx} {stored : DefType} :
      C.types[x.val]? = some stored →
      ActualSuperOriginA C dt (.idx x)
  | internal {qt : RecType} {i j : Nat} : dt = .defd qt i → j < i →
      ActualSuperOriginA C dt (.defd (.defd qt j))
  | nested {D : Context} {d : DefType} : D.types = C.types →
      Deftype_okA D d → wtDefType d < wtDefType dt →
      ActualSuperOriginA C dt (.defd d)

theorem Deftype_okA.actualSuperOrigin {C : Context}
    {dt : DefType} (h : Deftype_okA C dt)
    {fin : Option Final} {sups : TypeUses} {ct : CompType}
    (hunroll : unrollDt dt = some (.sub fin sups ct)) :
    ∀ tu ∈ TypeUses.toList sups, ActualSuperOriginA C dt tu := by
  cases h with
  | @mk C qt i x hrect hi =>
      cases qt with
      | recr sts =>
          intro tu htu
          have hentry : ∃ st, (SubTypes.toList sts)[i]? = some st := by
            have hi' : i < (SubTypes.toList sts).length := by
              simpa [RecType.count] using hi
            exact ⟨(SubTypes.toList sts)[i], List.getElem?_eq_getElem hi'⟩
          obtain ⟨st, hst⟩ := hentry
          have hu := unrollDt_recr_eq sts i
          rw [hst] at hu
          simp only [Option.map_some] at hu
          rw [hu] at hunroll
          have heq : substSubType st (recvTVars (SubTypes.length sts))
              (unrollTUses (.recr sts) (SubTypes.length sts)) =
              .sub fin sups ct := Option.some.inj hunroll
          cases st with
          | sub rawFin rawSups rawCt =>
              simp only [substSubType] at heq
              injection heq with hfin hsups hct
              subst sups
              rw [TypeUses.toList_substTypeUses'] at htu
              obtain ⟨raw, hraw, hrawEq⟩ := List.mem_map.mp htu
              have horigin := hrect.rawSuperOriginAt hst raw
                (by simpa [rawSupers] using hraw)
              cases horigin with
              | @idx y stored hlookup =>
                  subst tu
                  simp only [substTypeUse]
                  rw [show recvTVars (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map TypeVar.recv by rfl]
                  rw [show unrollTUses (.recr sts) (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map
                        (fun k => TypeUse.defd (.defd (.recr sts) k)) by rfl]
                  rw [substTypeVar_unrollIdxVars]
                  exact .source hlookup
              | @recu j hj =>
                  subst tu
                  have hjcount : j < SubTypes.length sts := by
                    have hiCount : i < SubTypes.length sts := by
                      simpa [RecType.count] using hi
                    omega
                  simp only [substTypeUse]
                  rw [show recvTVars (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map TypeVar.recv by rfl]
                  rw [show unrollTUses (.recr sts) (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map
                        (fun k => TypeUse.defd (.defd (.recr sts) k)) by rfl]
                  rw [substTypeVar_unrollRecVars, if_pos hjcount]
                  exact .internal rfl hj
              | @defd D d hDC hd =>
                  subst tu
                  simp only [substTypeUse]
                  rw [substDefType_unroll_id]
                  exact .nested hDC hd
                    (wtDefType_lt_of_defd_rawSuper
                      (List.mem_of_getElem? hst) (by simpa [rawSupers] using hraw))

/-- Every supertype exposed by unrolling an amended-valid literal defined
type has the same outer shape in the surrounding stored-type context. -/
theorem Deftype_okA.actualSuper_typeuseShape {C : Context}
    {dt : DefType} (h : Deftype_okA C dt)
    {fin : Option Final} {sups : TypeUses} {ct : CompType}
    (hunroll : unrollDt dt = some (.sub fin sups ct)) :
    ∀ tu ∈ TypeUses.toList sups,
      C.typeuseShape tu = some ct.absShape := by
  cases h with
  | @mk C qt i x hrect hi =>
      cases qt with
      | recr sts =>
          intro tu htu
          have hi' : i < (SubTypes.toList sts).length := by
            simpa [RecType.count] using hi
          let rawSt := (SubTypes.toList sts)[i]
          have hst : (SubTypes.toList sts)[i]? = some rawSt :=
            List.getElem?_eq_getElem hi'
          have hu := unrollDt_recr_eq sts i
          rw [hst] at hu
          simp only [Option.map_some] at hu
          rw [hu] at hunroll
          have heq : substSubType rawSt (recvTVars (SubTypes.length sts))
              (unrollTUses (.recr sts) (SubTypes.length sts)) =
              .sub fin sups ct := Option.some.inj hunroll
          cases hrawSt : rawSt with
          | sub rawFin rawSups rawCt =>
              simp only [hrawSt, substSubType] at heq
              injection heq with hfin hsups hct
              subst sups ct
              rw [TypeUses.toList_substTypeUses'] at htu
              obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htu
              have hshape := hrect.rawSuperShapeAt hst raw
                (by simpa [rawSupers, hrawSt] using hraw)
              cases hshape with
              | @idx y stored hlookup hdShape =>
                  simp only [hrawSt] at hdShape
                  simp only [substTypeUse]
                  rw [show recvTVars (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map TypeVar.recv by rfl]
                  rw [show unrollTUses (.recr sts) (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map
                        (fun k => TypeUse.defd (.defd (.recr sts) k)) by rfl]
                  rw [substTypeVar_unrollIdxVars]
                  simpa [Context.typeuseShape, hlookup,
                    CompType.absShape_substCompType] using hdShape
              | @recu j targetFin targetSups targetCt hj htarget hctShape =>
                  simp only [hrawSt] at hctShape
                  have hjcount : j < SubTypes.length sts := by
                    have hiCount : i < SubTypes.length sts := by
                      simpa [RecType.count] using hi
                    omega
                  simp only [substTypeUse]
                  rw [show recvTVars (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map TypeVar.recv by rfl]
                  rw [show unrollTUses (.recr sts) (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map
                        (fun k => TypeUse.defd (.defd (.recr sts) k)) by rfl]
                  rw [substTypeVar_unrollRecVars, if_pos hjcount]
                  have huTarget := unrollDt_recr_eq sts j
                  rw [htarget] at huTarget
                  simp only [Option.map_some, substSubType] at huTarget
                  have habs : (DefType.defd (.recr sts) j).absShape =
                      some targetCt.absShape := by
                    simp [DefType.absShape, expandDt, huTarget]
                  simp [Context.typeuseShape, habs, hctShape,
                    CompType.absShape_substCompType]
              | @defd d hdShape =>
                  simp only [hrawSt] at hdShape
                  simp only [substTypeUse]
                  rw [substDefType_unroll_id]
                  simpa [Context.typeuseShape,
                    CompType.absShape_substCompType] using hdShape

theorem Deftype_okA.actualSuper_absShape_of_types_nil {C : Context}
    (htypes : C.types = []) {dt : DefType} (h : Deftype_okA C dt)
    {fin : Option Final} {sups : TypeUses} {ct : CompType}
    (hunroll : unrollDt dt = some (.sub fin sups ct)) :
    ∀ tu ∈ TypeUses.toList sups,
      ∃ d : DefType, tu = .defd d ∧ d.absShape = some ct.absShape := by
  cases h with
  | @mk C qt i x hrect hi =>
      cases qt with
      | recr sts =>
          intro tu htu
          have hi' : i < (SubTypes.toList sts).length := by
            simpa [RecType.count] using hi
          let rawSt := (SubTypes.toList sts)[i]
          have hst : (SubTypes.toList sts)[i]? = some rawSt :=
            List.getElem?_eq_getElem hi'
          have hu := unrollDt_recr_eq sts i
          rw [hst] at hu
          simp only [Option.map_some] at hu
          rw [hu] at hunroll
          have heq : substSubType rawSt (recvTVars (SubTypes.length sts))
              (unrollTUses (.recr sts) (SubTypes.length sts)) =
              .sub fin sups ct := Option.some.inj hunroll
          cases hrawSt : rawSt with
          | sub rawFin rawSups rawCt =>
              simp only [hrawSt, substSubType] at heq
              injection heq with hfin hsups hct
              subst sups ct
              rw [TypeUses.toList_substTypeUses'] at htu
              obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htu
              have hshape := hrect.rawSuperShapeAt hst raw
                (by simpa [rawSupers, hrawSt] using hraw)
              cases hshape with
              | @idx y stored hdShape => exact False.elim (by
                  have horigin := hrect.rawSuperOriginAt hst (.idx y)
                    (by simpa [rawSupers, hrawSt] using hraw)
                  cases horigin with
                  | idx hlookup => simpa [htypes] using hlookup)
              | @recu j targetFin targetSups targetCt hj htarget hctShape =>
                  simp only [hrawSt] at hctShape
                  have hjcount : j < SubTypes.length sts := by
                    have hiCount : i < SubTypes.length sts := by
                      simpa [RecType.count] using hi
                    omega
                  simp only [substTypeUse]
                  rw [show recvTVars (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map TypeVar.recv by rfl]
                  rw [show unrollTUses (.recr sts) (SubTypes.length sts) =
                      (List.range (SubTypes.length sts)).map
                        (fun k => TypeUse.defd (.defd (.recr sts) k)) by rfl]
                  rw [substTypeVar_unrollRecVars, if_pos hjcount]
                  refine ⟨.defd (.recr sts) j, rfl, ?_⟩
                  have huTarget := unrollDt_recr_eq sts j
                  rw [htarget] at huTarget
                  simp only [Option.map_some, substSubType] at huTarget
                  have habs : (DefType.defd (.recr sts) j).absShape =
                      some targetCt.absShape := by
                    simp [DefType.absShape, expandDt, huTarget]
                  rw [habs, hctShape]
                  simpa using congrArg some
                    (CompType.absShape_substCompType rawCt
                      (recvTVars (SubTypes.length sts))
                      (unrollTUses (.recr sts) (SubTypes.length sts))).symm
              | @defd d hdShape =>
                  simp only [hrawSt] at hdShape
                  simp only [substTypeUse]
                  rw [substDefType_unroll_id]
                  exact ⟨d, rfl, by
                    simpa only [CompType.absShape_substCompType] using hdShape⟩

private theorem goodHeapShape_of_deftype_okA_types_nil_aux :
    ∀ n : Nat, ∀ {C D : Context} {dt : DefType},
      wtDefType dt = n → C.types = [] → Deftype_okA C dt →
      ∃ a : AbsHeapType, GoodHeapShapeA D (.use (.defd dt)) a := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n outerIH =>
      intro C D dt hweight htypes hvalid
      cases dt with
      | defd qt i =>
          cases hvalid with
          | mk hrect hi =>
              have hall : ∀ k : Nat, k < qt.count →
                  ∃ a : AbsHeapType,
                    GoodHeapShapeA D (.use (.defd (.defd qt k))) a := by
                intro k
                induction k using Nat.strongRecOn with
                | _ k innerIH =>
                    intro hk
                    let current : DefType := .defd qt k
                    have hcurrent : Deftype_okA C current := .mk hrect hk
                    obtain ⟨shapeCt, hexpand⟩ := hcurrent.expand_exists
                    cases hexpand with
                    | mk hexpandEq =>
                        cases hunroll : unrollDt current with
                        | none =>
                            simp [expandDt, hunroll] at hexpandEq
                        | some st =>
                            cases st with
                            | sub fin sups ct =>
                                have hct : ct = shapeCt := by
                                  simpa [expandDt, hunroll] using hexpandEq
                                subst shapeCt
                                refine ⟨ct.absShape,
                                  GoodHeapShapeA.use
                                    (by simpa [Context.unrollHt] using hunroll) ?_⟩
                                intro tu htu
                                obtain ⟨superDt, htuEq, hsuperShape⟩ :=
                                  hcurrent.actualSuper_absShape_of_types_nil
                                    htypes hunroll tu htu
                                subst tu
                                have horigin := hcurrent.actualSuperOrigin
                                  hunroll (.defd superDt) htu
                                cases horigin with
                                | @internal originQt originI j hdtEq hj =>
                                    dsimp [current] at hdtEq
                                    injection hdtEq with hq hiEq
                                    subst originQt
                                    subst originI
                                    obtain ⟨a, ha⟩ := innerIH j hj (by omega)
                                    have haShape := ha.typeuseShape (fun q hq => by cases hq)
                                    have hae : a = ct.absShape := Option.some.inj
                                      (haShape.symm.trans (by
                                        simpa [Context.typeuseShape] using hsuperShape))
                                    subst a
                                    exact ha
                                | nested hEtypes hd hsmaller =>
                                    rename_i E
                                    have hdn : wtDefType superDt < n := by
                                      rw [← hweight]
                                      exact hsmaller
                                    obtain ⟨a, ha⟩ := outerIH (wtDefType superDt) hdn
                                      (D := D) rfl (hEtypes.trans htypes) hd
                                    have haShape := ha.typeuseShape (fun q hq => by cases hq)
                                    have hae : a = ct.absShape := Option.some.inj
                                      (haShape.symm.trans (by
                                        simpa [Context.typeuseShape] using hsuperShape))
                                    subst a
                                    exact ha
              exact hall i hi

/-- Amended validity of a literal defined type in a context with no stored
type indices yields its full structural supertype-shape certificate.  The
target certificate context may differ because literal unrolling observes no
context component. -/
theorem Deftype_okA.goodHeapShape_of_types_nil {C D : Context}
    (htypes : C.types = []) {dt : DefType} (h : Deftype_okA C dt) :
    ∃ a : AbsHeapType, GoodHeapShapeA D (.use (.defd dt)) a := by
  exact goodHeapShape_of_deftype_okA_types_nil_aux
    (wtDefType dt) rfl htypes h

/-! ## Ranked source nodes -/

/-- Every ranked source type node carries the structural shape certificate
selected by its checked type section.  Index nodes recurse once to their
stored defined type; declared-super edges then strictly lower the certified
source rank. -/
theorem Context.SourceTypeNodeA.goodHeapShape
    {C : Context} (hgraph : C.SourceTypeGraphOkA)
    (hshapes : C.SourceTypeShapesOkA) :
    ∀ {r : Nat} {tu : TypeUse} {a : AbsHeapType},
      C.SourceTypeNodeA (.use tu) r →
      C.typeuseShape tu = some a →
      GoodHeapShapeA C (.use tu) a := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
      intro tu a hnode hshape
      cases hnode with
      | @idx x dt hlookup =>
          have hdefShape : C.typeuseShape (.defd dt) = some a := by
            simpa [Context.typeuseShape, hlookup] using hshape
          have hdef := ih (2 * x.val) (by omega)
            (Context.SourceTypeNodeA.defd hlookup) hdefShape
          exact hdef.idx_of_lookup hlookup
      | @defd i dt hlookup =>
          simp only [Context.typeuseShape, DefType.absShape, expandDt] at hshape
          cases hu : unrollDt dt with
          | none => simp [hu] at hshape
          | some st =>
              cases st with
              | sub fin sups ct =>
                  have hct : a = ct.absShape := by
                    have hs : some ct.absShape = some a := by
                      simpa [hu] using hshape
                    exact (Option.some.inj hs).symm
                  subst a
                  apply GoodHeapShapeA.use (by
                    simpa [Context.unrollHt] using hu)
                  intro u hsup
                  have hg : .use u ∈ C.heapSupers (.use (.defd dt)) := by
                    simp [Context.heapSupers, hu, hsup]
                  obtain ⟨s, hsr, htarget⟩ :=
                    hgraph (.defd hlookup) (.use u) hg
                  have hrootShape : C.typeuseShape (.defd dt) =
                      some ct.absShape := by
                    simp [Context.typeuseShape, DefType.absShape, expandDt, hu]
                  obtain ⟨u', heq, hshape'⟩ := hshapes (.defd hlookup)
                    hrootShape (.use u) hg
                  injection heq with heq
                  subst u'
                  exact ih s hsr htarget hshape'

private theorem goodHeapShape_of_deftype_okA_source_aux :
    ∀ n : Nat, ∀ {B C : Context} {dt : DefType},
      wtDefType dt = n → C.types = B.types →
      B.SourceTypeGraphOkA → B.SourceTypeShapesOkA →
      Deftype_okA C dt →
      ∃ a : AbsHeapType, GoodHeapShapeA B (.use (.defd dt)) a := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n outerIH =>
      intro B C dt hweight htypes hgraph hshapes hvalid
      cases dt with
      | defd qt i =>
          cases hvalid with
          | mk hrect hi =>
              have hall : ∀ k : Nat, k < qt.count →
                  ∃ a : AbsHeapType,
                    GoodHeapShapeA B (.use (.defd (.defd qt k))) a := by
                intro k
                induction k using Nat.strongRecOn with
                | _ k innerIH =>
                    intro hk
                    let current : DefType := .defd qt k
                    have hcurrent : Deftype_okA C current := .mk hrect hk
                    obtain ⟨shapeCt, hexpand⟩ := hcurrent.expand_exists
                    cases hexpand with
                    | mk hexpandEq =>
                        cases hunroll : unrollDt current with
                        | none => simp [expandDt, hunroll] at hexpandEq
                        | some st =>
                            cases st with
                            | sub fin sups ct =>
                                have hct : ct = shapeCt := by
                                  simpa [expandDt, hunroll] using hexpandEq
                                subst shapeCt
                                refine ⟨ct.absShape,
                                  GoodHeapShapeA.use
                                    (by simpa [Context.unrollHt] using hunroll) ?_⟩
                                intro tu htu
                                have hsuperShapeC :=
                                  hcurrent.actualSuper_typeuseShape hunroll tu htu
                                have hsuperShapeB : B.typeuseShape tu =
                                    some ct.absShape := by
                                  rw [← Context.typeuseShape_eq_of_types_eq
                                    htypes tu]
                                  exact hsuperShapeC
                                have horigin := hcurrent.actualSuperOrigin
                                  hunroll tu htu
                                cases horigin with
                                | @source x stored hlookup =>
                                    have hlookupB : B.types[x.val]? = some stored := by
                                      simpa [htypes] using hlookup
                                    exact Context.SourceTypeNodeA.goodHeapShape
                                      hgraph hshapes (.idx hlookupB) hsuperShapeB
                                | @internal originQt originI j hdtEq hj =>
                                    dsimp [current] at hdtEq
                                    injection hdtEq with hq hiEq
                                    subst originQt
                                    subst originI
                                    obtain ⟨a, ha⟩ := innerIH j hj (by omega)
                                    have haShape := ha.typeuseShape
                                      (fun q hq => by cases hq)
                                    have hae : a = ct.absShape := Option.some.inj
                                      (haShape.symm.trans hsuperShapeB)
                                    subst a
                                    exact ha
                                | @nested E d hEtypes hd hsmaller =>
                                    have hdn : wtDefType d < n := by
                                      rw [← hweight]
                                      exact hsmaller
                                    obtain ⟨a, ha⟩ := outerIH (wtDefType d) hdn
                                      (B := B) rfl (hEtypes.trans htypes)
                                      hgraph hshapes hd
                                    have haShape := ha.typeuseShape
                                      (fun q hq => by cases hq)
                                    have hae : a = ct.absShape := Option.some.inj
                                      (haShape.symm.trans hsuperShapeB)
                                    subst a
                                    exact ha
              exact hall i hi

/-- A valid literal defined type in a context backed by the same checked
source type graph has a structural shape certificate in that source context. -/
theorem Deftype_okA.goodHeapShape_of_source
    {B C : Context} (htypes : C.types = B.types)
    (hgraph : B.SourceTypeGraphOkA) (hshapes : B.SourceTypeShapesOkA)
    {dt : DefType} (h : Deftype_okA C dt) :
    ∃ a : AbsHeapType, GoodHeapShapeA B (.use (.defd dt)) a := by
  exact goodHeapShape_of_deftype_okA_source_aux
    (wtDefType dt) rfl htypes hgraph hshapes h

/-- Source graph, concrete-shape, and shape-preservation certificates provide
structural shape witnesses for every amended-valid heap type when recursive
scratch space is empty. -/
theorem Context.validHeapShapesA_of_source {C : Context}
    (hgraph : C.SourceTypeGraphOkA) (hconcrete : C.SourceTypesConcreteA)
    (hshapes : C.SourceTypeShapesOkA) (hrecs : C.recs = []) :
    C.ValidHeapShapesA := by
  intro ht hok
  cases hok with
  | abs => exact ⟨_, .abs _⟩
  | typeuse htu =>
      cases htu with
      | typeidx hlookup =>
          obtain ⟨a, ha, _⟩ := hconcrete (.idx hlookup)
          exact ⟨a, Context.SourceTypeNodeA.goodHeapShape
            hgraph hshapes (.idx hlookup) ha⟩
      | rec_ hlookup => simp [hrecs] at hlookup
      | deftype hdt =>
          exact hdt.goodHeapShape_of_source rfl hgraph hshapes

/-- A checked grammar type section equips every module-validation context
with the same stored type vector and empty recursive scratch space with the
full structural heap-shape environment. -/
theorem Types_okA.validHeapShapesA_in_context
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (hvalid : Types_okA Context.empty tds dts)
    (C : Context) (htypes : C.types = dts) (hrecs : C.recs = []) :
    C.ValidHeapShapesA := by
  exact Context.validHeapShapesA_of_source
    (hvalid.sourceTypeGraphOkA_in_context hsyn C htypes)
    (hvalid.sourceTypesConcreteA_in_context C htypes)
    (hvalid.sourceTypeShapesOkA_in_context hsyn C htypes)
    hrecs

/-- In the empty context, every amended-valid heap type carries a structural
shape certificate. -/
theorem Context.empty_validHeapShapesA :
    Context.empty.ValidHeapShapesA := by
  intro ht hok
  cases hok with
  | abs => exact ⟨_, .abs _⟩
  | typeuse htu =>
      cases htu with
      | typeidx hlookup => simp [Context.empty] at hlookup
      | rec_ hlookup => simp [Context.empty] at hlookup
      | deftype hdt =>
          exact hdt.goodHeapShape_of_types_nil (D := Context.empty)
            (by simp [Context.empty])

end WasmGemmGnaf.Wasm.Core
