import WasmGemmGnaf.Wasm.Core.ValidateTypesFullComplete
import WasmGemmGnaf.Wasm.Core.ValidateInstrSourceComplete
import WasmGemmGnaf.Wasm.Core.SubtypeTransport

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

def Instr.directSpecialA : Instr → Bool
  | .unreachable | .drop | .select none | .br _ | .brTable _ _
  | .brOnNull _ | .brOnNonNull _ | .brOnCast _ _ _
  | .brOnCastFail _ _ _ | .ret | .returnCall _ | .returnCallRef _
  | .returnCallIndirect _ _ | .throw _ | .throwRef | .refIsNull
  | .refAsNonNull | .refTest _ | .refCast _ | .externConvertAny
  | .anyConvertExtern | .block _ _ | .loop _ _ | .ifElse _ _ _
  | .tryTable _ _ _ => true
  | _ => false

theorem directSpecialA_eq_source (i : Instr) :
    Instr.directSpecialA i = Instr.directSourceSpecialA i := by
  cases i <;> rfl

private theorem all_hasDefault_of_defaultable {ts : List ValType}
    (h : SeqAll Defaultable ts) : ts.all ValType.hasDefault = true := by
  rw [List.all_eq_true]
  intro t ht
  cases h t ht with
  | mk hd => exact hd

theorem St.SatA.split_append {C : Context} {st : St}
    {frame args : List ValType} (h : St.SatA C st (frame ++ args)) :
    ∃ base, st.popsA C args = some base ∧ St.SatA C base frame := by
  obtain ⟨rest, hp, hempty⟩ := h
  rw [St.popsA_append] at hp
  cases hargs : st.popsA C args with
  | none => simp only [hargs] at hp; contradiction
  | some base =>
      simp only [hargs] at hp
      exact ⟨base, rfl, rest, hp, hempty⟩

private theorem St.SatA.pushs {C : Context} {st : St}
    {frame ts : List ValType} (h : St.SatA C st frame) :
    St.SatA C (st.pushs ts) (frame ++ ts) :=
  St.satA_append (St.pushs_popsA C st ts) h

private theorem splitLast?_append_singleton {X : Type} (xs : List X) (x : X) :
    splitLast? (xs ++ [x]) = some (xs, x) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simp only [List.cons_append, splitLast?]
          have ih' : splitLast? (z :: (zs ++ [x])) =
              some (z :: zs, x) := by
            simpa only [List.cons_append] using ih
          rw [ih']
          rfl

private theorem St.pop_of_popEA {C : Context} {st st' : St} {t : ValType}
    (h : st.popEA C t = some st') :
    ∃ u, st.pop = some (u, st') ∧ subOfA C u t = true := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA, St.pop] at h ⊢
          exact ⟨.bot, ⟨rfl, h⟩, rfl⟩
      | cons a rest =>
          simp only [St.popEA] at h
          split at h
          · rename_i hs
            simp only [Option.some.injEq] at h
            subst st'
            exact ⟨a, rfl, hs⟩
          · contradiction

private theorem St.SatA.popRef_of_ref {C : Context} {st : St}
    {frame : List ValType} {rt : RefType}
    (h : St.SatA C st (frame ++ [.ref rt])) :
    ∃ rt? base, st.popRef = some (rt?, base) ∧
      subOfA C (poppedRefValType rt?) (.ref rt) = true ∧
      St.SatA C base frame := by
  obtain ⟨base, hp, hbase⟩ := St.SatA.split_append h
  have hp' : st.popEA C (.ref rt) = some base := by
    simpa only [St.popsA] using hp
  obtain ⟨u, hpop, hsub⟩ := St.pop_of_popEA hp'
  cases u with
  | ref actual =>
      refine ⟨some actual, base, ?_, ?_, hbase⟩
      · simp [St.popRef, hpop]
      · simpa [poppedRefValType] using hsub
  | bot =>
      refine ⟨none, base, ?_, ?_, hbase⟩
      · simp [St.popRef, hpop]
      · simpa [poppedRefValType] using hsub
  | num nt => simp [subOfA, decValtypeSubN] at hsub
  | vec => simp [subOfA, decValtypeSubN] at hsub

/-- Heap component retained by the principal reference pop.  A polymorphic
stack pop is represented by the semantic bottom heap. -/
private def poppedHeapType : Option RefType → HeapType
  | some (.ref _ ht) => ht
  | none => .abs .bot

private theorem poppedNonNull_valid {C : Context} {rt? : Option RefType}
    (h : ValValidA C (poppedRefValType rt?)) :
    ValValidA C (.ref (.ref none (poppedHeapType rt?))) := by
  cases rt? with
  | none => exact ValValidA.refAbs C none .bot
  | some rt =>
      cases rt with
      | ref nul ht =>
          exact valValidA_ref_nonnull (by simpa [poppedRefValType] using h)

private theorem poppedNonNull_sub {C : Context} {rt? : Option RefType}
    {ht : HeapType}
    (htypes : SourceTypeCompleteA C)
    (hleft : (poppedHeapType rt?).SourceA C) (hright : Heaptype_okA C ht)
    (h : subOfA C (poppedRefValType rt?)
      (.ref (.ref (some .null) ht)) = true) :
    subOfA C (.ref (.ref none (poppedHeapType rt?)))
      (.ref (.ref none ht)) = true := by
  cases rt? with
  | none =>
      exact subOfA_ref_heap (htypes.completeLeft hleft hright Heaptype_subA.bot)
  | some rt =>
      cases rt with
      | ref nul actual =>
          have hs := valtype_subA_of_subOfA h
          cases hs with
          | ref href =>
              cases href with
              | null hactual =>
                  exact subOfA_ref_heap (htypes.completeLeft hleft hright hactual)

/-- The two conversion instructions retain the popped nullability and replace
only its abstract heap family.  Polymorphic bottom is principalized as a
non-null reference. -/
private def poppedAbstractRef (a : AbsHeapType) : Option RefType → ValType
  | some (.ref nul _) => .ref (.ref nul (.abs a))
  | none => .ref (.ref none (.abs a))

private theorem poppedAbstractRef_valid {C : Context} {a : AbsHeapType}
    (ha : Heaptype_okA C (.abs a)) {rt? : Option RefType} :
    ValValidA C (poppedAbstractRef a rt?) := by
  cases rt? with
  | none => exact ValValidA.refAbs C none a
  | some rt =>
      cases rt with
      | ref nul ht => exact ValValidA.refAbs C nul a

private theorem poppedAbstractRef_sub {C : Context} {a : AbsHeapType}
    {rt? : Option RefType} {nul : Option Null} {inputHeap : HeapType}
    (htypes : SourceTypeCompleteA C)
    (h : subOfA C (poppedRefValType rt?)
      (.ref (.ref nul inputHeap)) = true) :
    subOfA C (poppedAbstractRef a rt?) (.ref (.ref nul (.abs a))) = true := by
  apply htypes.valtypeComplete
  · cases rt? with
    | none => trivial
    | some rt => cases rt <;> trivial
  · trivial
  cases rt? with
  | none =>
      cases nul with
      | none => exact .ref (.nonnull .refl)
      | some n => cases n; exact .ref (.null .refl)
  | some rt =>
      cases rt with
      | ref actualNul actualHeap =>
          have hs := valtype_subA_of_subOfA h
          cases hs with
          | ref href =>
              cases href with
              | nonnull _ => exact .ref (.nonnull .refl)
              | null _ => exact .ref (.null .refl)

private theorem St.popEA_poly {C : Context} {st st' : St} {t : ValType}
    (h : st.popEA C t = some st') : st'.poly = st.poly := by
  obtain ⟨u, hp, _⟩ := St.pop_of_popEA h
  cases st with
  | mk poly vals =>
      cases vals <;> cases poly <;> simp [St.pop] at hp
      all_goals obtain ⟨rfl, rfl⟩ := hp <;> rfl

private theorem St.popsA_poly {C : Context} {st st' : St} :
    ∀ {ts : List ValType}, st.popsA C ts = some st' →
      st'.poly = st.poly := by
  intro ts
  induction ts generalizing st' with
  | nil => intro h; cases h; rfl
  | cons t ts ih =>
      intro h
      simp only [St.popsA] at h
      cases hp : st.popsA C ts with
      | none => simp only [hp] at h; contradiction
      | some s =>
          simp only [hp] at h
          rw [St.popEA_poly h, ih hp]

private theorem St.popsA_vals {C : Context} :
    ∀ {ts : List ValType} {st st' : St},
      st.popsA C ts = some st' →
      st'.vals = st.vals.drop ts.length := by
  intro ts
  induction ts with
  | nil => intro st st' h; cases h; simp
  | cons t ts ih =>
      intro st st' h
      simp only [St.popsA] at h
      cases hp : st.popsA C ts with
      | none => simp only [hp] at h; contradiction
      | some s =>
          simp only [hp] at h
          have hs : s.vals = st.vals.drop ts.length := ih hp
          have hd : st.vals.drop (t :: ts).length =
              (st.vals.drop ts.length).drop 1 := by
            rw [List.drop_drop]
            rfl
          cases hv : s.vals with
          | nil =>
              cases s with
              | mk poly vals =>
                  simp only at hv
                  subst vals
                  cases poly <;> simp [St.popEA] at h
                  subst st'
                  rw [hd, ← hs]
                  rfl
          | cons a rest =>
              cases s with
              | mk poly vals =>
                  simp only at hv
                  subst vals
                  simp only [St.popEA] at h
                  split at h
                  · simp only [Option.some.injEq] at h
                    subst st'
                    rw [hd, ← hs]
                    rfl
                  · contradiction

private theorem St.popN_principalA {C : Context} :
    ∀ {ts : List ValType} {st st' : St},
      st.popsA C ts = some st' →
      ∃ us s, st.popN ts.length = some (us, s) ∧
        subsA C us ts = true := by
  intro ts
  induction ts with
  | nil => intro st st' h; exact ⟨[], st, rfl, rfl⟩
  | cons t ts ih =>
      intro st st' h
      simp only [St.popsA] at h
      cases hp : st.popsA C ts with
      | none => simp only [hp] at h; contradiction
      | some s₁ =>
          simp only [hp] at h
          obtain ⟨us, s, hpn, hsub⟩ := ih hp
          have hs : s = s₁ :=
            St.eq_of (by rw [St.popN_poly hpn, St.popsA_poly hp])
              (by rw [St.popN_vals hpn, St.popsA_vals hp])
          obtain ⟨u, hpop, hsu⟩ := St.pop_of_popEA h
          refine ⟨u :: us, st', ?_, ?_⟩
          · rw [List.length_cons, St.popN_succ]
            simp only [hpn, hs, hpop]
          · simpa [subsA, decResulttypeSubN, decSeq₂] using
              And.intro hsu hsub

private theorem St.popEA_weaken_noValid {C : Context} {st st' : St}
    {t₁ t₂ : ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (ht₁ : Valtype_okA C t₁) (hsub : Valtype_subA C t₁ t₂)
    (hp : st.popEA C t₁ = some st') : st.popEA C t₂ = some st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at hp ⊢
          exact hp
      | cons a rest =>
          simp only [St.popEA] at hp ⊢
          split at hp
          · rename_i ha₁
            have ha₂ : decValtypeSubN C C.subtypeFuel a t₂ = true :=
              decValtypeSubN_complete_of_heap hheap
                (Valtype_subA.trans ht₁ (decValtypeSubN_sound ha₁) hsub)
            change subOfA C a t₂ = true at ha₂
            rw [if_pos ha₂]
            exact hp
          · contradiction

private theorem St.popsA_weaken_noValid {C : Context}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true) :
    ∀ {ts₁ ts₂ : List ValType} {st st' : St},
      Resulttype_okA C ts₁ → Resulttype_subA C ts₁ ts₂ →
      st.popsA C ts₁ = some st' → st.popsA C ts₂ = some st' := by
  intro ts₁
  induction ts₁ with
  | nil =>
      intro ts₂ st st' hok hsub hp
      cases hsub with
      | mk hlen _ =>
          have : ts₂ = [] :=
            List.eq_nil_of_length_eq_zero (by simpa [SeqLen₂] using hlen.symm)
          subst ts₂
          exact hp
  | cons t₁ ts₁ ih =>
      intro ts₂ st st' hok hsub hp
      cases ts₂ with
      | nil =>
          cases hsub with
          | mk hlen _ => simp [SeqLen₂] at hlen
      | cons t₂ ts₂ =>
          cases hok with
          | mk hok =>
              cases hsub with
              | mk hlen hall =>
                  simp only [St.popsA] at hp ⊢
                  cases hp₁ : st.popsA C ts₁ with
                  | none => simp only [hp₁] at hp; contradiction
                  | some s =>
                      simp only [hp₁] at hp
                      have htailOk : Resulttype_okA C ts₁ :=
                        .mk (fun u hu => hok u (by simp [hu]))
                      have htailSub : Resulttype_subA C ts₁ ts₂ := by
                        refine .mk (by simpa [SeqLen₂] using Nat.succ.inj hlen) ?_
                        intro i a b ha hb
                        exact hall (i + 1) a b (by simpa using ha) (by simpa using hb)
                      have hp₂ : st.popsA C ts₂ = some s :=
                        ih htailOk htailSub hp₁
                      simp only [hp₂]
                      exact St.popEA_weaken_noValid hheap
                        (hok t₁ (by simp)) (hall 0 t₁ t₂ rfl rfl) hp

private theorem St.SatA.weaken_noValid {C : Context} {st : St}
    {ts₁ ts₂ : List ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hok : Resulttype_okA C ts₁) (hsub : Resulttype_subA C ts₁ ts₂)
    (hsat : St.SatA C st ts₁) : St.SatA C st ts₂ := by
  obtain ⟨base, hp, hempty⟩ := hsat
  exact ⟨base, St.popsA_weaken_noValid hheap hok hsub hp, hempty⟩

private theorem instrDispatch_complete_of_heap {C : Context} {i : Instr}
    {it : InstrType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true)
    (hsyn : Instr.isSyn i = true)
    (hspecial : Instr.directSpecialA i = false) (h : Instr_okA C i it) :
    (match instrTypeA C i with
      | some it => some it
      | none => instrType C i) = some it := by
  have hwf : Instr.wf i = true := h.wf_of
  have href : ∀ {r₁ r₂ : RefType}, Reftype_subA C r₁ r₂ →
      decReftypeSubN C C.subtypeFuel r₁ r₂ = true :=
    fun hs => decReftypeSubN_complete_of_heap hheap hs
  have hstorage : ∀ {z₁ z₂ : StorageType}, Storagetype_subA C z₁ z₂ →
      decStoragetypeSubN C C.subtypeFuel z₁ z₂ = true :=
    fun hs => decStoragetypeSubN_complete_of_heap hheap hs
  cases h <;> simp_all only [Instr.directSpecialA]
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Expand _ _›
  all_goals try cases ‹Defaultable _›
  all_goals try cases ‹Option LoadOp›
  all_goals try cases ‹Option StoreOp›
  all_goals try cases ‹FieldType›
  all_goals try
    have hdecStorage := hstorage (by assumption)
  all_goals try
    have hdecRef := href (by assumption)
  all_goals try
    have hcheckVal := checkValtypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)
  all_goals try
    have hcheckHeap := checkHeaptypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)
  all_goals try
    have hdefaults := all_hasDefault_of_defaultable (by assumption)
  all_goals try
    rw [checkValtypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)]
  all_goals try
    rw [checkHeaptypeOkA_complete
      (by simpa [Instr.wf] using hwf) (by assumption)]
  all_goals
    simp_all [instrTypeA, instrTypeRawA, instrType, instrTypeRaw,
      funcTypeOfA, funcTypeOf, href, hstorage, StorageType.isUnpacked,
      ValType.hasDefault, VecType.size]
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

private theorem blockTypeA_complete {C : Context} {bt : BlockType}
    {dom cod : List ValType} (hsyn : bt.isSyn = true)
    (h : Blocktype_okA C bt ⟨dom, [], cod⟩) :
    blockTypeA C bt = some (dom, cod) := by
  cases h with
  | valtype hall =>
      rename_i t
      cases t with
      | none => rfl
      | some t =>
          have ht : Valtype_okA C t := hall t rfl
          simp only [BlockType.isSyn, Option.toList, List.all_cons,
            List.all_nil, Bool.and_true] at hsyn
          simp [blockTypeA, checkValtypeOkA_complete hsyn ht]
  | typeidx hx he =>
      cases he with
      | mk he => simp [blockTypeA, hx, funcTypeOfA, he]

theorem resultOk_nil (C : Context) : Resulttype_okA C [] :=
  .mk (fun t ht => nomatch ht)

theorem resultOk_cons {C : Context} {t : ValType}
    {ts : List ValType} (ht : Valtype_okA C t)
    (hts : Resulttype_okA C ts) : Resulttype_okA C (t :: ts) := by
  cases hts with
  | mk hall =>
      exact .mk (fun u hu => by
        simp only [List.mem_cons] at hu
        exact hu.elim (fun h => h ▸ ht) (hall u))

theorem resultOk_append {C : Context} {ts us : List ValType}
    (hts : Resulttype_okA C ts) (hus : Resulttype_okA C us) :
    Resulttype_okA C (ts ++ us) := by
  cases hts with
  | mk hts =>
      cases hus with
      | mk hus =>
          exact .mk (fun t ht => by
            rw [List.mem_append] at ht
            exact ht.elim (hts t) (hus t))

theorem resultOk_of_append_left {C : Context} {ts us : List ValType}
    (h : Resulttype_okA C (ts ++ us)) : Resulttype_okA C ts := by
  cases h with
  | mk hall => exact .mk (fun t ht => hall t (List.mem_append_left _ ht))

theorem resultOk_of_append_right {C : Context} {ts us : List ValType}
    (h : Resulttype_okA C (ts ++ us)) : Resulttype_okA C us := by
  cases h with
  | mk hall => exact .mk (fun t ht => hall t (List.mem_append_right _ ht))

theorem resultOk_singleton {C : Context} {t : ValType}
    (ht : Valtype_okA C t) : Resulttype_okA C [t] :=
  resultOk_cons ht (resultOk_nil C)

private theorem reftypeOk_diff {C : Context} {rt₁ rt₂ : RefType}
    (h : Reftype_okA C rt₁) : Reftype_okA C (RefType.diff rt₁ rt₂) := by
  cases rt₁ with
  | ref nul₁ ht₁ =>
      cases h with
      | mk hht =>
          cases rt₂ with
          | ref nul₂ ht₂ =>
              cases nul₂ <;> exact .mk hht

private theorem blockTypeResultOkA {C : Context} {bt : BlockType}
    {dom cod : List ValType} (hC : Context.ValidA C)
    (hsyn : bt.isSyn = true) (h : Blocktype_okA C bt ⟨dom, [], cod⟩) :
    Resulttype_okA C dom ∧ Resulttype_okA C cod := by
  have hc := blockTypeA_complete hsyn h
  obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hc
  exact ⟨ResultValidA.ok hdom, ResultValidA.ok hcod⟩

private theorem blockTypeResultSourceA {C : Context} {bt : BlockType}
    {dom cod : List ValType} (hC : C.SourceA) (hsyn : bt.isSyn = true)
    (h : Blocktype_okA C bt ⟨dom, [], cod⟩) :
    ResultSourceA C dom ∧ ResultSourceA C cod := by
  cases h with
  | valtype hall =>
      rename_i t
      cases t with
      | none => exact ⟨ResultSourceA.nil C, ResultSourceA.nil C⟩
      | some t =>
          have htOk : Valtype_okA C t := hall t rfl
          have htSyn : t.isSyn = true := by
            simpa [BlockType.isSyn] using hsyn
          exact ⟨ResultSourceA.nil C,
            ResultSourceA.singleton (htOk.sourceA_of_syn htSyn)⟩
  | typeidx hx he =>
      have hcomp := hC.types hx he
      exact hcomp

theorem instrResultOkA {C : Context} {i : Instr} {it : InstrType}
    (hC : Context.ValidA C)
    (htypes : SourceTypeCompleteA C) (hsource : C.SourceA)
    (hsyn : Instr.isSyn i = true) (h : Instr_okA C i it) :
    Resulttype_okA C it.dom ∧ Resulttype_okA C it.cod := by
  by_cases hspecial : Instr.directSpecialA i = true
  · cases h <;> simp_all only [Instr.directSpecialA]
    all_goals try contradiction
    case pos.unreachable =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hdom, hcod, _⟩
      exact ⟨hdom, hcod⟩
    case pos.drop =>
      exact ⟨resultOk_singleton (by assumption), resultOk_nil C⟩
    case pos.select_impl _ ht _ =>
      exact ⟨resultOk_cons ht (resultOk_cons ht
        (resultOk_singleton (.num .mk))), resultOk_singleton ht⟩
    case pos.block =>
      simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
      exact blockTypeResultOkA hC hsyn.1 (by assumption)
    case pos.loop =>
      simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
      exact blockTypeResultOkA hC hsyn.1 (by assumption)
    case pos.if_ =>
      simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
      obtain ⟨hdom, hcod⟩ := blockTypeResultOkA hC hsyn.1.1 (by assumption)
      exact ⟨resultOk_append hdom (resultOk_singleton (.num .mk)), hcod⟩
    case pos.br =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hlabel : Resulttype_okA C _ :=
        hC.labels (SameTypeEnv.refl C) (by assumption)
      exact ⟨resultOk_append hfree hlabel, hcod⟩
    case pos.br_table =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hdom, hcod, _⟩
      exact ⟨hdom, hcod⟩
    case pos.br_on_null =>
      have hlabel : Resulttype_okA C _ :=
        hC.labels (SameTypeEnv.refl C) (by assumption)
      refine ⟨resultOk_append hlabel (resultOk_singleton (.ref (.mk ?_))),
        resultOk_append hlabel (resultOk_singleton (.ref (.mk ?_)))⟩
      all_goals assumption
    case pos.br_on_non_null =>
      rename_i l ts nul ht hlookup
      have hlabelAll : Resulttype_okA C _ :=
        hC.labels (SameTypeEnv.refl C) (by assumption)
      have hlabel := resultOk_of_append_left hlabelAll
      have hlast := resultOk_of_append_right hlabelAll
      cases hlast with
      | mk hall =>
          have href := hall (.ref (.ref nul ht)) (by simp)
          cases href with
          | ref href =>
              cases href with
              | mk hht =>
                  exact ⟨resultOk_append hlabel
                    (resultOk_singleton (.ref (.mk hht))), hlabel⟩
    case pos.br_on_cast =>
      have hlabelAll : Resulttype_okA C _ :=
        hC.labels (SameTypeEnv.refl C) (by assumption)
      have hlabel := resultOk_of_append_left hlabelAll
      refine ⟨resultOk_append hlabel (resultOk_singleton (.ref ?_)),
        resultOk_append hlabel (resultOk_singleton (.ref (reftypeOk_diff ?_)))⟩
      all_goals assumption
    case pos.br_on_cast_fail =>
      have hlabelAll : Resulttype_okA C _ :=
        hC.labels (SameTypeEnv.refl C) (by assumption)
      have hlabel := resultOk_of_append_left hlabelAll
      refine ⟨resultOk_append hlabel (resultOk_singleton (.ref ?_)),
        resultOk_append hlabel (resultOk_singleton (.ref ?_))⟩
      all_goals assumption
    case pos.ret =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hret : Resulttype_okA C _ :=
        hC.ret (SameTypeEnv.refl C) (by assumption)
      exact ⟨resultOk_append hfree hret, hcod⟩
    case pos.return_call =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hargs := ResultValidA.ok
        (hC.funcDom (by assumption) (by assumption))
      exact ⟨resultOk_append hfree hargs, hcod⟩
    case pos.return_call_ref =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hargs := ResultValidA.ok
        (hC.typeFuncDom (by assumption) (by assumption))
      have hidx : Valtype_okA C (.ref (.ref (some .null) (.use (.idx _)))) :=
        .ref (.mk (.typeuse (.typeidx (by assumption))))
      exact ⟨resultOk_append (resultOk_append hfree hargs)
        (resultOk_singleton hidx), hcod⟩
    case pos.return_call_indirect =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hargs := ResultValidA.ok
        (hC.typeFuncDom (by assumption) (by assumption))
      exact ⟨resultOk_append (resultOk_append hfree hargs)
        (resultOk_singleton (.num .mk)), hcod⟩
    case pos.throw_ =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      have hargs : Resulttype_okA C _ :=
        hC.tags (SameTypeEnv.refl C) (by assumption) (by assumption) (by assumption)
      exact ⟨resultOk_append hfree hargs, hcod⟩
    case pos.throw_ref =>
      rcases (by assumption : Instrtype_okA C _) with ⟨hfree, hcod, _⟩
      exact ⟨resultOk_append hfree
        (resultOk_singleton (.ref (.mk .abs))), hcod⟩
    case pos.try_table =>
      simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
      exact blockTypeResultOkA hC hsyn.1 (by assumption)
    case pos.ref_is_null =>
      refine ⟨resultOk_singleton (.ref (.mk ?_)),
        resultOk_singleton (.num .mk)⟩
      assumption
    case pos.ref_as_non_null =>
      refine ⟨resultOk_singleton (.ref (.mk ?_)),
        resultOk_singleton (.ref (.mk ?_))⟩
      all_goals assumption
    case pos.ref_test =>
      exact ⟨resultOk_singleton (.ref (by assumption)),
        resultOk_singleton (.num .mk)⟩
    case pos.ref_cast =>
      exact ⟨resultOk_singleton (.ref (by assumption)),
        resultOk_singleton (.ref (by assumption))⟩
    case pos.extern_convert_any =>
      exact ⟨resultOk_singleton (.ref (.mk .abs)),
        resultOk_singleton (.ref (.mk .abs))⟩
    case pos.any_convert_extern =>
      exact ⟨resultOk_singleton (.ref (.mk .abs)),
        resultOk_singleton (.ref (.mk .abs))⟩
  · have hspecialSource : Instr.directSourceSpecialA i = false := by
      simpa [directSpecialA_eq_source] using hspecial
    have hd := instrDispatch_complete_of_source htypes hsource hsyn
      hspecialSource h
    cases ha : instrTypeA C i with
    | some jt =>
        simp only [ha, Option.some.injEq] at hd
        subst jt
        exact ⟨ResultValidA.ok (instrTypeA_dom_valid hC ha),
          ResultValidA.ok (instrTypeA_cod_valid hC ha)⟩
    | none =>
        simp only [ha] at hd
        cases hl : instrType C i with
        | none => simp only [hl] at hd; contradiction
        | some jt =>
            simp only [hl, Option.some.injEq] at hd
            subst jt
            exact ⟨ResultValidA.ok (instrType_dom_valid hl),
              ResultValidA.ok (instrType_cod_valid hl)⟩

/-! ## Full amended stack-pass completeness -/

/-- The checked source type section together with provenance for every
heap-bearing component of the current validation context.  Unlike the former
unrestricted heap-completeness premise, this package is constructible from a
grammar module and remains honest about arbitrary literal endpoints. -/
structure HeapSubCompleteA (C : Context) where
  types : SourceTypeCompleteA C
  context : C.SourceA

namespace HeapSubCompleteA

private theorem sameTypeEnv_withLocals {C : Context} :
    ∀ {xs : List LocalIdx} {lts : List LocalType},
      xs.length = lts.length → SameTypeEnv C (Context.withLocals C xs lts) := by
  intro xs
  induction xs generalizing C with
  | nil =>
      intro lts hlen
      cases lts with
      | nil => exact SameTypeEnv.refl C
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      intro lts hlen
      cases lts with
      | nil => simp at hlen
      | cons lt lts =>
          have hhead : SameTypeEnv C (C.setLocal x lt) := by
            simp [SameTypeEnv, Context.setLocal]
          have htail : SameTypeEnv (C.setLocal x lt)
              (Context.withLocals (C.setLocal x lt) xs lts) :=
            ih (by simpa using Nat.succ.inj hlen)
          exact SameTypeEnv.trans hhead htail

theorem here {C : Context}
    (h : HeapSubCompleteA C) {h₁ h₂ : HeapType}
    (h₁Source : h₁.SourceA C) (h₂Source : h₂.SourceA C)
    (hs : Heaptype_subA C h₁ h₂) :
    decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true :=
  h.types.complete h₁Source h₂Source hs

theorem hereLeft {C : Context}
    (h : HeapSubCompleteA C) {h₁ h₂ : HeapType}
    (h₁Source : h₁.SourceA C) (h₂Ok : Heaptype_okA C h₂)
    (hs : Heaptype_subA C h₁ h₂) :
    decHeaptypeSubN C C.subtypeFuel h₁ h₂ = true :=
  h.types.completeLeft h₁Source h₂Ok hs

theorem shapesHere {C : Context} (h : HeapSubCompleteA C) :
    C.ValidHeapShapesA :=
  h.types.shapes

theorem recsHere {C : Context} (h : HeapSubCompleteA C) : C.recs = [] :=
  h.types.recs

def pushLabel {C : Context} (h : HeapSubCompleteA C)
    {ts : List ValType} (hts : ResultSourceA C ts) :
    HeapSubCompleteA (Context.pushLabel ts C) := by
  have hsame : SameTypeEnv C (Context.pushLabel ts C) := by
    simp [SameTypeEnv, Context.pushLabel]
  exact ⟨h.types.transport hsame, h.context.pushLabel hts⟩

def withLocals {C : Context} (h : HeapSubCompleteA C)
    {xs : List LocalIdx} {ts : List ValType} (hlen : SeqLen₂ xs ts)
    (hall : SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
      ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs ts) :
    HeapSubCompleteA
      (Context.withLocals C xs (ts.map fun t => ⟨.set, t⟩)) := by
  have hsame : SameTypeEnv C
      (Context.withLocals C xs (ts.map fun t => ⟨.set, t⟩)) := by
    apply sameTypeEnv_withLocals
    simpa [SeqLen₂] using hlen
  exact ⟨h.types.transport hsame, h.context.withLocals hlen hall⟩

end HeapSubCompleteA

private theorem goodHeapShape_sub_abs_of_recsEmpty {C : Context}
    {ht : HeapType} {a : AbsHeapType} (hrecs : C.recs = [])
    (h : GoodHeapShapeA C ht a) : Heaptype_subA C ht (.abs a) := by
  cases ht with
  | abs b =>
      cases h
      exact .refl
  | use tu =>
      have hnrec : ∀ i : Nat, tu ≠ .recu i := by
        intro i heq
        subst tu
        cases h with
        | use hu hall => simp [Context.unrollHt, hrecs] at hu
      exact typeuseShape_sound (h.typeuseShape hnrec)

/-- The appendix family top is above every abstract shape above the target.
This is a finite check over the pinned amended abstract-heap lattice. -/
private theorem validationTopA_shape_upper {C : Context}
    {target : HeapType} {a b top : AbsHeapType}
    (hrecs : C.recs = [])
    (htop : validationTopA C target = some (.abs top))
    (ha : GoodHeapShapeA C target a)
    (hab : decAbsSub a b = true) : decAbsSub b top = true := by
  cases target with
  | abs x =>
      have hxa : x = a := (GoodHeapShapeA.abs x).unique ha
      subst a
      cases x <;> cases b <;> cases top <;>
        simp_all [validationTopA, decAbsSub]
  | use tu =>
      have hnrec : ∀ i : Nat, tu ≠ .recu i := by
        intro i heq
        subst tu
        cases ha with
        | use hu hall => simp [Context.unrollHt, hrecs] at hu
      have hs := ha.typeuseShape hnrec
      cases ha with
      | @use _ fin sups ct hu hall =>
          cases ct with
          | struct fts =>
              simp only [validationTopA, hs, Option.some.injEq,
                HeapType.abs.injEq] at htop
              cases b <;> cases top <;>
                simp_all [CompType.absShape, decAbsSub]
          | array ft =>
              simp only [validationTopA, hs, Option.some.injEq,
                HeapType.abs.injEq] at htop
              cases b <;> cases top <;>
                simp_all [CompType.absShape, decAbsSub]
          | func dom cod =>
              simp only [validationTopA, hs, Option.some.injEq,
                HeapType.abs.injEq] at htop
              cases b <;> cases top <;>
                simp_all [CompType.absShape, decAbsSub]

private theorem heaptypeSource_below_validationTopA {C : Context}
    {target source top : HeapType} (henv : C.ValidHeapShapesA)
    (hrecs : C.recs = []) (htarget : Heaptype_okA C target)
    (hsource : Heaptype_okA C source)
    (hsub : Heaptype_subA C target source)
    (htop : validationTopA C target = some top) :
    Heaptype_subA C source top := by
  obtain ⟨topAbs, rfl⟩ := validationTopA_abs htop
  obtain ⟨targetAbs, htargetShape⟩ := henv htarget
  obtain ⟨sourceAbs, hsourceShape⟩ := henv hsource
  have hshapeSub : decAbsSub targetAbs sourceAbs = true :=
    hsub.goodShape henv htargetShape hsourceShape
  have hsourceTop : decAbsSub sourceAbs topAbs = true :=
    validationTopA_shape_upper hrecs htop htargetShape hshapeSub
  exact .trans Heaptype_okA.abs
    (goodHeapShape_sub_abs_of_recsEmpty hrecs hsourceShape)
    (decAbsSub_soundA hsourceTop)

private theorem reftypeSource_below_validationInputTopA {C : Context}
    {target source input : RefType} (henv : C.ValidHeapShapesA)
    (hrecs : C.recs = []) (htarget : Reftype_okA C target)
    (hsource : Reftype_okA C source)
    (hsub : Reftype_subA C target source)
    (htop : validationInputTopA C target = some input) :
    Reftype_subA C source input := by
  cases target with
  | ref targetNul targetHeap =>
      cases source with
      | ref sourceNul sourceHeap =>
          cases htarget with
          | mk htargetHeapOk =>
              cases hsource with
              | mk hsourceHeapOk =>
                  simp only [validationInputTopA] at htop
                  cases hh : validationTopA C targetHeap with
                  | none =>
                      rw [hh] at htop
                      cases htop
                  | some top =>
                      rw [hh] at htop
                      simp only [Option.map_some, Option.some.injEq] at htop
                      subst input
                      cases hsub with
                      | nonnull hheap =>
                          exact .null (heaptypeSource_below_validationTopA
                            henv hrecs htargetHeapOk hsourceHeapOk hheap hh)
                      | null hheap =>
                          exact .null (heaptypeSource_below_validationTopA
                            henv hrecs htargetHeapOk hsourceHeapOk hheap hh)

private theorem validationTopA_complete {C : Context} {ht : HeapType}
    (henv : C.ValidHeapShapesA) (hsyn : ht.isSyn = true)
    (hok : Heaptype_okA C ht) : ∃ top, validationTopA C ht = some top := by
  cases ht with
  | abs a =>
      cases a <;> simp_all [HeapType.isSyn, AbsHeapType.isSyn, validationTopA]
  | use tu =>
      obtain ⟨a, hshape⟩ := henv hok
      have hnrec : ∀ i : Nat, tu ≠ .recu i := by
        intro i heq
        subst tu
        simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      have hs := hshape.typeuseShape hnrec
      cases hshape with
      | @use _ fin sups ct hu hall =>
          cases ct <;> simp [validationTopA, hs, CompType.absShape]

private theorem validationInputTopA_complete {C : Context}
    {rt : RefType} (henv : C.ValidHeapShapesA) (hsyn : rt.isSyn = true)
    (hok : Reftype_okA C rt) : ∃ input, validationInputTopA C rt = some input := by
  cases rt with
  | ref nul ht =>
      cases hok with
      | mk hht =>
          obtain ⟨top, htop⟩ := validationTopA_complete henv
            (by simpa [RefType.isSyn] using hsyn) hht
          exact ⟨.ref (some .null) top, by simp [validationInputTopA, htop]⟩

private theorem validationInputTopA_ok {C : Context}
    {target input : RefType}
    (h : validationInputTopA C target = some input) :
    Reftype_okA C input := by
  cases target with
  | ref nul ht =>
      simp only [validationInputTopA] at h
      cases hv : validationTopA C ht with
      | none => simp only [hv] at h; contradiction
      | some top =>
          simp only [hv, Option.map_some, Option.some.injEq] at h
          subst input
          obtain ⟨a, rfl⟩ := validationTopA_abs hv
          exact .mk .abs

private theorem checkInstrA_eq_dispatch {C : Context} {st : St} {i : Instr}
    (h : Instr.directSpecialA i = false) :
    checkInstrA C st i =
      (match instrTypeA C i with
       | some it => (applyTypeA C st it).map (it.locals, ·)
       | none => match instrType C i with
         | some it => (applyTypeA C st it).map (it.locals, ·)
         | none => none) := by
  cases i <;> try rfl
  case select ts =>
    cases ts with
    | none => simp [Instr.directSpecialA] at h
    | some _ => rfl
  all_goals simp [Instr.directSpecialA] at h

/-- Completeness of one instruction while preserving an arbitrary stack
frame.  Structured instructions consume the recursively supplied sequence
completeness proof for their bodies. -/
def InstrCompleteFullA (i : Instr) : Prop :=
  ∀ (C : Context) (it : InstrType), Context.ValidA C →
    HeapSubCompleteA C → Instr.isSyn i = true → Instr_okA C i it →
    ∀ (frame : List ValType) (st : St),
      St.ValidA C st →
      St.SourceA C st →
      St.SatA C st (frame ++ it.dom) →
      ∃ st', checkInstrA C st i = some (it.locals, st') ∧
        St.SatA C st' (frame ++ it.cod) ∧ St.SourceA C st'

/-- Completeness of a sequence.  The checker reports the exact accumulated
local effects; subsumption may leave that list existential at this layer. -/
def SeqCompleteFullA (s : InstrSeq) : Prop :=
  ∀ (C : Context) (it : InstrType), Context.ValidA C →
    HeapSubCompleteA C → InstrSeq.isSyn s = true →
    Instrs_okA C (InstrSeq.toList s) it →
    ∀ (frame : List ValType) (st : St),
      St.ValidA C st →
      St.SourceA C st →
      St.SatA C st (frame ++ it.dom) →
      ∃ xs st', checkSeqA C st s = some (xs, st') ∧
        St.SatA C st' (frame ++ it.cod) ∧ St.SourceA C st'

private theorem instrCompleteFullA_default {C : Context} {i : Instr}
    {it : InstrType} (hheap : HeapSubCompleteA C)
    (hsyn : Instr.isSyn i = true) (hspecial : Instr.directSpecialA i = false)
    (hok : Instr_okA C i it) {frame : List ValType} {st : St}
    (hstSource : St.SourceA C st)
    (hsat : St.SatA C st (frame ++ it.dom)) :
    ∃ st', checkInstrA C st i = some (it.locals, st') ∧
      St.SatA C st' (frame ++ it.cod) ∧ St.SourceA C st' := by
  have hspecial' : Instr.directSourceSpecialA i = false := by
    simpa [directSpecialA_eq_source] using hspecial
  exact instrDefault_complete_source_state hheap.types hheap.context
    hsyn hspecial' hok hstSource hsat

private theorem checkCatchA_complete {C : Context}
    (hheap : HeapSubCompleteA C) {c : Catch} (h : Catch_okA C c) :
    checkCatchA C c = true := by
  cases h with
  | «catch» hx hd he hl hs =>
      cases he with
      | mk he =>
          have hleft := hheap.context.tags hx hd (Expand.mk he)
          have hright := hheap.context.labels hl
          have hdec := hheap.types.resultComplete hleft hright hs
          simp [checkCatchA, hx, hd, he, hl, subsA,
            hdec]
  | catch_ref hx hd he hl hs =>
      cases he with
      | mk he =>
          have hdom := hheap.context.tags hx hd (Expand.mk he)
          have hleft : ResultSourceA C
              (ValTypes.toList _ ++
                [.ref (.ref none (.abs .exn))]) :=
            hdom.append (ResultSourceA.singleton trivial)
          have hright := hheap.context.labels hl
          have hdec := hheap.types.resultComplete hleft hright hs
          simp [checkCatchA, hx, hd, he, hl, subsA,
            hdec]
  | catch_all hl hs =>
      have hdec := hheap.types.resultComplete
        (ResultSourceA.nil C) (hheap.context.labels hl) hs
      simp [checkCatchA, hl, subsA,
        hdec]
  | catch_all_ref hl hs =>
      have hdec := hheap.types.resultComplete
        (ResultSourceA.singleton (C := C)
          (t := .ref (.ref none (.abs .exn))) trivial)
        (hheap.context.labels hl) hs
      simp [checkCatchA, hl, subsA,
        hdec]

private theorem blockCompleteFullA {C : Context} {bt : BlockType}
    {body : InstrSeq} {ts₁ ts₂ : List ValType} {xs : List LocalIdx}
    {frame : List ValType} {st : St}
    (hbody : SeqCompleteFullA body) (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hbtSyn : bt.isSyn = true)
    (hbodySyn : body.isSyn = true)
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_okA (Context.pushLabel ts₂ C) body.toList
      ⟨ts₁, xs, ts₂⟩)
    (hstSource : st.SourceA C)
    (hsat : St.SatA C st (frame ++ ts₁)) :
    ∃ st', checkInstrA C st (.block bt body) = some ([], st') ∧
      St.SatA C st' (frame ++ ts₂) ∧ St.SourceA C st' := by
  have hbtCheck := blockTypeA_complete hbtSyn hbt
  obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbtCheck
  obtain ⟨hdomSource, hcodSource⟩ :=
    blockTypeResultSourceA hheap.context hbtSyn hbt
  let CB := Context.pushLabel ts₂ C
  have hsame : SameTypeEnv C CB := by
    simp [CB, SameTypeEnv, Context.pushLabel]
  have hstart : St.SatA CB ((St.mk false []).pushs ts₁) ts₁ :=
    ⟨St.mk false [], St.pushs_popsA CB _ _, rfl⟩
  have hstartValid : St.ValidA CB ((St.mk false []).pushs ts₁) :=
    St.ValidA.pushs (St.ValidA.empty CB false)
      (ResultValidA.transport hsame hdom)
  have hstartSource : St.SourceA CB ((St.mk false []).pushs ts₁) :=
    (St.SourceA.empty CB false).pushs (hdomSource.transport hsame)
  obtain ⟨xsB, stB, hrun, hout, houtSource⟩ :=
    hbody CB ⟨ts₁, xs, ts₂⟩ (hC.pushLabel hcod)
      (hheap.pushLabel hcodSource) hbodySyn hok [] _ hstartValid hstartSource
      (by simpa using hstart)
  have hfin : stB.finishA CB ts₂ = true := by
    simpa [St.finishA] using (St.finishA_iff_satA.mpr hout)
  obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
  have hbaseSource : base.SourceA C := hstSource.popsA hp
  refine ⟨base.pushs ts₂, ?_, hbase.pushs, hbaseSource.pushs hcodSource⟩
  have hrun' : checkSeqA (Context.pushLabel ts₂ C)
      ((St.mk false []).pushs ts₁) body = some (xsB, stB) := by
    simpa [CB] using hrun
  have hfin' : stB.finishA (Context.pushLabel ts₂ C) ts₂ = true := by
    simpa [CB] using hfin
  simp [checkInstrA, hbtCheck, hp, hrun', hfin']

private theorem loopCompleteFullA {C : Context} {bt : BlockType}
    {body : InstrSeq} {ts₁ ts₂ : List ValType} {xs : List LocalIdx}
    {frame : List ValType} {st : St}
    (hbody : SeqCompleteFullA body) (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hbtSyn : bt.isSyn = true)
    (hbodySyn : body.isSyn = true)
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_okA (Context.pushLabel ts₁ C) body.toList
      ⟨ts₁, xs, ts₂⟩)
    (hstSource : st.SourceA C)
    (hsat : St.SatA C st (frame ++ ts₁)) :
    ∃ st', checkInstrA C st (.loop bt body) = some ([], st') ∧
      St.SatA C st' (frame ++ ts₂) ∧ St.SourceA C st' := by
  have hbtCheck := blockTypeA_complete hbtSyn hbt
  obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbtCheck
  obtain ⟨hdomSource, hcodSource⟩ :=
    blockTypeResultSourceA hheap.context hbtSyn hbt
  let CB := Context.pushLabel ts₁ C
  have hsame : SameTypeEnv C CB := by
    simp [CB, SameTypeEnv, Context.pushLabel]
  have hstart : St.SatA CB ((St.mk false []).pushs ts₁) ts₁ :=
    ⟨St.mk false [], St.pushs_popsA CB _ _, rfl⟩
  have hstartValid : St.ValidA CB ((St.mk false []).pushs ts₁) :=
    St.ValidA.pushs (St.ValidA.empty CB false)
      (ResultValidA.transport hsame hdom)
  have hstartSource : St.SourceA CB ((St.mk false []).pushs ts₁) :=
    (St.SourceA.empty CB false).pushs (hdomSource.transport hsame)
  obtain ⟨xsB, stB, hrun, hout, houtSource⟩ :=
    hbody CB ⟨ts₁, xs, ts₂⟩ (hC.pushLabel hdom)
      (hheap.pushLabel hdomSource) hbodySyn hok [] _ hstartValid hstartSource
      (by simpa using hstart)
  have hfin : stB.finishA CB ts₂ = true := by
    simpa [St.finishA] using (St.finishA_iff_satA.mpr hout)
  obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
  have hbaseSource : base.SourceA C := hstSource.popsA hp
  refine ⟨base.pushs ts₂, ?_, hbase.pushs, hbaseSource.pushs hcodSource⟩
  have hrun' : checkSeqA (Context.pushLabel ts₁ C)
      ((St.mk false []).pushs ts₁) body = some (xsB, stB) := by
    simpa [CB] using hrun
  have hfin' : stB.finishA (Context.pushLabel ts₁ C) ts₂ = true := by
    simpa [CB] using hfin
  simp [checkInstrA, hbtCheck, hp, hrun', hfin']

private theorem ifCompleteFullA {C : Context} {bt : BlockType}
    {thn els : InstrSeq} {ts₁ ts₂ : List ValType}
    {xs₁ xs₂ : List LocalIdx} {frame : List ValType} {st : St}
    (hthn : SeqCompleteFullA thn) (hels : SeqCompleteFullA els)
    (hC : Context.ValidA C) (hheap : HeapSubCompleteA C)
    (hbtSyn : bt.isSyn = true) (hthnSyn : thn.isSyn = true)
    (helsSyn : els.isSyn = true)
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hokT : Instrs_okA (Context.pushLabel ts₂ C) thn.toList
      ⟨ts₁, xs₁, ts₂⟩)
    (hokE : Instrs_okA (Context.pushLabel ts₂ C) els.toList
      ⟨ts₁, xs₂, ts₂⟩)
    (hstSource : st.SourceA C)
    (hsat : St.SatA C st (frame ++ (ts₁ ++ [ValType.i32]))) :
    ∃ st', checkInstrA C st (.ifElse bt thn els) = some ([], st') ∧
      St.SatA C st' (frame ++ ts₂) ∧ St.SourceA C st' := by
  have hbtCheck := blockTypeA_complete hbtSyn hbt
  obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbtCheck
  obtain ⟨hdomSource, hcodSource⟩ :=
    blockTypeResultSourceA hheap.context hbtSyn hbt
  let CB := Context.pushLabel ts₂ C
  have hsame : SameTypeEnv C CB := by
    simp [CB, SameTypeEnv, Context.pushLabel]
  have hstart : St.SatA CB ((St.mk false []).pushs ts₁) ts₁ :=
    ⟨St.mk false [], St.pushs_popsA CB _ _, rfl⟩
  have hstartValid : St.ValidA CB ((St.mk false []).pushs ts₁) :=
    St.ValidA.pushs (St.ValidA.empty CB false)
      (ResultValidA.transport hsame hdom)
  have hstartSource : St.SourceA CB ((St.mk false []).pushs ts₁) :=
    (St.SourceA.empty CB false).pushs (hdomSource.transport hsame)
  obtain ⟨xsT, stT, hrunT, houtT, houtTSource⟩ :=
    hthn CB ⟨ts₁, xs₁, ts₂⟩ (hC.pushLabel hcod)
      (hheap.pushLabel hcodSource) hthnSyn hokT [] _ hstartValid hstartSource
      (by simpa using hstart)
  obtain ⟨xsE, stE, hrunE, houtE, houtESource⟩ :=
    hels CB ⟨ts₁, xs₂, ts₂⟩ (hC.pushLabel hcod)
      (hheap.pushLabel hcodSource) helsSyn hokE [] _ hstartValid hstartSource
      (by simpa using hstart)
  have hfinT : stT.finishA (Context.pushLabel ts₂ C) ts₂ = true := by
    simpa [CB, St.finishA] using (St.finishA_iff_satA.mpr houtT)
  have hfinE : stE.finishA (Context.pushLabel ts₂ C) ts₂ = true := by
    simpa [CB, St.finishA] using (St.finishA_iff_satA.mpr houtE)
  have hrunT' : checkSeqA (Context.pushLabel ts₂ C)
      ((St.mk false []).pushs ts₁) thn = some (xsT, stT) := by
    simpa [CB] using hrunT
  have hrunE' : checkSeqA (Context.pushLabel ts₂ C)
      ((St.mk false []).pushs ts₁) els = some (xsE, stE) := by
    simpa [CB] using hrunE
  obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
  change st.popsA C (ts₁ ++ [ValType.i32]) = some base at hp
  rw [St.popsA_append] at hp
  cases hi32 : st.popsA C [ValType.i32] with
  | none => rw [hi32] at hp; contradiction
  | some s =>
      rw [hi32] at hp
      have hi32' : st.popEA C ValType.i32 = some s := by
        simpa only [St.popsA] using hi32
      have hsSource : s.SourceA C := hstSource.popsA hi32
      have hbaseSource : base.SourceA C := hsSource.popsA hp
      refine ⟨base.pushs ts₂, ?_, hbase.pushs,
        hbaseSource.pushs hcodSource⟩
      simp [checkInstrA, hbtCheck, hi32', hp, hrunT', hrunE',
        hfinT, hfinE]

private theorem tryCompleteFullA {C : Context} {bt : BlockType}
    {cs : List_ Catch} {body : InstrSeq} {ts₁ ts₂ : List ValType}
    {xs : List LocalIdx} {frame : List ValType} {st : St}
    (hbody : SeqCompleteFullA body) (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C) (hbtSyn : bt.isSyn = true)
    (hbodySyn : body.isSyn = true)
    (hbt : Blocktype_okA C bt ⟨ts₁, [], ts₂⟩)
    (hok : Instrs_okA (Context.pushLabel ts₂ C) body.toList
      ⟨ts₁, xs, ts₂⟩) (hcs : SeqAll (Catch_okA C) cs.val)
    (hstSource : st.SourceA C)
    (hsat : St.SatA C st (frame ++ ts₁)) :
    ∃ st', checkInstrA C st (.tryTable bt cs body) = some ([], st') ∧
      St.SatA C st' (frame ++ ts₂) ∧ St.SourceA C st' := by
  have hbtCheck := blockTypeA_complete hbtSyn hbt
  obtain ⟨hdom, hcod⟩ := blockTypeA_valid hC hbtCheck
  obtain ⟨hdomSource, hcodSource⟩ :=
    blockTypeResultSourceA hheap.context hbtSyn hbt
  have hcsCheck : cs.val.all (checkCatchA C) = true :=
    List.all_eq_true.mpr (fun c hc => checkCatchA_complete hheap (hcs c hc))
  let CB := Context.pushLabel ts₂ C
  have hsame : SameTypeEnv C CB := by
    simp [CB, SameTypeEnv, Context.pushLabel]
  have hstart : St.SatA CB ((St.mk false []).pushs ts₁) ts₁ :=
    ⟨St.mk false [], St.pushs_popsA CB _ _, rfl⟩
  have hstartValid : St.ValidA CB ((St.mk false []).pushs ts₁) :=
    St.ValidA.pushs (St.ValidA.empty CB false)
      (ResultValidA.transport hsame hdom)
  have hstartSource : St.SourceA CB ((St.mk false []).pushs ts₁) :=
    (St.SourceA.empty CB false).pushs (hdomSource.transport hsame)
  obtain ⟨xsB, stB, hrun, hout, houtSource⟩ :=
    hbody CB ⟨ts₁, xs, ts₂⟩ (hC.pushLabel hcod)
      (hheap.pushLabel hcodSource) hbodySyn hok [] _ hstartValid hstartSource
      (by simpa using hstart)
  have hrun' : checkSeqA (Context.pushLabel ts₂ C)
      ((St.mk false []).pushs ts₁) body = some (xsB, stB) := by
    simpa [CB] using hrun
  have hfin : stB.finishA (Context.pushLabel ts₂ C) ts₂ = true := by
    simpa [CB, St.finishA] using (St.finishA_iff_satA.mpr hout)
  obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
  have hbaseSource : base.SourceA C := hstSource.popsA hp
  refine ⟨base.pushs ts₂, ?_, hbase.pushs, hbaseSource.pushs hcodSource⟩
  simp [checkInstrA, hbtCheck, hcsCheck, hp, hrun', hfin]

theorem instrCompleteFullA_step (i : Instr)
    (hbodies : ∀ body : InstrSeq, InstrSeq.size body < Instr.size i →
      SeqCompleteFullA body) : InstrCompleteFullA i := by
  intro C it hC hheap hsyn hok frame st hst hstSource hsat
  have hitValid := instrResultOkA hC hheap.types hheap.context hsyn hok
  cases i
  case unreachable =>
    cases hok with
    | unreachable _ =>
        refine ⟨st.unreach, rfl, ?_⟩
        exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
          by simpa [St.unreach] using St.SourceA.empty C true⟩
  case drop =>
    cases hok with
    | drop ht =>
        rename_i t
        obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
        have hp' : st.popEA C t = some base := by
          simpa only [St.popsA] using hp
        obtain ⟨u, hpop, _⟩ := St.pop_of_popEA hp'
        exact ⟨base, by simp [checkInstrA, hpop], by simpa using hbase,
          hstSource.popsA hp⟩
  case select ot =>
    cases ot with
    | some ts =>
        exact instrCompleteFullA_default hheap hsyn rfl hok hstSource hsat
    | none =>
        cases hok with
        | select_impl ht hsub hnv =>
            rename_i t t'
            obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
            change st.popsA C [t, t, ValType.i32] = some base at hp
            change (match st.popsA C [t, ValType.i32] with
              | some s => s.popEA C t
              | none => none) = some base at hp
            cases htail : st.popsA C [t, ValType.i32] with
            | none => simp only [htail] at hp; contradiction
            | some s₂ =>
                simp only [htail] at hp
                change (match st.popsA C [ValType.i32] with
                  | some s => s.popEA C t
                  | none => none) = some s₂ at htail
                cases hi32 : st.popsA C [ValType.i32] with
                | none => simp only [hi32] at htail; contradiction
                | some s₁ =>
                    simp only [hi32] at htail
                    have hi32' : st.popEA C ValType.i32 = some s₁ := by
                      simpa only [St.popsA] using hi32
                    obtain ⟨u₁, hpop₁, hsub₁⟩ := St.pop_of_popEA htail
                    obtain ⟨u₂, hpop₂, hsub₂⟩ := St.pop_of_popEA hp
                    have hs₁Source := hstSource.popsA hi32
                    have hpop₁Source := hs₁Source.pop hpop₁
                    have hpop₂Source := hpop₁Source.2.pop hpop₂
                    have hu₁Source := hpop₁Source.1
                    have hu₂Source := hpop₂Source.1
                    have hbaseSource := hpop₂Source.2
                    have hsem₁ : Valtype_subA C u₁ t' :=
                      Valtype_subA.trans ht
                        (decValtypeSubN_sound hsub₁) hsub
                    have hsem₂ : Valtype_subA C u₂ t' :=
                      Valtype_subA.trans ht
                        (decValtypeSubN_sound hsub₂) hsub
                    have hnu₁ : ValType.nvb u₁ = true := by
                      cases hsem₁ <;>
                        simp_all [ValType.nvb, ValType.isNumOrVec]
                    have hnu₂ : ValType.nvb u₂ = true := by
                      cases hsem₂ <;>
                        simp_all [ValType.nvb, ValType.isNumOrVec]
                    have hor : subOfA C u₁ u₂ = true ∨
                        subOfA C u₂ u₁ = true := by
                      cases u₁ <;> cases u₂ <;> cases t <;>
                        simp_all [ValType.nvb, subOfA,
                          decValtypeSubN, decNumtypeSub, decVectypeSub]
                    let u := if u₁ == ValType.bot then u₂ else u₁
                    have huSource : u.SourceA C := by
                      dsimp [u]
                      split
                      · exact hu₂Source
                      · exact hu₁Source
                    have hu : subOfA C u t = true := by
                      dsimp [u]
                      by_cases hb : (u₁ == ValType.bot) = true
                      · simp only [hb, if_pos]
                        exact hsub₂
                      · simp only [hb, Bool.false_eq_true, if_false]
                        exact hsub₁
                    refine ⟨base.push u, ?_, ?_, hbaseSource.push huSource⟩
                    · simp [checkInstrA, hi32', hpop₁, hpop₂,
                        hnu₁, hnu₂, hor, u]
                    · apply St.satA_append (ts := [t])
                        (st₀ := base) (st := base.push u)
                      · simp [St.popsA, St.popEA, St.push, hu]
                      · exact hbase
  case block bt body =>
    cases hok with
    | block hbt hbodyOk =>
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        exact blockCompleteFullA
          (hbodies body (InstrSeq.size_body_block bt body)) hC hheap
          hsyn.1 hsyn.2 hbt hbodyOk hstSource hsat
  case loop bt body =>
    cases hok with
    | loop hbt hbodyOk =>
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        exact loopCompleteFullA
          (hbodies body (InstrSeq.size_body_loop bt body)) hC hheap
          hsyn.1 hsyn.2 hbt hbodyOk hstSource hsat
  case ifElse bt thn els =>
    cases hok with
    | if_ hbt hokT hokE =>
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        exact ifCompleteFullA
          (hbodies thn (InstrSeq.size_body_thn bt thn els))
          (hbodies els (InstrSeq.size_body_els bt thn els)) hC hheap
          hsyn.1.1 hsyn.1.2 hsyn.2 hbt hokT hokE hstSource hsat
  case tryTable bt cs body =>
    cases hok with
    | try_table hbt hbodyOk hcs =>
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        exact tryCompleteFullA
          (hbodies body (InstrSeq.size_body_tryTable bt cs body)) hC hheap
          hsyn.1 hsyn.2 hbt hbodyOk hcs hstSource hsat
  case br l =>
    cases hok with
    | br hl _ =>
        have hsat' := hsat
        rw [← List.append_assoc] at hsat'
        obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
        refine ⟨st.unreach, ?_, ?_⟩
        · simp [checkInstrA, hl, hp]
        · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
            by simpa [St.unreach] using St.SourceA.empty C true⟩
  case brTable ls l =>
    cases hok with
    | br_table hall hl hsub _ =>
        rename_i branchTs free out target hitok
        have htsFree : Resulttype_okA C (free ++ branchTs) := by
          apply resultOk_of_append_left (us := [ValType.i32])
          simpa only [List.append_assoc] using hitValid.1
        have hts : Resulttype_okA C branchTs :=
          resultOk_of_append_right htsFree
        have hsat' : St.SatA C st
            (((frame ++ free) ++ branchTs) ++ [ValType.i32]) := by
          simpa only [List.append_assoc] using hsat
        obtain ⟨s₁, hi32s, hs₁⟩ := St.SatA.split_append hsat'
        have hs₁Source : s₁.SourceA C := hstSource.popsA hi32s
        have hi32 : st.popEA C ValType.i32 = some s₁ := by
          simpa only [St.popsA] using hi32s
        obtain ⟨base, hpts, _⟩ := St.SatA.split_append hs₁
        obtain ⟨us, s₂, hpn, hus⟩ := St.popN_principalA hpts
        have husSource : ResultSourceA C us := (hs₁Source.popN hpn).1
        have husSem : Resulttype_subA C us branchTs :=
          resulttype_subA_of_subsA hus
        have htargetSem : Resulttype_subA C us target :=
          Resulttype_subA.trans hts husSem hsub
        have htargetCheck : subsA C us target = true :=
          hheap.types.resultComplete husSource
            (hheap.context.labels hl) htargetSem
        have hlen : branchTs.length = target.length := by
          cases hsub with
          | mk hlen _ => exact hlen
        have hpn' : s₁.popN target.length = some (us, s₂) := by
          simpa only [← hlen] using hpn
        have hallCheck : ls.all (fun l' =>
            match C.labels[l'.val]? with
            | some ts' => subsA C us ts'
            | none => false) = true := by
          rw [List.all_eq_true]
          intro l' hl'
          obtain ⟨ts', hlabel, hsub'⟩ := hall l' hl'
          have hsem : Resulttype_subA C us ts' :=
            Resulttype_subA.trans hts husSem hsub'
          have hc : subsA C us ts' = true :=
            hheap.types.resultComplete husSource
              (hheap.context.labels hlabel) hsem
          simpa only [hlabel] using hc
        have hcond : (subsA C us target && ls.all (fun l' =>
            match C.labels[l'.val]? with
            | some ts' => subsA C us ts'
            | none => false)) = true := by
          simp only [htargetCheck, hallCheck, Bool.and_self]
        refine ⟨st.unreach, ?_, ?_⟩
        · simp only [checkInstrA, hi32, hl, hpn']
          split
          · rfl
          · rename_i hn
            exact False.elim (hn hcond)
        · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
            by simpa [St.unreach] using St.SourceA.empty C true⟩
  case brOnNull l =>
    cases hok with
    | br_on_null hl hht =>
        rename_i ts ht
        have hsat' : St.SatA C st
            ((frame ++ ts) ++ [.ref (.ref (some .null) ht)]) := by
          simpa only [List.append_assoc] using hsat
        obtain ⟨rt?, s₁, href, hrefSub, hs₁⟩ :=
          St.SatA.popRef_of_ref hsat'
        have hrefSources := hstSource.popRef href
        have hs₁Source : s₁.SourceA C := hrefSources.1
        have hpoppedSource : (poppedHeapType rt?).SourceA C := by
          cases rt? with
          | none => trivial
          | some rt =>
              cases rt with
              | ref nul actual =>
                  exact hrefSources.2 (.ref nul actual) rfl
        obtain ⟨base, hpts, hbase⟩ := St.SatA.split_append hs₁
        have hbaseSource : base.SourceA C := hs₁Source.popsA hpts
        have hlabelSource := hheap.context.labels hl
        have htsSource := hlabelSource
        have hactualSource : ResultSourceA C
            (ts ++ [.ref (.ref none (poppedHeapType rt?))]) :=
          ResultSourceA.append htsSource (ResultSourceA.singleton hpoppedSource)
        have htsOk := hC.labels (SameTypeEnv.refl C) hl
        have hexpectedOk : Resulttype_okA C
            (ts ++ [.ref (.ref none ht)]) :=
          resultOk_append htsOk (resultOk_singleton (.ref (.mk hht)))
        obtain ⟨_, hrefValid⟩ := St.popRef_valid hst href
        have hactualValid :
            ValValidA C (.ref (.ref none (poppedHeapType rt?))) :=
          poppedNonNull_valid hrefValid
        have hactualOk : Resulttype_okA C
            (ts ++ [.ref (.ref none (poppedHeapType rt?))]) :=
          resultOk_append
            (hC.labels (SameTypeEnv.refl C) hl)
            (resultOk_singleton (hactualValid C (SameTypeEnv.refl C)))
        have hlastSub : subOfA C
            (.ref (.ref none (poppedHeapType rt?)))
            (.ref (.ref none ht)) = true :=
          poppedNonNull_sub hheap.types hpoppedSource hht hrefSub
        have hsubs : subsA C
            (ts ++ [.ref (.ref none (poppedHeapType rt?))])
            (ts ++ [.ref (.ref none ht)]) = true :=
          subsA_append C (subsA_refl C ts) (by
            simpa [subsA, decResulttypeSubN, decSeq₂] using hlastSub)
        have hpActual : (base.pushs
            (ts ++ [.ref (.ref none (poppedHeapType rt?))])).popsA C
              (ts ++ [.ref (.ref none (poppedHeapType rt?))]) = some base :=
          St.pushs_popsA C base _
        have hpExpected : (base.pushs
            (ts ++ [.ref (.ref none (poppedHeapType rt?))])).popsA C
              (ts ++ [.ref (.ref none ht)]) = some base :=
          St.SourceA.popsA_weaken_to_valid hheap.types
            (hbaseSource.pushs hactualSource) hactualOk hexpectedOk
            (resulttype_subA_of_subsA hsubs) hpActual
        refine ⟨base.pushs (ts ++ [.ref (.ref none (poppedHeapType rt?))]),
          ?_, St.satA_append hpExpected hbase,
          hbaseSource.pushs hactualSource⟩
        simp [checkInstrA, hl, href, hpts, poppedHeapType]
        rfl
  case brOnNonNull l =>
    cases hok with
    | br_on_non_null hl =>
        rename_i ts nul ht
        have hsplit := splitLast?_append_singleton ts
          (ValType.ref (RefType.ref nul ht))
        have htsSource := ResultSourceA.of_append_left
          (hheap.context.labels hl)
        obtain ⟨st', happly, hout⟩ := applyTypeA_complete_frame hsat
        refine ⟨st', ?_, hout, hstSource.of_applyTypeA htsSource happly⟩
        simp [checkInstrA, hl, hsplit, happly]
  case brOnCast l rt₁ rt₂ =>
    cases hok with
    | br_on_cast hl hok₁ hok₂ hsub₁ hsub₂ =>
        rename_i rt ts
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        have hc₁ := checkReftypeOkA_complete hsyn.1 hok₁
        have hc₂ := checkReftypeOkA_complete hsyn.2 hok₂
        have hrt₁Source := hok₁.sourceA_of_syn hsyn.1
        have hrt₂Source := hok₂.sourceA_of_syn hsyn.2
        have hlabelSource := hheap.context.labels hl
        have htsSource := ResultSourceA.of_append_left hlabelSource
        have hrtValSource : (ValType.ref rt).SourceA C :=
          hlabelSource (ValType.ref rt) (List.mem_append_right _ (by simp))
        have hrtSource : rt.SourceA C := hrtValSource
        have hdiffSource := hrt₁Source.diff_left (right := rt₂)
        have hcodSource := ResultSourceA.append htsSource
          (ResultSourceA.singleton (t := .ref (rt₁.diff rt₂)) hdiffSource)
        have hd₁ := hheap.types.reftypeComplete hrt₂Source hrt₁Source hsub₁
        have hd₂ := hheap.types.reftypeComplete hrt₂Source hrtSource hsub₂
        have hsplit := splitLast?_append_singleton ts (ValType.ref rt)
        obtain ⟨st', happly, hout⟩ := applyTypeA_complete_frame hsat
        refine ⟨st', ?_, hout, hstSource.of_applyTypeA hcodSource happly⟩
        simp [checkInstrA, hl, hsplit, hc₁, hc₂, hd₁, hd₂, happly]
  case brOnCastFail l rt₁ rt₂ =>
    cases hok with
    | br_on_cast_fail hl hok₁ hok₂ hsub₁ hsub₂ =>
        rename_i rt ts
        simp only [Instr.isSyn, Bool.and_eq_true] at hsyn
        have hc₁ := checkReftypeOkA_complete hsyn.1 hok₁
        have hc₂ := checkReftypeOkA_complete hsyn.2 hok₂
        have hrt₁Source := hok₁.sourceA_of_syn hsyn.1
        have hrt₂Source := hok₂.sourceA_of_syn hsyn.2
        have hlabelSource := hheap.context.labels hl
        have htsSource := ResultSourceA.of_append_left hlabelSource
        have hrtValSource : (ValType.ref rt).SourceA C :=
          hlabelSource (ValType.ref rt) (List.mem_append_right _ (by simp))
        have hrtSource : rt.SourceA C := hrtValSource
        have hdiffSource := hrt₁Source.diff_left (right := rt₂)
        have hcodSource := ResultSourceA.append htsSource
          (ResultSourceA.singleton (t := .ref rt₂) hrt₂Source)
        have hd₁ := hheap.types.reftypeComplete hrt₂Source hrt₁Source hsub₁
        have hd₂ := hheap.types.reftypeComplete hdiffSource hrtSource hsub₂
        have hsplit := splitLast?_append_singleton ts (ValType.ref rt)
        obtain ⟨st', happly, hout⟩ := applyTypeA_complete_frame hsat
        refine ⟨st', ?_, hout, hstSource.of_applyTypeA hcodSource happly⟩
        simp [checkInstrA, hl, hsplit, hc₁, hc₂, hd₁, hd₂, happly]
  case ret =>
    cases hok with
    | ret hret _ =>
        have hsat' := hsat
        rw [← List.append_assoc] at hsat'
        obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
        refine ⟨st.unreach, ?_, ?_⟩
        · simp [checkInstrA, hret, hp]
        · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
            by simpa [St.unreach] using St.SourceA.empty C true⟩
  case returnCall x =>
    cases hok with
    | return_call hfun hexp hret hsub _ =>
        rename_i dt dom cod ret free out
        cases hexp with
        | mk hexp =>
            have hfunSource := hheap.context.funcs hfun (Expand.mk hexp)
            have hsubCheck : subsA C (ValTypes.toList dom) cod = true :=
              hheap.types.resultComplete hfunSource.2
                (hheap.context.ret hret) hsub
            have hsat' := hsat
            rw [← List.append_assoc] at hsat'
            obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
            refine ⟨st.unreach, ?_, ?_⟩
            · simp [checkInstrA, hfun, funcTypeOfA, hexp, hret,
                hsubCheck, hp]
            · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
                by simpa [St.unreach] using St.SourceA.empty C true⟩
  case returnCallRef tu =>
    cases tu with
    | recu i => cases hok
    | defd dt => cases hok
    | idx x =>
        cases hok with
        | return_call_ref hty hexp hret hsub _ =>
            rename_i dt dom cod ret free out
            cases hexp with
            | mk hexp =>
                have htypeSource := hheap.context.types hty (Expand.mk hexp)
                have hsubCheck : subsA C (ValTypes.toList dom) cod = true :=
                  hheap.types.resultComplete htypeSource.2
                    (hheap.context.ret hret) hsub
                have hsat' : St.SatA C st
                    ((frame ++ ret) ++ (dt.toList ++
                      [ValType.ref (RefType.ref (some .null) (.use (.idx x)))])) := by
                  simpa only [List.append_assoc] using hsat
                obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
                refine ⟨st.unreach, ?_, ?_⟩
                · simp [checkInstrA, hty, funcTypeOfA, hexp, hret,
                    hsubCheck, hp]
                · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
                    by simpa [St.unreach] using St.SourceA.empty C true⟩
  case returnCallIndirect x tu =>
    cases tu with
    | recu i => cases hok
    | defd dt => cases hok
    | idx y =>
        cases hok with
        | return_call_indirect htab href hty hexp hret hsub _ =>
            rename_i tableTy tt dt dom cod ret free out
            cases hexp with
            | mk hexp =>
                have htableSource := hheap.context.tables htab
                have hrefCheck := hheap.types.reftypeComplete htableSource
                  (by trivial) href
                have htypeSource := hheap.context.types hty (Expand.mk hexp)
                have hsubCheck : subsA C (ValTypes.toList dom) cod = true :=
                  hheap.types.resultComplete htypeSource.2
                    (hheap.context.ret hret) hsub
                have hsat' : St.SatA C st
                    ((frame ++ ret) ++ (dt.toList ++ [tableTy.addr.toValType])) := by
                  simpa only [List.append_assoc] using hsat
                obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
                refine ⟨st.unreach, ?_, ?_⟩
                · simp [checkInstrA, htab, hty, funcTypeOfA, hexp,
                    hret, hrefCheck, hsubCheck, hp]
                · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
                    by simpa [St.unreach] using St.SourceA.empty C true⟩
  case throw x =>
    cases hok with
    | throw_ htag hasD hexp _ =>
        rename_i jt dt dom free out
        cases hexp with
        | mk hexp =>
            have hsat' := hsat
            rw [← List.append_assoc] at hsat'
            obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
            refine ⟨st.unreach, ?_, ?_⟩
            · simp [checkInstrA, htag, hasD, hexp, hp]
            · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
                by simpa [St.unreach] using St.SourceA.empty C true⟩
  case throwRef =>
    cases hok with
    | throw_ref _ =>
        have hsat' := hsat
        rw [← List.append_assoc] at hsat'
        obtain ⟨s, hp, _⟩ := St.SatA.split_append hsat'
        have hp' : st.popEA C (.ref (.ref (some .null) (.abs .exn))) =
            some s := by simpa only [St.popsA] using hp
        refine ⟨st.unreach, ?_, ?_⟩
        · simp [checkInstrA, hp']
        · exact ⟨by simpa [St.unreach] using (St.satA_unreach C _),
            by simpa [St.unreach] using St.SourceA.empty C true⟩
  case refIsNull =>
    cases hok with
    | ref_is_null hht =>
        rename_i ht
        obtain ⟨rt?, base, href, _, hbase⟩ :=
          St.SatA.popRef_of_ref hsat
        have hbaseSource := (hstSource.popRef href).1
        refine ⟨base.push ValType.i32, ?_, ?_, hbaseSource.push (by trivial)⟩
        · simp [checkInstrA, href, St.push]
        · simpa using hbase.pushs (ts := [ValType.i32])
  case refAsNonNull =>
    cases hok with
    | ref_as_non_null hht =>
        rename_i ht
        obtain ⟨rt?, base, href, hrefSub, hbase⟩ :=
          St.SatA.popRef_of_ref hsat
        have hrefSources := hstSource.popRef href
        have hbaseSource : base.SourceA C := hrefSources.1
        have hpoppedSource : (poppedHeapType rt?).SourceA C := by
          cases rt? with
          | none => trivial
          | some rt =>
              cases rt with
              | ref nul actual => exact hrefSources.2 (.ref nul actual) rfl
        obtain ⟨_, hrefValid⟩ := St.popRef_valid hst href
        have hactualValid :
            ValValidA C (.ref (.ref none (poppedHeapType rt?))) :=
          poppedNonNull_valid hrefValid
        have hactualOk : Resulttype_okA C
            [.ref (.ref none (poppedHeapType rt?))] :=
          resultOk_singleton (hactualValid C (SameTypeEnv.refl C))
        have hlastSub : subOfA C
            (.ref (.ref none (poppedHeapType rt?)))
            (.ref (.ref none ht)) = true :=
          poppedNonNull_sub hheap.types hpoppedSource hht hrefSub
        have hpActual : (base.push
            (.ref (.ref none (poppedHeapType rt?)))).popsA C
              [.ref (.ref none (poppedHeapType rt?))] = some base := by
          simpa [St.push] using St.pushs_popsA C base
            [.ref (.ref none (poppedHeapType rt?))]
        have hpExpected : (base.push
            (.ref (.ref none (poppedHeapType rt?)))).popsA C
              [.ref (.ref none ht)] = some base :=
          St.SourceA.popsA_weaken_to_valid hheap.types
            (hbaseSource.push hpoppedSource) hactualOk
            (resultOk_singleton (.ref (.mk hht)))
            (resulttype_subA_of_subsA (by
              simpa [subsA, decResulttypeSubN, decSeq₂] using hlastSub))
            hpActual
        refine ⟨base.push (.ref (.ref none (poppedHeapType rt?))),
          ?_, St.satA_append hpExpected hbase,
          hbaseSource.push hpoppedSource⟩
        simp [checkInstrA, href, poppedHeapType, St.push]
        rfl
  case refTest rt =>
    cases hok with
    | ref_test htargetOk hsourceOk hsub =>
        rename_i source
        have hrtSyn : rt.isSyn = true := by
          simpa [Instr.isSyn] using hsyn
        have hrtCheck := checkReftypeOkA_complete hrtSyn htargetOk
        obtain ⟨input, htop⟩ := validationInputTopA_complete
          hheap.shapesHere hrtSyn htargetOk
        have hinputOk := validationInputTopA_ok htop
        have hsourceInput : Reftype_subA C source input :=
          reftypeSource_below_validationInputTopA hheap.shapesHere
            hheap.recsHere htargetOk hsourceOk hsub htop
        have hresultSub : Resulttype_subA C [.ref source] [.ref input] :=
          .mk (by simp [SeqLen₂]) (by
            intro j left right hleft hright
            cases j with
            | zero =>
                simp at hleft hright
                subst left
                subst right
                exact .ref hsourceInput
            | succ j => simp at hleft)
        obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
        have hbaseSource := hstSource.popsA hp
        have hpInput : st.popsA C [.ref input] = some base :=
          St.SourceA.popsA_weaken_to_valid hheap.types hstSource
            (resultOk_singleton (.ref hsourceOk))
            (resultOk_singleton (.ref hinputOk)) hresultSub hp
        have hpInput' : st.popEA C (.ref input) = some base := by
          simpa only [St.popsA] using hpInput
        refine ⟨base.push ValType.i32, ?_, ?_, hbaseSource.push (by trivial)⟩
        · simp [checkInstrA, hrtCheck, htop, hpInput', St.push]
        · simpa using hbase.pushs (ts := [ValType.i32])
  case refCast rt =>
    cases hok with
    | ref_cast htargetOk hsourceOk hsub =>
        rename_i source
        have hrtSyn : rt.isSyn = true := by
          simpa [Instr.isSyn] using hsyn
        have hrtCheck := checkReftypeOkA_complete hrtSyn htargetOk
        obtain ⟨input, htop⟩ := validationInputTopA_complete
          hheap.shapesHere hrtSyn htargetOk
        have hinputOk := validationInputTopA_ok htop
        have hsourceInput : Reftype_subA C source input :=
          reftypeSource_below_validationInputTopA hheap.shapesHere
            hheap.recsHere htargetOk hsourceOk hsub htop
        have hresultSub : Resulttype_subA C [.ref source] [.ref input] :=
          .mk (by simp [SeqLen₂]) (by
            intro j left right hleft hright
            cases j with
            | zero =>
                simp at hleft hright
                subst left
                subst right
                exact .ref hsourceInput
            | succ j => simp at hleft)
        obtain ⟨base, hp, hbase⟩ := St.SatA.split_append hsat
        have hbaseSource := hstSource.popsA hp
        have hpInput : st.popsA C [.ref input] = some base :=
          St.SourceA.popsA_weaken_to_valid hheap.types hstSource
            (resultOk_singleton (.ref hsourceOk))
            (resultOk_singleton (.ref hinputOk)) hresultSub hp
        have hpInput' : st.popEA C (.ref input) = some base := by
          simpa only [St.popsA] using hpInput
        have hrtSource := htargetOk.sourceA_of_syn hrtSyn
        refine ⟨base.push (.ref rt), ?_, ?_, hbaseSource.push hrtSource⟩
        · simp [checkInstrA, hrtCheck, htop, hpInput', St.push]
        · simpa using hbase.pushs (ts := [.ref rt])
  case externConvertAny =>
    cases hok with
    | extern_convert_any =>
        rename_i nul
        obtain ⟨rt?, base, href, hrefSub, hbase⟩ :=
          St.SatA.popRef_of_ref hsat
        have hrefSources := hstSource.popRef href
        have hbaseSource : base.SourceA C := hrefSources.1
        have houtSource : (poppedAbstractRef .extern rt?).SourceA C := by
          cases rt? with
          | none => trivial
          | some rt => cases rt <;> trivial
        have houtValid : ValValidA C
            (poppedAbstractRef .extern rt?) :=
          poppedAbstractRef_valid (C := C) Heaptype_okA.abs
        have houtOk : Resulttype_okA C [poppedAbstractRef .extern rt?] :=
          resultOk_singleton (houtValid C (SameTypeEnv.refl C))
        have houtSub : subOfA C (poppedAbstractRef .extern rt?)
            (.ref (.ref nul (.abs .extern))) = true :=
          poppedAbstractRef_sub hheap.types hrefSub
        have hpActual : (base.push (poppedAbstractRef .extern rt?)).popsA C
            [poppedAbstractRef .extern rt?] = some base := by
          simpa [St.push] using St.pushs_popsA C base
            [poppedAbstractRef .extern rt?]
        have hpExpected : (base.push (poppedAbstractRef .extern rt?)).popsA C
            [.ref (.ref nul (.abs .extern))] = some base :=
          St.SourceA.popsA_weaken hheap.types
            (hbaseSource.push houtSource) houtOk
            (ResultSourceA.singleton (by trivial))
            (resulttype_subA_of_subsA (by
              simpa [subsA, decResulttypeSubN, decSeq₂] using houtSub))
            hpActual
        refine ⟨base.push (poppedAbstractRef .extern rt?), ?_,
          St.satA_append hpExpected hbase, hbaseSource.push houtSource⟩
        cases rt? with
        | none => simp [checkInstrA, href, poppedAbstractRef, St.push]
        | some rt =>
            cases rt with
            | ref actualNul actualHeap =>
                have hactualSource : actualHeap.SourceA C :=
                  hrefSources.2 (.ref actualNul actualHeap) rfl
                have hs := valtype_subA_of_subOfA hrefSub
                have hgate : decHeaptypeSubN C C.subtypeFuel actualHeap
                    (.abs .any) = true := by
                  cases hs with
                  | ref hrefSem =>
                      cases hrefSem with
                      | nonnull hh | null hh =>
                          exact hheap.types.complete hactualSource (by trivial) hh
                simp [checkInstrA, href, hgate, poppedAbstractRef, St.push]
  case anyConvertExtern =>
    cases hok with
    | any_convert_extern =>
        rename_i nul
        obtain ⟨rt?, base, href, hrefSub, hbase⟩ :=
          St.SatA.popRef_of_ref hsat
        have hrefSources := hstSource.popRef href
        have hbaseSource : base.SourceA C := hrefSources.1
        have houtSource : (poppedAbstractRef .any rt?).SourceA C := by
          cases rt? with
          | none => trivial
          | some rt => cases rt <;> trivial
        have houtValid : ValValidA C (poppedAbstractRef .any rt?) :=
          poppedAbstractRef_valid (C := C) Heaptype_okA.abs
        have houtOk : Resulttype_okA C [poppedAbstractRef .any rt?] :=
          resultOk_singleton (houtValid C (SameTypeEnv.refl C))
        have houtSub : subOfA C (poppedAbstractRef .any rt?)
            (.ref (.ref nul (.abs .any))) = true :=
          poppedAbstractRef_sub hheap.types hrefSub
        have hpActual : (base.push (poppedAbstractRef .any rt?)).popsA C
            [poppedAbstractRef .any rt?] = some base := by
          simpa [St.push] using St.pushs_popsA C base
            [poppedAbstractRef .any rt?]
        have hpExpected : (base.push (poppedAbstractRef .any rt?)).popsA C
            [.ref (.ref nul (.abs .any))] = some base :=
          St.SourceA.popsA_weaken hheap.types
            (hbaseSource.push houtSource) houtOk
            (ResultSourceA.singleton (by trivial))
            (resulttype_subA_of_subsA (by
              simpa [subsA, decResulttypeSubN, decSeq₂] using houtSub))
            hpActual
        refine ⟨base.push (poppedAbstractRef .any rt?), ?_,
          St.satA_append hpExpected hbase, hbaseSource.push houtSource⟩
        cases rt? with
        | none => simp [checkInstrA, href, poppedAbstractRef, St.push]
        | some rt =>
            cases rt with
            | ref actualNul actualHeap =>
                have hactualSource : actualHeap.SourceA C :=
                  hrefSources.2 (.ref actualNul actualHeap) rfl
                have hs := valtype_subA_of_subOfA hrefSub
                have hgate : decHeaptypeSubN C C.subtypeFuel actualHeap
                    (.abs .extern) = true := by
                  cases hs with
                  | ref hrefSem =>
                      cases hrefSem with
                      | nonnull hh | null hh =>
                          exact hheap.types.complete hactualSource (by trivial) hh
                simp [checkInstrA, href, hgate, poppedAbstractRef, St.push]
  all_goals exact instrCompleteFullA_default hheap hsyn rfl hok hstSource hsat

theorem Context.setEffects_complete {C : Context} :
    ∀ {xs : List LocalIdx} {ts : List ValType},
      SeqLen₂ xs ts →
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
        ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs ts →
      Context.setEffects C xs = some
        (Context.withLocals C xs (ts.map fun t => ⟨.set, t⟩)) := by
  intro xs
  induction xs generalizing C with
  | nil =>
      intro ts hlen hall
      cases ts with
      | nil => rfl
      | cons t ts => simp [SeqLen₂] at hlen
  | cons x xs ih =>
      intro ts hlen hall
      cases ts with
      | nil => simp [SeqLen₂] at hlen
      | cons t ts =>
          obtain ⟨ini, hx⟩ := hall 0 x t (by simp) (by simp)
          have htailLen : SeqLen₂ xs ts := by
            simp only [SeqLen₂, List.length_cons] at hlen ⊢
            omega
          have htail : SeqAll₂ (fun (y : LocalIdx) (u : ValType) =>
              ∃ ini : Init,
                (C.setLocal x ⟨.set, t⟩).locals[y.val]? = some ⟨ini, u⟩)
              xs ts := by
            intro j y u hy hu
            obtain ⟨iniY, hyC⟩ := hall (j + 1) y u
              (by simpa using hy) (by simpa using hu)
            by_cases heq : y.val = x.val
            · have hyx : y = x := Subtype.ext heq
              subst y
              have hlocalEq : LocalType.mk ini t = LocalType.mk iniY u :=
                Option.some.inj (hx.symm.trans hyC)
              injection hlocalEq with hini htu
              subst u
              refine ⟨.set, ?_⟩
              have hlt : x.val < C.locals.length :=
                (List.getElem?_eq_some_iff.mp hx).1
              simp [Context.setLocal, List.getElem?_set_self hlt]
            · exact ⟨iniY, by
                simpa [Context.setLocal,
                  List.getElem?_set_ne (Ne.symm heq)] using hyC⟩
          simp only [Context.setEffects, hx, Context.withLocals, List.map_cons]
          exact ih htailLen htail

theorem checkInstrA_preserves_valid {C : Context} {i : Instr}
    {st st' : St} {xs : List LocalIdx} (hC : Context.ValidA C)
    (hrun : checkInstrA C st i = some (xs, st')) (hst : St.ValidA C st) :
    St.ValidA C st' := by
  exact (instrSoundFullA_step i
    (fun body hb => seqSoundFullA (InstrSeq.size body) body (Nat.le_refl _))
    C hC st st' xs hrun hst).1

end Validate
end WasmGemmGnaf.Wasm.Core
