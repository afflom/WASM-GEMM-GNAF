import WasmGemmGnaf.Wasm.Core.ValidateSeqFullComplete

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-- Declarative sequence typing preserves well-formed endpoint result types
when every instruction in the sequence is grammar syntax. -/
theorem instrsResultOkA_of_source {C : Context} {is : List Instr}
    {it : InstrType} (hC : Context.ValidA C)
    (hheap : HeapSubCompleteA C)
    (hsyn : ∀ i ∈ is, Instr.isSyn i = true)
    (h : Instrs_okA C is it) :
    Resulttype_okA C it.dom ∧ Resulttype_okA C it.cod := by
  revert hC hheap hsyn
  induction h using Instrs_okA.rec
      (motive_1 := fun _ _ _ _ => True)
  case empty =>
      intro hC hheap hsyn
      exact ⟨resultOk_nil _, resultOk_nil _⟩
  case seq =>
      rename_i C i is ts₀ ts₁ ts₂ ts₃ ts xs₁ xs₂ hi hlen hall hts₀ htail _ ih
      intro hC hheap hsyn
      have hiSyn : Instr.isSyn i = true := hsyn i (by simp)
      have htailSyn : ∀ j ∈ is, Instr.isSyn j = true := by
        intro j hj
        exact hsyn j (by simp [hj])
      have hiOk := instrResultOkA hC hheap.types hheap.context hiSyn hi
      have hset := Context.setEffects_complete hlen hall
      have hC' : Context.ValidA
          (Context.withLocals C xs₁ (ts.map fun t => ⟨Init.set, t⟩)) :=
        hC.setEffects hset
      have hheap' := hheap.withLocals hlen hall
      have htailOk := ih hC' hheap' htailSyn
      have hsame := Context.setEffects_sameTypeEnv hset
      exact ⟨resultOk_append hts₀ hiOk.1,
        Resulttype_okA.transport hsame.1.symm hsame.2.symm htailOk.2⟩
  case sub =>
      rename_i C is it it' hbase hsub hitOk ih
      intro hC hheap hsyn
      cases hitOk with
      | mk hdom hcod _ => exact ⟨hdom, hcod⟩
  case frame =>
      rename_i C is ts ts₁ ts₂ xs hbase hts ih
      intro hC hheap hsyn
      have hbaseOk := ih hC hheap hsyn
      exact ⟨resultOk_append hts hbaseOk.1,
        resultOk_append hts hbaseOk.2⟩
  all_goals trivial

private theorem InstrSeq.isSyn_eq_all (s : InstrSeq) :
    InstrSeq.isSyn s = (InstrSeq.toList s).all Instr.isSyn := by
  induction s using InstrSeq.rec (motive_1 := fun _ => True)
  case nil => rfl
  case cons i rest _ ih => simp [InstrSeq.isSyn, InstrSeq.toList, ih]
  all_goals trivial

private theorem St.SatA.of_split_append {C : Context} {st base : St}
    {frame args : List ValType} (hp : st.popsA C args = some base)
    (hbase : St.SatA C base frame) : St.SatA C st (frame ++ args) := by
  obtain ⟨rest, hframe, hempty⟩ := hbase
  exact ⟨rest, by rw [St.popsA_append, hp]; exact hframe, hempty⟩

private theorem seqCompleteFullA_aux :
    ∀ {C : Context} {js : List Instr} {it : InstrType},
      Instrs_okA C js it → ∀ s : InstrSeq, js = InstrSeq.toList s →
      (∀ i : Instr, Instr.size i < InstrSeq.size s →
        InstrCompleteFullA i) →
      (∀ rest : InstrSeq, InstrSeq.size rest < InstrSeq.size s →
        SeqCompleteFullA rest) →
      Context.ValidA C → HeapSubCompleteA C →
      InstrSeq.isSyn s = true →
      ∀ (frame : List ValType) (st : St),
        St.ValidA C st → St.SourceA C st →
        St.SatA C st (frame ++ it.dom) →
        ∃ xs st', checkSeqA C st s = some (xs, st') ∧
          St.SatA C st' (frame ++ it.cod) ∧ St.SourceA C st' := by
  intro C js it h
  induction h using Instrs_okA.rec
      (motive_1 := fun _ _ _ _ => True)
  case empty =>
      intro s he hi hr hC hheap hsyn frame st hst hsource hsat
      have hs : s = InstrSeq.nil := by
        rw [← InstrSeq.ofList_toList s, ← he]
        rfl
      subst s
      exact ⟨[], st, rfl, hsat, hsource⟩
  case seq =>
      rename_i C i is ts₀ ts₁ ts₂ ts₃ ts xs₁ xs₂
        hiOk hlen hall hts₀ htail _ ih
      intro s he hi hr hC hheap hsyn frame st hst hsource hsat
      have hs : s = InstrSeq.cons i (InstrSeq.ofList is) := by
        rw [← InstrSeq.ofList_toList s, ← he]
        rfl
      subst s
      simp only [InstrSeq.isSyn, Bool.and_eq_true] at hsyn
      have hheadSat : St.SatA C st ((frame ++ ts₀) ++ ts₁) := by
        simpa only [List.append_assoc] using hsat
      obtain ⟨st₁, hrun₁, hsat₁, hsource₁⟩ :=
        hi i (InstrSeq.size_head i (InstrSeq.ofList is)) C
          ⟨ts₁, xs₁, ts₂⟩ hC hheap hsyn.1 hiOk
          (frame ++ ts₀) st hst hsource hheadSat
      have heffects := Context.setEffects_complete hlen hall
      let C' := Context.withLocals C xs₁
        (ts.map fun t => ⟨Init.set, t⟩)
      have hsame : SameTypeEnv C C' := by
        exact Context.setEffects_sameTypeEnv heffects
      have hC' : Context.ValidA C' := hC.setEffects heffects
      have hheap' : HeapSubCompleteA C' := hheap.withLocals hlen hall
      have hst₁' : St.ValidA C' st₁ :=
        (checkInstrA_preserves_valid hC hrun₁ hst).transport hsame
      have hsource₁' : St.SourceA C' st₁ := hsource₁.transport hsame
      have hsat₁' : St.SatA C' st₁ (frame ++ (ts₀ ++ ts₂)) := by
        apply St.SatA.transport hsame
        simpa only [List.append_assoc] using hsat₁
      obtain ⟨xs₂', st₂, hrun₂, hsat₂, hsource₂⟩ :=
        ih (InstrSeq.ofList is) (InstrSeq.toList_ofList is).symm
          (fun j hj => hi j (by
            have hhead := InstrSeq.size_head i (InstrSeq.ofList is)
            have htailSize := InstrSeq.size_tail i (InstrSeq.ofList is)
            omega))
          (fun rest hrest => hr rest (by
            have htailSize := InstrSeq.size_tail i (InstrSeq.ofList is)
            omega))
          hC' hheap' hsyn.2 frame st₁ hst₁' hsource₁' hsat₁'
      refine ⟨xs₁ ++ xs₂', st₂, ?_, ?_, hsource₂.transport hsame.symm⟩
      · simp [checkSeqA, hrun₁, heffects, hrun₂]
      · exact St.SatA.transport hsame.symm hsat₂
  case sub =>
      rename_i C is it it' hbase hsub hitOk ih
      intro s he hi hr hC hheap hsyn frame st hst hsource hsat
      have hsynAll : ∀ i ∈ is, Instr.isSyn i = true := by
        have hsAll : ∀ i ∈ InstrSeq.toList s, Instr.isSyn i = true := by
          rw [InstrSeq.isSyn_eq_all, List.all_eq_true] at hsyn
          exact hsyn
        intro i hi
        exact hsAll i (by simpa only [← he] using hi)
      have hbaseOk := instrsResultOkA_of_source hC hheap hsynAll hbase
      cases hitOk with
      | mk houterDom houterCod hlocals =>
          cases hsub with
          | mk hdomSub hcodSub hlocalsSub =>
              obtain ⟨base, hp, hframe⟩ := St.SatA.split_append hsat
              have hp' : st.popsA C it.dom = some base :=
                St.SourceA.popsA_weaken_to_valid hheap.types hsource
                  houterDom hbaseOk.1 hdomSub hp
              have hsat' : St.SatA C st (frame ++ it.dom) :=
                St.SatA.of_split_append hp' hframe
              obtain ⟨xs, st', hrun, hout, houtSource⟩ :=
                ih s he hi hr hC hheap hsyn frame st hst hsource hsat'
              obtain ⟨outBase, houtPop, houtFrame⟩ :=
                St.SatA.split_append hout
              have houtPop' : st'.popsA C it'.cod = some outBase :=
                St.SourceA.popsA_weaken_to_valid hheap.types houtSource
                  hbaseOk.2 houterCod hcodSub houtPop
              exact ⟨xs, st', hrun,
                St.SatA.of_split_append houtPop' houtFrame,
                houtSource⟩
  case frame =>
      rename_i C is ts ts₁ ts₂ xs hbase hts ih
      intro s he hi hr hC hheap hsyn frame st hst hsource hsat
      have hsat' : St.SatA C st ((frame ++ ts) ++ ts₁) := by
        simpa only [List.append_assoc] using hsat
      obtain ⟨ys, st', hrun, hout, houtSource⟩ :=
        ih s he hi hr hC hheap hsyn (frame ++ ts) st hst hsource hsat'
      refine ⟨ys, st', hrun, ?_, houtSource⟩
      simpa only [List.append_assoc] using hout
  all_goals trivial

theorem seqCompleteFullA_step (s : InstrSeq)
    (hi : ∀ i : Instr, Instr.size i < InstrSeq.size s →
      InstrCompleteFullA i)
    (hr : ∀ rest : InstrSeq, InstrSeq.size rest < InstrSeq.size s →
      SeqCompleteFullA rest) : SeqCompleteFullA s := by
  intro C it hC hheap hsyn hok frame st hst hsource hsat
  exact seqCompleteFullA_aux hok s rfl hi hr hC hheap hsyn frame st
    hst hsource hsat

theorem seqCompleteFullA : ∀ (n : Nat) (s : InstrSeq),
    InstrSeq.size s ≤ n → SeqCompleteFullA s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      exact seqCompleteFullA_step s
        (fun i hi => absurd hi (by omega))
        (fun rest hr => absurd hr (by omega))
  | succ n ih =>
      intro s hs
      exact seqCompleteFullA_step s
        (fun i hi => instrCompleteFullA_step i
          (fun body hbody => ih body (by omega)))
        (fun rest hrest => ih rest (by omega))

/-- Full syntax-directed sequence completeness at the sequence's own size. -/
theorem checkSeqA_complete_full (s : InstrSeq) : SeqCompleteFullA s :=
  seqCompleteFullA (InstrSeq.size s) s (Nat.le_refl _)

end Validate
end WasmGemmGnaf.Wasm.Core
