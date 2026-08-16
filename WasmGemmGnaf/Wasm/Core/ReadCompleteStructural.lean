import WasmGemmGnaf.Wasm.Core.ReadCompleteSimple

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem readResult_mem_completeReadSuccessorsOf_of_readResults
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is : List AdminInstr} (result : StepAResult (z, is))
    (hmem : result ∈ readResults z is) :
    result.toPair ∈ completeReadSuccessorsOf fuel (z, is) complete := by
  apply mem_completeReadSuccessorsOf_of_mem_readSuccessorsOf complete
  unfold readSuccessorsOf
  simp only [List.mem_map]
  refine ⟨result, ?_, rfl⟩
  unfold readResultsOf
  exact List.mem_append_left _ hmem

theorem readResult_mem_completeReadSuccessorsOf_of_structuralReadResults
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is : List AdminInstr} (result : StepAResult (z, is))
    (hmem : result ∈ structuralReadResults z is) :
    result.toPair ∈ completeReadSuccessorsOf fuel (z, is) complete := by
  apply readResult_mem_completeReadSuccessorsOf_of_readResults
    complete result
  unfold readResults
  exact List.mem_append_right _ hmem

theorem readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is : List AdminInstr} (result : StepAResult (z, is))
    (hmem : result ∈ certifiedWrapperReadResults z is) :
    result.toPair ∈ completeReadSuccessorsOf fuel (z, is) complete := by
  unfold completeReadSuccessorsOf
  simp only [List.mem_map]
  refine ⟨result, ?_, rfl⟩
  unfold completeReadResultsOf
  apply List.mem_append_right
  exact List.mem_append_right _ hmem

theorem splitLastValue?_append_singleton {α : Type}
    (initial : List α) (last : α) :
    splitLastValue? (initial ++ [last]) = some (initial, last) := by
  induction initial with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [List.cons_append, splitLastValue?]
          have ih' : splitLastValue? (next :: (rest ++ [last])) =
              some (next :: rest, last) := by
            simpa only [List.cons_append] using ih
          rw [ih']
          rfl

@[simp] theorem splitVals_vals_append_singleton_nonval
    (values : List Val) {instruction : AdminInstr}
    (hnonvalue : adminToVal instruction = none) (suffix : List AdminInstr) :
    splitVals (vals values ++ [instruction] ++ suffix) =
      (values, instruction :: suffix) := by
  simpa only [List.append_assoc, List.singleton_append] using
    splitVals_vals_append_nonval values hnonvalue suffix

theorem refNullIdx_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refNullIdx is is') :
    (.read .refNullIdx (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refNullIdx typeIndex type htype =>
      let result : StepAResult
          (z, [.plain (.refNull (.use (.idx typeIndex)))]) :=
        readResult .refNullIdx
          (Step_read.refNullIdx (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htype)
      apply readResult_mem_completeReadSuccessorsOf_of_readResults
        complete result
      unfold readResults
      apply List.mem_append_left
      apply List.mem_append_left
      simp only [elementaryReadResults]
      split
      · rename_i hnone
        rw [htype] at hnone
        contradiction
      · rename_i foundType hfoundType
        have heq := Option.some.inj (hfoundType.symm.trans htype)
        subst foundType
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefNull is is') :
    (.read .throwRefNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefNull heapType =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType)]) (instruction := .throwRef) complete
        (Step_read.throwRefNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefLabel_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefLabel is is') :
    (.read .throwRefLabel (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefLabel arity continuation address =>
      let result : StepAResult
          (z, [.label arity continuation
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefLabel
          (Step_read.throwRefLabel (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply readResult_mem_completeReadSuccessorsOf_of_readResults
        complete result
      unfold readResults
      apply List.mem_append_right
      unfold structuralReadResults
      apply List.mem_append_right
      dsimp only
      apply List.mem_append_right
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefFrame_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefFrame is is') :
    (.read .throwRefFrame (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefFrame arity frame address =>
      let result : StepAResult
          (z, [.frame arity frame
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefFrame
          (Step_read.throwRefFrame (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply readResult_mem_completeReadSuccessorsOf_of_readResults
        complete result
      unfold readResults
      apply List.mem_append_right
      unfold structuralReadResults
      apply List.mem_append_right
      dsimp only
      apply List.mem_append_right
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefHandlerEmpty_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerEmpty is is') :
    (.read .throwRefHandlerEmpty (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerEmpty arity address =>
      let result : StepAResult
          (z, [.handler arity []
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefHandlerEmpty
          (Step_read.throwRefHandlerEmpty
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply readResult_mem_completeReadSuccessorsOf_of_readResults
        complete result
      unfold readResults
      apply List.mem_append_right
      unfold structuralReadResults
      apply List.mem_append_right
      dsimp only
      unfold throwRefHandlerResults
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefHandlerResult_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    (arity : Nat) (catches : List Catch) (address : ExnAddr)
    (result : StepAResult
      (z, [.handler arity catches
        [.addrref (.exnAddr address), .plain .throwRef]]))
    (hmem : result ∈ throwRefHandlerResults z arity catches address) :
    result.toPair ∈ completeReadSuccessorsOf fuel
      (z, [.handler arity catches
        [.addrref (.exnAddr address), .plain .throwRef]]) complete := by
  apply readResult_mem_completeReadSuccessorsOf_of_readResults
    complete result
  unfold readResults
  apply List.mem_append_right
  unfold structuralReadResults
  apply List.mem_append_right
  dsimp only
  exact List.mem_append_right _ hmem

theorem throwRefHandlerCatchAll_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerCatchAll is is') :
    (.read .throwRefHandlerCatchAll (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerCatchAll arity label catches address =>
      let result : StepAResult
          (z, [.handler arity (.all label :: catches)
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefHandlerCatchAll
          (Step_read.throwRefHandlerCatchAll
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
        arity (.all label :: catches) address result
      unfold throwRefHandlerResults
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefHandlerCatchAllRef_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerCatchAllRef is is') :
    (.read .throwRefHandlerCatchAllRef (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerCatchAllRef arity label catches address =>
      let result : StepAResult
          (z, [.handler arity (.allRef label :: catches)
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefHandlerCatchAllRef
          (Step_read.throwRefHandlerCatchAllRef
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
        arity (.allRef label :: catches) address result
      unfold throwRefHandlerResults
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefHandlerCatch_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerCatch is is') :
    (.read .throwRefHandlerCatch (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerCatch arity tagIndex label catches address exception
      tagAddress hexception htag heq =>
      let result : StepAResult
          (z, [.handler arity (.tag tagIndex label :: catches)
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefHandlerCatch
          (Step_read.throwRefHandlerCatch
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hexception htag heq)
      apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
        arity (.tag tagIndex label :: catches) address result
      unfold throwRefHandlerResults
      dsimp only
      split
      · rename_i foundException foundTag hfoundException hfoundTag
        have he := Option.some.inj (hfoundException.symm.trans hexception)
        have ht := Option.some.inj (hfoundTag.symm.trans htag)
        subst foundException
        subst foundTag
        split
        · apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
        · simp_all
      · rename_i hnone
        rw [hexception] at hnone
        contradiction
      · rename_i htagNone _
        rw [htag] at htagNone
        contradiction

theorem throwRefHandlerCatchRef_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerCatchRef is is') :
    (.read .throwRefHandlerCatchRef (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerCatchRef arity tagIndex label catches address exception
      tagAddress hexception htag heq =>
      let result : StepAResult
          (z, [.handler arity (.tagRef tagIndex label :: catches)
            [.addrref (.exnAddr address), .plain .throwRef]]) :=
        readResult .throwRefHandlerCatchRef
          (Step_read.throwRefHandlerCatchRef
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hexception htag heq)
      apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
        arity (.tagRef tagIndex label :: catches) address result
      unfold throwRefHandlerResults
      dsimp only
      split
      · rename_i foundException foundTag hfoundException hfoundTag
        have he := Option.some.inj (hfoundException.symm.trans hexception)
        have ht := Option.some.inj (hfoundTag.symm.trans htag)
        subst foundException
        subst foundTag
        split
        · apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
        · simp_all
      · rename_i hnone
        rw [hexception] at hnone
        contradiction
      · rename_i htagNone _
        rw [htag] at htagNone
        contradiction

theorem throwRefHandlerNext_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefHandlerNext is is') :
    (.read .throwRefHandlerNext (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefHandlerNext arity caught catches address hnot =>
      cases caught with
      | all label =>
          exact False.elim (hnot (by simp [catchMatches]))
      | allRef label =>
          exact False.elim (hnot (by simp [catchMatches]))
      | tag tagIndex label =>
          let result : StepAResult
              (z, [.handler arity (.tag tagIndex label :: catches)
                [.addrref (.exnAddr address), .plain .throwRef]]) :=
            readResult .throwRefHandlerNext
              (Step_read.throwRefHandlerNext
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hnot)
          apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
            arity (.tag tagIndex label :: catches) address result
          unfold throwRefHandlerResults
          dsimp only
          split
          · rename_i exception tagAddress hexception htag
            split
            · rename_i heq
              exact False.elim (hnot (by
                simp [catchMatches, hexception, htag, heq]))
            · apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
      | tagRef tagIndex label =>
          let result : StepAResult
              (z, [.handler arity (.tagRef tagIndex label :: catches)
                [.addrref (.exnAddr address), .plain .throwRef]]) :=
            readResult .throwRefHandlerNext
              (Step_read.throwRefHandlerNext
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hnot)
          apply throwRefHandlerResult_mem_completeReadSuccessorsOf complete
            arity (.tagRef tagIndex label :: catches) address result
          unfold throwRefHandlerResults
          dsimp only
          split
          · rename_i exception tagAddress hexception htag
            split
            · rename_i heq
              exact False.elim (hnot (by
                simp [catchMatches, hexception, htag, heq]))
            · apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl

theorem tryTable_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tryTable is is') :
    (.read .tryTable (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tryTable values blockType catches body domain codomain m n htype
      hdomain hcodomain hvalues =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := values) (instruction := .tryTable blockType catches body)
        complete
        (Step_read.tryTable (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) htype hdomain hcodomain hvalues) rfl
      simp only [instructionReadResults]
      split
      · rename_i hnone
        rw [htype] at hnone
        contradiction
      · rename_i computedDomain computedCodomain hcomputed
        have hpair := Option.some.inj (hcomputed.symm.trans htype)
        simp only [Prod.mk.injEq] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        split <;> simp_all [readResult] <;> omega

theorem returnCallRefLabel_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .returnCallRefLabel is is') :
    (.read .returnCallRefLabel (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @returnCallRefLabel arity continuation values typeUse suffix =>
      let result : StepAResult
          (z, [.label arity continuation
            (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)]) :=
        readResult .returnCallRefLabel
          (Step_read.returnCallRefLabel
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply
        readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
          complete result
      simp only [certifiedWrapperReadResults]
      let supplied : CertifiedValueSplit
          (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix) :=
        { values := values
          tail := .plain (.returnCallRef typeUse) :: suffix
          rebuild := by simp [List.append_assoc] }
      have hsplit : certifiedValueSplit
            (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix) =
          supplied := by
        apply CertifiedValueSplit.eq_of_values_tail
        · change (splitVals
              (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)).1 =
            values
          rw [splitVals_vals_append_singleton_nonval values rfl suffix]
        · change (splitVals
              (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)).2 =
            .plain (.returnCallRef typeUse) :: suffix
          rw [splitVals_vals_append_singleton_nonval values rfl suffix]
      rw [hsplit]
      unfold returnCallRefLabelResultsFromSplit
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem returnCallRefHandler_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .returnCallRefHandler is is') :
    (.read .returnCallRefHandler (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @returnCallRefHandler arity catches values typeUse suffix =>
      let result : StepAResult
          (z, [.handler arity catches
            (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)]) :=
        readResult .returnCallRefHandler
          (Step_read.returnCallRefHandler
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply
        readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
          complete result
      simp only [certifiedWrapperReadResults]
      let supplied : CertifiedValueSplit
          (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix) :=
        { values := values
          tail := .plain (.returnCallRef typeUse) :: suffix
          rebuild := by simp [List.append_assoc] }
      have hsplit : certifiedValueSplit
            (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix) =
          supplied := by
        apply CertifiedValueSplit.eq_of_values_tail
        · change (splitVals
              (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)).1 =
            values
          rw [splitVals_vals_append_singleton_nonval values rfl suffix]
        · change (splitVals
              (vals values ++ [.plain (.returnCallRef typeUse)] ++ suffix)).2 =
            .plain (.returnCallRef typeUse) :: suffix
          rw [splitVals_vals_append_singleton_nonval values rfl suffix]
      rw [hsplit]
      unfold returnCallRefHandlerResultsFromSplit
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem returnCallRefFrameNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .returnCallRefFrameNull is is') :
    (.read .returnCallRefFrameNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @returnCallRefFrameNull arity frame values heapType typeUse suffix =>
      let result : StepAResult
          (z, [.frame arity frame
            (vals values ++ [Ref.toAdmin (.null heapType),
              .plain (.returnCallRef typeUse)] ++ suffix)]) :=
        readResult .returnCallRefFrameNull
          (Step_read.returnCallRefFrameNull
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics))
      apply
        readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
          complete result
      simp only [certifiedWrapperReadResults]
      apply List.mem_append_right
      let supplied : CertifiedValueSplit
          (vals values ++ [Ref.toAdmin (.null heapType),
            .plain (.returnCallRef typeUse)] ++ suffix) :=
        { values := values ++ [.ref (.null heapType)]
          tail := .plain (.returnCallRef typeUse) :: suffix
          rebuild := by
            simp [vals, Ref.toAdmin, Val.toAdmin, List.map_append,
              List.append_assoc] }
      have hsource :
          vals values ++ [Ref.toAdmin (.null heapType),
              .plain (.returnCallRef typeUse)] ++ suffix =
            vals (values ++ [.ref (.null heapType)]) ++
              [.plain (.returnCallRef typeUse)] ++ suffix := by
        simp [vals, Ref.toAdmin, Val.toAdmin, List.map_append,
          List.append_assoc]
      have hsplit : certifiedValueSplit
            (vals values ++ [Ref.toAdmin (.null heapType),
              .plain (.returnCallRef typeUse)] ++ suffix) = supplied := by
        apply CertifiedValueSplit.eq_of_values_tail
        · change (splitVals
              (vals values ++ [Ref.toAdmin (.null heapType),
                .plain (.returnCallRef typeUse)] ++ suffix)).1 =
            values ++ [.ref (.null heapType)]
          rw [hsource]
          change (splitVals
                (vals (values ++ [.ref (.null heapType)]) ++
                  [.plain (.returnCallRef typeUse)] ++ suffix)).1 =
              values ++ [.ref (.null heapType)]
          exact congrArg Prod.fst
            (splitVals_vals_append_singleton_nonval
              (values ++ [.ref (.null heapType)])
              (instruction := .plain (.returnCallRef typeUse)) rfl suffix)
        · change (splitVals
              (vals values ++ [Ref.toAdmin (.null heapType),
                .plain (.returnCallRef typeUse)] ++ suffix)).2 =
            .plain (.returnCallRef typeUse) :: suffix
          rw [hsource]
          change (splitVals
                (vals (values ++ [.ref (.null heapType)]) ++
                  [.plain (.returnCallRef typeUse)] ++ suffix)).2 =
              .plain (.returnCallRef typeUse) :: suffix
          exact congrArg Prod.snd
            (splitVals_vals_append_singleton_nonval
              (values ++ [.ref (.null heapType)])
              (instruction := .plain (.returnCallRef typeUse)) rfl suffix)
      rw [hsplit]
      unfold returnCallRefFrameNullResultsFromSplit
      simp only [supplied]
      split <;> simp_all [splitLastValue?_append_singleton,
        StepAResult.eq_of_event_next]
      rename_i initial' heapType' hlast
      have hp := Option.some.inj
        (hlast.symm.trans
          (splitLastValue?_append_singleton values
            (.ref (.null heapType))))
      simp only [Prod.mk.injEq, Val.ref.injEq, Ref.null.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      apply Or.inl
      apply StepAResult.eq_of_event_next <;> rfl

theorem throwRefInstrs_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .throwRefInstrs is is') :
    (.read .throwRefInstrs (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @throwRefInstrs values address suffix hnonempty =>
      let result : StepAResult
          (z, vals values ++
            [.addrref (.exnAddr address), .plain .throwRef] ++ suffix) :=
        readResult .throwRefInstrs
          (Step_read.throwRefInstrs
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hnonempty)
      apply
        readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
          complete result
      simp only [certifiedWrapperReadResults]
      apply List.mem_append_left
      let supplied : CertifiedValueSplit
          (vals values ++
            [.addrref (.exnAddr address), .plain .throwRef] ++ suffix) :=
        { values := values ++ [.ref (.addr (.exnAddr address))]
          tail := .plain .throwRef :: suffix
          rebuild := by
            simp [vals, Ref.toAdmin, Val.toAdmin, List.map_append,
              List.append_assoc] }
      have hsource :
          vals values ++
              [.addrref (.exnAddr address), .plain .throwRef] ++ suffix =
            vals (values ++ [.ref (.addr (.exnAddr address))]) ++
              [.plain .throwRef] ++ suffix := by
        simp [vals, Val.toAdmin, List.map_append, List.append_assoc]
      have hsplit : certifiedValueSplit
            (vals values ++
              [.addrref (.exnAddr address), .plain .throwRef] ++ suffix) =
          supplied := by
        apply CertifiedValueSplit.eq_of_values_tail
        · change (splitVals
              (vals values ++
                [.addrref (.exnAddr address), .plain .throwRef] ++ suffix)).1 =
            values ++ [.ref (.addr (.exnAddr address))]
          rw [hsource]
          change (splitVals
                (vals (values ++ [.ref (.addr (.exnAddr address))]) ++
                  [.plain .throwRef] ++ suffix)).1 =
              values ++ [.ref (.addr (.exnAddr address))]
          exact congrArg Prod.fst
            (splitVals_vals_append_singleton_nonval
              (values ++ [.ref (.addr (.exnAddr address))])
              (instruction := .plain .throwRef) rfl suffix)
        · change (splitVals
              (vals values ++
                [.addrref (.exnAddr address), .plain .throwRef] ++ suffix)).2 =
            .plain .throwRef :: suffix
          rw [hsource]
          change (splitVals
                (vals (values ++ [.ref (.addr (.exnAddr address))]) ++
                  [.plain .throwRef] ++ suffix)).2 =
              .plain .throwRef :: suffix
          exact congrArg Prod.snd
            (splitVals_vals_append_singleton_nonval
              (values ++ [.ref (.addr (.exnAddr address))])
              (instruction := .plain .throwRef) rfl suffix)
      rw [hsplit]
      unfold throwRefInstrResultsFromSplit
      simp only [supplied]
      split <;> simp_all [splitLastValue?_append_singleton,
        StepAResult.eq_of_event_next]
      rename_i initial' address' hlast
      have hp := Option.some.inj
        (hlast.symm.trans
          (splitLastValue?_append_singleton values
            (.ref (.addr (.exnAddr address)))))
      simp only [Prod.mk.injEq, Val.ref.injEq, Ref.addr.injEq,
        AddrRef.exnAddr.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      exact ⟨hnonempty, by apply StepAResult.eq_of_event_next <;> rfl⟩

theorem returnCallRefFrameAddr_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .returnCallRefFrameAddr is is') :
    (.read .returnCallRefFrameAddr (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @returnCallRefFrameAddr arity frame discarded arguments address typeUse
      suffix function domain codomain n m hfunc hexpand hdomain hcodomain
      harguments =>
      cases hexpand with
      | mk hexpand =>
        let result : StepAResult
            (z, [.frame arity frame
              (vals discarded ++ vals arguments ++
                [.addrref (.funcAddr address),
                  .plain (.returnCallRef typeUse)] ++ suffix)]) :=
          readResult .returnCallRefFrameAddr
            (Step_read.returnCallRefFrameAddr
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hfunc (.mk hexpand) hdomain
              hcodomain harguments)
        apply
          readResult_mem_completeReadSuccessorsOf_of_certifiedWrapper
            complete result
        simp only [certifiedWrapperReadResults]
        apply List.mem_append_right
        apply List.mem_append_right
        let valuePrefix := discarded ++ arguments
        let supplied : CertifiedValueSplit
            (vals discarded ++ vals arguments ++
              [.addrref (.funcAddr address),
                .plain (.returnCallRef typeUse)] ++ suffix) :=
          { values := valuePrefix ++ [.ref (.addr (.funcAddr address))]
            tail := .plain (.returnCallRef typeUse) :: suffix
            rebuild := by
              simp [valuePrefix, vals, Val.toAdmin, List.map_append,
                List.append_assoc] }
        have hsource :
            vals discarded ++ vals arguments ++
                [.addrref (.funcAddr address),
                  .plain (.returnCallRef typeUse)] ++ suffix =
              vals (valuePrefix ++ [.ref (.addr (.funcAddr address))]) ++
                [.plain (.returnCallRef typeUse)] ++ suffix := by
          simp [valuePrefix, vals, Val.toAdmin, List.map_append,
            List.append_assoc]
        have hsplit : certifiedValueSplit
              (vals discarded ++ vals arguments ++
                [.addrref (.funcAddr address),
                  .plain (.returnCallRef typeUse)] ++ suffix) = supplied := by
          apply CertifiedValueSplit.eq_of_values_tail
          · change (splitVals
                (vals discarded ++ vals arguments ++
                  [.addrref (.funcAddr address),
                    .plain (.returnCallRef typeUse)] ++ suffix)).1 =
              valuePrefix ++ [.ref (.addr (.funcAddr address))]
            rw [hsource]
            exact congrArg Prod.fst
              (splitVals_vals_append_singleton_nonval
                (valuePrefix ++ [.ref (.addr (.funcAddr address))])
                (instruction := .plain (.returnCallRef typeUse)) rfl suffix)
          · change (splitVals
                (vals discarded ++ vals arguments ++
                  [.addrref (.funcAddr address),
                    .plain (.returnCallRef typeUse)] ++ suffix)).2 =
              .plain (.returnCallRef typeUse) :: suffix
            rw [hsource]
            exact congrArg Prod.snd
              (splitVals_vals_append_singleton_nonval
                (valuePrefix ++ [.ref (.addr (.funcAddr address))])
                (instruction := .plain (.returnCallRef typeUse)) rfl suffix)
        rw [hsplit]
        unfold returnCallRefFrameAddrResultsFromSplit
        simp only [supplied]
        split <;> simp_all [splitLastValue?_append_singleton]
        rename_i beforeAddress address' hlast
        have hp := Option.some.inj
          (hlast.symm.trans
            (splitLastValue?_append_singleton valuePrefix
              (.ref (.addr (.funcAddr address)))))
        simp only [Prod.mk.injEq, Val.ref.injEq, Ref.addr.injEq,
          AddrRef.funcAddr.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        split
        · rename_i hnone
          rw [hfunc] at hnone
          contradiction
        · rename_i foundFunction hfoundFunction
          have hfunction := Option.some.inj
            (hfoundFunction.symm.trans hfunc)
          subst foundFunction
          split <;> simp_all
          rename_i foundDomain foundCodomain hfoundExpand
          have htypes := Option.some.inj
            (hfoundExpand.symm.trans hexpand)
          simp only [CompType.func.injEq] at htypes
          rcases htypes with ⟨rfl, rfl⟩
          have hfits : foundDomain.length ≤ valuePrefix.length := by
            simp only [valuePrefix, List.length_append]
            omega
          refine ⟨hfits, ?_⟩
          have hcut : valuePrefix.length - foundDomain.length =
              discarded.length := by
            simp only [valuePrefix, List.length_append]
            omega
          have htake : valuePrefix.take
                (valuePrefix.length - foundDomain.length) = discarded := by
            rw [hcut]
            simp [valuePrefix]
          have hdrop : valuePrefix.drop
                (valuePrefix.length - foundDomain.length) = arguments := by
            rw [hcut]
            simp [valuePrefix]
          apply StepAResult.eq_of_event_next
          · rw [StepAResult.castSource_event]
            change Event.read .returnCallRefFrameAddr
                (sourcePlains
                  [.frame arity frame
                    (vals discarded ++ vals arguments ++
                      [.addrref (.funcAddr address'),
                        .plain (.returnCallRef typeUse)] ++ suffix)]) =
              Event.read .returnCallRefFrameAddr
                (sourcePlains
                  [.frame arity frame
                    (vals (valuePrefix.take
                        (valuePrefix.length - foundDomain.length)) ++
                      vals (valuePrefix.drop
                        (valuePrefix.length - foundDomain.length)) ++
                      [.addrref (.funcAddr address'),
                        .plain (.returnCallRef typeUse)] ++ suffix)])
            rw [htake, hdrop]
          · rw [StepAResult.castSource_next]
            change (z, vals arguments ++
                [.addrref (.funcAddr address'), .plain (.callRef typeUse)]) =
              (z, vals (valuePrefix.drop
                  (valuePrefix.length - foundDomain.length)) ++
                [.addrref (.funcAddr address'), .plain (.callRef typeUse)])
            rw [hdrop]

theorem callRefFunc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .callRefFunc is is') :
    (.read .callRefFunc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @callRefFunc arguments address typeUse function fn domain codomain n m
      frame hfunc hexpand hdomain hcodomain harguments hcode hframe =>
      cases hexpand with
      | mk hexpand =>
        subst frame
        let canonicalStep : Step_readA z .callRefFunc
            (vals (arguments ++ [.ref (.addr (.funcAddr address))]) ++
              [.plain (.callRef typeUse)])
            [.frame m
              { locals := arguments.map some ++
                  fn.locals.map (fun localDecl => default_ localDecl.valtype)
                mod := function.mod }
              [.label m [] (plains fn.body.toList)]] := by
          simpa [vals, Val.toAdmin, List.map_append, List.append_assoc] using
            Step_read.callRefFunc
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hfunc (.mk hexpand) hdomain hcodomain
              harguments hcode rfl
        have hmem : readResult .callRefFunc canonicalStep ∈
            instructionReadResults z
              (arguments ++ [.ref (.addr (.funcAddr address))])
              (.callRef typeUse) := by
          simp only [instructionReadResults]
          apply List.mem_append_right
          split
          · rename_i hnone
            have hcanonical :=
              splitLastValue?_append_singleton arguments
                (.ref (.addr (.funcAddr address)))
            rw [hnone] at hcanonical
            contradiction
          · rename_i foundArguments foundAddress hlast
            have hp := Option.some.inj
              (hlast.symm.trans
                (splitLastValue?_append_singleton arguments
                  (.ref (.addr (.funcAddr address)))))
            simp only [Prod.mk.injEq, Val.ref.injEq, Ref.addr.injEq,
              AddrRef.funcAddr.injEq] at hp
            rcases hp with ⟨rfl, rfl⟩
            unfold callRefFuncResults
            split
            · rename_i hnone
              rw [hfunc] at hnone
              contradiction
            · rename_i foundFunction hfoundFunction
              have hfunction := Option.some.inj
                (hfoundFunction.symm.trans hfunc)
              subst foundFunction
              split <;> simp_all
              rename_i foundFn hfoundCode
              have hfn := FuncCode.func.inj (hfoundCode.symm.trans hcode)
              subst foundFn
              split <;> simp_all
              rename_i foundDomain foundCodomain hfoundExpand
              have htypes := Option.some.inj
                (hfoundExpand.symm.trans hexpand)
              simp only [CompType.func.injEq] at htypes
              rcases htypes with ⟨rfl, rfl⟩
              have hlength : foundDomain.length =
                  foundArguments.length := by omega
              refine ⟨_, ⟨hdomain, rfl⟩, ?_⟩
              apply StepAResult.eq_of_event_next
              · rw [StepAResult.castSource_event]
                change Event.read .callRefFunc
                    (sourcePlains
                      (vals foundArguments ++
                        [.addrref (.funcAddr foundAddress),
                          .plain (.callRef typeUse)])) =
                  Event.read .callRefFunc
                    (sourcePlains
                      (vals (foundArguments ++
                          [.ref (.addr (.funcAddr foundAddress))]) ++
                        [.plain (.callRef typeUse)]))
                simp [vals, Val.toAdmin, List.map_append,
                  List.append_assoc]
              · rw [StepAResult.castSource_next]
                change (z,
                    [AdminInstr.frame foundCodomain.length
                      { locals := foundArguments.map some ++
                          fn.locals.map
                            (fun localDecl => default_ localDecl.valtype)
                        mod := function.mod }
                      [.label foundCodomain.length []
                        (plains fn.body.toList)]]) =
                  (z,
                    [AdminInstr.frame m
                      { locals := foundArguments.map some ++
                          fn.locals.map
                            (fun localDecl => default_ localDecl.valtype)
                        mod := function.mod }
                      [.label m [] (plains fn.body.toList)]])
                rw [hcodomain]
          · rename_i other hnot hlast
            have hp := Option.some.inj
              (hlast.symm.trans
                (splitLastValue?_append_singleton arguments
                  (.ref (.addr (.funcAddr address)))))
            exact False.elim (hnot arguments address hp)
        simpa [vals, Val.toAdmin, List.map_append, List.append_assoc] using
          readResult_mem_completeReadSuccessorsOf_of_instruction complete
            canonicalStep rfl hmem
