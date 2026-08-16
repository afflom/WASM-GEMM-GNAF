import WasmGemmGnaf.Wasm.Core.ReadComplete
import WasmGemmGnaf.Wasm.Core.ByteSolvedLiteralComplete

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Completeness of byte-solved store-reading rules

These are the memory/data rules whose witnesses are reconstructed from byte
sequences.  AMD-016's syntax-sort premises make the canonical executable
decoders complete for the relational rules without admitting malformed float
literals that share a wrapped representation.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem mem_instructionReadResults_load {z : State}
    (address : AddressLiteral) (numberType : NumType)
    (memoryIndex : MemIdx) (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.load numberType none memoryIndex argument)])}
    (hresult : result ∈
      loadNumResults z address numberType memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.load numberType none memoryIndex argument) := by
  simp only [instructionReadResults]
  split
  · rename_i hnone
    rw [addressLiteral?_toVal address] at hnone
    contradiction
  · rename_i foundAddress hfoundAddress
    have heq := Option.some.inj
      (hfoundAddress.symm.trans (addressLiteral?_toVal address))
    subst foundAddress
    apply List.mem_map.mpr
    refine ⟨result, hresult, ?_⟩
    apply StepAResult.eq_of_event_next <;> rfl

theorem loadNumOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .loadNumOob is is') :
    (.read .loadNumOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @loadNumOob addressType index numberType memoryIndex argument memory
      hmemory hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      let step : Step_readA z .loadNumOob
          [constAddr addressType index,
            .plain (.load numberType none memoryIndex argument)] [.trap] :=
        Step_read.loadNumOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [address.toVal])
        (instruction := .load numberType none memoryIndex argument)
        complete step rfl
      apply mem_instructionReadResults_load address numberType memoryIndex
        argument
      unfold loadNumResults
      split
      · rename_i hnone
        rw [hmemory] at hnone
        contradiction
      · rename_i foundMemory hfound
        have heq := Option.some.inj (hfound.symm.trans hmemory)
        subst foundMemory
        split
        · apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;>
            simp [step, readResult, address, AddressLiteral.toAdmin,
              sourcePlains, constAddr, addrLitToNum]
        · rename_i hin
          exact False.elim (hin (by simpa [address] using hoob))

theorem loadNumVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .loadNumVal is is') :
    (.read .loadNumVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @loadNumVal addressType index numberType memoryIndex argument memory value
      hmemory hbytes hwf =>
      let address : AddressLiteral := ⟨addressType, index⟩
      let step : Step_readA z .loadNumVal
          [constAddr addressType index,
            .plain (.load numberType none memoryIndex argument)]
          [.plain (.const numberType value)] :=
        Step_read.loadNumVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hbytes hwf
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [address.toVal])
        (instruction := .load numberType none memoryIndex argument)
        complete step rfl
      apply mem_instructionReadResults_load address numberType memoryIndex
        argument
      unfold loadNumResults
      split
      · rename_i hnone
        rw [hmemory] at hnone
        contradiction
      · rename_i foundMemory hfound
        have heq := Option.some.inj (hfound.symm.trans hmemory)
        subst foundMemory
        have hbytesAddress : releasedNumerics.nbytes_ numberType value =
            slice memory.bytes
              (address.value.val + argument.offset.val)
              (numberType.size / 8) := by
          simpa [address] using hbytes
        split
        · rename_i hoob
          have hsliceLength :
              (slice memory.bytes
                (address.value.val + argument.offset.val)
                (numberType.size / 8)).length = numberType.size / 8 := by
            rw [← hbytesAddress]
            exact nbytes_length_eq_size_div_eight value
          have hwidth : 0 < numberType.size / 8 := by
            cases numberType <;> decide
          simp [slice] at hsliceLength
          omega
        · let bytes := slice memory.bytes
              (address.value.val + argument.offset.val)
              (numberType.size / 8)
          have hcandidate := numOfBytes?_nbytes_complete value hwf
          have hbytesDef : releasedNumerics.nbytes_ numberType value =
              bytes := by simpa [bytes] using hbytesAddress
          rw [hbytesDef] at hcandidate
          dsimp only [bytes] at hcandidate hbytesDef ⊢
          split
          · rename_i hnone
            rw [hcandidate] at hnone
            contradiction
          · rename_i candidate hfound
            have heq := Option.some.inj (hfound.symm.trans hcandidate)
            subst candidate
            rw [dif_pos hbytesDef]
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [step, readResult, bytes, address,
                AddressLiteral.toAdmin, sourcePlains, constAddr,
                addrLitToNum]

theorem arrayNewDataOob_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayNewDataOob is is') :
    (.read .arrayNewDataOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayNewDataOob offset count typeIndex dataIndex definedType fieldType
      data size htype hexpand hsize hdata hoob =>
      cases hexpand with
      | mk hexpand =>
          let step : Step_readA z .arrayNewDataOob
              [constI32 offset, constI32 count,
                .plain (.arrayNewData typeIndex dataIndex)] [.trap] :=
            Step_read.arrayNewDataOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htype (.mk hexpand) hsize hdata hoob
          apply readResult_mem_completeReadSuccessorsOf_of_instruction
            (values := [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩])
            (instruction := .arrayNewData typeIndex dataIndex)
            complete step rfl
          simp only [instructionReadResults]
          unfold arrayNewDataResults
          split
          · rename_i hnone
            rw [htype] at hnone
            contradiction
          · rename_i foundType hfound
            have heq := Option.some.inj (hfound.symm.trans htype)
            subst foundType
            split
            · rename_i foundField hfoundField
              have hfield := Option.some.inj (hfoundField.symm.trans hexpand)
              injection hfield with hfield
              subst foundField
              split
              · rename_i foundSize foundData hfoundSize hfoundData
                have hsizeEq := Option.some.inj (hfoundSize.symm.trans hsize)
                subst foundSize
                have hdataEq := Option.some.inj (hfoundData.symm.trans hdata)
                subst foundData
                apply List.mem_append_left
                split
                · apply List.mem_cons.mpr
                  left
                  apply StepAResult.eq_of_event_next <;>
                    simp [step, readResult]
                · rename_i hin
                  exact False.elim (hin hoob)
              · rename_i hbad
                exact False.elim (hbad size data hsize hdata)
            · rename_i hbad
              exact False.elim (hbad fieldType hexpand)

theorem arrayNewDataNum_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayNewDataNum is is') :
    (.read .arrayNewDataNum (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayNewDataNum offset count typeIndex dataIndex definedType fieldType
      data size literals instructions htype hexpand hsize hdata hlength
      hwidth hbytes hinstructions hwf =>
      cases hexpand with
      | mk hexpand =>
          have hread : Step_readA z .arrayNewDataNum
              [constI32 offset, constI32 count,
                .plain (.arrayNewData typeIndex dataIndex)]
              (plains instructions ++
                [.plain (.arrayNewFixed typeIndex count)]) := by
            exact Step_read.arrayNewDataNum
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htype (.mk hexpand) hsize hdata
              hlength hwidth hbytes hinstructions hwf
          let raw := readResult .arrayNewDataNum hread
          have hraw : raw ∈
              arrayNewDataResults z offset count typeIndex dataIndex := by
            unfold arrayNewDataResults
            split
            · rename_i hnone
              rw [htype] at hnone
              contradiction
            · rename_i foundType hfoundType
              have ht := Option.some.inj (hfoundType.symm.trans htype)
              subst foundType
              split
              · rename_i foundField hfoundField
                have hf := Option.some.inj
                  (hfoundField.symm.trans hexpand)
                injection hf with hf
                subst foundField
                split
                · rename_i foundSize foundData hfoundSize hfoundData
                  have hs := Option.some.inj (hfoundSize.symm.trans hsize)
                  have hd := Option.some.inj (hfoundData.symm.trans hdata)
                  subst foundSize
                  subst foundData
                  apply List.mem_append_right
                  have hcandidates :=
                    storageLiteralCandidates_zbytes_complete
                      (fieldStorage fieldType) (size / 8) literals
                      hwidth hwf
                  rw [hlength, hbytes] at hcandidates
                  split
                  · rename_i hnone
                    rw [hcandidates] at hnone
                    contradiction
                  · rename_i foundLiterals hfoundLiterals
                    have hl := Option.some.inj
                      (hfoundLiterals.symm.trans hcandidates)
                    subst foundLiterals
                    rw [dif_pos hlength, dif_pos hwidth,
                      dif_pos hbytes]
                    split
                    · rename_i hnone
                      rw [hinstructions] at hnone
                      contradiction
                    · rename_i foundInstructions hfoundInstructions
                      have hi := Option.some.inj
                        (hfoundInstructions.symm.trans hinstructions)
                      subst foundInstructions
                      apply List.mem_singleton.mpr
                      apply StepAResult.eq_of_event_next <;> rfl
                · rename_i hbad
                  exact False.elim (hbad size data hsize hdata)
              · rename_i hbad
                exact False.elim (hbad fieldType hexpand)
          have hcomplete :=
            readResult_mem_completeReadSuccessorsOf_of_instruction
              (values := [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩])
              (instruction := .arrayNewData typeIndex dataIndex)
              complete hread rfl hraw
          simpa [raw, StepAResult.toPair, readResult, sourcePlains,
            Val.toAdmin, constI32] using hcomplete

theorem arrayInitDataNull_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitDataNull is is') :
    (.read .arrayInitDataNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitDataNull heapType arrayIndex dataIndex count typeIndex
      segmentIndex =>
      let step : Step_readA z .arrayInitDataNull
          [Ref.toAdmin (.null heapType), constI32 arrayIndex,
            constI32 dataIndex, constI32 count,
            .plain (.arrayInitData typeIndex segmentIndex)] [.trap] :=
        Step_read.arrayInitDataNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType), .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayInitData typeIndex segmentIndex)
        complete step rfl
      simp only [instructionReadResults]
      unfold arrayInitDataResults
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayInitDataOob1_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitDataOob1 is is') :
    (.read .arrayInitDataOob1 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitDataOob1 address arrayIndex dataIndex count typeIndex
      segmentIndex array harray hoob =>
      let reference : Ref := .addr (.arrayAddr address)
      let step : Step_readA z .arrayInitDataOob1
          [reference.toAdmin, constI32 arrayIndex, constI32 dataIndex,
            constI32 count, .plain (.arrayInitData typeIndex segmentIndex)]
          [.trap] :=
        Step_read.arrayInitDataOob1
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) harray hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref reference, .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayInitData typeIndex segmentIndex)
        complete step rfl
      simp only [instructionReadResults]
      unfold arrayInitDataResults
      apply List.mem_append_left
      apply List.mem_append_left
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfound
        have heq := Option.some.inj (hfound.symm.trans harray)
        subst foundArray
        split
        · apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;>
            simp [step, readResult, reference]
        · rename_i hin
          exact False.elim (hin hoob)

theorem arrayInitDataOob2_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitDataOob2 is is') :
    (.read .arrayInitDataOob2 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitDataOob2 address arrayIndex dataIndex count typeIndex
      segmentIndex definedType fieldType data size htype hexpand hsize hdata
      hoob =>
      cases hexpand with
      | mk hexpand =>
          let reference : Ref := .addr (.arrayAddr address)
          let step : Step_readA z .arrayInitDataOob2
              [reference.toAdmin, constI32 arrayIndex, constI32 dataIndex,
                constI32 count,
                .plain (.arrayInitData typeIndex segmentIndex)] [.trap] :=
            Step_read.arrayInitDataOob2
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htype (.mk hexpand) hsize hdata hoob
          apply readResult_mem_completeReadSuccessorsOf_of_instruction
            (values := [.ref reference, .num ⟨.i32, arrayIndex⟩,
              .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩])
            (instruction := .arrayInitData typeIndex segmentIndex)
            complete step rfl
          simp only [instructionReadResults]
          unfold arrayInitDataResults
          apply List.mem_append_left
          apply List.mem_append_right
          split
          · rename_i hnone
            rw [htype] at hnone
            contradiction
          · rename_i foundType hfound
            have heq := Option.some.inj (hfound.symm.trans htype)
            subst foundType
            split
            · rename_i foundField hfoundField
              have hfield := Option.some.inj (hfoundField.symm.trans hexpand)
              injection hfield with hfield
              subst foundField
              split
              · rename_i foundSize foundData hfoundSize hfoundData
                have hsizeEq := Option.some.inj (hfoundSize.symm.trans hsize)
                subst foundSize
                have hdataEq := Option.some.inj (hfoundData.symm.trans hdata)
                subst foundData
                split
                · apply List.mem_singleton.mpr
                  apply StepAResult.eq_of_event_next <;>
                    simp [step, readResult, reference]
                · rename_i hin
                  exact False.elim (hin hoob)
              · rename_i hbad
                exact False.elim (hbad size data hsize hdata)
            · rename_i hbad
              exact False.elim (hbad fieldType hexpand)

theorem arrayInitDataZero_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitDataZero is is') :
    (.read .arrayInitDataZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitDataZero address arrayIndex dataIndex count typeIndex
      segmentIndex array definedType fieldType data size harray harrayIn
      htype hexpand hsize hdata hdataIn hzero =>
      cases hexpand with
      | mk hexpand =>
          let reference : Ref := .addr (.arrayAddr address)
          let step : Step_readA z .arrayInitDataZero
              [reference.toAdmin, constI32 arrayIndex, constI32 dataIndex,
                constI32 count,
                .plain (.arrayInitData typeIndex segmentIndex)] [] :=
            Step_read.arrayInitDataZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) harray harrayIn htype (.mk hexpand)
              hsize hdata hdataIn hzero
          apply readResult_mem_completeReadSuccessorsOf_of_instruction
            (values := [.ref reference, .num ⟨.i32, arrayIndex⟩,
              .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩])
            (instruction := .arrayInitData typeIndex segmentIndex)
            complete step rfl
          simp only [instructionReadResults]
          unfold arrayInitDataResults
          apply List.mem_append_right
          split
          · rename_i foundArray foundType hfoundArray hfoundType
            have harrayEq := Option.some.inj (hfoundArray.symm.trans harray)
            subst foundArray
            have htypeEq := Option.some.inj (hfoundType.symm.trans htype)
            subst foundType
            split
            · rename_i foundField hfoundField
              have hfield := Option.some.inj (hfoundField.symm.trans hexpand)
              injection hfield with hfield
              subst foundField
              split
              · rename_i foundSize foundData hfoundSize hfoundData
                have hsizeEq := Option.some.inj (hfoundSize.symm.trans hsize)
                subst foundSize
                have hdataEq := Option.some.inj (hfoundData.symm.trans hdata)
                subst foundData
                rw [dif_pos harrayIn, dif_pos hdataIn, dif_pos hzero]
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next <;>
                  simp [step, readResult, reference]
              · rename_i hbad
                exact False.elim (hbad size data hsize hdata)
            · rename_i hbad
              exact False.elim (hbad fieldType hexpand)
          · rename_i hbad
            exact False.elim (hbad array definedType harray htype)

theorem arrayInitDataNum_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitDataNum is is') :
    (.read .arrayInitDataNum (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitDataNum address arrayIndex dataIndex count nextArray nextData
      nextCount typeIndex segmentIndex array definedType fieldType data size
      literal instruction harray harrayIn htype hexpand hsize hdata hdataIn
      hnonzero hbytes hinstruction hwf hnextArray hnextData hnextCount =>
      cases hexpand with
      | mk hexpand =>
          let reference : Ref := .addr (.arrayAddr address)
          have hread : Step_readA z .arrayInitDataNum
              [reference.toAdmin, constI32 arrayIndex, constI32 dataIndex,
                constI32 count,
                .plain (.arrayInitData typeIndex segmentIndex)]
              [reference.toAdmin, constI32 arrayIndex, .plain instruction,
                .plain (.arraySet typeIndex), reference.toAdmin,
                constI32 nextArray, constI32 nextData, constI32 nextCount,
                .plain (.arrayInitData typeIndex segmentIndex)] := by
            exact Step_read.arrayInitDataNum
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) harray harrayIn htype (.mk hexpand)
              hsize hdata hdataIn hnonzero hbytes hinstruction hwf
              hnextArray hnextData hnextCount
          let raw := readResult .arrayInitDataNum hread
          have hnextArrayOption : u32? (arrayIndex.val + 1) =
              some nextArray := by
            change addressLiteralOfNat? .i32 (arrayIndex.val + 1) =
              some nextArray
            rw [← hnextArray]
            exact addressLiteralOfNat?_val _ _
          have hnextDataOption : u32? (dataIndex.val + size / 8) =
              some nextData := by
            change addressLiteralOfNat? .i32 (dataIndex.val + size / 8) =
              some nextData
            rw [← hnextData]
            exact addressLiteralOfNat?_val _ _
          have hnextCountValue : nextCount.val = count.val - 1 := by omega
          have hnextCountOption : u32? (count.val - 1) =
              some nextCount := by
            change addressLiteralOfNat? .i32 (count.val - 1) =
              some nextCount
            rw [← hnextCountValue]
            exact addressLiteralOfNat?_val _ _
          have hraw : raw ∈ arrayInitDataResults z reference arrayIndex
              dataIndex count typeIndex segmentIndex := by
            unfold arrayInitDataResults
            apply List.mem_append_right
            split
            · rename_i foundArray foundType hfoundArray hfoundType
              have ha := Option.some.inj (hfoundArray.symm.trans harray)
              have ht := Option.some.inj (hfoundType.symm.trans htype)
              subst foundArray
              subst foundType
              split
              · rename_i foundField hfoundField
                have hf := Option.some.inj
                  (hfoundField.symm.trans hexpand)
                injection hf with hf
                subst foundField
                split
                · rename_i foundSize foundData hfoundSize hfoundData
                  have hs := Option.some.inj (hfoundSize.symm.trans hsize)
                  have hd := Option.some.inj (hfoundData.symm.trans hdata)
                  subst foundSize
                  subst foundData
                  rw [dif_pos harrayIn, dif_pos hdataIn,
                    dif_neg hnonzero]
                  let selected := slice data.bytes dataIndex.val (size / 8)
                  have hliteral :=
                    storageLiteralCandidate?_zbytes_complete literal hwf
                  have hbytesDef : releasedNumerics.zbytes_
                      (fieldStorage fieldType) literal = selected := by
                    simpa [selected] using hbytes
                  rw [hbytesDef] at hliteral
                  dsimp only [selected] at hliteral hbytesDef ⊢
                  split
                  · rename_i hnone
                    rw [hliteral] at hnone
                    contradiction
                  · rename_i foundLiteral hfoundLiteral
                    have hl := Option.some.inj
                      (hfoundLiteral.symm.trans hliteral)
                    subst foundLiteral
                    rw [dif_pos hbytesDef]
                    split
                    · rename_i hnone
                      rw [hinstruction] at hnone
                      contradiction
                    · rename_i foundInstruction hfoundInstruction
                      have hi := Option.some.inj
                        (hfoundInstruction.symm.trans hinstruction)
                      subst foundInstruction
                      split
                      · rename_i foundNextArray foundNextData foundNextCount
                          hfoundNextArray hfoundNextData hfoundNextCount
                        have hna := Option.some.inj
                          (hfoundNextArray.symm.trans hnextArrayOption)
                        have hnd := Option.some.inj
                          (hfoundNextData.symm.trans hnextDataOption)
                        have hnc := Option.some.inj
                          (hfoundNextCount.symm.trans hnextCountOption)
                        subst foundNextArray
                        subst foundNextData
                        subst foundNextCount
                        apply List.mem_singleton.mpr
                        apply StepAResult.eq_of_event_next <;> rfl
                      · rename_i hmissing
                        exact False.elim
                          (hmissing nextArray nextData nextCount
                            hnextArrayOption hnextDataOption hnextCountOption)
                · rename_i hbad
                  exact False.elim (hbad size data hsize hdata)
              · rename_i hbad
                exact False.elim (hbad fieldType hexpand)
            · rename_i hbad
              exact False.elim
                (hbad array definedType harray htype)
          have hcomplete :=
            readResult_mem_completeReadSuccessorsOf_of_instruction
              (values := [.ref reference, .num ⟨.i32, arrayIndex⟩,
                .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩])
              (instruction := .arrayInitData typeIndex segmentIndex)
              complete hread rfl hraw
          simpa [reference, raw, StepAResult.toPair, readResult,
            sourcePlains, Val.toAdmin, constI32] using hcomplete

end WasmGemmGnaf.Wasm.Core.Exec
