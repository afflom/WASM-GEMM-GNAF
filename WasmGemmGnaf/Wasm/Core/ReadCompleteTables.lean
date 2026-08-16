import WasmGemmGnaf.Wasm.Core.ReadComplete

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem mem_instructionReadResults_tableCopy {z : State}
    (destination source count : AddressLiteral)
    (destinationTable sourceTable : TableIdx)
    {result : StepAResult
      (z, vals [destination.toVal, source.toVal, count.toVal] ++
        [.plain (.tableCopy destinationTable sourceTable)])}
    (hresult : result ∈ tableCopyResults z destination source count
      destinationTable sourceTable) :
    result ∈ instructionReadResults z
      [destination.toVal, source.toVal, count.toVal]
      (.tableCopy destinationTable sourceTable) := by
  simp only [instructionReadResults]
  split
  · rename_i foundDestination foundSource foundCount
      hfoundDestination hfoundSource hfoundCount
    have hd := Option.some.inj
      (hfoundDestination.symm.trans (addressLiteral?_toVal destination))
    have hs := Option.some.inj
      (hfoundSource.symm.trans (addressLiteral?_toVal source))
    have hc := Option.some.inj
      (hfoundCount.symm.trans (addressLiteral?_toVal count))
    subst foundDestination
    subst foundSource
    subst foundCount
    apply List.mem_map.mpr
    refine ⟨result, hresult, ?_⟩
    apply StepAResult.eq_of_event_next <;> rfl
  · rename_i hmissing
    exact False.elim
      (hmissing destination source count
        (addressLiteral?_toVal destination)
        (addressLiteral?_toVal source)
        (addressLiteral?_toVal count))

theorem mem_instructionReadResults_tableInit {z : State}
    (destination : AddressLiteral) (source count : U32)
    (tableIndex : TableIdx) (elemIndex : ElemIdx)
    {result : StepAResult
      (z, vals [destination.toVal, .num ⟨.i32, source⟩,
          .num ⟨.i32, count⟩] ++
        [.plain (.tableInit tableIndex elemIndex)])}
    (hresult : result ∈ tableInitResults z destination source count
      tableIndex elemIndex) :
    result ∈ instructionReadResults z
      [destination.toVal, .num ⟨.i32, source⟩, .num ⟨.i32, count⟩]
      (.tableInit tableIndex elemIndex) := by
  simp only [instructionReadResults]
  split
  · rename_i hnone
    rw [addressLiteral?_toVal destination] at hnone
    contradiction
  · rename_i foundDestination hfoundDestination
    have hd := Option.some.inj
      (hfoundDestination.symm.trans (addressLiteral?_toVal destination))
    subst foundDestination
    apply List.mem_map.mpr
    refine ⟨result, hresult, ?_⟩
    apply StepAResult.eq_of_event_next <;> rfl

theorem tableSize_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableSize is is') :
    (.read .tableSize (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableSize tableIndex table addressType size htable hlength htype =>
      let raw : StepAResult (z, [.plain (.tableSize tableIndex)]) :=
        readResult .tableSize
          (Step_read.tableSize
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hlength htype)
      have hraw : raw ∈ tableSizeResults z tableIndex := by
        unfold tableSizeResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i foundTable hfoundTable
          have heq := Option.some.inj (hfoundTable.symm.trans htable)
          subst foundTable
          subst addressType
          have hsize : addressLiteralOfNat? table.type.addr table.refs.length =
              some size := by
            rw [hlength]
            exact addressLiteralOfNat?_val _ _
          split
          · rename_i hnone
            rw [hsize] at hnone
            contradiction
          · rename_i foundSize hfoundSize
            have heq := Option.some.inj (hfoundSize.symm.trans hsize)
            subst foundSize
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .tableSize tableIndex) complete
        (Step_read.tableSize (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) htable hlength htype) rfl
      simp only [instructionReadResults]
      split
      · apply List.mem_map.mpr
        refine ⟨raw, hraw, ?_⟩
        apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

theorem tableFillOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableFillOob is is') :
    (.read .tableFillOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableFillOob addressType index count value tableIndex table htable hoob =>
      have hread : Step_readA z .tableFillOob
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.tableFill tableIndex)]) [.trap] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.tableFillOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hoob
      let raw : StepAResult
          (z, vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.tableFill tableIndex)]) :=
        readResult .tableFillOob hread
      have hraw : raw ∈ tableFillResults z addressType index count value
          tableIndex := by
        unfold tableFillResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i foundTable hfoundTable
          have heq := Option.some.inj (hfoundTable.symm.trans htable)
          subst foundTable
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · simp_all
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩])
          (instruction := .tableFill tableIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem tableFillZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableFillZero is is') :
    (.read .tableFillZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableFillZero addressType index count value tableIndex table htable
      hbound hzero =>
      have hread : Step_readA z .tableFillZero
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.tableFill tableIndex)]) [] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.tableFillZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hbound hzero
      let raw := readResult .tableFillZero hread
      have hraw : raw ∈ tableFillResults z addressType index count value
          tableIndex := by
        unfold tableFillResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i foundTable hfoundTable
          have heq := Option.some.inj (hfoundTable.symm.trans htable)
          subst foundTable
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩])
          (instruction := .tableFill tableIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem tableFillSucc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableFillSucc is is') :
    (.read .tableFillSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableFillSucc addressType index count nextIndex nextCount value tableIndex
      table htable hbound hnonzero hnextIndex hnextCount =>
      have hread : Step_readA z .tableFillSucc
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.tableFill tableIndex)])
          [constAddr addressType index, value.toAdmin,
            .plain (.tableSet tableIndex),
            constAddr addressType nextIndex, value.toAdmin,
            constAddr addressType nextCount,
            .plain (.tableFill tableIndex)] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.tableFillSucc
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hbound hnonzero hnextIndex
              hnextCount
      let raw := readResult .tableFillSucc hread
      have hnextIndexOption : addressLiteralOfNat? addressType
          (index.val + 1) = some nextIndex := by
        rw [← hnextIndex]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : nextCount.val = count.val - 1 := by omega
      have hnextCountOption : addressLiteralOfNat? addressType
          (count.val - 1) = some nextCount := by
        rw [← hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      have hraw : raw ∈ tableFillResults z addressType index count value
          tableIndex := by
        unfold tableFillResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i foundTable hfoundTable
          have heq := Option.some.inj (hfoundTable.symm.trans htable)
          subst foundTable
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · split
            · rename_i foundNextIndex foundNextCount hfoundNextIndex
                hfoundNextCount
              have hi := Option.some.inj
                (hfoundNextIndex.symm.trans hnextIndexOption)
              have hn := Option.some.inj
                (hfoundNextCount.symm.trans hnextCountOption)
              subst foundNextIndex
              subst foundNextCount
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing nextIndex nextCount hnextIndexOption
                  hnextCountOption)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩])
          (instruction := .tableFill tableIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem tableCopyOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableCopyOob is is') :
    (.read .tableCopyOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableCopyOob destinationType sourceType countType destinationValue
      sourceValue countValue destinationTable sourceTable destinationInstance
      sourceInstance hdestination hsource hoob =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .tableCopyOob
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.tableCopy destinationTable sourceTable)]) [.trap] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.tableCopyOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hoob
      let raw := readResult .tableCopyOob hread
      have hraw : raw ∈ tableCopyResults z destination source count
          destinationTable sourceTable := by
        unfold tableCopyResults
        split
        · rename_i foundDestination foundSource hfoundDestination
            hfoundSource
          have hd := Option.some.inj
            (hfoundDestination.symm.trans hdestination)
          have hs := Option.some.inj (hfoundSource.symm.trans hsource)
          subst foundDestination
          subst foundSource
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · simp_all [destination, source, count]
        · rename_i hmissing
          exact False.elim
            (hmissing destinationInstance sourceInstance hdestination hsource)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, source.toVal, count.toVal])
          (instruction := .tableCopy destinationTable sourceTable) complete
          hread rfl
          (by
            simp only [instructionReadResults]
            split
            · rename_i foundDestination foundSource foundCount
                hfoundDestination hfoundSource hfoundCount
              have hd := Option.some.inj
                (hfoundDestination.symm.trans
                  (addressLiteral?_toVal destination))
              have hs := Option.some.inj
                (hfoundSource.symm.trans (addressLiteral?_toVal source))
              have hc := Option.some.inj
                (hfoundCount.symm.trans (addressLiteral?_toVal count))
              subst foundDestination
              subst foundSource
              subst foundCount
              apply List.mem_map.mpr
              refine ⟨raw, hraw, ?_⟩
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing destination source count
                  (addressLiteral?_toVal destination)
                  (addressLiteral?_toVal source)
                  (addressLiteral?_toVal count)))
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem tableCopyZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableCopyZero is is') :
    (.read .tableCopyZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableCopyZero destinationType sourceType countType destinationValue
      sourceValue countValue destinationTable sourceTable destinationInstance
      sourceInstance hdestination hsource hbound hzero =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .tableCopyZero
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.tableCopy destinationTable sourceTable)]) [] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.tableCopyZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hzero
      let raw := readResult .tableCopyZero hread
      have hraw : raw ∈ tableCopyResults z destination source count
          destinationTable sourceTable := by
        unfold tableCopyResults
        split
        · rename_i foundDestination foundSource hfoundDestination
            hfoundSource
          have hd := Option.some.inj
            (hfoundDestination.symm.trans hdestination)
          have hs := Option.some.inj (hfoundSource.symm.trans hsource)
          subst foundDestination
          subst foundSource
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
        · rename_i hmissing
          exact False.elim
            (hmissing destinationInstance sourceInstance hdestination hsource)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, source.toVal, count.toVal])
          (instruction := .tableCopy destinationTable sourceTable) complete
          hread rfl
          (mem_instructionReadResults_tableCopy destination source count
            destinationTable sourceTable hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem tableCopyLe_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableCopyLe is is') :
    (.read .tableCopyLe (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableCopyLe destinationType sourceType countType destinationValue
      nextDestination sourceValue nextSource countValue nextCount
      destinationTable sourceTable destinationInstance sourceInstance
      hdestination hsource hbound hnonzero horder hnextDestination
      hnextSource hnextCount =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .tableCopyLe
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.tableCopy destinationTable sourceTable)])
          [destination.toAdmin, source.toAdmin,
            .plain (.tableGet sourceTable), .plain (.tableSet destinationTable),
            constAddr destinationType nextDestination,
            constAddr sourceType nextSource, constAddr countType nextCount,
            .plain (.tableCopy destinationTable sourceTable)] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.tableCopyLe
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hnonzero
              horder hnextDestination hnextSource hnextCount
      let raw := readResult .tableCopyLe hread
      have hnextDestinationOption : addressLiteralOfNat? destinationType
          (destinationValue.val + 1) = some nextDestination := by
        rw [← hnextDestination]
        exact addressLiteralOfNat?_val _ _
      have hnextSourceOption : addressLiteralOfNat? sourceType
          (sourceValue.val + 1) = some nextSource := by
        rw [← hnextSource]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : nextCount.val = countValue.val - 1 := by omega
      have hnextCountOption : addressLiteralOfNat? countType
          (countValue.val - 1) = some nextCount := by
        rw [← hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      have hraw : raw ∈ tableCopyResults z destination source count
          destinationTable sourceTable := by
        unfold tableCopyResults
        split
        · rename_i foundDestination foundSource hfoundDestination
            hfoundSource
          have hd := Option.some.inj
            (hfoundDestination.symm.trans hdestination)
          have hs := Option.some.inj (hfoundSource.symm.trans hsource)
          subst foundDestination
          subst foundSource
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · split
            · rename_i foundNextDestination foundNextSource foundNextCount
                hfoundNextDestination hfoundNextSource hfoundNextCount
              have hd' := Option.some.inj
                (hfoundNextDestination.symm.trans hnextDestinationOption)
              have hs' := Option.some.inj
                (hfoundNextSource.symm.trans hnextSourceOption)
              have hc' := Option.some.inj
                (hfoundNextCount.symm.trans hnextCountOption)
              subst foundNextDestination
              subst foundNextSource
              subst foundNextCount
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing nextDestination nextSource nextCount
                  hnextDestinationOption hnextSourceOption hnextCountOption)
        · rename_i hmissing
          exact False.elim
            (hmissing destinationInstance sourceInstance hdestination hsource)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, source.toVal, count.toVal])
          (instruction := .tableCopy destinationTable sourceTable) complete
          hread rfl
          (mem_instructionReadResults_tableCopy destination source count
            destinationTable sourceTable hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem tableCopyGt_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableCopyGt is is') :
    (.read .tableCopyGt (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableCopyGt destinationType sourceType countType destinationValue
      lastDestination sourceValue lastSource countValue nextCount
      destinationTable sourceTable destinationInstance sourceInstance
      hdestination hsource hbound hnonzero horder hlastDestination
      hlastSource hnextCount =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .tableCopyGt
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.tableCopy destinationTable sourceTable)])
          [constAddr destinationType lastDestination,
            constAddr sourceType lastSource, .plain (.tableGet sourceTable),
            .plain (.tableSet destinationTable), destination.toAdmin,
            source.toAdmin, constAddr countType nextCount,
            .plain (.tableCopy destinationTable sourceTable)] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.tableCopyGt
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hnonzero
              horder hlastDestination hlastSource hnextCount
      let raw := readResult .tableCopyGt hread
      have hlastDestinationValue : lastDestination.val =
          destinationValue.val + countValue.val - 1 := by omega
      have hlastDestinationOption : addressLiteralOfNat? destinationType
          (destinationValue.val + countValue.val - 1) =
            some lastDestination := by
        rw [← hlastDestinationValue]
        exact addressLiteralOfNat?_val _ _
      have hlastSourceValue : lastSource.val =
          sourceValue.val + countValue.val - 1 := by omega
      have hlastSourceOption : addressLiteralOfNat? sourceType
          (sourceValue.val + countValue.val - 1) = some lastSource := by
        rw [← hlastSourceValue]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : nextCount.val = countValue.val - 1 := by omega
      have hnextCountOption : addressLiteralOfNat? countType
          (countValue.val - 1) = some nextCount := by
        rw [← hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      have hraw : raw ∈ tableCopyResults z destination source count
          destinationTable sourceTable := by
        unfold tableCopyResults
        split
        · rename_i foundDestination foundSource hfoundDestination
            hfoundSource
          have hd := Option.some.inj
            (hfoundDestination.symm.trans hdestination)
          have hs := Option.some.inj (hfoundSource.symm.trans hsource)
          subst foundDestination
          subst foundSource
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · split
            · rename_i foundLastDestination foundLastSource foundNextCount
                hfoundLastDestination hfoundLastSource hfoundNextCount
              have hd' := Option.some.inj
                (hfoundLastDestination.symm.trans hlastDestinationOption)
              have hs' := Option.some.inj
                (hfoundLastSource.symm.trans hlastSourceOption)
              have hc' := Option.some.inj
                (hfoundNextCount.symm.trans hnextCountOption)
              subst foundLastDestination
              subst foundLastSource
              subst foundNextCount
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing lastDestination lastSource nextCount
                  hlastDestinationOption hlastSourceOption hnextCountOption)
        · rename_i hmissing
          exact False.elim
            (hmissing destinationInstance sourceInstance hdestination hsource)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, source.toVal, count.toVal])
          (instruction := .tableCopy destinationTable sourceTable) complete
          hread rfl
          (mem_instructionReadResults_tableCopy destination source count
            destinationTable sourceTable hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem tableInitOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableInitOob is is') :
    (.read .tableInitOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableInitOob addressType destinationValue sourceValue countValue tableIndex
      elemIndex table elem htable helem hoob =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .tableInitOob
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.tableInit tableIndex elemIndex)]) [.trap] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.tableInitOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable helem hoob
      let raw := readResult .tableInitOob hread
      have hraw : raw ∈ tableInitResults z destination sourceValue countValue
          tableIndex elemIndex := by
        unfold tableInitResults
        split
        · rename_i foundTable foundElem hfoundTable hfoundElem
          have ht := Option.some.inj (hfoundTable.symm.trans htable)
          have he := Option.some.inj (hfoundElem.symm.trans helem)
          subst foundTable
          subst foundElem
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · simp_all [destination]
        · rename_i hmissing
          exact False.elim (hmissing table elem htable helem)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .tableInit tableIndex elemIndex) complete hread rfl
          (mem_instructionReadResults_tableInit destination sourceValue
            countValue tableIndex elemIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

theorem tableInitZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableInitZero is is') :
    (.read .tableInitZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableInitZero addressType destinationValue sourceValue countValue
      tableIndex elemIndex table elem htable helem hbound hzero =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .tableInitZero
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.tableInit tableIndex elemIndex)]) [] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.tableInitZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable helem hbound hzero
      let raw := readResult .tableInitZero hread
      have hraw : raw ∈ tableInitResults z destination sourceValue countValue
          tableIndex elemIndex := by
        unfold tableInitResults
        split
        · rename_i foundTable foundElem hfoundTable hfoundElem
          have ht := Option.some.inj (hfoundTable.symm.trans htable)
          have he := Option.some.inj (hfoundElem.symm.trans helem)
          subst foundTable
          subst foundElem
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
        · rename_i hmissing
          exact False.elim (hmissing table elem htable helem)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .tableInit tableIndex elemIndex) complete hread rfl
          (mem_instructionReadResults_tableInit destination sourceValue
            countValue tableIndex elemIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

theorem tableInitSucc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableInitSucc is is') :
    (.read .tableInitSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableInitSucc addressType destinationValue nextDestination sourceValue
      nextSource countValue nextCount tableIndex elemIndex table elem reference
      htable helem hbound hnonzero href hnextDestination hnextSource
      hnextCount =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .tableInitSucc
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.tableInit tableIndex elemIndex)])
          [destination.toAdmin, reference.toAdmin,
            .plain (.tableSet tableIndex),
            constAddr addressType nextDestination, constI32 nextSource,
            constI32 nextCount, .plain (.tableInit tableIndex elemIndex)] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.tableInitSucc
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable helem hbound hnonzero href
              hnextDestination hnextSource hnextCount
      let raw := readResult .tableInitSucc hread
      have hnextDestinationOption : addressLiteralOfNat? addressType
          (destinationValue.val + 1) = some nextDestination := by
        rw [← hnextDestination]
        exact addressLiteralOfNat?_val _ _
      have hnextSourceOption : u32? (sourceValue.val + 1) =
          some nextSource := by
        change addressLiteralOfNat? .i32 (sourceValue.val + 1) =
          some nextSource
        rw [← hnextSource]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : nextCount.val = countValue.val - 1 := by omega
      have hnextCountOption : u32? (countValue.val - 1) = some nextCount := by
        change addressLiteralOfNat? .i32 (countValue.val - 1) = some nextCount
        rw [← hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      have hraw : raw ∈ tableInitResults z destination sourceValue countValue
          tableIndex elemIndex := by
        unfold tableInitResults
        split
        · rename_i foundTable foundElem hfoundTable hfoundElem
          have ht := Option.some.inj (hfoundTable.symm.trans htable)
          have he := Option.some.inj (hfoundElem.symm.trans helem)
          subst foundTable
          subst foundElem
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · split
            · rename_i foundReference foundNextDestination foundNextSource
                foundNextCount hfoundReference hfoundNextDestination
                hfoundNextSource hfoundNextCount
              have hr := Option.some.inj (hfoundReference.symm.trans href)
              have hd := Option.some.inj
                (hfoundNextDestination.symm.trans hnextDestinationOption)
              have hs := Option.some.inj
                (hfoundNextSource.symm.trans hnextSourceOption)
              have hc := Option.some.inj
                (hfoundNextCount.symm.trans hnextCountOption)
              subst foundReference
              subst foundNextDestination
              subst foundNextSource
              subst foundNextCount
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing reference nextDestination nextSource nextCount href
                  hnextDestinationOption hnextSourceOption hnextCountOption)
        · rename_i hmissing
          exact False.elim (hmissing table elem htable helem)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .tableInit tableIndex elemIndex) complete hread rfl
          (mem_instructionReadResults_tableInit destination sourceValue
            countValue tableIndex elemIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

end WasmGemmGnaf.Wasm.Core.Exec
