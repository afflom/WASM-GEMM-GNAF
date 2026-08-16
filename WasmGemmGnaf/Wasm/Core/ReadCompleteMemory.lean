import WasmGemmGnaf.Wasm.Core.ReadComplete

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem mem_instructionReadResults_memoryCopy {z : State}
    (destination source count : AddressLiteral)
    (destinationMemory sourceMemory : MemIdx)
    {result : StepAResult
      (z, vals [destination.toVal, source.toVal, count.toVal] ++
        [.plain (.memoryCopy destinationMemory sourceMemory)])}
    (hresult : result ∈ memoryCopyResults z destination source count
      destinationMemory sourceMemory) :
    result ∈ instructionReadResults z
      [destination.toVal, source.toVal, count.toVal]
      (.memoryCopy destinationMemory sourceMemory) := by
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

theorem mem_instructionReadResults_memoryInit {z : State}
    (destination : AddressLiteral) (source count : U32)
    (memoryIndex : MemIdx) (dataIndex : DataIdx)
    {result : StepAResult
      (z, vals [destination.toVal, .num ⟨.i32, source⟩,
          .num ⟨.i32, count⟩] ++
        [.plain (.memoryInit memoryIndex dataIndex)])}
    (hresult : result ∈ memoryInitResults z destination source count
      memoryIndex dataIndex) :
    result ∈ instructionReadResults z
      [destination.toVal, .num ⟨.i32, source⟩, .num ⟨.i32, count⟩]
      (.memoryInit memoryIndex dataIndex) := by
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

theorem memorySize_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memorySize is is') :
    (.read .memorySize (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memorySize memoryIndex memory addressType size hmemory hlength htype =>
      subst addressType
      let raw : StepAResult (z, [.plain (.memorySize memoryIndex)]) :=
        readResult .memorySize
          (Step_read.memorySize
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hlength rfl)
      have hraw : raw ∈ memorySizeResults z memoryIndex := by
        unfold memorySizeResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have heq := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          have hpagesValue : memory.bytes.length / (64 * Ki) = size.val := by
            rw [← hlength]
            exact Nat.mul_div_cancel size.val (by decide)
          have hmultiple : (memory.bytes.length / (64 * Ki)) * (64 * Ki) =
              memory.bytes.length := by
            rw [hpagesValue]
            exact hlength
          have hsize : addressLiteralOfNat? memory.type.addr
                (memory.bytes.length / (64 * Ki)) = some size := by
            rw [hpagesValue]
            exact addressLiteralOfNat?_val _ _
          dsimp only
          split
          · split
            · rename_i hnone
              rw [hsize] at hnone
              contradiction
            · rename_i foundSize hfoundSize
              have heq := Option.some.inj (hfoundSize.symm.trans hsize)
              subst foundSize
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
          · rename_i hnotMultiple
            exact False.elim (hnotMultiple hmultiple)
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .memorySize memoryIndex) complete
        (Step_read.memorySize (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hlength rfl) rfl
      simp only [instructionReadResults]
      split
      · apply List.mem_map.mpr
        refine ⟨raw, hraw, ?_⟩
        apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

theorem memoryFillOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryFillOob is is') :
    (.read .memoryFillOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryFillOob addressType index count value memoryIndex memory hmemory hoob =>
      have hread : Step_readA z .memoryFillOob
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.memoryFill memoryIndex)]) [.trap] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.memoryFillOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hoob
      let raw : StepAResult
          (z, vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.memoryFill memoryIndex)]) :=
        readResult .memoryFillOob hread
      have hraw : raw ∈ memoryFillResults z addressType index count value
          memoryIndex := by
        unfold memoryFillResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have heq := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
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
          (instruction := .memoryFill memoryIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem memoryFillZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryFillZero is is') :
    (.read .memoryFillZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryFillZero addressType index count value memoryIndex memory hmemory
      hbound hzero =>
      have hread : Step_readA z .memoryFillZero
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.memoryFill memoryIndex)]) [] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.memoryFillZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hbound hzero
      let raw := readResult .memoryFillZero hread
      have hraw : raw ∈ memoryFillResults z addressType index count value
          memoryIndex := by
        unfold memoryFillResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have heq := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
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
          (instruction := .memoryFill memoryIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem memoryFillSucc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryFillSucc is is') :
    (.read .memoryFillSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryFillSucc addressType index count nextIndex nextCount value memoryIndex
      memory hmemory hbound hnonzero hnextIndex hnextCount =>
      have hread : Step_readA z .memoryFillSucc
          (vals [.num ⟨addrNumType addressType,
              addrLitToNum addressType index⟩, value,
            .num ⟨addrNumType addressType,
              addrLitToNum addressType count⟩] ++
            [.plain (.memoryFill memoryIndex)])
          [constAddr addressType index, value.toAdmin,
            .plain (.store .i32 (some ⟨.s8⟩) memoryIndex MemArg.zero),
            constAddr addressType nextIndex, value.toAdmin,
            constAddr addressType nextCount,
            .plain (.memoryFill memoryIndex)] := by
        simpa [vals, constAddr, Val.toAdmin] using
          Step_read.memoryFillSucc
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hbound hnonzero hnextIndex
              hnextCount
      let raw := readResult .memoryFillSucc hread
      have hnextIndexOption : addressLiteralOfNat? addressType
          (index.val + 1) = some nextIndex := by
        rw [← hnextIndex]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : nextCount.val = count.val - 1 := by omega
      have hnextCountOption : addressLiteralOfNat? addressType
          (count.val - 1) = some nextCount := by
        rw [← hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      have hraw : raw ∈ memoryFillResults z addressType index count value
          memoryIndex := by
        unfold memoryFillResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have heq := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
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
          (instruction := .memoryFill memoryIndex) complete hread rfl
          (by
            cases addressType <;>
              simpa [instructionReadResults] using hraw)
      simpa [raw, StepAResult.toPair, readResult, vals, constAddr,
        Val.toAdmin] using hcomplete

theorem memoryCopyOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryCopyOob is is') :
    (.read .memoryCopyOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryCopyOob destinationType sourceType countType destinationValue
      sourceValue countValue destinationMemory sourceMemory destinationInstance
      sourceInstance hdestination hsource hoob =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .memoryCopyOob
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.memoryCopy destinationMemory sourceMemory)]) [.trap] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.memoryCopyOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hoob
      let raw := readResult .memoryCopyOob hread
      have hraw : raw ∈ memoryCopyResults z destination source count
          destinationMemory sourceMemory := by
        unfold memoryCopyResults
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
          (instruction := .memoryCopy destinationMemory sourceMemory) complete
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

theorem memoryCopyZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryCopyZero is is') :
    (.read .memoryCopyZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryCopyZero destinationType sourceType countType destinationValue
      sourceValue countValue destinationMemory sourceMemory destinationInstance
      sourceInstance hdestination hsource hbound hzero =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .memoryCopyZero
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.memoryCopy destinationMemory sourceMemory)]) [] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.memoryCopyZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hzero
      let raw := readResult .memoryCopyZero hread
      have hraw : raw ∈ memoryCopyResults z destination source count
          destinationMemory sourceMemory := by
        unfold memoryCopyResults
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
          (instruction := .memoryCopy destinationMemory sourceMemory) complete
          hread rfl
          (mem_instructionReadResults_memoryCopy destination source count
            destinationMemory sourceMemory hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem memoryCopyLe_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryCopyLe is is') :
    (.read .memoryCopyLe (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryCopyLe destinationType sourceType countType destinationValue
      nextDestination sourceValue nextSource countValue nextCount
      destinationMemory sourceMemory destinationInstance sourceInstance
      hdestination hsource hbound hnonzero horder hnextDestination
      hnextSource hnextCount =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .memoryCopyLe
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.memoryCopy destinationMemory sourceMemory)])
          [destination.toAdmin, source.toAdmin,
            .plain (.load .i32 (some ⟨.s8, .u⟩) sourceMemory MemArg.zero),
            .plain (.store .i32 (some ⟨.s8⟩) destinationMemory MemArg.zero),
            constAddr destinationType nextDestination,
            constAddr sourceType nextSource, constAddr countType nextCount,
            .plain (.memoryCopy destinationMemory sourceMemory)] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.memoryCopyLe
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hnonzero
              horder hnextDestination hnextSource hnextCount
      let raw := readResult .memoryCopyLe hread
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
      have hraw : raw ∈ memoryCopyResults z destination source count
          destinationMemory sourceMemory := by
        unfold memoryCopyResults
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
          (instruction := .memoryCopy destinationMemory sourceMemory) complete
          hread rfl
          (mem_instructionReadResults_memoryCopy destination source count
            destinationMemory sourceMemory hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem memoryCopyGt_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryCopyGt is is') :
    (.read .memoryCopyGt (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryCopyGt destinationType sourceType countType destinationValue
      lastDestination sourceValue lastSource countValue nextCount
      destinationMemory sourceMemory destinationInstance sourceInstance
      hdestination hsource hbound hnonzero horder hlastDestination
      hlastSource hnextCount =>
      let destination : AddressLiteral :=
        ⟨destinationType, destinationValue⟩
      let source : AddressLiteral := ⟨sourceType, sourceValue⟩
      let count : AddressLiteral := ⟨countType, countValue⟩
      have hread : Step_readA z .memoryCopyGt
          (vals [destination.toVal, source.toVal, count.toVal] ++
            [.plain (.memoryCopy destinationMemory sourceMemory)])
          [constAddr destinationType lastDestination,
            constAddr sourceType lastSource,
            .plain (.load .i32 (some ⟨.s8, .u⟩) sourceMemory MemArg.zero),
            .plain (.store .i32 (some ⟨.s8⟩) destinationMemory MemArg.zero),
            destination.toAdmin,
            source.toAdmin, constAddr countType nextCount,
            .plain (.memoryCopy destinationMemory sourceMemory)] := by
        simpa [destination, source, count, vals, AddressLiteral.toAdmin,
          Val.toAdmin] using
          Step_read.memoryCopyGt
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hdestination hsource hbound hnonzero
              horder hlastDestination hlastSource hnextCount
      let raw := readResult .memoryCopyGt hread
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
      have hraw : raw ∈ memoryCopyResults z destination source count
          destinationMemory sourceMemory := by
        unfold memoryCopyResults
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
          (instruction := .memoryCopy destinationMemory sourceMemory) complete
          hread rfl
          (mem_instructionReadResults_memoryCopy destination source count
            destinationMemory sourceMemory hraw)
      simpa [destination, source, count, raw, StepAResult.toPair,
        readResult, AddressLiteral.toAdmin, Val.toAdmin] using hcomplete

theorem memoryInitOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryInitOob is is') :
    (.read .memoryInitOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryInitOob addressType destinationValue sourceValue countValue memoryIndex
      dataIndex memory data hmemory hdata hoob =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .memoryInitOob
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.memoryInit memoryIndex dataIndex)]) [.trap] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.memoryInitOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hdata hoob
      let raw := readResult .memoryInitOob hread
      have hraw : raw ∈ memoryInitResults z destination sourceValue countValue
          memoryIndex dataIndex := by
        unfold memoryInitResults
        split
        · rename_i foundMemory foundElem hfoundMemory hfoundElem
          have ht := Option.some.inj (hfoundMemory.symm.trans hmemory)
          have he := Option.some.inj (hfoundElem.symm.trans hdata)
          subst foundMemory
          subst foundElem
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
          · simp_all [destination]
        · rename_i hmissing
          exact False.elim (hmissing memory data hmemory hdata)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .memoryInit memoryIndex dataIndex) complete hread rfl
          (mem_instructionReadResults_memoryInit destination sourceValue
            countValue memoryIndex dataIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

theorem memoryInitZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryInitZero is is') :
    (.read .memoryInitZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryInitZero addressType destinationValue sourceValue countValue
      memoryIndex dataIndex memory data hmemory hdata hbound hzero =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .memoryInitZero
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.memoryInit memoryIndex dataIndex)]) [] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.memoryInitZero
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hdata hbound hzero
      let raw := readResult .memoryInitZero hread
      have hraw : raw ∈ memoryInitResults z destination sourceValue countValue
          memoryIndex dataIndex := by
        unfold memoryInitResults
        split
        · rename_i foundMemory foundElem hfoundMemory hfoundElem
          have ht := Option.some.inj (hfoundMemory.symm.trans hmemory)
          have he := Option.some.inj (hfoundElem.symm.trans hdata)
          subst foundMemory
          subst foundElem
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
        · rename_i hmissing
          exact False.elim (hmissing memory data hmemory hdata)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .memoryInit memoryIndex dataIndex) complete hread rfl
          (mem_instructionReadResults_memoryInit destination sourceValue
            countValue memoryIndex dataIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

theorem memoryInitSucc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .memoryInitSucc is is') :
    (.read .memoryInitSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @memoryInitSucc addressType destinationValue nextDestination sourceValue
      nextSource countValue nextCount memoryIndex dataIndex memory data byte
      byteValue hmemory hdata hbound hnonzero hbyte hbyteValue hnextDestination
      hnextSource hnextCount =>
      let destination : AddressLiteral := ⟨addressType, destinationValue⟩
      have hread : Step_readA z .memoryInitSucc
          (vals [destination.toVal, .num ⟨.i32, sourceValue⟩,
              .num ⟨.i32, countValue⟩] ++
            [.plain (.memoryInit memoryIndex dataIndex)])
          [destination.toAdmin, constI32 byteValue,
            .plain (.store .i32 (some ⟨.s8⟩) memoryIndex MemArg.zero),
            constAddr addressType nextDestination, constI32 nextSource,
            constI32 nextCount, .plain (.memoryInit memoryIndex dataIndex)] := by
        simpa [destination, vals, AddressLiteral.toAdmin, Val.toAdmin,
          constI32] using
          Step_read.memoryInitSucc
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hmemory hdata hbound hnonzero hbyte
              hbyteValue hnextDestination hnextSource hnextCount
      let raw := readResult .memoryInitSucc hread
      have hbyteValueOption :
          u32? (data.bytes[sourceValue.val]?.getD default).val =
            some byteValue := by
        have hdefault : data.bytes[sourceValue.val]?.getD default = byte := by
          simp [hbyte]
        change addressLiteralOfNat? .i32
            (data.bytes[sourceValue.val]?.getD default).val = some byteValue
        rw [hdefault, ← hbyteValue]
        exact addressLiteralOfNat?_val _ _
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
      have hraw : raw ∈ memoryInitResults z destination sourceValue countValue
          memoryIndex dataIndex := by
        unfold memoryInitResults
        split
        · rename_i foundMemory foundData hfoundMemory hfoundData
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          have hd := Option.some.inj (hfoundData.symm.trans hdata)
          subst foundMemory
          subst foundData
          split
          · rename_i hbad
            exact False.elim (hbound hbad)
          · split
            · rename_i foundByte foundByteValue foundNextDestination
                foundNextSource foundNextCount hfoundByte hfoundByteValue
                hfoundNextDestination hfoundNextSource hfoundNextCount
              have hb := Option.some.inj (hfoundByte.symm.trans hbyte)
              have hbv := Option.some.inj
                (hfoundByteValue.symm.trans hbyteValueOption)
              have hdi := Option.some.inj
                (hfoundNextDestination.symm.trans hnextDestinationOption)
              have hs := Option.some.inj
                (hfoundNextSource.symm.trans hnextSourceOption)
              have hc := Option.some.inj
                (hfoundNextCount.symm.trans hnextCountOption)
              subst foundByte
              subst foundByteValue
              subst foundNextDestination
              subst foundNextSource
              subst foundNextCount
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
            · rename_i hmissing
              exact False.elim
                (hmissing byte byteValue nextDestination nextSource nextCount
                  hbyte hbyteValueOption hnextDestinationOption
                  hnextSourceOption hnextCountOption)
        · rename_i hmissing
          exact False.elim (hmissing memory data hmemory hdata)
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [destination.toVal, .num ⟨.i32, sourceValue⟩,
            .num ⟨.i32, countValue⟩])
          (instruction := .memoryInit memoryIndex dataIndex) complete hread rfl
          (mem_instructionReadResults_memoryInit destination sourceValue
            countValue memoryIndex dataIndex hraw)
      simpa [destination, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constI32] using hcomplete

