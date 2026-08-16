import WasmGemmGnaf.Wasm.Core.ReadComplete
import WasmGemmGnaf.Wasm.Core.ByteSolvedLiteralComplete

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Completeness of packed and vector memory loads

The read relation solves fixed-width bit patterns from memory bytes.  These
proofs show that the executable candidates recover every relational result.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem mem_instructionReadResults_loadPack {z : State}
    (address : AddressLiteral) (input : Inn) (operation : LoadOp)
    (memoryIndex : MemIdx) (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.load input.toNumType (some operation) memoryIndex
          argument)])}
    (hresult : result ∈
      loadPackResults z address input operation memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.load input.toNumType (some operation) memoryIndex argument) := by
  cases input <;> simp only [Inn.toNumType, instructionReadResults] <;> split
  all_goals
    first
    | rename_i hnone
      rw [addressLiteral?_toVal address] at hnone
      contradiction
    | rename_i foundAddress hfoundAddress
      have heq := Option.some.inj
        (hfoundAddress.symm.trans (addressLiteral?_toVal address))
      subst foundAddress
      apply List.mem_map.mpr
      refine ⟨result, hresult, ?_⟩
      apply StepAResult.eq_of_event_next <;> rfl

theorem mem_instructionReadResults_vload {z : State}
    (address : AddressLiteral) (memoryIndex : MemIdx) (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 none memoryIndex argument)])}
    (hresult : result ∈ vloadResults z address memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.vload .v128 none memoryIndex argument) := by
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

theorem mem_instructionReadResults_vloadPack {z : State}
    (address : AddressLiteral) (size : Sz) (count : Nat) (extension : Sx)
    (memoryIndex : MemIdx) (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.shape size count extension))
          memoryIndex argument)])}
    (hresult : result ∈
      vloadPackResults z address size count extension memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.vload .v128 (some (.shape size count extension)) memoryIndex
        argument) := by
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

theorem mem_instructionReadResults_vloadZero {z : State}
    (address : AddressLiteral) (size : Sz) (memoryIndex : MemIdx)
    (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.zero size)) memoryIndex argument)])}
    (hresult : result ∈
      vloadZeroResults z address size memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.vload .v128 (some (.zero size)) memoryIndex argument) := by
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

theorem mem_instructionReadResults_vloadSplat {z : State}
    (address : AddressLiteral) (size : Sz) (memoryIndex : MemIdx)
    (argument : MemArg)
    {result : StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.splat size)) memoryIndex argument)])}
    (hresult : result ∈
      vloadSplatResults z address size memoryIndex argument) :
    result ∈ instructionReadResults z [address.toVal]
      (.vload .v128 (some (.splat size)) memoryIndex argument) := by
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

theorem mem_instructionReadResults_vloadLane {z : State}
    (address : AddressLiteral) (original : V128Lit) (size : Sz)
    (memoryIndex : MemIdx) (argument : MemArg) (laneIndex : LaneIdx)
    {result : StepAResult
      (z, vals [address.toVal, .vec ⟨.v128, original⟩] ++
        [.plain (.vloadLane .v128 size memoryIndex argument laneIndex)])}
    (hresult : result ∈
      vloadLaneResults z address original size memoryIndex argument laneIndex) :
    result ∈ instructionReadResults z
      [address.toVal, .vec ⟨.v128, original⟩]
      (.vloadLane .v128 size memoryIndex argument laneIndex) := by
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

private theorem shape_eq_storeLaneShape_of_inToLane
    {shape : Shape} {size : Sz} {bits : IN shape.lane.size}
    {lane : Lane_ shape.lane}
    (hsize : shape.lane.size = size.toNat)
    (hdim : shape.dim.toNat = 128 / size.toNat)
    (hlane : inToLane shape.lane bits = some lane) :
    shape = storeLaneShape size := by
  rcases shape with ⟨laneType, dimension⟩
  cases laneType with
  | num numberType =>
      cases numberType <;> cases dimension <;> cases size <;>
        simp [LaneType.size, NumType.size, Sz.toNat, Dim.toNat, inToLane,
          storeLaneShape] at hsize hdim hlane ⊢
  | pack packType =>
      cases packType <;> cases dimension <;> cases size <;>
        simp [LaneType.size, PackType.size, Sz.toNat, Dim.toNat, inToLane,
          storeLaneShape] at hsize hdim hlane ⊢

theorem loadPackOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .loadPackOob is is') :
    (.read .loadPackOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @loadPackOob addressType index input size extension memoryIndex argument
      memory hmemory hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      let operation : LoadOp := ⟨size, extension⟩
      have hread : Step_readA z .loadPackOob
          [constAddr addressType index,
            .plain (.load input.toNumType (some operation) memoryIndex
              argument)] [.trap] :=
        Step_read.loadPackOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .loadPackOob hread
      have hraw : raw ∈
          loadPackResults z address input operation memoryIndex argument := by
        unfold loadPackResults
        dsimp only
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address, operation,
                AddressLiteral.toAdmin, AddressLiteral.toVal, Val.toAdmin,
                constAddr]
          · rename_i hin
            exact False.elim (hin (by simpa [address, operation] using hoob))
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .load input.toNumType (some operation) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_loadPack address input operation
            memoryIndex argument hraw)
      simpa [address, operation, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constAddr, sourcePlains]
        using hcomplete

theorem loadPackVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .loadPackVal is is') :
    (.read .loadPackVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @loadPackVal addressType index input size extension memoryIndex argument
      memory bits value hmemory hbytes hextend =>
      let address : AddressLiteral := ⟨addressType, index⟩
      let operation : LoadOp := ⟨size, extension⟩
      have hread : Step_readA z .loadPackVal
          [constAddr addressType index,
            .plain (.load input.toNumType (some operation) memoryIndex
              argument)] [constInn input value] :=
        Step_read.loadPackVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hbytes hextend
      let raw := readResult .loadPackVal hread
      have hraw : raw ∈
          loadPackResults z address input operation memoryIndex argument := by
        unfold loadPackResults
        dsimp only
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · rename_i hoob
            have hoob' : address.value.val + argument.offset.val +
                size.toNat / 8 > memory.bytes.length := by
              simpa [operation] using hoob
            have hbytesAddress : releasedNumerics.ibytes_ size.toNat bits =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              simpa [address] using hbytes
            have hsliceLength :
                (slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8)).length = size.toNat / 8 := by
              rw [← hbytesAddress]
              cases size <;>
                simp [ConcreteNumerics.ibytes, Sz.toNat]
            have hpositive : 0 < size.toNat / 8 := by
              cases size <;> decide
            simp [slice] at hsliceLength
            omega
          · let bytes := slice memory.bytes
                (address.value.val + argument.offset.val) (size.toNat / 8)
            have hbytesDef : releasedNumerics.ibytes_ size.toNat bits =
                bytes := by simpa [bytes, address] using hbytes
            have hbits : Numerics.ofNatWrap size.toNat
                (Binary.leNat bytes) = bits := by
              rw [← hbytesDef]
              exact ofNatWrap_leNat_ibytes bits (by cases size <;> decide)
            dsimp only [bytes] at hbytesDef hbits ⊢
            have hgeneratedBytes : releasedNumerics.ibytes_
                operation.sz.toNat
                  (Numerics.ofNatWrap operation.sz.toNat
                    (Binary.leNat (slice memory.bytes
                      (address.value.val + argument.offset.val)
                      (operation.sz.toNat / 8)))) =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (operation.sz.toNat / 8) := by
              rw [show operation.sz.toNat = size.toNat by rfl]
              rw [hbits]
              exact hbytesDef
            rw [dif_pos hgeneratedBytes]
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next
            · simp [raw, hread, readResult, address, operation, hbits,
                AddressLiteral.toAdmin, AddressLiteral.toVal, Val.toAdmin,
                constAddr, constInn]
            · simp [raw, hread, readResult, address, operation, hbits,
                AddressLiteral.toAdmin, AddressLiteral.toVal, Val.toAdmin,
                constAddr, constInn]
              exact congrArg (innLitToNum input) hextend.symm
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .load input.toNumType (some operation) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_loadPack address input operation
            memoryIndex argument hraw)
      simpa [address, operation, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constAddr, sourcePlains]
        using hcomplete

theorem vloadOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadOob is is') :
    (.read .vloadOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadOob addressType index memoryIndex argument memory hmemory hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadOob
          [constAddr addressType index,
            .plain (.vload .v128 none memoryIndex argument)] [.trap] :=
        Step_read.vloadOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .vloadOob hread
      have hraw : raw ∈ vloadResults z address memoryIndex argument := by
        unfold vloadResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address,
                AddressLiteral.toAdmin, AddressLiteral.toVal, Val.toAdmin,
                constAddr]
          · rename_i hin
            exact False.elim (hin (by simpa [address] using hoob))
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 none memoryIndex argument)
          complete hread rfl
          (mem_instructionReadResults_vload address memoryIndex argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constAddr, sourcePlains]
        using hcomplete

theorem vloadVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadVal is is') :
    (.read .vloadVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadVal addressType index memoryIndex argument memory value hmemory
      hbytes =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadVal
          [constAddr addressType index,
            .plain (.vload .v128 none memoryIndex argument)]
          [.plain (.vconst .v128 value)] :=
        Step_read.vloadVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hbytes
      let raw := readResult .vloadVal hread
      have hraw : raw ∈ vloadResults z address memoryIndex argument := by
        unfold vloadResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · rename_i hoob
            have hwidth : VecType.v128.size / 8 = 16 := rfl
            have hbytesAddress : releasedNumerics.vbytes_ .v128 value =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (VecType.v128.size / 8) := by
              simpa [address] using hbytes
            have hsliceLength :
                (slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (VecType.v128.size / 8)).length =
                    VecType.v128.size / 8 := by
              rw [← hbytesAddress]
              simp [ConcreteNumerics.vbytes, ConcreteNumerics.ibytes,
                VecType.size]
            rw [hwidth] at hoob hsliceLength
            simp [slice] at hsliceLength
            omega
          · let bytes := slice memory.bytes
                (address.value.val + argument.offset.val)
                (VecType.v128.size / 8)
            have hbytesDef : releasedNumerics.vbytes_ .v128 value =
                bytes := by simpa [bytes, address] using hbytes
            have hvalue : Numerics.ofNatWrap 128
                (Binary.leNat bytes) = value := by
              rw [← hbytesDef]
              exact ofNatWrap_leNat_vbytes_v128 value
            dsimp only [bytes] at hbytesDef hvalue ⊢
            have hgeneratedBytes : releasedNumerics.vbytes_ .v128
                (Numerics.ofNatWrap 128
                  (Binary.leNat (slice memory.bytes
                    (address.value.val + argument.offset.val)
                    (VecType.v128.size / 8)))) =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (VecType.v128.size / 8) := by
              rw [hvalue]
              exact hbytesDef
            rw [dif_pos hgeneratedBytes]
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address, hvalue,
                AddressLiteral.toAdmin, AddressLiteral.toVal, Val.toAdmin,
                constAddr]
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 none memoryIndex argument)
          complete hread rfl
          (mem_instructionReadResults_vload address memoryIndex argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toAdmin, Val.toAdmin, constAddr, sourcePlains]
        using hcomplete

theorem vloadPackOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadPackOob is is') :
    (.read .vloadPackOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadPackOob addressType index size count extension memoryIndex argument
      memory hmemory hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadPackOob
          [constAddr addressType index,
            .plain (.vload .v128 (some (.shape size count extension))
              memoryIndex argument)] [.trap] :=
        Step_read.vloadPackOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .vloadPackOob hread
      have hraw : raw ∈
          vloadPackResults z address size count extension memoryIndex
            argument := by
        unfold vloadPackResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          apply List.mem_append.mpr
          apply Or.inl
          rw [dif_pos (by simpa [address] using hoob)]
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;>
            simp [raw, hread, readResult, address, AddressLiteral.toVal,
              AddressLiteral.toAdmin, Val.toAdmin, constAddr]
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.shape size count extension))
            memoryIndex argument)
          complete hread rfl
          (mem_instructionReadResults_vloadPack address size count extension
            memoryIndex argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadPackVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadPackVal is is') :
    (.read .vloadPackVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadPackVal addressType index size count extension memoryIndex argument
      memory shape chunks lanes value hmemory hsize hdim hlength hbytes
      hlanes hinv =>
      let address : AddressLiteral := ⟨addressType, index⟩
      let bitAt (m : Nat) : IN size.toNat :=
        Numerics.ofNatWrap size.toNat
          (Binary.leNat (slice memory.bytes
            (address.value.val + argument.offset.val +
              m * (size.toNat / 8))
            (size.toNat / 8)))
      let bits := (List.range count).map bitAt
      have hbitsLength : bits.length = count := by
        change ((List.range count).map bitAt).length = count
        simp
      have hbitsEq : bits = chunks := by
        apply List.ext_getElem
        · exact hbitsLength.trans hlength.symm
        · intro m hmBits hmChunks
          have hchunkSome : chunks[m]? = some chunks[m] :=
            List.getElem?_eq_getElem hmChunks
          have hchunkBytes := hbytes m chunks[m] hchunkSome
          have hcanonical : bitAt m = chunks[m] := by
            dsimp [bitAt]
            rw [← hchunkBytes]
            exact ofNatWrap_leNat_ibytes chunks[m]
              (by cases size <;> decide)
          have hmCount : m < count := by
            rw [← hbitsLength]
            exact hmBits
          have hbitsGet : bits[m] = bitAt m := by
            simp [bits, hmCount]
          rw [hbitsGet]
          exact hcanonical
      have hgeneratedBytes : ∀ m : Fin count,
          releasedNumerics.ibytes_ size.toNat (bitAt m.val) =
            slice memory.bytes
              (address.value.val + argument.offset.val +
                m.val * (size.toNat / 8))
              (size.toNat / 8) := by
        intro m
        have hmChunks : m.val < chunks.length := by
          rw [hlength]
          exact m.isLt
        have hchunkSome : chunks[m.val]? = some chunks[m.val] :=
          List.getElem?_eq_getElem hmChunks
        have hbitEq : bitAt m.val = chunks[m.val] := by
          dsimp [bitAt]
          rw [← hbytes m.val chunks[m.val] hchunkSome]
          exact ofNatWrap_leNat_ibytes chunks[m.val]
            (by cases size <;> decide)
        rw [hbitEq]
        exact hbytes m.val chunks[m.val] hchunkSome
      have hgeneratedLanes : bits.mapM (fun bit =>
          inToLane shape.lane
            (releasedNumerics.extend__ size.toNat shape.lane.size extension
              bit)) = some lanes := by
        rw [hbitsEq]
        exact hlanes
      have hread : Step_readA z .vloadPackVal
          [constAddr addressType index,
            .plain (.vload .v128 (some (.shape size count extension))
              memoryIndex argument)] [.plain (.vconst .v128 value)] :=
        Step_read.vloadPackVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hsize hdim hlength hbytes hlanes
            hinv
      let raw := readResult .vloadPackVal hread
      have hraw : raw ∈
          vloadPackResults z address size count extension memoryIndex
            argument := by
        unfold vloadPackResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          apply List.mem_append.mpr
          apply Or.inr
          apply List.mem_flatMap.mpr
          refine ⟨shape, mem_readVectorShapes shape, ?_⟩
          rw [dif_pos hsize, dif_pos hdim]
          rw [dif_pos (by
            intro m
            exact hgeneratedBytes m)]
          split
          · rename_i hnone
            rw [hgeneratedLanes] at hnone
            contradiction
          · rename_i foundLanes hfoundLanes
            have hls := Option.some.inj
              (hfoundLanes.symm.trans hgeneratedLanes)
            subst foundLanes
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next
            · simp [raw, hread, readResult, address, AddressLiteral.toVal,
                AddressLiteral.toAdmin, Val.toAdmin, constAddr]
            · simp [raw, hread, readResult, address, AddressLiteral.toVal,
                AddressLiteral.toAdmin, Val.toAdmin, constAddr]
              exact hinv.symm
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.shape size count extension))
            memoryIndex argument)
          complete hread rfl
          (mem_instructionReadResults_vloadPack address size count extension
            memoryIndex argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadZeroOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadZeroOob is is') :
    (.read .vloadZeroOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadZeroOob addressType index size memoryIndex argument memory hmemory
      hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadZeroOob
          [constAddr addressType index,
            .plain (.vload .v128 (some (.zero size)) memoryIndex argument)]
          [.trap] :=
        Step_read.vloadZeroOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .vloadZeroOob hread
      have hraw : raw ∈
          vloadZeroResults z address size memoryIndex argument := by
        unfold vloadZeroResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address, AddressLiteral.toVal,
                AddressLiteral.toAdmin, Val.toAdmin, constAddr]
          · rename_i hin
            exact False.elim (hin (by simpa [address] using hoob))
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.zero size)) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_vloadZero address size memoryIndex
            argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadZeroVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadZeroVal is is') :
    (.read .vloadZeroVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadZeroVal addressType index size memoryIndex argument memory bits value
      hmemory hbytes hextend =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadZeroVal
          [constAddr addressType index,
            .plain (.vload .v128 (some (.zero size)) memoryIndex argument)]
          [.plain (.vconst .v128 value)] :=
        Step_read.vloadZeroVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hbytes hextend
      let raw := readResult .vloadZeroVal hread
      have hraw : raw ∈
          vloadZeroResults z address size memoryIndex argument := by
        unfold vloadZeroResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · rename_i hoob
            have hbytesAddress : releasedNumerics.ibytes_ size.toNat bits =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              simpa [address] using hbytes
            have hsliceLength :
                (slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8)).length = size.toNat / 8 := by
              rw [← hbytesAddress]
              cases size <;> simp [ConcreteNumerics.ibytes, Sz.toNat]
            have hpositive : 0 < size.toNat / 8 := by
              cases size <;> decide
            simp [slice] at hsliceLength
            omega
          · let bytes := slice memory.bytes
                (address.value.val + argument.offset.val) (size.toNat / 8)
            have hbytesDef : releasedNumerics.ibytes_ size.toNat bits =
                bytes := by simpa [bytes, address] using hbytes
            have hbits : Numerics.ofNatWrap size.toNat
                (Binary.leNat bytes) = bits := by
              rw [← hbytesDef]
              exact ofNatWrap_leNat_ibytes bits (by cases size <;> decide)
            dsimp only [bytes] at hbytesDef hbits ⊢
            have hgeneratedBytes : releasedNumerics.ibytes_ size.toNat
                (Numerics.ofNatWrap size.toNat
                  (Binary.leNat (slice memory.bytes
                    (address.value.val + argument.offset.val)
                    (size.toNat / 8)))) =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              rw [hbits]
              exact hbytesDef
            rw [dif_pos hgeneratedBytes]
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next
            · simp [raw, hread, readResult, address, hbits,
                AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin,
                constAddr]
            · simp [raw, hread, readResult, address, hbits,
                AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin,
                constAddr]
              exact congrArg (fun x : V128Lit => x) hextend.symm
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.zero size)) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_vloadZero address size memoryIndex
            argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadSplatOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadSplatOob is is') :
    (.read .vloadSplatOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadSplatOob addressType index size memoryIndex argument memory hmemory
      hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadSplatOob
          [constAddr addressType index,
            .plain (.vload .v128 (some (.splat size)) memoryIndex argument)]
          [.trap] :=
        Step_read.vloadSplatOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .vloadSplatOob hread
      have hraw : raw ∈
          vloadSplatResults z address size memoryIndex argument := by
        unfold vloadSplatResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address, AddressLiteral.toVal,
                AddressLiteral.toAdmin, Val.toAdmin, constAddr]
          · rename_i hin
            exact False.elim (hin (by simpa [address] using hoob))
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.splat size)) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_vloadSplat address size memoryIndex
            argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadSplatVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadSplatVal is is') :
    (.read .vloadSplatVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadSplatVal addressType index size memoryIndex argument memory shape
      bits lane value hmemory hsize hdim hbytes hlane hinv =>
      have hshape := shape_eq_storeLaneShape_of_inToLane hsize hdim hlane
      subst shape
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadSplatVal
          [constAddr addressType index,
            .plain (.vload .v128 (some (.splat size)) memoryIndex argument)]
          [.plain (.vconst .v128 value)] :=
        Step_read.vloadSplatVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hsize hdim hbytes hlane hinv
      let raw := readResult .vloadSplatVal hread
      have hraw : raw ∈
          vloadSplatResults z address size memoryIndex argument := by
        unfold vloadSplatResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · rename_i hoob
            have hbytesAddress : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size bits =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              simpa [address] using hbytes
            have hsliceLength :
                (slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8)).length = size.toNat / 8 := by
              rw [← hbytesAddress]
              cases size <;> simp [storeLaneShape, ConcreteNumerics.ibytes,
                LaneType.size, NumType.size, PackType.size, Sz.toNat]
            have hpositive : 0 < size.toNat / 8 := by
              cases size <;> decide
            simp [slice] at hsliceLength
            omega
          · let bytes := slice memory.bytes
                (address.value.val + argument.offset.val) (size.toNat / 8)
            have hbytesDef : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size bits = bytes := by
              simpa [bytes, address] using hbytes
            have hbits : Numerics.ofNatWrap
                (storeLaneShape size).lane.size (Binary.leNat bytes) =
                bits := by
              rw [← hbytesDef]
              exact ofNatWrap_leNat_ibytes bits (by cases size <;> decide)
            dsimp only [bytes] at hbytesDef hbits ⊢
            have hgeneratedBytes : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size
                  (Numerics.ofNatWrap (storeLaneShape size).lane.size
                    (Binary.leNat (slice memory.bytes
                      (address.value.val + argument.offset.val)
                      (size.toNat / 8)))) =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              rw [hbits]
              exact hbytesDef
            rw [dif_pos hgeneratedBytes]
            have hgeneratedLane : inToLane (storeLaneShape size).lane
                (Numerics.ofNatWrap (storeLaneShape size).lane.size
                  (Binary.leNat (slice memory.bytes
                    (address.value.val + argument.offset.val)
                    (size.toNat / 8)))) = some lane := by
              rw [hbits]
              exact hlane
            have hinv' : releasedNumerics.inv_lanes_ (storeLaneShape size)
                (List.replicate (128 / size.toNat) lane) = value := by
              rw [← hdim]
              exact hinv
            split
            · rename_i hnone
              rw [hgeneratedLane] at hnone
              contradiction
            · rename_i foundLane hfoundLane
              have hl := Option.some.inj
                (hfoundLane.symm.trans hgeneratedLane)
              subst foundLane
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next
              · simp [raw, hread, readResult, address, AddressLiteral.toVal,
                  AddressLiteral.toAdmin, Val.toAdmin, constAddr]
              · simp [raw, hread, readResult, address, AddressLiteral.toVal,
                  AddressLiteral.toAdmin, Val.toAdmin, constAddr]
                exact hinv'.symm
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal])
          (instruction := .vload .v128 (some (.splat size)) memoryIndex
            argument)
          complete hread rfl
          (mem_instructionReadResults_vloadSplat address size memoryIndex
            argument hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadLaneOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadLaneOob is is') :
    (.read .vloadLaneOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadLaneOob addressType index original size memoryIndex argument
      laneIndex memory hmemory hoob =>
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadLaneOob
          [constAddr addressType index, .plain (.vconst .v128 original),
            .plain (.vloadLane .v128 size memoryIndex argument laneIndex)]
          [.trap] :=
        Step_read.vloadLaneOob
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hoob
      let raw := readResult .vloadLaneOob hread
      have hraw : raw ∈
          vloadLaneResults z address original size memoryIndex argument
            laneIndex := by
        unfold vloadLaneResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;>
              simp [raw, hread, readResult, address, AddressLiteral.toVal,
                AddressLiteral.toAdmin, Val.toAdmin, constAddr]
          · rename_i hin
            exact False.elim (hin (by simpa [address] using hoob))
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal, .vec ⟨.v128, original⟩])
          (instruction :=
            .vloadLane .v128 size memoryIndex argument laneIndex)
          complete hread rfl
          (mem_instructionReadResults_vloadLane address original size
            memoryIndex argument laneIndex hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

theorem vloadLaneVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .vloadLaneVal is is') :
    (.read .vloadLaneVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @vloadLaneVal addressType index original value size memoryIndex argument
      laneIndex memory shape bits lane lanes hmemory hsize hdim hbytes hlane
      hset hinv =>
      have hdim' : shape.dim.toNat = 128 / size.toNat := by
        simpa [VecType.size] using hdim
      have hshape :=
        shape_eq_storeLaneShape_of_inToLane hsize hdim' hlane
      subst shape
      let address : AddressLiteral := ⟨addressType, index⟩
      have hread : Step_readA z .vloadLaneVal
          [constAddr addressType index, .plain (.vconst .v128 original),
            .plain (.vloadLane .v128 size memoryIndex argument laneIndex)]
          [.plain (.vconst .v128 value)] :=
        Step_read.vloadLaneVal
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hmemory hsize hdim hbytes hlane hset hinv
      let raw := readResult .vloadLaneVal hread
      have hraw : raw ∈
          vloadLaneResults z address original size memoryIndex argument
            laneIndex := by
        unfold vloadLaneResults
        split
        · rename_i hnone
          rw [hmemory] at hnone
          contradiction
        · rename_i foundMemory hfoundMemory
          have hm := Option.some.inj (hfoundMemory.symm.trans hmemory)
          subst foundMemory
          split
          · rename_i hoob
            have hbytesAddress : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size bits =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              simpa [address] using hbytes
            have hsliceLength :
                (slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8)).length = size.toNat / 8 := by
              rw [← hbytesAddress]
              cases size <;> simp [storeLaneShape, ConcreteNumerics.ibytes,
                LaneType.size, NumType.size, PackType.size, Sz.toNat]
            have hpositive : 0 < size.toNat / 8 := by
              cases size <;> decide
            simp [slice] at hsliceLength
            omega
          · let bytes := slice memory.bytes
                (address.value.val + argument.offset.val) (size.toNat / 8)
            have hbytesDef : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size bits = bytes := by
              simpa [bytes, address] using hbytes
            have hbits : Numerics.ofNatWrap
                (storeLaneShape size).lane.size (Binary.leNat bytes) =
                bits := by
              rw [← hbytesDef]
              exact ofNatWrap_leNat_ibytes bits (by cases size <;> decide)
            dsimp only [bytes] at hbytesDef hbits ⊢
            have hgeneratedBytes : releasedNumerics.ibytes_
                (storeLaneShape size).lane.size
                  (Numerics.ofNatWrap (storeLaneShape size).lane.size
                    (Binary.leNat (slice memory.bytes
                      (address.value.val + argument.offset.val)
                      (size.toNat / 8)))) =
                slice memory.bytes
                  (address.value.val + argument.offset.val)
                  (size.toNat / 8) := by
              rw [hbits]
              exact hbytesDef
            rw [dif_pos hgeneratedBytes]
            have hgeneratedLane : inToLane (storeLaneShape size).lane
                (Numerics.ofNatWrap (storeLaneShape size).lane.size
                  (Binary.leNat (slice memory.bytes
                    (address.value.val + argument.offset.val)
                    (size.toNat / 8)))) = some lane := by
              rw [hbits]
              exact hlane
            split
            · rename_i hnone
              rw [hgeneratedLane] at hnone
              contradiction
            · rename_i foundLane hfoundLane
              have hl := Option.some.inj
                (hfoundLane.symm.trans hgeneratedLane)
              subst foundLane
              split
              · rename_i hnone
                rw [hset] at hnone
                contradiction
              · rename_i foundLanes hfoundLanes
                have hls := Option.some.inj
                  (hfoundLanes.symm.trans hset)
                subst foundLanes
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next
                · simp [raw, hread, readResult, address,
                    AddressLiteral.toVal, AddressLiteral.toAdmin,
                    Val.toAdmin, constAddr]
                · simp [raw, hread, readResult, address,
                    AddressLiteral.toVal, AddressLiteral.toAdmin,
                    Val.toAdmin, constAddr]
                  exact hinv.symm
      have hcomplete :=
        readResult_mem_completeReadSuccessorsOf_of_instruction
          (values := [address.toVal, .vec ⟨.v128, original⟩])
          (instruction :=
            .vloadLane .v128 size memoryIndex argument laneIndex)
          complete hread rfl
          (mem_instructionReadResults_vloadLane address original size
            memoryIndex argument laneIndex hraw)
      simpa [address, raw, StepAResult.toPair, readResult,
        AddressLiteral.toVal, AddressLiteral.toAdmin, Val.toAdmin, constAddr,
        sourcePlains] using hcomplete

end WasmGemmGnaf.Wasm.Core.Exec
