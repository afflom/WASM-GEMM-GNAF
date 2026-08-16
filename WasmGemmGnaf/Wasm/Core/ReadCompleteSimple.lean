import WasmGemmGnaf.Wasm.Core.ReadCompleteMemory
import WasmGemmGnaf.Wasm.Core.ReadCompleteTables

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem localGet_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .localGet is is') :
    (.read .localGet (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @localGet localIndex value hlocal =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .localGet localIndex) complete
        (Step_read.localGet (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hlocal) rfl
      simp only [instructionReadResults]
      split
      · split
        · rename_i foundValue hfoundValue
          have heq : foundValue = value := by
            simpa using hfoundValue.symm.trans hlocal
          subst foundValue
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
        · rename_i hmissing
          exact False.elim (hmissing value hlocal)
      · simp_all

theorem globalGet_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .globalGet is is') :
    (.read .globalGet (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @globalGet globalIndex global hglobal =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .globalGet globalIndex) complete
        (Step_read.globalGet (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) hglobal) rfl
      simp only [instructionReadResults]
      split
      · split
        · rename_i hnone
          rw [hglobal] at hnone
          contradiction
        · rename_i foundGlobal hfoundGlobal
          have heq := Option.some.inj (hfoundGlobal.symm.trans hglobal)
          subst foundGlobal
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

theorem callRefNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .callRefNull is is') :
    (.read .callRefNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @callRefNull heapType typeUse =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType)]) (instruction := .callRef typeUse)
        complete
        (Step_read.callRefNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem refFunc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refFunc is is') :
    (.read .refFunc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refFunc functionIndex address haddress =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .refFunc functionIndex) complete
        (Step_read.refFunc (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) haddress) rfl
      simp only [instructionReadResults]
      split
      · split
        · rename_i hnone
          rw [haddress] at hnone
          contradiction
        · rename_i foundAddress hfoundAddress
          have heq := Option.some.inj (hfoundAddress.symm.trans haddress)
          subst foundAddress
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

theorem structGetNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .structGetNull is is') :
    (.read .structGetNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @structGetNull heapType extension typeIndex fieldIndex =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType)])
        (instruction := .structGet extension typeIndex fieldIndex) complete
        (Step_read.structGetNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, structGetResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayGetNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayGetNull is is') :
    (.read .arrayGetNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayGetNull heapType index extension typeIndex =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType), .num ⟨.i32, index⟩])
        (instruction := .arrayGet extension typeIndex) complete
        (Step_read.arrayGetNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayGetResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayLenNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayLenNull is is') :
    (.read .arrayLenNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayLenNull heapType =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType)]) (instruction := .arrayLen) complete
        (Step_read.arrayLenNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayLenResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayFillNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayFillNull is is') :
    (.read .arrayFillNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayFillNull heapType index count value typeIndex =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType), .num ⟨.i32, index⟩, value,
          .num ⟨.i32, count⟩]) (instruction := .arrayFill typeIndex) complete
        (Step_read.arrayFillNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayFillResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayCopyNull1_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyNull1 is is') :
    (.read .arrayCopyNull1 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyNull1 heapType destinationIndex sourceIndex count source
      destinationType sourceType =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType), .num ⟨.i32, destinationIndex⟩,
          .ref source, .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete
        (Step_read.arrayCopyNull1 (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayCopyNull2_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyNull2 is is') :
    (.read .arrayCopyNull2 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyNull2 heapType destinationIndex sourceIndex count destination
      destinationType sourceType =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref destination, .num ⟨.i32, destinationIndex⟩,
          .ref (.null heapType), .num ⟨.i32, sourceIndex⟩,
          .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete
        (Step_read.arrayCopyNull2 (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl

theorem arrayInitElemNull_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitElemNull is is') :
    (.read .arrayInitElemNull (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitElemNull heapType arrayIndex elemIndex count typeIndex
      segmentIndex =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.null heapType), .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, elemIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayInitElem typeIndex segmentIndex) complete
        (Step_read.arrayInitElemNull (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics)) rfl
      simp only [instructionReadResults, arrayInitElemResults]
      apply List.mem_singleton.mpr
      apply StepAResult.eq_of_event_next <;> rfl
