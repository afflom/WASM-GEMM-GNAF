import WasmGemmGnaf.Wasm.Core.ReadComplete

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Completeness of GC object and array reads

These proofs recover every relational struct/array read or recursive expansion
from the proof-carrying executable read candidates.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem structNewDefault_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .structNewDefault is is') :
    (.read .structNewDefault (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @structNewDefault typeIndex type fields values htype hexpand hdefaults =>
      have hread := Step_read.structNewDefault
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        htype hexpand hdefaults
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .structNewDefault typeIndex) complete
        hread rfl
      simp only [instructionReadResults]
      rw [dif_pos trivial]
      apply List.mem_map.mpr
      refine ⟨readResult .structNewDefault hread, ?_, ?_⟩
      · unfold structNewDefaultResults
        rcases hexpand with ⟨hexpand⟩
        split
        · rename_i hnone
          rw [htype] at hnone
          contradiction
        · rename_i foundType hfoundType
          have ht := Option.some.inj (hfoundType.symm.trans htype)
          subst foundType
          split
          · rename_i hfoundExpand
            have hc := Option.some.inj (hfoundExpand.symm.trans hexpand)
            cases hc
            split
            · rename_i hnone
              rw [hdefaults] at hnone
              contradiction
            · rename_i foundValues hfoundValues
              have hv := Option.some.inj
                (hfoundValues.symm.trans hdefaults)
              subst foundValues
              apply List.mem_singleton.mpr
              apply StepAResult.eq_of_event_next <;> rfl
          · simp_all
      · apply StepAResult.eq_of_event_next <;> rfl

theorem structGetStruct_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .structGetStruct is is') :
    (.read .structGetStruct (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @structGetStruct address extension typeIndex fieldIndex type fields
      struct fieldType field value htype hexpand hstruct hfieldType hfield
      hvalue =>
      have hread := Step_read.structGetStruct
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        htype hexpand hstruct hfieldType hfield hvalue
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.structAddr address))])
        (instruction := .structGet extension typeIndex fieldIndex) complete
        hread rfl
      simp only [instructionReadResults, structGetResults]
      rcases hexpand with ⟨hexpand⟩
      split
      · rename_i hnone
        rw [htype] at hnone
        contradiction
      · rename_i foundType hfoundType
        have ht := Option.some.inj (hfoundType.symm.trans htype)
        subst foundType
        split
        · rename_i hfoundExpand
          have hc := Option.some.inj (hfoundExpand.symm.trans hexpand)
          cases hc
          split
          · rename_i foundStruct foundFieldType hfoundStruct hfoundFieldType
            have hs := Option.some.inj (hfoundStruct.symm.trans hstruct)
            subst foundStruct
            have hft := Option.some.inj
              (hfoundFieldType.symm.trans hfieldType)
            subst foundFieldType
            split
            · rename_i hnone
              rw [hfield] at hnone
              contradiction
            · rename_i foundField hfoundField
              have hf := Option.some.inj (hfoundField.symm.trans hfield)
              subst foundField
              split
              · rename_i hnone
                rw [hvalue] at hnone
                contradiction
              · rename_i foundValue hfoundValue
                have hv := Option.some.inj (hfoundValue.symm.trans hvalue)
                subst foundValue
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next <;> rfl
          · simp_all
        · simp_all

theorem arrayNewDefault_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayNewDefault is is') :
    (.read .arrayNewDefault (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayNewDefault count typeIndex type fieldType value htype hexpand
      hdefault =>
      have hread := Step_read.arrayNewDefault
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (n := count) (x := typeIndex) htype hexpand hdefault
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.num ⟨.i32, count⟩])
        (instruction := .arrayNewDefault typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayNewDefaultResults]
      rcases hexpand with ⟨hexpand⟩
      split
      · rename_i hnone
        rw [htype] at hnone
        contradiction
      · rename_i foundType hfoundType
        have ht := Option.some.inj (hfoundType.symm.trans htype)
        subst foundType
        split
        · rename_i hfoundExpand
          have hc := Option.some.inj (hfoundExpand.symm.trans hexpand)
          cases hc
          split
          · rename_i hnone
            rw [hdefault] at hnone
            contradiction
          · rename_i foundValue hfoundValue
            have hv := Option.some.inj (hfoundValue.symm.trans hdefault)
            subst foundValue
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
        · simp_all

theorem arrayNewElemOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayNewElemOob is is') :
    (.read .arrayNewElemOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayNewElemOob offset count typeIndex elemIndex elem helem hoob =>
      have hread := Step_read.arrayNewElemOob
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x := typeIndex) helem hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayNewElem typeIndex elemIndex) complete hread rfl
      simp only [instructionReadResults, arrayNewElemResults]
      split
      · rename_i hnone
        rw [helem] at hnone
        contradiction
      · rename_i foundElem hfoundElem
        have he := Option.some.inj (hfoundElem.symm.trans helem)
        subst foundElem
        apply List.mem_append.mpr
        apply Or.inl
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayNewElemAlloc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayNewElemAlloc is is') :
    (.read .arrayNewElemAlloc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayNewElemAlloc offset count typeIndex elemIndex elem references helem
      hrefs hlength =>
      subst references
      have hread := Step_read.arrayNewElemAlloc
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x := typeIndex) helem rfl hlength
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayNewElem typeIndex elemIndex) complete hread rfl
      simp only [instructionReadResults, arrayNewElemResults]
      split
      · rename_i hnone
        rw [helem] at hnone
        contradiction
      · rename_i foundElem hfoundElem
        have he := Option.some.inj (hfoundElem.symm.trans helem)
        subst foundElem
        apply List.mem_append.mpr
        apply Or.inr
        rw [dif_pos hlength]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayGetOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayGetOob is is') :
    (.read .arrayGetOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayGetOob address index extension typeIndex array harray hoob =>
      have hread := Step_read.arrayGetOob
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (sx := extension) (x := typeIndex) harray hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩])
        (instruction := .arrayGet extension typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayGetResults]
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayGetArray_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayGetArray is is') :
    (.read .arrayGetArray (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayGetArray address index extension typeIndex array type fieldType
      field value htype hexpand harray hfield hvalue =>
      have hread := Step_read.arrayGetArray
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        htype hexpand harray hfield hvalue
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩])
        (instruction := .arrayGet extension typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayGetResults]
      rcases hexpand with ⟨hexpand⟩
      have hin : ¬ index.val ≥ array.fields.length := by
        rcases List.getElem?_eq_some_iff.mp hfield with ⟨hindex, _⟩
        omega
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_neg hin]
        split
        · rename_i hnone
          rw [htype] at hnone
          contradiction
        · rename_i foundType hfoundType
          have ht := Option.some.inj (hfoundType.symm.trans htype)
          subst foundType
          split
          · rename_i hfoundExpand
            have hc := Option.some.inj (hfoundExpand.symm.trans hexpand)
            cases hc
            split
            · rename_i hnone
              rw [hfield] at hnone
              contradiction
            · rename_i foundField hfoundField
              have hf := Option.some.inj (hfoundField.symm.trans hfield)
              subst foundField
              split
              · rename_i hnone
                rw [hvalue] at hnone
                contradiction
              · rename_i foundValue hfoundValue
                have hv := Option.some.inj (hfoundValue.symm.trans hvalue)
                subst foundValue
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next <;> rfl
          · simp_all

theorem arrayLenArray_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayLenArray is is') :
    (.read .arrayLenArray (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayLenArray address array length harray hlength =>
      have hread := Step_read.arrayLenArray
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        harray hlength
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address))])
        (instruction := .arrayLen) complete hread rfl
      simp only [instructionReadResults, arrayLenResults]
      have hu32 : u32? array.fields.length = some length := by
        unfold u32?
        rw [dif_pos (by rw [← hlength]; exact length.property)]
        congr 1
        exact Subtype.ext hlength.symm
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        split
        · rename_i hnone
          rw [hu32] at hnone
          contradiction
        · rename_i foundLength hfoundLength
          have hl := Option.some.inj (hfoundLength.symm.trans hu32)
          subst foundLength
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl

theorem arrayFillOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayFillOob is is') :
    (.read .arrayFillOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayFillOob address index count value typeIndex array harray hoob =>
      have hread := Step_read.arrayFillOob
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (v := value) (x := typeIndex) harray hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩,
          value, .num ⟨.i32, count⟩])
        (instruction := .arrayFill typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayFillResults]
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayFillZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayFillZero is is') :
    (.read .arrayFillZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayFillZero address index count value typeIndex array harray hin hzero =>
      have hread := Step_read.arrayFillZero
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (v := value) (x := typeIndex) harray hin hzero
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩,
          value, .num ⟨.i32, count⟩])
        (instruction := .arrayFill typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayFillResults]
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_neg hin, dif_pos hzero]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayFillSucc_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayFillSucc is is') :
    (.read .arrayFillSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayFillSucc address index count nextIndex nextCount value typeIndex array
      harray hin hnonzero hnextIndex hnextCount =>
      have hread := Step_read.arrayFillSucc
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (v := value) (x := typeIndex) harray hin hnonzero hnextIndex
          hnextCount
      have hnextIndexOption : u32? (index.val + 1) = some nextIndex := by
        unfold u32?
        rw [dif_pos (by rw [← hnextIndex]; exact nextIndex.property)]
        congr 1
        exact Subtype.ext hnextIndex.symm
      have hnextCountOption : u32? (count.val - 1) = some nextCount := by
        have hvalue : count.val - 1 = nextCount.val := by omega
        unfold u32?
        rw [dif_pos (by rw [hvalue]; exact nextCount.property)]
        congr 1
        exact Subtype.ext hvalue
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩,
          value, .num ⟨.i32, count⟩])
        (instruction := .arrayFill typeIndex) complete hread rfl
      simp only [instructionReadResults, arrayFillResults]
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_neg hin, dif_neg hnonzero]
        split
        · rename_i foundIndex foundCount hfoundIndex hfoundCount
          have hi := Option.some.inj
            (hfoundIndex.symm.trans hnextIndexOption)
          subst foundIndex
          have hn := Option.some.inj
            (hfoundCount.symm.trans hnextCountOption)
          subst foundCount
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
        · simp_all

theorem arrayCopyOob1_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyOob1 is is') :
    (.read .arrayCopyOob1 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyOob1 destination source destinationIndex sourceIndex count
      destinationType sourceType destinationArray hdestination hoob =>
      have hread := Step_read.arrayCopyOob1
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (a₂ := source) (i₂ := sourceIndex)
        (x₁ := destinationType) (x₂ := sourceType)
        hdestination hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr destination)),
          .num ⟨.i32, destinationIndex⟩, .ref (.addr (.arrayAddr source)),
          .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete hread
        rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      split
      · rename_i hnone
        rw [hdestination] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans hdestination)
        subst foundArray
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayCopyOob2_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyOob2 is is') :
    (.read .arrayCopyOob2 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyOob2 destination source destinationIndex sourceIndex count
      destinationType sourceType sourceArray hsource hoob =>
      have hread := Step_read.arrayCopyOob2
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (a₁ := destination) (i₁ := destinationIndex)
        (x₁ := destinationType) (x₂ := sourceType)
        hsource hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr destination)),
          .num ⟨.i32, destinationIndex⟩, .ref (.addr (.arrayAddr source)),
          .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete hread
        rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_left
      apply List.mem_append_right
      split
      · rename_i hnone
        rw [hsource] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans hsource)
        subst foundArray
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayCopyZero_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyZero is is') :
    (.read .arrayCopyZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyZero destination source destinationIndex sourceIndex count
      destinationType sourceType destinationArray sourceArray hdestination
      hsource hdestinationIn hsourceIn hzero =>
      have hread := Step_read.arrayCopyZero
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x₁ := destinationType) (x₂ := sourceType)
        hdestination hsource hdestinationIn hsourceIn hzero
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr destination)),
          .num ⟨.i32, destinationIndex⟩, .ref (.addr (.arrayAddr source)),
          .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete hread
        rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_right
      split
      · rename_i foundDestination foundSource hfoundDestination hfoundSource
        have hd := Option.some.inj
          (hfoundDestination.symm.trans hdestination)
        subst foundDestination
        have hs := Option.some.inj (hfoundSource.symm.trans hsource)
        subst foundSource
        rw [dif_neg hdestinationIn, dif_neg hsourceIn,
          dif_pos hdestinationIn, dif_pos hsourceIn, dif_pos hzero]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl
      · rename_i hbad
        exact False.elim
          (hbad destinationArray sourceArray hdestination hsource)

theorem arrayCopyLe_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyLe is is') :
    (.read .arrayCopyLe (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyLe destination source destinationIndex sourceIndex count
      nextDestination nextSource nextCount destinationType sourceType
      destinationArray sourceArray definedType fieldType extension
      hdestination hsource hdestinationIn hsourceIn hnonzero htype hexpand
      horder hextension hnextDestination hnextSource hnextCount =>
      have hread := Step_read.arrayCopyLe
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x₁ := destinationType) hdestination hsource hdestinationIn hsourceIn
        hnonzero htype hexpand horder hextension hnextDestination hnextSource
        hnextCount
      have hnextDestinationOption : u32? (destinationIndex.val + 1) =
          some nextDestination := by
        change addressLiteralOfNat? .i32 (destinationIndex.val + 1) =
          some nextDestination
        rw [← hnextDestination]
        exact addressLiteralOfNat?_val _ _
      have hnextSourceOption : u32? (sourceIndex.val + 1) =
          some nextSource := by
        change addressLiteralOfNat? .i32 (sourceIndex.val + 1) =
          some nextSource
        rw [← hnextSource]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : count.val - 1 = nextCount.val := by omega
      have hnextCountOption : u32? (count.val - 1) = some nextCount := by
        change addressLiteralOfNat? .i32 (count.val - 1) = some nextCount
        rw [hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr destination)),
          .num ⟨.i32, destinationIndex⟩, .ref (.addr (.arrayAddr source)),
          .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete hread
        rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_right
      rcases hexpand with ⟨hexpand⟩
      split
      · rename_i foundDestination foundSource hfoundDestination hfoundSource
        have hd := Option.some.inj
          (hfoundDestination.symm.trans hdestination)
        subst foundDestination
        have hs := Option.some.inj (hfoundSource.symm.trans hsource)
        subst foundSource
        rw [dif_neg hdestinationIn, dif_neg hsourceIn,
          dif_pos hdestinationIn, dif_pos hsourceIn, dif_neg hnonzero]
        split
        · rename_i hnone
          rw [htype] at hnone
          contradiction
        · rename_i foundType hfoundType
          have ht := Option.some.inj (hfoundType.symm.trans htype)
          subst foundType
          split
          · rename_i foundFieldType hfoundFieldType
            have hf := Option.some.inj (hfoundFieldType.symm.trans hexpand)
            injection hf with hf
            subst foundFieldType
            split
            · rename_i hnone
              rw [hextension] at hnone
              contradiction
            · rename_i foundExtension hfoundExtension
              have he := Option.some.inj
                (hfoundExtension.symm.trans hextension)
              subst foundExtension
              rw [dif_pos horder]
              split
              · rename_i foundDestination foundSource foundCount
                  hfoundDestination hfoundSource hfoundCount
                have hnd := Option.some.inj
                  (hfoundDestination.symm.trans hnextDestinationOption)
                subst foundDestination
                have hns := Option.some.inj
                  (hfoundSource.symm.trans hnextSourceOption)
                subst foundSource
                have hnc := Option.some.inj
                  (hfoundCount.symm.trans hnextCountOption)
                subst foundCount
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next <;> rfl
              · rename_i hmissing
                exact False.elim
                  (hmissing nextDestination nextSource nextCount
                    hnextDestinationOption hnextSourceOption hnextCountOption)
          · simp_all
      · rename_i hbad
        exact False.elim
          (hbad destinationArray sourceArray hdestination hsource)

theorem arrayCopyGt_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .arrayCopyGt is is') :
    (.read .arrayCopyGt (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayCopyGt destination source destinationIndex sourceIndex count
      lastDestination lastSource nextCount destinationType sourceType
      destinationArray sourceArray definedType fieldType extension
      hdestination hsource hdestinationIn hsourceIn hnonzero horder htype
      hexpand hextension hlastDestination hlastSource hnextCount =>
      have hread := Step_read.arrayCopyGt
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x₁ := destinationType) hdestination hsource hdestinationIn hsourceIn
        hnonzero horder htype hexpand hextension hlastDestination hlastSource
        hnextCount
      have hlastDestinationValue :
          destinationIndex.val + count.val - 1 = lastDestination.val := by
        omega
      have hlastDestinationOption :
          u32? (destinationIndex.val + count.val - 1) =
            some lastDestination := by
        change addressLiteralOfNat? .i32
          (destinationIndex.val + count.val - 1) = some lastDestination
        rw [hlastDestinationValue]
        exact addressLiteralOfNat?_val _ _
      have hlastSourceValue :
          sourceIndex.val + count.val - 1 = lastSource.val := by
        omega
      have hlastSourceOption : u32? (sourceIndex.val + count.val - 1) =
          some lastSource := by
        change addressLiteralOfNat? .i32 (sourceIndex.val + count.val - 1) =
          some lastSource
        rw [hlastSourceValue]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : count.val - 1 = nextCount.val := by omega
      have hnextCountOption : u32? (count.val - 1) = some nextCount := by
        change addressLiteralOfNat? .i32 (count.val - 1) = some nextCount
        rw [hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr destination)),
          .num ⟨.i32, destinationIndex⟩, .ref (.addr (.arrayAddr source)),
          .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩])
        (instruction := .arrayCopy destinationType sourceType) complete hread
        rfl
      simp only [instructionReadResults, arrayCopyResults]
      apply List.mem_append_right
      rcases hexpand with ⟨hexpand⟩
      split
      · rename_i foundDestination foundSource hfoundDestination hfoundSource
        have hd := Option.some.inj
          (hfoundDestination.symm.trans hdestination)
        subst foundDestination
        have hs := Option.some.inj (hfoundSource.symm.trans hsource)
        subst foundSource
        rw [dif_neg hdestinationIn, dif_neg hsourceIn,
          dif_pos hdestinationIn, dif_pos hsourceIn, dif_neg hnonzero]
        split
        · rename_i hnone
          rw [htype] at hnone
          contradiction
        · rename_i foundType hfoundType
          have ht := Option.some.inj (hfoundType.symm.trans htype)
          subst foundType
          split
          · rename_i foundFieldType hfoundFieldType
            have hf := Option.some.inj (hfoundFieldType.symm.trans hexpand)
            injection hf with hf
            subst foundFieldType
            split
            · rename_i hnone
              rw [hextension] at hnone
              contradiction
            · rename_i foundExtension hfoundExtension
              have he := Option.some.inj
                (hfoundExtension.symm.trans hextension)
              subst foundExtension
              rw [dif_neg horder]
              split
              · rename_i foundDestination foundSource foundCount
                  hfoundDestination hfoundSource hfoundCount
                have hld := Option.some.inj
                  (hfoundDestination.symm.trans hlastDestinationOption)
                subst foundDestination
                have hls := Option.some.inj
                  (hfoundSource.symm.trans hlastSourceOption)
                subst foundSource
                have hnc := Option.some.inj
                  (hfoundCount.symm.trans hnextCountOption)
                subst foundCount
                apply List.mem_singleton.mpr
                apply StepAResult.eq_of_event_next <;> rfl
              · rename_i hmissing
                exact False.elim
                  (hmissing lastDestination lastSource nextCount
                    hlastDestinationOption hlastSourceOption hnextCountOption)
          · simp_all
      · rename_i hbad
        exact False.elim
          (hbad destinationArray sourceArray hdestination hsource)

theorem arrayInitElemOob1_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitElemOob1 is is') :
    (.read .arrayInitElemOob1 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitElemOob1 address arrayIndex elemIndex count typeIndex
      segmentIndex array harray hoob =>
      have hread := Step_read.arrayInitElemOob1
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (j := elemIndex) (x := typeIndex) (y := segmentIndex)
        harray hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)),
          .num ⟨.i32, arrayIndex⟩, .num ⟨.i32, elemIndex⟩,
          .num ⟨.i32, count⟩])
        (instruction := .arrayInitElem typeIndex segmentIndex) complete hread
        rfl
      simp only [instructionReadResults, arrayInitElemResults]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      split
      · rename_i hnone
        rw [harray] at hnone
        contradiction
      · rename_i foundArray hfoundArray
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayInitElemOob2_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitElemOob2 is is') :
    (.read .arrayInitElemOob2 (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitElemOob2 address arrayIndex elemIndex count typeIndex
      segmentIndex elem helem hoob =>
      have hread := Step_read.arrayInitElemOob2
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (a := address) (i := arrayIndex) (x := typeIndex) helem hoob
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)),
          .num ⟨.i32, arrayIndex⟩, .num ⟨.i32, elemIndex⟩,
          .num ⟨.i32, count⟩])
        (instruction := .arrayInitElem typeIndex segmentIndex) complete hread
        rfl
      simp only [instructionReadResults, arrayInitElemResults]
      apply List.mem_append_left
      apply List.mem_append_right
      split
      · rename_i hnone
        rw [helem] at hnone
        contradiction
      · rename_i foundElem hfoundElem
        have he := Option.some.inj (hfoundElem.symm.trans helem)
        subst foundElem
        rw [dif_pos hoob]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl

theorem arrayInitElemZero_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitElemZero is is') :
    (.read .arrayInitElemZero (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitElemZero address arrayIndex elemIndex count typeIndex
      segmentIndex array elem harray helem harrayIn helemIn hzero =>
      have hread := Step_read.arrayInitElemZero
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x := typeIndex)
        harray helem harrayIn helemIn hzero
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)),
          .num ⟨.i32, arrayIndex⟩, .num ⟨.i32, elemIndex⟩,
          .num ⟨.i32, count⟩])
        (instruction := .arrayInitElem typeIndex segmentIndex) complete hread
        rfl
      simp only [instructionReadResults, arrayInitElemResults]
      apply List.mem_append_right
      split
      · rename_i foundArray foundElem hfoundArray hfoundElem
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        have he := Option.some.inj (hfoundElem.symm.trans helem)
        subst foundElem
        rw [dif_neg harrayIn, dif_neg helemIn,
          dif_pos harrayIn, dif_pos helemIn, dif_pos hzero]
        apply List.mem_singleton.mpr
        apply StepAResult.eq_of_event_next <;> rfl
      · rename_i hbad
        exact False.elim (hbad array elem harray helem)

theorem arrayInitElemSucc_mem_completeReadSuccessorsOf
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .arrayInitElemSucc is is') :
    (.read .arrayInitElemSucc (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @arrayInitElemSucc address arrayIndex elemIndex count nextArray nextElem
      nextCount typeIndex segmentIndex array elem reference harray helem
      harrayIn helemIn hnonzero href hnextArray hnextElem hnextCount =>
      have hread := Step_read.arrayInitElemSucc
        (authority := amendedExecutionAuthority) (Nm := releasedNumerics)
        (x := typeIndex) harray helem harrayIn helemIn hnonzero href
        hnextArray hnextElem hnextCount
      have hnextArrayOption : u32? (arrayIndex.val + 1) =
          some nextArray := by
        change addressLiteralOfNat? .i32 (arrayIndex.val + 1) =
          some nextArray
        rw [← hnextArray]
        exact addressLiteralOfNat?_val _ _
      have hnextElemOption : u32? (elemIndex.val + 1) = some nextElem := by
        change addressLiteralOfNat? .i32 (elemIndex.val + 1) = some nextElem
        rw [← hnextElem]
        exact addressLiteralOfNat?_val _ _
      have hnextCountValue : count.val - 1 = nextCount.val := by omega
      have hnextCountOption : u32? (count.val - 1) = some nextCount := by
        change addressLiteralOfNat? .i32 (count.val - 1) = some nextCount
        rw [hnextCountValue]
        exact addressLiteralOfNat?_val _ _
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := [.ref (.addr (.arrayAddr address)),
          .num ⟨.i32, arrayIndex⟩, .num ⟨.i32, elemIndex⟩,
          .num ⟨.i32, count⟩])
        (instruction := .arrayInitElem typeIndex segmentIndex) complete hread
        rfl
      simp only [instructionReadResults, arrayInitElemResults]
      apply List.mem_append_right
      split
      · rename_i foundArray foundElem hfoundArray hfoundElem
        have ha := Option.some.inj (hfoundArray.symm.trans harray)
        subst foundArray
        have he := Option.some.inj (hfoundElem.symm.trans helem)
        subst foundElem
        rw [dif_neg harrayIn, dif_neg helemIn,
          dif_pos harrayIn, dif_pos helemIn, dif_neg hnonzero]
        split
        · rename_i foundReference foundArrayIndex foundElemIndex foundCount
            hfoundReference hfoundArrayIndex hfoundElemIndex hfoundCount
          have hr := Option.some.inj (hfoundReference.symm.trans href)
          subst foundReference
          have hai := Option.some.inj
            (hfoundArrayIndex.symm.trans hnextArrayOption)
          subst foundArrayIndex
          have hei := Option.some.inj
            (hfoundElemIndex.symm.trans hnextElemOption)
          subst foundElemIndex
          have hnc := Option.some.inj
            (hfoundCount.symm.trans hnextCountOption)
          subst foundCount
          apply List.mem_singleton.mpr
          apply StepAResult.eq_of_event_next <;> rfl
        · rename_i hmissing
          exact False.elim
            (hmissing reference nextArray nextElem nextCount href
              hnextArrayOption hnextElemOption hnextCountOption)
      · rename_i hbad
        exact False.elim (hbad array elem harray helem)

end WasmGemmGnaf.Wasm.Core.Exec
