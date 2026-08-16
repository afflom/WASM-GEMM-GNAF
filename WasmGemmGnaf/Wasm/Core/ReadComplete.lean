import WasmGemmGnaf.Wasm.Core.ReadSuccessors

/-! Completeness of the executable store-reading successor layer. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem StepAResult.eq_of_event_next {source : Config}
    (left right : StepAResult source) (hevent : left.event = right.event)
    (hnext : left.next = right.next) : left = right := by
  cases left with
  | mk leftEvent leftNext leftStep =>
      cases right with
      | mk rightEvent rightNext rightStep =>
          simp only at hevent hnext
          subst rightEvent
          subst rightNext
          rfl

@[simp] theorem StepAResult.castSource_event {source rebuilt : Config}
    (result : StepAResult source) (h : source = rebuilt) :
    (result.castSource h).event = result.event := by
  subst rebuilt
  rfl

@[simp] theorem StepAResult.castSource_next {source rebuilt : Config}
    (result : StepAResult source) (h : source = rebuilt) :
    (result.castSource h).next = result.next := by
  subst rebuilt
  rfl

/-- The maximal value-prefix split together with its reconstruction proof. -/
structure CertifiedValueSplit (source : List AdminInstr) where
  values : List Val
  tail : List AdminInstr
  rebuild : source = vals values ++ tail

/-- Compute the canonical value-prefix split and retain its source equation. -/
def certifiedValueSplit (source : List AdminInstr) :
    CertifiedValueSplit source :=
  { values := (splitVals source).1
    tail := (splitVals source).2
    rebuild := (splitVals_append source).symm }

theorem CertifiedValueSplit.eq_of_values_tail {source : List AdminInstr}
    (left right : CertifiedValueSplit source)
    (hvalues : left.values = right.values) (htail : left.tail = right.tail) :
    left = right := by
  cases left with
  | mk leftValues leftTail leftRebuild =>
      cases right with
      | mk rightValues rightTail rightRebuild =>
          simp only at hvalues htail
          subst rightValues
          subst rightTail
          rfl

theorem certifiedValueSplit_vals_append_nonval (values : List Val)
    {instruction : AdminInstr} (hnonvalue : adminToVal instruction = none)
    (tail : List AdminInstr) :
    certifiedValueSplit (vals values ++ instruction :: tail) =
      { values := values, tail := instruction :: tail, rebuild := rfl } := by
  apply CertifiedValueSplit.eq_of_values_tail
  · simp [certifiedValueSplit,
      splitVals_vals_append_nonval values hnonvalue tail]
  · simp [certifiedValueSplit,
      splitVals_vals_append_nonval values hnonvalue tail]

/-- Run both instruction-reading layers from a supplied proof-carrying split. -/
def instructionReadResultsFromSplit (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) {source : List AdminInstr}
    (split : CertifiedValueSplit source) :
    List (StepAResult (z, source)) :=
  match htail : split.tail with
  | [.plain instruction] =>
      (instructionReadResults z split.values instruction ++
        referenceInstructionReadResults fuel z complete split.values
          instruction).map fun result =>
        result.castSource (by
          apply Prod.ext
          · rfl
          · calc
              vals split.values ++ [.plain instruction] =
                  vals split.values ++ split.tail := by rw [htail]
              _ = source := split.rebuild.symm)
  | _ => []

/-- Run both instruction-reading layers from the canonical split.  This has
the same executable projection as `splitVals`, while its separate helper makes
the canonicity theorem directly reusable by completeness proofs. -/
def certifiedInstructionReadResults (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) (source : List AdminInstr) :
    List (StepAResult (z, source)) :=
  instructionReadResultsFromSplit fuel z complete
    (certifiedValueSplit source)

/-- Recover `return_call_ref` escaping a label from a supplied certified
value-prefix split of the label body.  Keeping the reconstruction equality in
the split avoids dependent rewriting through the legacy raw `splitVals`
enumerator. -/
def returnCallRefLabelResultsFromSplit (z : State) (arity : Nat)
    (continuation : List AdminInstr) {body : List AdminInstr}
    (split : CertifiedValueSplit body) :
    List (StepAResult (z, [.label arity continuation body])) :=
  match htail : split.tail with
  | .plain (.returnCallRef typeUse) :: suffix =>
      [(readResult .returnCallRefLabel
          (Step_read.returnCallRefLabel
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (k := arity)
            (cont := continuation) (vs := split.values) (yy := typeUse)
            (is := suffix)))
        |>.castSource (by
          apply Prod.ext
          · rfl
          · apply congrArg (fun inner =>
              [AdminInstr.label arity continuation inner])
            calc
              vals split.values ++ [.plain (.returnCallRef typeUse)] ++
                    suffix =
                  vals split.values ++ split.tail := by
                    rw [htail]
                    simp [List.append_assoc]
              _ = body := split.rebuild.symm)]
  | _ => []

/-- Recover `return_call_ref` escaping a handler from a supplied certified
value-prefix split of the handler body. -/
def returnCallRefHandlerResultsFromSplit (z : State) (arity : Nat)
    (catches : List Catch) {body : List AdminInstr}
    (split : CertifiedValueSplit body) :
    List (StepAResult (z, [.handler arity catches body])) :=
  match htail : split.tail with
  | .plain (.returnCallRef typeUse) :: suffix =>
      [(readResult .returnCallRefHandler
          (Step_read.returnCallRefHandler
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (k := arity)
            (cs := catches) (vs := split.values) (yy := typeUse)
            (is := suffix)))
        |>.castSource (by
          apply Prod.ext
          · rfl
          · apply congrArg (fun inner =>
              [AdminInstr.handler arity catches inner])
            calc
              vals split.values ++ [.plain (.returnCallRef typeUse)] ++
                    suffix =
                  vals split.values ++ split.tail := by
                    rw [htail]
                    simp [List.append_assoc]
              _ = body := split.rebuild.symm)]
  | _ => []

/-- Recover the null callee branch of `return_call_ref` at a frame from a
certified split of the frame body. -/
def returnCallRefFrameNullResultsFromSplit (z : State) (arity : Nat)
    (frame : Frame) {body : List AdminInstr}
    (split : CertifiedValueSplit body) :
    List (StepAResult (z, [.frame arity frame body])) :=
  match htail : split.tail with
  | .plain (.returnCallRef typeUse) :: suffix =>
      match hlast : splitLastValue? split.values with
      | some (initial, .ref (.null heapType)) =>
          [(readResult .returnCallRefFrameNull
              (Step_read.returnCallRefFrameNull
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) (z := z) (k := arity)
                (f := frame) (vs := initial) (ht := heapType)
                (yy := typeUse) (is := suffix)))
            |>.castSource (by
              apply Prod.ext
              · rfl
              · apply congrArg (fun inner =>
                  [AdminInstr.frame arity frame inner])
                have hprefix : split.values =
                    initial ++ [.ref (.null heapType)] :=
                  splitLastValue?_eq_append hlast
                calc
                  vals initial ++ [Ref.toAdmin (.null heapType),
                        .plain (.returnCallRef typeUse)] ++ suffix =
                      vals split.values ++ split.tail := by
                    rw [hprefix, htail]
                    simp [vals, Ref.toAdmin, Val.toAdmin, List.map_append,
                      List.append_assoc]
                  _ = body := split.rebuild.symm)]
      | _ => []
  | _ => []

/-- Recover the function-address branch of `return_call_ref` at a frame from
a certified split of the frame body. -/
def returnCallRefFrameAddrResultsFromSplit (z : State) (arity : Nat)
    (frame : Frame) {body : List AdminInstr}
    (split : CertifiedValueSplit body) :
    List (StepAResult (z, [.frame arity frame body])) :=
  match htail : split.tail with
  | .plain (.returnCallRef typeUse) :: suffix =>
      match hlast : splitLastValue? split.values with
      | some (beforeAddress, .ref (.addr (.funcAddr address))) =>
          match hfunc : z.funcinst[address]? with
          | none => []
          | some function =>
              match hexpand : expandDt function.type with
              | some (.func domain codomain) =>
                  if hfits : domain.length ≤ beforeAddress.length then
                    let cut := beforeAddress.length - domain.length
                    let discarded := beforeAddress.take cut
                    let arguments := beforeAddress.drop cut
                    have harguments : arguments.length = domain.length := by
                      simp only [arguments, cut, List.length_drop]
                      omega
                    [(readResult .returnCallRefFrameAddr
                        (Step_read.returnCallRefFrameAddr
                          (authority := amendedExecutionAuthority)
                          (Nm := releasedNumerics) (z := z) (k := arity)
                          (f := frame) (vs' := discarded) (vs := arguments)
                          (a := address) (yy := typeUse) (is := suffix)
                          (fi := function) (t₁ := domain) (t₂ := codomain)
                          (n := domain.length) (m := codomain.length)
                          hfunc (.mk hexpand) rfl rfl harguments))
                      |>.castSource (by
                        apply Prod.ext
                        · rfl
                        · apply congrArg (fun inner =>
                            [AdminInstr.frame arity frame inner])
                          have hbefore : discarded ++ arguments =
                              beforeAddress :=
                            List.take_append_drop cut beforeAddress
                          have hprefix : split.values =
                              beforeAddress ++
                                [.ref (.addr (.funcAddr address))] :=
                            splitLastValue?_eq_append hlast
                          have hprefix' : split.values =
                              (discarded ++ arguments) ++
                                [.ref (.addr (.funcAddr address))] := by
                            rw [hbefore]
                            exact hprefix
                          calc
                            vals discarded ++ vals arguments ++
                                  [.addrref (.funcAddr address),
                                    .plain (.returnCallRef typeUse)] ++ suffix =
                                vals split.values ++ split.tail := by
                              rw [hprefix', htail]
                              simp [vals, Val.toAdmin, List.map_append,
                                List.append_assoc]
                            _ = body := split.rebuild.symm)]
                  else []
              | _ => []
      | _ => []
  | _ => []

/-- Recover propagation of `throw_ref` across surrounding instructions from
a certified split of the entire instruction sequence. -/
def throwRefInstrResultsFromSplit (z : State) {body : List AdminInstr}
    (split : CertifiedValueSplit body) : List (StepAResult (z, body)) :=
  match htail : split.tail with
  | .plain .throwRef :: suffix =>
      match hlast : splitLastValue? split.values with
      | some (initial, .ref (.addr (.exnAddr address))) =>
          if hnonempty : initial ≠ [] ∨ suffix ≠ [] then
            [(readResult .throwRefInstrs
                (Step_read.throwRefInstrs
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) (z := z) (vs := initial)
                  (a := address) (is := suffix) hnonempty))
              |>.castSource (by
                apply Prod.ext
                · rfl
                · have hprefix : split.values =
                      initial ++ [.ref (.addr (.exnAddr address))] :=
                    splitLastValue?_eq_append hlast
                  calc
                    vals initial ++ [.addrref (.exnAddr address),
                          .plain .throwRef] ++ suffix =
                        vals split.values ++ split.tail := by
                      rw [hprefix, htail]
                      simp [vals, Val.toAdmin, List.map_append,
                        List.append_assoc]
                    _ = body := split.rebuild.symm)]
          else []
      | _ => []
  | _ => []

/-- Canonical proof-carrying wrapper reads.  This supplements, rather than
replaces, the legacy structural enumerator, so every pre-existing executable
successor remains present. -/
def certifiedWrapperReadResults (z : State) (source : List AdminInstr) :
    List (StepAResult (z, source)) :=
  throwRefInstrResultsFromSplit z (certifiedValueSplit source) ++
    match source with
    | [.label arity continuation body] =>
        returnCallRefLabelResultsFromSplit z arity continuation
          (certifiedValueSplit body)
    | [.handler arity catches body] =>
        returnCallRefHandlerResultsFromSplit z arity catches
          (certifiedValueSplit body)
    | [.frame arity frame body] =>
        returnCallRefFrameNullResultsFromSplit z arity frame
            (certifiedValueSplit body) ++
          returnCallRefFrameAddrResultsFromSplit z arity frame
            (certifiedValueSplit body)
    | _ => []

/-- Complete proof-carrying read results: retain every result emitted by the
existing sound layer, then add the certified canonical instruction split used
by completeness proofs. -/
def completeReadResultsOf (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) (source : List AdminInstr) :
    List (StepAResult (z, source)) :=
  readResultsOf fuel z complete source ++
    (certifiedInstructionReadResults fuel z complete source ++
      certifiedWrapperReadResults z source)

def completeReadSuccessorsOf (fuel : Nat) (config : Config)
    (complete : RefMatchCompleteAt fuel config.1) : List (Event × Config) :=
  (completeReadResultsOf fuel config.1 complete config.2).map
    StepAResult.toPair

theorem mem_completeReadSuccessorsOf_stepA {fuel : Nat} {config : Config}
    (complete : RefMatchCompleteAt fuel config.1) {event : Event}
    {next : Config}
    (hmem : (event, next) ∈ completeReadSuccessorsOf fuel config complete) :
    StepA config event next := by
  rcases config with ⟨z, instructions⟩
  simp only [completeReadSuccessorsOf, List.mem_map] at hmem
  obtain ⟨result, _, heq⟩ := hmem
  rcases result with ⟨emitted, successor, hstep⟩
  simp only [StepAResult.toPair, Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact hstep

theorem mem_completeReadSuccessorsOf_of_mem_readSuccessorsOf
    {fuel : Nat} {config : Config}
    (complete : RefMatchCompleteAt fuel config.1) {edge : Event × Config}
    (hmem : edge ∈ readSuccessorsOf fuel config complete) :
    edge ∈ completeReadSuccessorsOf fuel config complete := by
  rcases config with ⟨state, instructions⟩
  unfold readSuccessorsOf at hmem
  unfold completeReadSuccessorsOf
  simp only [List.mem_map] at hmem ⊢
  obtain ⟨result, hresult, rfl⟩ := hmem
  refine ⟨result, ?_, rfl⟩
  unfold completeReadResultsOf
  exact List.mem_append_left _ hresult

theorem mem_completeReadSuccessorsOf_of_instruction
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    (values : List Val) (instruction : Instr)
    (hnonvalue : adminToVal (AdminInstr.plain instruction) = none)
    {result : StepAResult
      (z, vals values ++ [AdminInstr.plain instruction])}
    (hresult : result ∈ instructionReadResults z values instruction ∨
      result ∈ referenceInstructionReadResults fuel z complete values
        instruction) :
    result.toPair ∈ completeReadSuccessorsOf fuel
      (z, vals values ++ [AdminInstr.plain instruction]) complete := by
  unfold completeReadSuccessorsOf
  simp only [List.mem_map]
  refine ⟨result, ?_, rfl⟩
  unfold completeReadResultsOf
  apply List.mem_append_right
  apply List.mem_append_left
  unfold certifiedInstructionReadResults
  rw [certifiedValueSplit_vals_append_nonval values hnonvalue []]
  unfold instructionReadResultsFromSplit
  simp only
  apply List.mem_map.mpr
  refine ⟨result, ?_, ?_⟩
  · exact List.mem_append.mpr hresult
  · apply StepAResult.eq_of_event_next <;> rfl

inductive ReferenceInstruction : Instr → Prop where
  | brOnCast (label : LabelIdx) (sourceType targetType : RefType) :
      ReferenceInstruction (.brOnCast label sourceType targetType)
  | brOnCastFail (label : LabelIdx) (sourceType targetType : RefType) :
      ReferenceInstruction (.brOnCastFail label sourceType targetType)
  | refTest (referenceType : RefType) :
      ReferenceInstruction (.refTest referenceType)
  | refCast (referenceType : RefType) :
      ReferenceInstruction (.refCast referenceType)

theorem mem_readSuccessorsOf_of_mem_reference {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) (reference : Ref)
    (instruction : Instr) (hshape : ReferenceInstruction instruction)
    {result : StepAResult
      (z, vals [.ref reference] ++ [AdminInstr.plain instruction])}
    (hresult : result ∈ referenceInstructionReadResults fuel z complete
      [.ref reference] instruction) :
    result.toPair ∈ readSuccessorsOf fuel
      (z, vals [.ref reference] ++ [AdminInstr.plain instruction]) complete := by
  unfold readSuccessorsOf
  simp only [List.mem_map]
  refine ⟨result, ?_, rfl⟩
  unfold readResultsOf
  apply List.mem_append_right
  cases hshape <;> cases reference <;>
    simp [splitReferenceInstructionReadResults, splitVals, adminToVal,
      Val.toAdmin] <;>
    refine List.mem_map.mpr ⟨result, hresult, ?_⟩ <;>
    apply StepAResult.eq_of_event_next <;> rfl

theorem brOnCastSucceed_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z)
    {is is' : List AdminInstr}
    (h : Step_readA z .brOnCastSucceed is is') :
    (.read .brOnCastSucceed (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @brOnCastSucceed reference label sourceType targetType actual href hsub =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod targetType) = true :=
        complete ⟨actual, href, hsub⟩
      let result : StepAResult
          (z, [reference.toAdmin,
            .plain (.brOnCast label sourceType targetType)]) :=
        readResult .brOnCastSucceed
          (Step_read.brOnCastSucceed
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) href hsub)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.brOnCast label sourceType targetType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.brOnCast label sourceType targetType)
          (.brOnCast label sourceType targetType) hresult

theorem brOnCastFail_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .brOnCastFail is is') :
    (.read .brOnCastFail (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @brOnCastFail reference label sourceType targetType hnone =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod targetType) ≠ true := by
        intro htrue
        exact hnone (refMatchesN_sound htrue)
      let result : StepAResult
          (z, [reference.toAdmin,
            .plain (.brOnCast label sourceType targetType)]) :=
        readResult .brOnCastFail
          (Step_read.brOnCastFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hnone)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.brOnCast label sourceType targetType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.brOnCast label sourceType targetType)
          (.brOnCast label sourceType targetType) hresult

theorem brOnCastFailSucceed_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .brOnCastFailSucceed is is') :
    (.read .brOnCastFailSucceed (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @brOnCastFailSucceed reference label sourceType targetType actual href hsub =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod targetType) = true :=
        complete ⟨actual, href, hsub⟩
      let result : StepAResult
          (z, [reference.toAdmin,
            .plain (.brOnCastFail label sourceType targetType)]) :=
        readResult .brOnCastFailSucceed
          (Step_read.brOnCastFailSucceed
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) href hsub)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.brOnCastFail label sourceType targetType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.brOnCastFail label sourceType targetType)
          (.brOnCastFail label sourceType targetType) hresult

theorem brOnCastFailFail_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .brOnCastFailFail is is') :
    (.read .brOnCastFailFail (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @brOnCastFailFail reference label sourceType targetType hnone =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod targetType) ≠ true := by
        intro htrue
        exact hnone (refMatchesN_sound htrue)
      let result : StepAResult
          (z, [reference.toAdmin,
            .plain (.brOnCastFail label sourceType targetType)]) :=
        readResult .brOnCastFailFail
          (Step_read.brOnCastFailFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hnone)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.brOnCastFail label sourceType targetType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.brOnCastFail label sourceType targetType)
          (.brOnCastFail label sourceType targetType) hresult

theorem refTestTrue_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refTestTrue is is') :
    (.read .refTestTrue (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refTestTrue reference referenceType actual value href hsub hvalue =>
      have heq : value = (⟨1, by omega⟩ : U32) := by
        apply Subtype.ext
        exact hvalue
      rw [heq]
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod referenceType) = true :=
        complete ⟨actual, href, hsub⟩
      let result : StepAResult
          (z, [reference.toAdmin, .plain (.refTest referenceType)]) :=
        readResult .refTestTrue
          (Step_read.refTestTrue
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (c := ⟨1, by omega⟩) href hsub rfl)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.refTest referenceType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.refTest referenceType) (.refTest referenceType) hresult

theorem refTestFalse_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refTestFalse is is') :
    (.read .refTestFalse (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refTestFalse reference referenceType value hnone hvalue =>
      have heq : value = (⟨0, by omega⟩ : U32) := by
        apply Subtype.ext
        exact hvalue
      rw [heq]
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod referenceType) ≠ true := by
        intro htrue
        exact hnone (refMatchesN_sound htrue)
      let result : StepAResult
          (z, [reference.toAdmin, .plain (.refTest referenceType)]) :=
        readResult .refTestFalse
          (Step_read.refTestFalse
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (c := ⟨0, by omega⟩) hnone rfl)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.refTest referenceType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.refTest referenceType) (.refTest referenceType) hresult

theorem refCastSucceed_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refCastSucceed is is') :
    (.read .refCastSucceed (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refCastSucceed reference referenceType actual href hsub =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod referenceType) = true :=
        complete ⟨actual, href, hsub⟩
      let result : StepAResult
          (z, [reference.toAdmin, .plain (.refCast referenceType)]) :=
        readResult .refCastSucceed
          (Step_read.refCastSucceed
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) href hsub)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.refCast referenceType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.refCast referenceType) (.refCast referenceType) hresult

theorem refCastFail_mem_readSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .refCastFail is is') :
    (.read .refCastFail (sourcePlains is), (z, is')) ∈
      readSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @refCastFail reference referenceType hnone =>
      have hmatch : refMatchesN fuel z.store reference
          (instRefType z.frame.mod referenceType) ≠ true := by
        intro htrue
        exact hnone (refMatchesN_sound htrue)
      let result : StepAResult
          (z, [reference.toAdmin, .plain (.refCast referenceType)]) :=
        readResult .refCastFail
          (Step_read.refCastFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) hnone)
      have hresult : result ∈ referenceInstructionReadResults fuel z complete
          [.ref reference] (.refCast referenceType) := by
        simp [referenceInstructionReadResults, hmatch, result]
        apply List.mem_cons.mpr
        left
        apply StepAResult.eq_of_event_next <;> rfl
      simpa [result, StepAResult.toPair, readResult] using
        mem_readSuccessorsOf_of_mem_reference complete reference
          (.refCast referenceType) (.refCast referenceType) hresult

theorem block_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .block is is') :
    (.read .block (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @block values blockType body domain codomain m n htype hdomain hcodomain
      hvalues =>
      let result : StepAResult
          (z, vals values ++ [.plain (.block blockType body)]) :=
        readResult .block
          (Step_read.block
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htype hdomain hcodomain hvalues)
      have hlength : domain.length = values.length := by omega
      have hresult : result ∈ instructionReadResults z values
          (.block blockType body) := by
        simp only [instructionReadResults]
        split
        · rename_i hnone
          rw [htype] at hnone
          contradiction
        · rename_i computedDomain computedCodomain hcomputed
          have hpair := Option.some.inj (hcomputed.symm.trans htype)
          simp only [Prod.mk.injEq] at hpair
          rcases hpair with ⟨rfl, rfl⟩
          split
          · apply List.mem_cons.mpr
            left
            apply StepAResult.eq_of_event_next
            · rfl
            · simp [result, readResult]
              omega
          · rename_i hfalse
            exact False.elim (hfalse hlength)
      simpa [result, StepAResult.toPair, readResult] using
        mem_completeReadSuccessorsOf_of_instruction complete values
          (.block blockType body) rfl (Or.inl hresult)

theorem tableGetOob_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableGetOob is is') :
    (.read .tableGetOob (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableGetOob addressType index tableIndex table htable hoob =>
      let result : StepAResult
          (z, [constAddr addressType index, .plain (.tableGet tableIndex)]) :=
        readResult .tableGetOob
          (Step_read.tableGetOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hoob)
      let address : AddressLiteral := ⟨addressType, index⟩
      let raw : StepAResult
          (z, vals [address.toVal] ++ [.plain (.tableGet tableIndex)]) :=
        readResult .tableGetOob
          (Step_read.tableGetOob
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hoob)
      have hraw : raw ∈ tableGetResults z address tableIndex := by
        unfold tableGetResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i computedTable hcomputed
          have heq := Option.some.inj (hcomputed.symm.trans htable)
          subst computedTable
          split
          · apply List.mem_cons.mpr
            left
            apply StepAResult.eq_of_event_next
            · rfl
            · simp [raw, readResult]
          · rename_i hfalse
            exact False.elim (hfalse (by simpa [address] using hoob))
      have hresult : result ∈ instructionReadResults z
          [.num ⟨addrNumType addressType, addrLitToNum addressType index⟩]
          (.tableGet tableIndex) := by
        cases addressType <;>
          simp only [instructionReadResults, addressLiteral?, addrNumType,
            addrLitToNum]
        all_goals apply List.mem_map.mpr
        all_goals refine ⟨raw, hraw, ?_⟩
        all_goals apply StepAResult.eq_of_event_next <;>
          simp [result, raw, address, AddressLiteral.toAdmin, readResult]
      simpa [result, StepAResult.toPair, readResult] using
        mem_completeReadSuccessorsOf_of_instruction complete
          [.num ⟨addrNumType addressType, addrLitToNum addressType index⟩]
          (.tableGet tableIndex) rfl (Or.inl hresult)

theorem tableGetVal_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .tableGetVal is is') :
    (.read .tableGetVal (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @tableGetVal addressType index tableIndex table reference htable hvalue =>
      let result : StepAResult
          (z, [constAddr addressType index, .plain (.tableGet tableIndex)]) :=
        readResult .tableGetVal
          (Step_read.tableGetVal
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hvalue)
      let address : AddressLiteral := ⟨addressType, index⟩
      let raw : StepAResult
          (z, vals [address.toVal] ++ [.plain (.tableGet tableIndex)]) :=
        readResult .tableGetVal
          (Step_read.tableGetVal
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) htable hvalue)
      have hbound : index.val < table.refs.length := by
        obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hvalue
        exact hbound
      have hraw : raw ∈ tableGetResults z address tableIndex := by
        unfold tableGetResults
        split
        · rename_i hnone
          rw [htable] at hnone
          contradiction
        · rename_i computedTable hcomputed
          have heq := Option.some.inj (hcomputed.symm.trans htable)
          subst computedTable
          split
          · rename_i hoob
            exact False.elim
              (by simpa [address] using (Nat.not_le_of_lt hbound hoob))
          · split
            · rename_i hnone
              rw [hvalue] at hnone
              contradiction
            · rename_i computedReference hcomputedReference
              have href := Option.some.inj
                (hcomputedReference.symm.trans hvalue)
              subst computedReference
              apply List.mem_cons.mpr
              left
              apply StepAResult.eq_of_event_next
              · rfl
              · simp [raw, readResult]
      have hresult : result ∈ instructionReadResults z
          [.num ⟨addrNumType addressType, addrLitToNum addressType index⟩]
          (.tableGet tableIndex) := by
        cases addressType <;>
          simp only [instructionReadResults, addressLiteral?, addrNumType,
            addrLitToNum]
        all_goals apply List.mem_map.mpr
        all_goals refine ⟨raw, hraw, ?_⟩
        all_goals apply StepAResult.eq_of_event_next <;>
          simp [result, raw, address, AddressLiteral.toAdmin, readResult]
      simpa [result, StepAResult.toPair, readResult] using
        mem_completeReadSuccessorsOf_of_instruction complete
          [.num ⟨addrNumType addressType, addrLitToNum addressType index⟩]
          (.tableGet tableIndex) rfl (Or.inl hresult)

/-- Package completeness of one canonical value-prefix instruction result. -/
theorem readResult_mem_completeReadSuccessorsOf_of_instruction
    {fuel : Nat} {z : State} (complete : RefMatchCompleteAt fuel z)
    {rule : ReadRule} {values : List Val} {instruction : Instr}
    {target : List AdminInstr}
    (h : Step_readA z rule
      (vals values ++ [AdminInstr.plain instruction]) target)
    (hnonvalue : adminToVal (AdminInstr.plain instruction) = none)
    (hmem : readResult rule h ∈ instructionReadResults z values instruction) :
    (.read rule
        (sourcePlains (vals values ++ [AdminInstr.plain instruction])),
      (z, target)) ∈ completeReadSuccessorsOf fuel
        (z, vals values ++ [AdminInstr.plain instruction]) complete := by
  simpa [StepAResult.toPair, readResult] using
    mem_completeReadSuccessorsOf_of_instruction complete values instruction
      hnonvalue (Or.inl hmem)

theorem loop_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .loop is is') :
    (.read .loop (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @loop values blockType body domain codomain m n htype hdomain hcodomain
      hvalues =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := values) (instruction := .loop blockType body) complete
        (Step_read.loop (authority := amendedExecutionAuthority)
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

theorem call_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .call is is') :
    (.read .call (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @call functionIndex address function haddress hfunction =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .call functionIndex) complete
        (Step_read.call (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) haddress hfunction) rfl
      simp only [instructionReadResults]
      split
      · split
        · rename_i hnone
          rw [haddress] at hnone
          contradiction
        · rename_i foundAddress hfoundAddress
          have heq := Option.some.inj (hfoundAddress.symm.trans haddress)
          subst foundAddress
          split
          · rename_i hnone
            rw [hfunction] at hnone
            contradiction
          · rename_i foundFunction hfoundFunction
            have heq := Option.some.inj (hfoundFunction.symm.trans hfunction)
            subst foundFunction
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

theorem returnCall_mem_completeReadSuccessorsOf {fuel : Nat} {z : State}
    (complete : RefMatchCompleteAt fuel z) {is is' : List AdminInstr}
    (h : Step_readA z .returnCall is is') :
    (.read .returnCall (sourcePlains is), (z, is')) ∈
      completeReadSuccessorsOf fuel (z, is) complete := by
  cases h with
  | @returnCall functionIndex address function haddress hfunction =>
      apply readResult_mem_completeReadSuccessorsOf_of_instruction
        (values := []) (instruction := .returnCall functionIndex) complete
        (Step_read.returnCall (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) haddress hfunction) rfl
      simp only [instructionReadResults]
      split
      · split
        · rename_i hnone
          rw [haddress] at hnone
          contradiction
        · rename_i foundAddress hfoundAddress
          have heq := Option.some.inj (hfoundAddress.symm.trans haddress)
          subst foundAddress
          split
          · rename_i hnone
            rw [hfunction] at hnone
            contradiction
          · rename_i foundFunction hfoundFunction
            have heq := Option.some.inj (hfoundFunction.symm.trans hfunction)
            subst foundFunction
            apply List.mem_singleton.mpr
            apply StepAResult.eq_of_event_next <;> rfl
      · simp_all

end WasmGemmGnaf.Wasm.Core.Exec
