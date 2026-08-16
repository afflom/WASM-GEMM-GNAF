import WasmGemmGnaf.GNAF.CompilePublic

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Packaging direct GNAF lowering as a public amended-Core module

The encoder-section proofs below turn the source-side budget from
`CompilePublic.lean` into a concrete amended binary derivation.  Only after
that derivation is complete does this module expose `GNAF.compile` at the
public `Wasm.Module` carrier.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectEncoding

theorem allLocalEq_replicate_self (l : Wasm.Core.Local) : ∀ n : Nat,
    Wasm.Core.Binary.allLocalEq l (List.replicate n l) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Wasm.Core.Binary.allLocalEq, ih]

theorem localRuns_replicate (l : Wasm.Core.Local) : ∀ n : Nat,
    Wasm.Core.Binary.localRuns (List.replicate n l) =
      if n = 0 then [] else [List.replicate n l] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, Wasm.Core.Binary.localRuns, ih]
      by_cases hn : n = 0
      · subst n
        rfl
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp [Wasm.Core.Binary.prependLocalRun, List.replicate_succ]

theorem lebU_u32_nat_length_le (n : Nat) (h : n < 2 ^ 32) :
    (Wasm.Core.Binary.lebU n).length ≤ 5 := by
  exact lebU_u32_length_le ⟨n, h⟩

theorem compiled_funcBody_encoded (locals : Nat) (body : List Wasm.Core.Instr)
    (hlocals : locals < 2 ^ 32)
    {bodyBytes : Wasm.Core.Binary.Bytes}
    (hbody : @Wasm.Core.Binary.encInstrs Wasm.Core.Binary.amendedBinaryAuthority
      (Wasm.Core.InstrSeq.ofList body) = some bodyBytes) :
    ∃ payload,
      @Wasm.Core.Binary.encFuncBody Wasm.Core.Binary.amendedBinaryAuthority
        (List.replicate locals { valtype := .num .i64 },
          Wasm.Core.InstrSeq.ofList body) = some payload ∧
      payload.length ≤ bodyBytes.length + 8 := by
  cases locals with
  | zero =>
      refine ⟨Wasm.Core.Binary.lebU 0 ++
          (bodyBytes ++ [Wasm.Core.Binary.tb 0x0B]), ?_, ?_⟩
      · simp [Wasm.Core.Binary.encFuncBody, Wasm.Core.Binary.localRuns,
          Wasm.Core.Binary.encList, Wasm.Core.Binary.encRep,
          Wasm.Core.Binary.encExpr, Wasm.Core.Binary.catO, hbody]
      · have hz : (Wasm.Core.Binary.lebU 0).length = 1 := by decide
        simp [hz]
        omega
  | succ n =>
      have hcount : n + 1 < 2 ^ 32 := by omega
      have hleb := lebU_u32_nat_length_le (n + 1) hcount
      refine ⟨Wasm.Core.Binary.lebU 1 ++
          (Wasm.Core.Binary.lebU (n + 1) ++ [Wasm.Core.Binary.tb 0x7E]) ++
          (bodyBytes ++ [Wasm.Core.Binary.tb 0x0B]), ?_, ?_⟩
      · simp only [Wasm.Core.Binary.encFuncBody]
        simp only [List.length_replicate]
        rw [if_pos hcount]
        rw [localRuns_replicate]
        rw [if_neg (by omega : n + 1 ≠ 0)]
        simp [Wasm.Core.Binary.encList, Wasm.Core.Binary.encRep,
          Wasm.Core.Binary.encLocalRun, allLocalEq_replicate_self,
          Wasm.Core.Binary.encExpr, Wasm.Core.Binary.catO, hbody, hcount,
          List.replicate_succ, Wasm.Core.Binary.encValType,
          Wasm.Core.Binary.encNumType]
      · have hone : (Wasm.Core.Binary.lebU 1).length = 1 := by decide
        simp only [List.length_append, List.length_singleton, hone]
        omega

theorem compiled_codeSection_encoded (locals : Nat) (body : List Wasm.Core.Instr)
    (hlocals : locals < 2 ^ 32)
    {bodyBytes : Wasm.Core.Binary.Bytes}
    (hbody : @Wasm.Core.Binary.encInstrs Wasm.Core.Binary.amendedBinaryAuthority
      (Wasm.Core.InstrSeq.ofList body) = some bodyBytes)
    (hlimit : bodyBytes.length + 32 < 2 ^ 32) :
    EncoderHasValue
      (@Wasm.Core.Binary.encCodeSec Wasm.Core.Binary.amendedBinaryAuthority
        [(List.replicate locals { valtype := .num .i64 },
          Wasm.Core.InstrSeq.ofList body)]) := by
  obtain ⟨payload, hpayload, hpayloadLen⟩ :=
    compiled_funcBody_encoded locals body hlocals hbody
  have hpayloadLt : payload.length < 2 ^ 32 := by omega
  have hlebPayload := lebU_u32_nat_length_le payload.length hpayloadLt
  let codeBytes := Wasm.Core.Binary.lebU payload.length ++ payload
  have hcodeBytes : codeBytes.length ≤ payload.length + 5 := by
    simp only [codeBytes, List.length_append]
    omega
  let sectionPayload := Wasm.Core.Binary.lebU 1 ++ codeBytes
  have hone : (Wasm.Core.Binary.lebU 1).length = 1 := by decide
  have hsectionPayload : sectionPayload.length < 2 ^ 32 := by
    simp only [sectionPayload, List.length_append, hone]
    omega
  refine ⟨Wasm.Core.Binary.tb 10 ::
      (Wasm.Core.Binary.lebU sectionPayload.length ++ sectionPayload), ?_⟩
  simp [Wasm.Core.Binary.encCodeSec, Wasm.Core.Binary.encListSection,
    Wasm.Core.Binary.encList, Wasm.Core.Binary.encRep, Wasm.Core.Binary.encCode,
    Wasm.Core.Binary.encSized, Wasm.Core.Binary.encSectionBody, hpayload,
    hpayloadLt, codeBytes, sectionPayload,
    Wasm.Core.Binary.catO]
  omega

theorem compileCore_encodable {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.Binary.encodableA (compileCore checked) = true := by
  let env := envOf checked.inputSig checked.plan
  let body := bodyCode env checked.inputSig.scratch checked.plan
  have represented :
      max checked.plan.coreImmediateCeiling
          (max (3 + checked.inputSig.regs + checked.plan.depth)
            (checked.plan.coreLayoutBytes checked.inputSig)) < 2 ^ 32 ∧
        checked.plan.coreLayoutPages checked.inputSig ≤ P.body.maxPages ∧
        checked.plan.coreLayoutPages checked.inputSig ≤ G.body.resources.maxPages ∧
        checked.inputSig.regs + checked.plan.depth + 2 ≤ P.body.limits.maxLocals ∧
        checked.plan.coreModuleByteBudget < 2 ^ 32 ∧
        checked.plan.coreModuleByteBudget ≤ P.body.limits.maxModuleBytes ∧
        checked.plan.charges.dataBytes ≤ G.body.resources.maxInvocationBytes ∧
        checked.inputSig.tables * checked.plan.tableWords ≤
          G.body.resources.maxTableElements := by
    exact of_decide_eq_true checked.coreRepresentable
  have hinner :
      max (3 + checked.inputSig.regs + checked.plan.depth)
          (checked.plan.coreLayoutBytes checked.inputSig) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) represented.1
  have hlocalIndex :
      3 + checked.inputSig.regs + checked.plan.depth < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hinner
  have hlocals : env.declaredLocals < 2 ^ 32 := by
    simp only [env, envOf, CompileEnv.declaredLocals]
    omega
  obtain ⟨bodyBytes, hbodyBytes, hbodyBytesLen⟩ :=
    DirectEncoding.bodyCode_encoded env checked.inputSig.scratch checked.plan
  have hcodeSize := DirectEncoding.code_size_le env checked.plan 0
    checked.inputSig.scratch
  have hbodySize : DirectEncoding.seqSize body ≤ checked.plan.codeBudget + 4 := by
    simp only [body, bodyCode, DirectEncoding.seqSize_append]
    have hstatus :
        DirectEncoding.seqSize [localGet env.statusLocal, wrapI64] = 4 := by
      simp
    omega
  have hbodyLimit : bodyBytes.length + 32 < 2 ^ 32 := by
    have hmoduleLimit := represented.2.2.2.2.1
    change 32 * (checked.plan.codeBudget + 4) + 4096 < 2 ^ 32 at hmoduleLimit
    unfold DirectEncoding.seqSize at hbodySize
    simp only [body] at hbodySize
    omega
  have hcode : EncoderHasValue
      (@Wasm.Core.Binary.encCodeSec Wasm.Core.Binary.amendedBinaryAuthority
        (Wasm.Core.Binary.funcCodes (moduleOf env body).funcs)) := by
    simpa [moduleOf, Wasm.Core.Binary.funcCodes] using
      (DirectEncoding.compiled_codeSection_encoded env.declaredLocals body hlocals
        hbodyBytes hbodyLimit)
  have henc := moduleOf_encodable env body (moduleOf_dataCount_encoded env body) hcode
  simpa [compileCore, env, body] using henc

end DirectEncoding

/-- The direct Core AST of every source-checked plan is concretely encodable
under the amended Core binary grammar. -/
theorem compileCore_encodable {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.Binary.encodableA (compileCore checked) = true :=
  DirectEncoding.compileCore_encodable checked

/-- **SPEC §11.4.** Compile a profile/problem-indexed checked GNAF plan
directly to the public representable amended-Core carrier. -/
def compile {P : Wasm.Profile} {G : Gemm.Problem P} :
    CheckedPlan P G → Wasm.Module :=
  fun checked => Wasm.Module.ofEncodableCore (compileCore checked)
    (compileCore_encodable checked)

@[simp] theorem compile_core {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    (compile checked).core = compileCore checked := rfl

/-- Public compilation is deterministic as a function of its checked source. -/
theorem compile_deterministic {P : Wasm.Profile} {G : Gemm.Problem P}
    (a b : CheckedPlan P G) (h : a = b) : compile a = compile b := by
  rw [h]

end WasmGemmGnaf.GNAF
