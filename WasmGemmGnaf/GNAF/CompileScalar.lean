import WasmGemmGnaf.GNAF.Compile

set_option autoImplicit false

/-!
# Syntactic safety of the admitted scalar lowering

The direct compiler is defined on the complete GNAF grammar, while
`CheckedPlan.check?` currently admits only the implemented straight-line
scalar/status fragment.  Its scalar-register writes are observationally dead:
the checker rejects every memory, control, reduction, table, and vector node
that could consume them, while `Accepts` observes memory, effects, and returned
status.  The compiler therefore eliminates those writes and retains only
status construction plus the final result epilogue. This file proves that exact
small Core fragment contains no trap, call, memory, exception, or relaxed
numeric instruction.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectScalar

mutual

/-- The exact Core instruction fragment used by the admitted scalar lowering. -/
def InstrSafe : Wasm.Core.Instr → Bool
  | .const .i32 _ | .const .i64 _ => true
  | .localGet _ | .localSet _ => true
  | .binop .i32 (.int .sub) | .binop .i64 (.int .sub) => true
  | .relop .i32 (.int (.lt .u)) | .relop .i32 (.int (.gt .u)) |
      .relop .i32 (.int (.ge .u)) | .relop .i64 (.int (.lt .u)) |
      .relop .i64 (.int (.gt .u)) | .relop .i64 (.int (.ge .u)) => true
  | .cvtop .i32 .i64 (.ii .wrap) => true
  | _ => false

/-- Every instruction in a Core sequence is in `InstrSafe`, recursively
including structured bodies. -/
def SeqSafe : Wasm.Core.InstrSeq → Bool
  | .nil => true
  | .cons instruction rest => InstrSafe instruction && SeqSafe rest

end

/-- List-facing spelling used by the compiler, whose internal lowering builds
ordinary instruction lists before `InstrSeq.ofList`. -/
def ListSafe (instructions : List Wasm.Core.Instr) : Bool :=
  SeqSafe (Wasm.Core.InstrSeq.ofList instructions)

@[simp] theorem listSafe_nil : ListSafe [] = true := rfl

@[simp] theorem listSafe_cons (instruction : Wasm.Core.Instr)
    (rest : List Wasm.Core.Instr) :
    ListSafe (instruction :: rest) =
      (InstrSafe instruction && ListSafe rest) := rfl

theorem listSafe_append (first second : List Wasm.Core.Instr) :
    ListSafe (first ++ second) = (ListSafe first && ListSafe second) := by
  induction first with
  | nil => simp
  | cons instruction rest ih =>
      change ListSafe (instruction :: (rest ++ second)) =
        ((InstrSafe instruction && ListSafe rest) && ListSafe second)
      rw [listSafe_cons, ih, Bool.and_assoc]

/-! ## Exact profile-family footprint -/

/-- Every feature attributed to an admitted scalar instruction, including its
complete (unstructured) instruction footprint, is the base scalar Core family.  This is stronger than
merely showing that the emitted module avoids one presently rejected feature:
it gives the complete family footprint consumed by profile admission. -/
theorem instrSafe_requiredFeatures_scalar (instruction : Wasm.Core.Instr)
    (safe : InstrSafe instruction = true) :
    ∀ family ∈ instruction.requiredFeatures,
      family = Wasm.FeatureFamily.scalarCore := by
  cases instruction <;>
    simp_all [InstrSafe, Wasm.Core.Instr.requiredFeatures,
      Wasm.Core.Instr.requiredFeature]

/-- Sequence form of `instrSafe_requiredFeatures_scalar`. -/
theorem seqSafe_requiredFeatures_scalar (instructions : Wasm.Core.InstrSeq)
    (safe : SeqSafe instructions = true) :
    ∀ family ∈ instructions.requiredFeatures,
      family = Wasm.FeatureFamily.scalarCore := by
  cases instructions with
  | nil => simp [Wasm.Core.InstrSeq.requiredFeatures]
  | cons instruction rest =>
      simp only [SeqSafe, Bool.and_eq_true] at safe
      intro family membership
      simp only [Wasm.Core.InstrSeq.requiredFeatures, List.mem_append] at membership
      cases membership with
      | inl head => exact instrSafe_requiredFeatures_scalar instruction safe.1 family head
      | inr tail => exact seqSafe_requiredFeatures_scalar rest safe.2 family tail

/-- Every attributed feature of a safe list is exactly scalar Core. -/
theorem listSafe_requiredFeatures_scalar (instructions : List Wasm.Core.Instr)
    (safe : ListSafe instructions = true) :
    ∀ family ∈ (Wasm.Core.InstrSeq.ofList instructions).requiredFeatures,
      family = Wasm.FeatureFamily.scalarCore :=
  seqSafe_requiredFeatures_scalar _ safe

@[simp] theorem constI_safe (value : Nat) : InstrSafe (constI value) = true := rfl

@[simp] theorem constL_safe (value : Nat) : InstrSafe (constL value) = true := rfl

@[simp] theorem localGet_safe (index : Nat) : InstrSafe (localGet index) = true := rfl

@[simp] theorem localSet_safe (index : Nat) : InstrSafe (localSet index) = true := rfl

@[simp] theorem subI_safe : InstrSafe subI = true := rfl

@[simp] theorem ltUI_safe : InstrSafe ltUI = true := rfl

@[simp] theorem gtUI_safe : InstrSafe gtUI = true := rfl

@[simp] theorem geUI_safe : InstrSafe geUI = true := rfl

@[simp] theorem subL_safe : InstrSafe subL = true := rfl

@[simp] theorem ltUL_safe : InstrSafe ltUL = true := rfl

@[simp] theorem gtUL_safe : InstrSafe gtUL = true := rfl

@[simp] theorem geUL_safe : InstrSafe geUL = true := rfl

@[simp] theorem wrapI64_safe : InstrSafe wrapI64 = true := rfl

/-- The executable source admission check excludes every lowering branch that
is not in `DirectScalar.InstrSafe`. -/
theorem code_safe_of_coreSupported {P : Wasm.Profile} {G : Gemm.Problem P}
    {signature : Sig} (environment : CompileEnv) :
    ∀ (plan : Plan) (depth scratch : Nat),
      plan.coreSupported P G signature = true →
        ListSafe (code environment depth scratch plan) = true := by
  intro plan
  induction plan with
  | nop => simp [code]
  | seq first second ihFirst ihSecond =>
      intro depth scratch supported
      simp only [Plan.coreSupported, Bool.and_eq_true] at supported
      rw [code, listSafe_append, ihFirst depth scratch supported.1,
        ihSecond depth scratch supported.2]
      rfl
  | classifyRaw => simp [Plan.coreSupported]
  | dispatchLayout => simp [Plan.coreSupported]
  | branch => simp [Plan.coreSupported]
  | pack => simp [Plan.coreSupported]
  | unpack => simp [Plan.coreSupported]
  | storeReg => simp [Plan.coreSupported]
  | loadReg => simp [Plan.coreSupported]
  | loopNest => simp [Plan.coreSupported]
  | loopReg => simp [Plan.coreSupported]
  | tiled => simp [Plan.coreSupported]
  | reduce => simp [Plan.coreSupported]
  | allocScratch bytes body ih =>
      intro depth scratch supported
      simp only [Plan.coreSupported] at supported
      simpa [code] using ih depth (scratch + bytes) supported
  | setReg =>
      intro depth scratch supported
      rfl
  | scalarOp operation =>
      intro depth scratch supported
      cases operation <;>
        simp [Plan.coreSupported, Plan.coreScalarOpSupported, code] at supported ⊢
  | vectorOp => simp [Plan.coreSupported]
  | emitTable => simp [Plan.coreSupported]
  | tableLoad => simp [Plan.coreSupported]
  | setStatus =>
      intro depth scratch supported
      simp only [code, listSafe_cons, listSafe_nil, constL_safe, localSet_safe,
        Bool.true_and]
  | buildOutput => simp [Plan.coreSupported, code]
  | opaqueProcess spec body ih =>
      intro depth scratch supported
      simp only [Plan.coreSupported] at supported
      simpa [code] using ih depth scratch supported

/-- The actual function body of every public checked compilation is entirely
inside the proved scalar Core fragment, including its status epilogue. -/
theorem bodyCode_safe {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    ListSafe
      (bodyCode (envOf checked.inputSig checked.plan)
        checked.inputSig.scratch checked.plan) = true := by
  rw [bodyCode, listSafe_append,
    code_safe_of_coreSupported _ checked.plan 0 checked.inputSig.scratch
      checked.coreSupported]
  rfl

/-! ## Exact admitted instruction image

`coreSupported` rejects every constructor whose lowering can observe a scalar
register.  Consequently the DCE performed by `code` leaves exactly the
source's ordered status assignments.  Recording that image independently of
`code` makes the dynamic simulation and its event accounting structural rather
than dependent on simplifier reduction through the complete compiler. -/

/-- The exact Core instruction list retained from an admitted source plan. -/
def statusCode (environment : CompileEnv) : Plan → List Wasm.Core.Instr
  | .seq first second =>
      statusCode environment first ++ statusCode environment second
  | .allocScratch _ body | .opaqueProcess _ body =>
      statusCode environment body
  | .setStatus status =>
      [constL status.code, localSet environment.statusLocal]
  | _ => []

/-- Every independently admitted plan lowers to exactly `statusCode`; no
memory, control, call, table, exception, or vector instruction is hidden in
the checked compiler image. -/
theorem code_eq_statusCode_of_coreSupported
    {P : Wasm.Profile} {G : Gemm.Problem P} {signature : Sig}
    (environment : CompileEnv) :
    ∀ (plan : Plan) (depth scratch : Nat),
      plan.coreSupported P G signature = true →
        code environment depth scratch plan = statusCode environment plan := by
  intro plan
  induction plan with
  | nop => simp [code, statusCode]
  | seq first second ihFirst ihSecond =>
      intro depth scratch supported
      simp only [Plan.coreSupported, Bool.and_eq_true] at supported
      simp [code, statusCode, ihFirst depth scratch supported.1,
        ihSecond depth scratch supported.2]
  | classifyRaw => simp [Plan.coreSupported]
  | dispatchLayout => simp [Plan.coreSupported]
  | branch => simp [Plan.coreSupported]
  | pack => simp [Plan.coreSupported]
  | unpack => simp [Plan.coreSupported]
  | storeReg => simp [Plan.coreSupported]
  | loadReg => simp [Plan.coreSupported]
  | loopNest => simp [Plan.coreSupported]
  | loopReg => simp [Plan.coreSupported]
  | tiled => simp [Plan.coreSupported]
  | reduce => simp [Plan.coreSupported]
  | allocScratch bytes body ih =>
      intro depth scratch supported
      simp only [Plan.coreSupported] at supported
      simpa [code, statusCode] using ih depth (scratch + bytes) supported
  | setReg => simp [code, statusCode]
  | scalarOp operation =>
      intro depth scratch supported
      cases operation <;>
        simp [Plan.coreSupported, Plan.coreScalarOpSupported, code, statusCode]
          at supported ⊢
  | vectorOp => simp [Plan.coreSupported]
  | emitTable => simp [Plan.coreSupported]
  | tableLoad => simp [Plan.coreSupported]
  | setStatus => simp [code, statusCode]
  | buildOutput => simp [Plan.coreSupported, code, statusCode]
  | opaqueProcess spec body ih =>
      intro depth scratch supported
      simp only [Plan.coreSupported] at supported
      simpa [code, statusCode] using ih depth scratch supported

/-- The complete emitted body is the exact ordered status image followed by
the fixed `i64`-to-ABI-`i32` result epilogue. -/
theorem bodyCode_eq_statusCode {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    bodyCode (envOf checked.inputSig checked.plan)
        checked.inputSig.scratch checked.plan =
      statusCode (envOf checked.inputSig checked.plan) checked.plan ++
        [localGet (envOf checked.inputSig checked.plan).statusLocal, wrapI64] := by
  rw [bodyCode, code_eq_statusCode_of_coreSupported
    (envOf checked.inputSig checked.plan) checked.plan 0
      checked.inputSig.scratch checked.coreSupported]

/-- Every retained status assignment contributes exactly two Core
instructions. -/
theorem statusCode_length_even (environment : CompileEnv) (plan : Plan) :
    ∃ assignments, (statusCode environment plan).length = 2 * assignments := by
  induction plan with
  | seq first second ihFirst ihSecond =>
      obtain ⟨firstCount, hFirst⟩ := ihFirst
      obtain ⟨secondCount, hSecond⟩ := ihSecond
      refine ⟨firstCount + secondCount, ?_⟩
      simp [statusCode, hFirst, hSecond]
      omega
  | allocScratch _ body ih | opaqueProcess _ body ih =>
      simpa [statusCode] using ih
  | setStatus => exact ⟨1, by simp [statusCode]⟩
  | nop | classifyRaw | dispatchLayout | branch | pack | unpack | storeReg |
      loadReg | loopNest | loopReg | tiled | reduce | setReg | scalarOp |
      vectorOp | emitTable | tableLoad | buildOutput =>
      exact ⟨0, by simp [statusCode]⟩

end DirectScalar

end WasmGemmGnaf.GNAF
