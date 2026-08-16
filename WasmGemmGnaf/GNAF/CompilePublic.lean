import WasmGemmGnaf.GNAF.CompileEncoding

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Public representable Core compiler

This layer relates the source-only `Plan.codeBudget` certificate to the direct
Core instruction tree, constructs the bounded amended code section, and exposes
`GNAF.compile` at the public `Wasm.Module` carrier.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectEncoding

def seqSize (xs : List Wasm.Core.Instr) : Nat :=
  Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList xs)

@[simp] theorem seqSize_nil : seqSize [] = 0 := rfl

@[simp] theorem seqSize_cons (i : Wasm.Core.Instr) (is : List Wasm.Core.Instr) :
    seqSize (i :: is) = Wasm.Core.Binary.instrSize i + seqSize is + 1 := rfl

@[simp] theorem constI_size (n : Nat) :
    Wasm.Core.Binary.instrSize (constI n) = 1 := rfl
@[simp] theorem constL_size (n : Nat) :
    Wasm.Core.Binary.instrSize (constL n) = 1 := rfl
@[simp] theorem localGet_size (n : Nat) :
    Wasm.Core.Binary.instrSize (localGet n) = 1 := rfl
@[simp] theorem localSet_size (n : Nat) :
    Wasm.Core.Binary.instrSize (localSet n) = 1 := rfl
@[simp] theorem br_size (n : Nat) : Wasm.Core.Binary.instrSize (br n) = 1 := rfl
@[simp] theorem brIf_size (n : Nat) : Wasm.Core.Binary.instrSize (brIf n) = 1 := rfl
@[simp] theorem loadW_size : Wasm.Core.Binary.instrSize loadW = 1 := rfl
@[simp] theorem load8U_size : Wasm.Core.Binary.instrSize load8U = 1 := rfl
@[simp] theorem storeW_size : Wasm.Core.Binary.instrSize storeW = 1 := rfl
@[simp] theorem loadL_size : Wasm.Core.Binary.instrSize loadL = 1 := rfl
@[simp] theorem load8UL_size : Wasm.Core.Binary.instrSize load8UL = 1 := rfl
@[simp] theorem load16UL_size : Wasm.Core.Binary.instrSize load16UL = 1 := rfl
@[simp] theorem load32UL_size : Wasm.Core.Binary.instrSize load32UL = 1 := rfl
@[simp] theorem storeL_size : Wasm.Core.Binary.instrSize storeL = 1 := rfl
@[simp] theorem store8L_size : Wasm.Core.Binary.instrSize store8L = 1 := rfl
@[simp] theorem store16L_size : Wasm.Core.Binary.instrSize store16L = 1 := rfl
@[simp] theorem store32L_size : Wasm.Core.Binary.instrSize store32L = 1 := rfl
@[simp] theorem addI_size : Wasm.Core.Binary.instrSize addI = 1 := rfl
@[simp] theorem subI_size : Wasm.Core.Binary.instrSize subI = 1 := rfl
@[simp] theorem mulI_size : Wasm.Core.Binary.instrSize mulI = 1 := rfl
@[simp] theorem andI_size : Wasm.Core.Binary.instrSize andI = 1 := rfl
@[simp] theorem orI_size : Wasm.Core.Binary.instrSize orI = 1 := rfl
@[simp] theorem eqI_size : Wasm.Core.Binary.instrSize eqI = 1 := rfl
@[simp] theorem ltUI_size : Wasm.Core.Binary.instrSize ltUI = 1 := rfl
@[simp] theorem gtUI_size : Wasm.Core.Binary.instrSize gtUI = 1 := rfl
@[simp] theorem geUI_size : Wasm.Core.Binary.instrSize geUI = 1 := rfl
@[simp] theorem addL_size : Wasm.Core.Binary.instrSize addL = 1 := rfl
@[simp] theorem subL_size : Wasm.Core.Binary.instrSize subL = 1 := rfl
@[simp] theorem mulL_size : Wasm.Core.Binary.instrSize mulL = 1 := rfl
@[simp] theorem andL_size : Wasm.Core.Binary.instrSize andL = 1 := rfl
@[simp] theorem orL_size : Wasm.Core.Binary.instrSize orL = 1 := rfl
@[simp] theorem eqL_size : Wasm.Core.Binary.instrSize eqL = 1 := rfl
@[simp] theorem ltUL_size : Wasm.Core.Binary.instrSize ltUL = 1 := rfl
@[simp] theorem gtUL_size : Wasm.Core.Binary.instrSize gtUL = 1 := rfl
@[simp] theorem geUL_size : Wasm.Core.Binary.instrSize geUL = 1 := rfl
@[simp] theorem extendI32U_size : Wasm.Core.Binary.instrSize extendI32U = 1 := rfl
@[simp] theorem wrapI64_size : Wasm.Core.Binary.instrSize wrapI64 = 1 := rfl

@[simp] theorem loadWidthL_size (width : Nat) :
    Wasm.Core.Binary.instrSize (loadWidthL width) = 1 := by
  unfold loadWidthL
  split <;> rfl

@[simp] theorem storeWidthL_size (width : Nat) :
    Wasm.Core.Binary.instrSize (storeWidthL width) = 1 := by
  unfold storeWidthL
  split <;> rfl
@[simp] theorem unreachable_size :
    Wasm.Core.Binary.instrSize Wasm.Core.Instr.unreachable = 1 := rfl
@[simp] theorem ifE_size (a b : List Wasm.Core.Instr) :
    Wasm.Core.Binary.instrSize (ifE a b) = seqSize a + seqSize b + 1 := rfl
@[simp] theorem blockE_size (body : List Wasm.Core.Instr) :
    Wasm.Core.Binary.instrSize (blockE body) = seqSize body + 1 := rfl
@[simp] theorem loopE_size (body : List Wasm.Core.Instr) :
    Wasm.Core.Binary.instrSize (loopE body) = seqSize body + 1 := rfl

theorem seqSize_append (a b : List Wasm.Core.Instr) :
    seqSize (a ++ b) = seqSize a + seqSize b :=
  instrsSize_append a b

theorem classifyCode_size_le (e : CompileEnv) (temp : Nat) :
    seqSize (classifyCode e temp) ≤ 2048 := by
  unfold classifyCode
  split
  · simp
  · simp [headerOkCode, tagsKnownCode, compatCode, keyChain, compatibleKeys,
      keyCode, cellCode, u16Code, eqConst, loadInputCell, inputAddr,
      seqSize_append]

theorem layoutCode_size_le (e : CompileEnv) (temp : Nat) :
    seqSize (layoutCode e temp) ≤ 1024 := by
  simp [layoutCode, layoutTestCode, widthCode, widthChain, ScalarKind.all,
    u16Code, cellCode, loadInputCell, inputAddr, seqSize_append]

theorem condCode_size_le (e : CompileEnv) (scratch : Nat) (cond : Cond) :
    seqSize (condCode e scratch cond) ≤ 32 := by
  cases cond <;> simp [condCode, loadAt, eqConst]

theorem countLoop_size_le (counter bound : Nat) (body : List Wasm.Core.Instr) :
    seqSize (countLoop counter bound body) ≤ 64 + seqSize body := by
  simp [countLoop, seqSize_append]
  omega

theorem countLoopVar_size_le (counter extent : Nat) (body : List Wasm.Core.Instr) :
    seqSize (countLoopVar counter extent body) ≤ 64 + seqSize body := by
  simp [countLoopVar, seqSize_append]
  omega

theorem dispatchOn_size_le (temp key : Nat) (a b : List Wasm.Core.Instr) :
    seqSize (dispatchOn temp key a b) ≤ 32 + seqSize a + seqSize b := by
  simp [dispatchOn]
  omega

theorem tableStores_size_le (base start : Nat) (data : List Nat) :
    seqSize (tableStores base start data) ≤ 16 * data.length := by
  induction data generalizing start with
  | nil => simp [tableStores]
  | cons value rest ih =>
      simp only [tableStores, seqSize_append]
      have h := ih (start := start + 1)
      simp at *
      omega

theorem code_size_le (e : CompileEnv) : ∀ (plan : Plan) (depth scratch : Nat),
    seqSize (code e depth scratch plan) ≤ plan.codeBudget := by
  intro plan
  induction plan with
  | nop => intro; simp [code, Plan.codeBudget]
  | seq a b iha ihb =>
      intro depth scratch
      rw [code, seqSize_append]
      simp only [Plan.codeBudget]
      exact Nat.add_le_add (iha depth scratch) (ihb depth scratch)
  | classifyRaw a b c d iha ihb ihc ihd =>
      intro depth scratch
      rw [code, seqSize_append]
      simp only [Plan.codeBudget]
      have hc := classifyCode_size_le e (e.tempLocal depth)
      have h1 := dispatchOn_size_le (e.tempLocal depth) 0 (code e depth scratch a)
        (dispatchOn (e.tempLocal depth) 1 (code e depth scratch b)
          (dispatchOn (e.tempLocal depth) 2 (code e depth scratch c)
            (code e depth scratch d)))
      have h2 := dispatchOn_size_le (e.tempLocal depth) 1 (code e depth scratch b)
        (dispatchOn (e.tempLocal depth) 2 (code e depth scratch c)
          (code e depth scratch d))
      have h3 := dispatchOn_size_le (e.tempLocal depth) 2 (code e depth scratch c)
        (code e depth scratch d)
      have ha := iha depth scratch
      have hb := ihb depth scratch
      have hcc := ihc depth scratch
      have hd := ihd depth scratch
      omega
  | dispatchLayout a b c iha ihb ihc =>
      intro depth scratch
      rw [code, seqSize_append]
      simp only [Plan.codeBudget]
      have hc := layoutCode_size_le e (e.tempLocal depth)
      have h1 := dispatchOn_size_le (e.tempLocal depth) 0 (code e depth scratch a)
        (dispatchOn (e.tempLocal depth) 1 (code e depth scratch b)
          (code e depth scratch c))
      have h2 := dispatchOn_size_le (e.tempLocal depth) 1 (code e depth scratch b)
        (code e depth scratch c)
      have ha := iha depth scratch
      have hb := ihb depth scratch
      have hcc := ihc depth scratch
      omega
  | branch cond a b iha ihb =>
      intro depth scratch
      rw [code, seqSize_append]
      simp only [Plan.codeBudget]
      have hc := condCode_size_le e scratch cond
      have hi := dispatchOn_size_le 0 0 (code e depth scratch a) (code e depth scratch b)
      simp [dispatchOn] at hi
      have ha := iha depth scratch
      have hb := ihb depth scratch
      simp
      omega
  | pack src dst map width =>
      intro depth scratch
      simp [code, Plan.codeBudget, countLoop, inputAddr64, seqSize_append]
  | unpack src dst map width =>
      intro depth scratch
      simp [code, Plan.codeBudget, countLoop, inputAddr64, seqSize_append]
  | storeReg dst map width src =>
      intro depth scratch
      simp [code, Plan.codeBudget, mappedInputAddr, inputAddr64, seqSize_append]
  | loadReg dst src map width =>
      intro depth scratch
      simp [code, Plan.codeBudget, mappedInputAddr, inputAddr64, seqSize_append]
  | loopNest axis body ih =>
      intro depth scratch
      have hb := ih (depth + 1) scratch
      simp [code, Plan.codeBudget, countLoop, seqSize_append]
      omega
  | loopReg indexReg extentReg map body ih =>
      intro depth scratch
      have hb := ih (depth + 1) scratch
      simp [code, Plan.codeBudget, countLoopVar, seqSize_append]
      omega
  | tiled order tiling extents body ih =>
      intro depth scratch
      have hb := ih (depth + 1) scratch
      by_cases hr : 0 < e.regs <;>
        simp [code, Plan.codeBudget, countLoop, hr, seqSize_append] <;>
        omega
  | reduce contract acc lhs rhs =>
      intro depth scratch
      simp only [code, Plan.codeBudget]
      split
      · simp [countLoop, inputAddr64, seqSize_append]
      · simp
  | allocScratch bytes body ih =>
      intro depth scratch
      simpa [code, Plan.codeBudget] using ih depth (scratch + bytes)
  | setReg dst value =>
      intro depth scratch
      simp [code, Plan.codeBudget]
  | scalarOp op dst a b =>
      intro depth scratch
      cases op <;> simp [code, Plan.codeBudget]
  | vectorOp op lanes dst a b =>
      intro depth scratch
      simp [code, Plan.codeBudget]
  | emitTable index data =>
      intro depth scratch
      simp only [code, Plan.codeBudget]
      have h := tableStores_size_le
        (e.tableBase + 8 * (index * e.tableStride)) 0 data
      omega
  | tableLoad table index dst =>
      intro depth scratch
      simp [code, loadAt, Plan.codeBudget]
  | setStatus status =>
      intro depth scratch
      simp [code, Plan.codeBudget]
  | buildOutput src =>
      intro depth scratch
      simp [code, Plan.codeBudget, inputAddr, seqSize_append]
  | opaqueProcess spec body ih =>
      intro depth scratch
      simpa [code, Plan.codeBudget] using ih depth scratch

end DirectEncoding

/-! ## Section bounds and the public carrier -/

/-- The direct module has no data segments, so its optional data-count section
is encodable under either branch of the grammar's conservative occurrence
test. -/
theorem moduleOf_dataCount_encoded (env : CompileEnv) (body : List Wasm.Core.Instr) :
    EncoderHasValue (Wasm.Core.Binary.encDataCntSec (moduleOf env body)) := by
  unfold EncoderHasValue Wasm.Core.Binary.encDataCntSec
  split
  · refine ⟨Wasm.Core.Binary.tb 12 ::
      (Wasm.Core.Binary.lebU (Wasm.Core.Binary.lebU 0).length ++
        Wasm.Core.Binary.lebU 0), ?_⟩
    simp [moduleOf, Wasm.Core.Binary.encSectionBody] <;> decide
  · exact ⟨[], rfl⟩

end WasmGemmGnaf.GNAF
