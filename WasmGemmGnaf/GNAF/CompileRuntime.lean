import WasmGemmGnaf.GNAF.CompileCorrectPublic
import WasmGemmGnaf.Wasm.CoreErasure
import WasmGemmGnaf.Wasm.Core.HarnessSuccessors
import WasmGemmGnaf.Wasm.Table

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Executable initialization of directly compiled GNAF plans

This module is deliberately downstream of both static compiler correctness
and the public amended-Core evaluator.  It proves that the fixed direct module
shape really allocates, resolves its two ABI exports, and reaches a typed
pre-start configuration for every lawful public raw invocation.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

/-- The fixed module shape emitted by the direct compiler executes every
phase of amended closed allocation.  The computed module instance exposes
exactly memory zero and function zero under the required public names. -/
theorem moduleOf_instantiateA?_some (env : CompileEnv)
    (body : List Wasm.Core.Instr) :
    ∃ core, Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (moduleOf env body) [] = some core ∧
      core.1.frame.mod.exports =
        [{ name := Wasm.Core.memoryExportName, addr := .mem 0 },
         { name := Wasm.Core.gemmExportName, addr := .func 0 }] := by
  simp [Wasm.Core.Exec.instantiateA?, moduleOf,
    Wasm.Core.Exec.allocModuleA?, Wasm.Core.Exec.evalGlobals,
    Wasm.Core.Exec.evalRefExprs, Wasm.Core.Exec.evalRefExprLists,
    Wasm.Core.Exec.allocTypes, Wasm.Core.Exec.allocTags,
    Wasm.Core.Exec.allocGlobals, Wasm.Core.Exec.allocMems,
    Wasm.Core.Exec.allocMem, Wasm.Core.Exec.allocTables,
    Wasm.Core.Exec.allocDatas, Wasm.Core.Exec.allocElems,
    Wasm.Core.Exec.allocFuncs, Wasm.Core.Exec.allocFunc,
    Wasm.Core.Exec.allocExports, Wasm.Core.Exec.allocExport,
    Wasm.Core.Exec.Store.carryConstHeap,
    Wasm.Core.substAllMemType, Wasm.Core.substMemType,
    Wasm.Core.gemmTypeDef, Wasm.Core.Exec.allocTypes,
    Wasm.Core.rollDt, Wasm.Core.rollRt,
    Wasm.Core.substAllDefTypes, Wasm.Core.substAllDefType,
    Wasm.Core.substDefType, Wasm.Core.substRecType,
    Wasm.Core.substSubTypes, Wasm.Core.substSubType,
    Wasm.Core.substTypeUses, Wasm.Core.substCompType,
    Wasm.Core.substValTypes, Wasm.Core.substValType,
    Wasm.Core.idxVars, Wasm.Core.SubTypes.ofList,
    Wasm.Core.SubTypes.length, Wasm.Core.ValTypes.ofList,
    Wasm.Core.TypeIdx.ofNat, Wasm.Core.Exec.memsxa,
    Wasm.Core.Exec.funcsxa, Wasm.Core.Exec.tagsxa,
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa, coreU32]

/-- Fresh allocation of the fixed direct module has exactly one zero-filled
memory and one function, and no residual start instructions.  These are the
concrete store facts needed to relate Harness raw-byte installation to the
independent GNAF source machine; none is supplied by a compiler certificate. -/
theorem moduleOf_instantiateA?_shape (env : CompileEnv)
    (body : List Wasm.Core.Instr) :
    ∃ core, Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
        (moduleOf env body) [] = some core ∧
      core.2 = [] ∧
      core.1.frame.mod.mems = [0] ∧
      core.1.frame.mod.funcs = [0] ∧
      core.1.store.mems.length = 1 ∧
      (core.1.store.mems[0]?).map Wasm.Core.Exec.MemInst.bytes =
        some (List.replicate ((coreU64 env.pages).val *
          (64 * Wasm.Core.Exec.Ki)) ⟨0, by decide⟩) ∧
      core.1.store.funcs.length = 1 ∧
      core.1.frame.mod.exports =
        [{ name := Wasm.Core.memoryExportName, addr := .mem 0 },
         { name := Wasm.Core.gemmExportName, addr := .func 0 }] := by
  simp [Wasm.Core.Exec.instantiateA?, moduleOf,
    Wasm.Core.Exec.allocModuleA?, Wasm.Core.Exec.evalGlobals,
    Wasm.Core.Exec.evalRefExprs, Wasm.Core.Exec.evalRefExprLists,
    Wasm.Core.Exec.allocTypes, Wasm.Core.Exec.allocTags,
    Wasm.Core.Exec.allocGlobals, Wasm.Core.Exec.allocMems,
    Wasm.Core.Exec.allocMem, Wasm.Core.Exec.allocTables,
    Wasm.Core.Exec.allocDatas, Wasm.Core.Exec.allocElems,
    Wasm.Core.Exec.allocFuncs, Wasm.Core.Exec.allocFunc,
    Wasm.Core.Exec.allocExports, Wasm.Core.Exec.allocExport,
    Wasm.Core.Exec.plains,
    Wasm.Core.Exec.Store.carryConstHeap,
    Wasm.Core.substAllMemType, Wasm.Core.substMemType,
    Wasm.Core.gemmTypeDef, Wasm.Core.Exec.allocTypes,
    Wasm.Core.rollDt, Wasm.Core.rollRt,
    Wasm.Core.substAllDefTypes, Wasm.Core.substAllDefType,
    Wasm.Core.substDefType, Wasm.Core.substRecType,
    Wasm.Core.substSubTypes, Wasm.Core.substSubType,
    Wasm.Core.substTypeUses, Wasm.Core.substCompType,
    Wasm.Core.substValTypes, Wasm.Core.substValType,
    Wasm.Core.idxVars, Wasm.Core.SubTypes.ofList,
    Wasm.Core.SubTypes.length, Wasm.Core.ValTypes.ofList,
    Wasm.Core.TypeIdx.ofNat, Wasm.Core.Exec.memsxa,
    Wasm.Core.Exec.funcsxa, Wasm.Core.Exec.tagsxa,
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa, coreU32]

/-- The exact zero-filled memory instance allocated at the direct compiler's
chosen initial page count. -/
def initialCompilerMemory (pages : Nat) : Wasm.Core.Exec.MemInst :=
  { type := Wasm.Core.MemType.mk .i32
      { min := coreU64 pages, max := some (coreU64 65536) },
    bytes := List.replicate ((coreU64 pages).val *
      (64 * Wasm.Core.Exec.Ki)) ⟨0, by decide⟩ }

theorem memoryPages_initialCompilerMemory (pages : Nat)
    (hpages : pages ≤ 65536) :
    Wasm.Core.Harness.memoryPages (initialCompilerMemory pages) = pages := by
  have hpages64 : pages < 2 ^ 64 := by omega
  simp [Wasm.Core.Harness.memoryPages, initialCompilerMemory, coreU64,
    Nat.mod_eq_of_lt hpages64]
  have hpageSize : 64 * Wasm.Core.Exec.Ki > 0 := by decide
  rw [Nat.mul_comm]
  exact Nat.mul_div_right pages hpageSize

/-- Exact singleton memory instance allocated by `moduleOf`, including its
declared wasm32 limit and every initial zero byte. -/
theorem moduleOf_instantiateA?_memory (env : CompileEnv)
    (body : List Wasm.Core.Instr) :
    ∃ core, Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
        (moduleOf env body) [] = some core ∧
      core.1.frame.mod.mems = [0] ∧
      core.1.store.mems = [initialCompilerMemory env.pages] := by
  simp [Wasm.Core.Exec.instantiateA?, moduleOf,
    Wasm.Core.Exec.allocModuleA?, Wasm.Core.Exec.evalGlobals,
    Wasm.Core.Exec.evalRefExprs, Wasm.Core.Exec.evalRefExprLists,
    Wasm.Core.Exec.allocTypes, Wasm.Core.Exec.allocTags,
    Wasm.Core.Exec.allocGlobals, Wasm.Core.Exec.allocMems,
    Wasm.Core.Exec.allocMem, Wasm.Core.Exec.allocTables,
    Wasm.Core.Exec.allocDatas, Wasm.Core.Exec.allocElems,
    Wasm.Core.Exec.allocFuncs, Wasm.Core.Exec.allocFunc,
    Wasm.Core.Exec.allocExports, Wasm.Core.Exec.allocExport,
    Wasm.Core.Exec.plains,
    Wasm.Core.Exec.Store.carryConstHeap,
    Wasm.Core.substAllMemType, Wasm.Core.substMemType,
    Wasm.Core.gemmTypeDef, Wasm.Core.Exec.allocTypes,
    Wasm.Core.rollDt, Wasm.Core.rollRt,
    Wasm.Core.substAllDefTypes, Wasm.Core.substAllDefType,
    Wasm.Core.substDefType, Wasm.Core.substRecType,
    Wasm.Core.substSubTypes, Wasm.Core.substSubType,
    Wasm.Core.substTypeUses, Wasm.Core.substCompType,
    Wasm.Core.substValTypes, Wasm.Core.substValType,
    Wasm.Core.idxVars, Wasm.Core.SubTypes.ofList,
    Wasm.Core.SubTypes.length, Wasm.Core.ValTypes.ofList,
    Wasm.Core.TypeIdx.ofNat, Wasm.Core.Exec.memsxa,
    Wasm.Core.Exec.funcsxa, Wasm.Core.Exec.tagsxa,
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa,
    initialCompilerMemory, CompileEnv.maxPages, coreU32]

/-- Fresh allocation installs the direct compiler's exact function body at
function address zero.  This is the executable counterpart of the static
module-body equation used by the validator proof. -/
theorem moduleOf_instantiateA?_function (env : CompileEnv)
    (body : List Wasm.Core.Instr) :
    ∃ core, Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
        (moduleOf env body) [] = some core ∧
      (core.1.store.funcs[0]?).map Wasm.Core.Exec.FuncInst.code =
        some (.func
          { typeidx := coreU32 0
            locals := List.replicate env.declaredLocals { valtype := .num .i64 }
            body := Wasm.Core.InstrSeq.ofList body }) := by
  simp [Wasm.Core.Exec.instantiateA?, moduleOf,
    Wasm.Core.Exec.allocModuleA?, Wasm.Core.Exec.evalGlobals,
    Wasm.Core.Exec.evalRefExprs, Wasm.Core.Exec.evalRefExprLists,
    Wasm.Core.Exec.allocTypes, Wasm.Core.Exec.allocTags,
    Wasm.Core.Exec.allocGlobals, Wasm.Core.Exec.allocMems,
    Wasm.Core.Exec.allocMem, Wasm.Core.Exec.allocTables,
    Wasm.Core.Exec.allocDatas, Wasm.Core.Exec.allocElems,
    Wasm.Core.Exec.allocFuncs, Wasm.Core.Exec.allocFunc,
    Wasm.Core.Exec.allocExports, Wasm.Core.Exec.allocExport,
    Wasm.Core.Exec.plains,
    Wasm.Core.Exec.Store.carryConstHeap,
    Wasm.Core.substAllMemType, Wasm.Core.substMemType,
    Wasm.Core.gemmTypeDef, Wasm.Core.Exec.allocTypes,
    Wasm.Core.rollDt, Wasm.Core.rollRt,
    Wasm.Core.substAllDefTypes, Wasm.Core.substAllDefType,
    Wasm.Core.substDefType, Wasm.Core.substRecType,
    Wasm.Core.substSubTypes, Wasm.Core.substSubType,
    Wasm.Core.substTypeUses, Wasm.Core.substCompType,
    Wasm.Core.substValTypes, Wasm.Core.substValType,
    Wasm.Core.idxVars, Wasm.Core.SubTypes.ofList,
    Wasm.Core.SubTypes.length, Wasm.Core.ValTypes.ofList,
    Wasm.Core.TypeIdx.ofNat, Wasm.Core.Exec.memsxa,
    Wasm.Core.Exec.funcsxa, Wasm.Core.Exec.tagsxa,
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa,
    initialCompilerMemory, CompileEnv.maxPages, coreU32]

/-- The function at address zero has exactly the released two-`i32` GEMM
domain and one-`i32` codomain after Core recursive-type expansion. -/
theorem moduleOf_instantiateA?_function_type (env : CompileEnv)
    (body : List Wasm.Core.Instr) :
    ∃ core, Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
        (moduleOf env body) [] = some core ∧
      (core.1.store.funcs[0]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) := by
  simp [Wasm.Core.Exec.instantiateA?, moduleOf,
    Wasm.Core.Exec.allocModuleA?, Wasm.Core.Exec.evalGlobals,
    Wasm.Core.Exec.evalRefExprs, Wasm.Core.Exec.evalRefExprLists,
    Wasm.Core.Exec.allocTypes, Wasm.Core.Exec.allocTags,
    Wasm.Core.Exec.allocGlobals, Wasm.Core.Exec.allocMems,
    Wasm.Core.Exec.allocMem, Wasm.Core.Exec.allocTables,
    Wasm.Core.Exec.allocDatas, Wasm.Core.Exec.allocElems,
    Wasm.Core.Exec.allocFuncs, Wasm.Core.Exec.allocFunc,
    Wasm.Core.Exec.allocExports, Wasm.Core.Exec.allocExport,
    Wasm.Core.Exec.plains,
    Wasm.Core.Exec.Store.carryConstHeap,
    Wasm.Core.substAllMemType, Wasm.Core.substMemType,
    Wasm.Core.gemmTypeDef, Wasm.Core.Exec.allocTypes,
    Wasm.Core.rollDt, Wasm.Core.rollRt,
    Wasm.Core.substAllDefTypes, Wasm.Core.substAllDefType,
    Wasm.Core.substDefType, Wasm.Core.substRecType,
    Wasm.Core.substSubTypes, Wasm.Core.substSubType,
    Wasm.Core.substTypeUses, Wasm.Core.substCompType,
    Wasm.Core.substValTypes, Wasm.Core.substValType,
    Wasm.Core.idxVars, Wasm.Core.SubTypes.ofList,
    Wasm.Core.SubTypes.length, Wasm.Core.ValTypes.ofList,
    Wasm.Core.TypeIdx.ofNat, Wasm.Core.Exec.memsxa,
    Wasm.Core.Exec.funcsxa, Wasm.Core.Exec.tagsxa,
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa,
    CompileEnv.maxPages, coreU32, Wasm.Core.expandDt,
    Wasm.Core.unrollDt, Wasm.Core.unrollRt, Wasm.Core.SubTypes.toList]

/-- A function whose expanded type is the released GEMM type is executable by
the ordinary Harness invocation decision.  The resulting configuration is
computed, not postulated. -/
theorem invokeResult?_exists_of_gemm_type
    {harness : Wasm.Core.Harness.Harness} {store : Wasm.Core.Exec.Store}
    (htype : (store.funcs[harness.gemmAddr]?).bind
        (fun function => Wasm.Core.expandDt function.type) =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32]))) :
    ∃ invoked,
      Wasm.Core.Harness.invokeResult? harness store = some invoked := by
  unfold Wasm.Core.Harness.invokeResult?
  cases hfunction : store.funcs[harness.gemmAddr]? with
  | none => simp [hfunction] at htype
  | some function =>
      simp only [hfunction, Option.bind_some] at htype
      simp only [hfunction]
      simp [Wasm.Core.ValTypes.ofList] at htype
      rw [htype]
      exact ⟨_, rfl⟩

/-- Exact configuration computed by Harness invocation once the exported
function and its expanded GEMM type are known. -/
theorem invokeResult?_eq_of_gemm_type
    {harness : Wasm.Core.Harness.Harness} {store : Wasm.Core.Exec.Store}
    {function : Wasm.Core.Exec.FuncInst}
    (hfunction : store.funcs[harness.gemmAddr]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32]))) :
    Wasm.Core.Harness.invokeResult? harness store =
      some
        (⟨store, { mod := {} }⟩,
          Wasm.Core.Exec.vals harness.args ++
            [.addrref (.funcAddr harness.gemmAddr),
             .plain (.callRef (.defd function.type))]) := by
  unfold Wasm.Core.Harness.invokeResult?
  rw [hfunction]
  simp only [hfunction]
  simp [Wasm.Core.ValTypes.ofList] at htype
  rw [htype]

/-- The first Core rule after Harness entry is the ordinary `call_ref` rule.
It creates the released one-result frame/label around the exact function body
and the argument/default-local frame prescribed by Core. -/
theorem invoke_callRefFunc_step
    {harness : Wasm.Core.Harness.Harness} {store : Wasm.Core.Exec.Store}
    {function : Wasm.Core.Exec.FuncInst} {fn : Wasm.Core.Func}
    (hfunction : store.funcs[harness.gemmAddr]? = some function)
    (htype : Wasm.Core.expandDt function.type =
      some (.func
        (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
        (Wasm.Core.ValTypes.ofList [.num .i32])))
    (hcode : function.code = .func fn) :
    let outerState : Wasm.Core.Exec.State := ⟨store, { mod := {} }⟩
    let functionFrame : Wasm.Core.Exec.Frame :=
      { locals := harness.args.map some ++
          fn.locals.map (fun lc => Wasm.Core.Exec.default_ lc.valtype)
        mod := function.mod }
    let source :=
      Wasm.Core.Exec.vals harness.args ++
        [.addrref (.funcAddr harness.gemmAddr),
         .plain (.callRef (.defd function.type))]
    Wasm.Core.Exec.StepA
      (outerState, source)
      (.read .callRefFunc (Wasm.Core.Exec.sourcePlains source))
      (outerState,
        [.frame 1 functionFrame
          [.label 1 [] (Wasm.Core.Exec.plains fn.body.toList)]]) := by
  intro outerState functionFrame
  letI : Wasm.Core.Exec.ExecutionAuthority :=
    Wasm.Core.Exec.amendedExecutionAuthority
  apply Wasm.Core.Exec.StepA.read
  apply Wasm.Core.Exec.Step_read.callRefFunc (n := 2) (m := 1)
  · exact hfunction
  · exact .mk htype
  · simp [Wasm.Core.ValTypes.ofList, Wasm.Core.ValTypes.length]
  · simp [Wasm.Core.ValTypes.ofList, Wasm.Core.ValTypes.length]
  · simp [Wasm.Core.Harness.Harness.args]
  · exact hcode
  · rfl

/-- Growing a fresh compiler memory by the Harness delta succeeds exactly and
produces a zero image at the larger of the static and invocation page counts. -/
theorem grow_initialCompilerMemory (request : Wasm.Core.Harness.Request)
    (pages : Nat) (hpages : pages ≤ 65536) :
    ∃ grown,
      Wasm.Core.Exec.growMem (initialCompilerMemory pages)
          (Wasm.Core.Harness.rawGrowthPages request
            (initialCompilerMemory pages)) = some grown ∧
      grown.bytes = List.replicate
        (Nat.max pages (Wasm.Core.Harness.rawTargetPages request) *
          (64 * Wasm.Core.Exec.Ki)) ⟨0, by decide⟩ := by
  have hpages64 : pages < 2 ^ 64 := by omega
  have htarget := request.rawPageBound
  change Wasm.Core.Harness.rawTargetPages request ≤ 65536 at htarget
  have htarget64 : Wasm.Core.Harness.rawTargetPages request < 2 ^ 64 := by
    omega
  simp only [initialCompilerMemory, Wasm.Core.Harness.rawGrowthPages,
    Wasm.Core.Harness.memoryPages, List.length_replicate,
    coreU64, Nat.mod_eq_of_lt hpages64]
  have hpageSize : 64 * Wasm.Core.Exec.Ki > 0 := by decide
  have hdiv : pages * (64 * Wasm.Core.Exec.Ki) /
      (64 * Wasm.Core.Exec.Ki) = pages := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_right pages hpageSize
  rw [hdiv]
  unfold Wasm.Core.Exec.growMem
  simp only [List.length_replicate, hdiv]
  have hnew : pages + (Wasm.Core.Harness.rawTargetPages request - pages) =
      Nat.max pages (Wasm.Core.Harness.rawTargetPages request) := by
    by_cases h : pages ≤ Wasm.Core.Harness.rawTargetPages request
    · rw [Nat.add_sub_of_le h]
      exact (Nat.max_eq_right h).symm
    · have hle : Wasm.Core.Harness.rawTargetPages request ≤ pages := by omega
      rw [Nat.sub_eq_zero_of_le hle, Nat.add_zero]
      exact (Nat.max_eq_left hle).symm
  have hsum64 : pages + (Wasm.Core.Harness.rawTargetPages request - pages) <
      2 ^ 64 := by rw [hnew]; omega
  have hsumMax : pages + (Wasm.Core.Harness.rawTargetPages request - pages) ≤
      65536 := by rw [hnew]; omega
  simp only [dif_pos hsum64]
  simp only [Nat.mod_eq_of_lt (by decide : 65536 < 2 ^ 64)]
  rw [if_pos (by simpa using hsumMax)]
  refine ⟨_, rfl, ?_⟩
  rw [List.replicate_append_replicate, ← Nat.add_mul]
  change List.replicate
      ((pages + (Wasm.Core.Harness.rawTargetPages request - pages)) *
        (64 * Wasm.Core.Exec.Ki))
        (⟨0, by decide⟩ : Wasm.Core.Byte) = _
  rw [hnew]

/-- The actual Harness raw installer succeeds over a freshly allocated direct
compiler state, retains its precise growth operands, and replaces only the
singleton memory instance with the exact spliced byte image. -/
theorem installRaw_initialCompilerMemory
    (request : Wasm.Core.Harness.Request) (state : Wasm.Core.Exec.State)
    (pages : Nat) (hpages : pages ≤ 65536)
    (hmoduleMems : state.frame.mod.mems = [0])
    (hstoreMems : state.store.mems = [initialCompilerMemory pages]) :
    ∃ (grown : Wasm.Core.Exec.MemInst) (installedBytes : List Wasm.Core.Byte)
        (installedState : Wasm.Core.Exec.State),
      Wasm.Core.Exec.growMem (initialCompilerMemory pages)
          (Wasm.Core.Harness.rawGrowthPages request
            (initialCompilerMemory pages)) = some grown ∧
      Wasm.Core.Exec.spliceAt? grown.bytes request.rawPtr.val request.rawLen.val
          request.rawBytes = some installedBytes ∧
      Wasm.Core.Harness.installRaw?
          { request := request, memoryAddr := 0, gemmAddr := 0 } state =
        some (pages, Wasm.Core.Harness.rawTargetPages request - pages,
          installedState) ∧
      installedState.store.mems = [{ grown with bytes := installedBytes }] ∧
      installedState.store.funcs = state.store.funcs ∧
      installedState.frame = state.frame := by
  obtain ⟨grown, hgrow, _⟩ :=
    grow_initialCompilerMemory request pages hpages
  obtain ⟨installedBytes, hsplice⟩ :=
    Wasm.Core.Harness.growMemoryForRaw_splice_available request hgrow
  refine ⟨grown, installedBytes,
    { state with store :=
        { state.store with mems := [{ grown with bytes := installedBytes }] } },
    hgrow, hsplice, ?_, rfl, rfl, rfl⟩
  unfold Wasm.Core.Harness.installRaw?
  simp only [hmoduleMems, List.getElem?_cons_zero, hstoreMems]
  simp [Option.bind, hmoduleMems, hstoreMems,
    memoryPages_initialCompilerMemory pages hpages, hgrow,
    Wasm.Core.Exec.State.withMemInst, Wasm.Core.Harness.idx0,
    List.getElem?_cons_zero, Wasm.Core.Exec.setAt?,
    ↓reduceIte, List.set_cons_zero,
    Wasm.Core.Exec.State.withMem, hsplice]
  unfold Wasm.Core.Harness.rawGrowthPages
  rw [memoryPages_initialCompilerMemory pages hpages]

/-- Installing a raw byte window leaves every source-memory cell at or after
the end of the window unchanged. -/
theorem installRawCells_getElem?_ge (bytes : List UInt8) :
    ∀ (memory : List Nat) (address i : Nat),
      address + bytes.length ≤ i →
      (installRawCells memory address bytes)[i]? = memory[i]? := by
  induction bytes with
  | nil => intro memory address i _; rfl
  | cons byte rest ih =>
      intro memory address i hi
      simp only [List.length_cons] at hi
      have hrest : address + 1 + rest.length ≤ i := by omega
      rw [installRawCells, ih _ _ _ hrest]
      apply List.getElem?_set_ne
      omega

/-- The ABI byte embedding used by the public Harness is the bounded Core-byte
view of the corresponding natural-valued GNAF source cell. -/
theorem invocationByte_eq_byteOfNat (byte : UInt8) :
    Wasm.invocationByte byte = Wasm.Core.Byte.ofNat byte.toNat := by
  apply Subtype.ext
  simp [Wasm.invocationByte, Wasm.Core.Byte.ofNat]

/-- An in-bounds public Core raw splice and the independent source-machine raw
installation agree byte-for-byte on the complete source-visible memory prefix.
The Core image may be larger because the Harness grows in whole pages. -/
theorem installedBytes_matches_source (bytes : List UInt8)
    (ptr sourceLength coreLength : Nat) (installed : List Wasm.Core.Byte)
    (hwindow : ptr + bytes.length ≤ sourceLength)
    (hsource : sourceLength ≤ coreLength)
    (hsplice : Wasm.Core.Exec.spliceAt?
      (List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))
      ptr bytes.length (bytes.map Wasm.invocationByte) = some installed) :
    installed.take sourceLength =
      (installRawCells (List.replicate sourceLength 0) ptr bytes).map
        Wasm.Core.Byte.ofNat := by
  have hcoreWindow : ptr + bytes.length ≤ coreLength :=
    Nat.le_trans hwindow hsource
  unfold Wasm.Core.Exec.spliceAt? at hsplice
  rw [if_pos (by simpa using hcoreWindow)] at hsplice
  have hinstalled : installed = Wasm.spliceAt
      (List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))
      ptr (bytes.map Wasm.invocationByte) := by
    have heq := Option.some.inj hsplice
    simpa only [Wasm.spliceAt, List.length_map, List.append_assoc] using heq.symm
  rw [hinstalled]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_map]
  by_cases hi : i < sourceLength
  · rw [if_pos hi]
    have hiCore : i < coreLength := Nat.lt_of_lt_of_le hi hsource
    have hptrCore : ptr ≤ coreLength := by omega
    have hptrRep : ptr ≤
        (List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte)).length := by
      simpa using hptrCore
    by_cases hbefore : i < ptr
    · rw [Wasm.getElem?_spliceAt_lt
            (l := List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))
            (i := ptr) (j := i) (xs := bytes.map Wasm.invocationByte)
            hptrRep hbefore,
          installRawCells_getElem?_lt _ _ _ _ hbefore]
      have hcoreZero :
          (List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))[i]? =
            some (⟨0, by decide⟩ : Wasm.Core.Byte) := by
        rw [List.getElem?_eq_getElem (by simpa using hiCore)]
        simp
      have hsourceZero : (List.replicate sourceLength 0)[i]? = some 0 := by
        rw [List.getElem?_eq_getElem (by simpa using hi)]
        simp
      rw [hcoreZero, hsourceZero]
      rfl
    · by_cases hinside : i < ptr + bytes.length
      · rw [Wasm.getElem?_spliceAt_mem
              (l := List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))
              (i := ptr) (j := i) (xs := bytes.map Wasm.invocationByte)
              hptrRep (Nat.le_of_not_gt hbefore) (by simpa using hinside)]
        have hcell := installRawCells_getElem?_mem bytes
          (List.replicate sourceLength 0) ptr (i - ptr) (by omega)
            (by simpa using hwindow)
        have hindex : ptr + (i - ptr) = i := by omega
        rw [hindex] at hcell
        rw [hcell]
        rw [List.getElem?_map]
        have hfun : Wasm.invocationByte =
            (fun byte : UInt8 => Wasm.Core.Byte.ofNat byte.toNat) := by
          funext byte
          exact invocationByte_eq_byteOfNat byte
        rw [hfun]
        cases bytes[i - ptr]? <;> rfl
      · rw [Wasm.getElem?_spliceAt_ge
              (l := List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))
              (i := ptr) (j := i) (xs := bytes.map Wasm.invocationByte)
              hptrRep (by simpa using Nat.le_of_not_gt hinside),
            installRawCells_getElem?_ge bytes _ _ _ (by omega)]
        have hcoreZero :
            (List.replicate coreLength (⟨0, by decide⟩ : Wasm.Core.Byte))[i]? =
              some (⟨0, by decide⟩ : Wasm.Core.Byte) := by
          rw [List.getElem?_eq_getElem (by simpa using hiCore)]
          simp
        have hsourceZero : (List.replicate sourceLength 0)[i]? = some 0 := by
          rw [List.getElem?_eq_getElem (by simpa using hi)]
          simp
        rw [hcoreZero, hsourceZero]
        rfl
  · rw [if_neg hi]
    have hlength :
        (installRawCells (List.replicate sourceLength 0) ptr bytes).length =
          sourceLength := by simp
    rw [List.getElem?_eq_none (by rw [hlength]; omega)]
    rfl

/-- The larger of the compiler's static minimum and the Harness raw-window
target covers the complete source-visible initial machine. -/
theorem initialMemoryLength_le_runtime {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) :
    let environment := envOf checked.inputSig checked.plan
    let request := Wasm.requestOfInvocation (compile checked)
      (Gemm.toWasmInvocation G raw)
    initialMemoryLength checked raw ≤
      Nat.max environment.pages (Wasm.Core.Harness.rawTargetPages request) *
        (64 * Wasm.Core.Exec.Ki) := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  have hlayout : checked.inputSig.mem ≤ environment.byteSize := by
    simp [environment, envOf, CompileEnv.byteSize, CompileEnv.outLenAddr,
      CompileEnv.statusAddr, CompileEnv.tableBase, CompileEnv.scratchBase]
    omega
  have hstaticCover := Wasm.le_pagesFor_mul environment.byteSize
  have hstatic : checked.inputSig.mem ≤
      environment.pages * (64 * Wasm.Core.Exec.Ki) := by
    calc
      checked.inputSig.mem ≤ environment.byteSize := hlayout
      _ ≤ environment.pages * Wasm.pageSize := by
        simpa [CompileEnv.pages] using hstaticCover
      _ = environment.pages * (64 * Wasm.Core.Exec.Ki) := by
        simp [Wasm.pageSize, Wasm.Core.Exec.Ki]
  have hrawCover := Wasm.Core.Harness.requiredPages_covers
    (raw.body.ptr.toNat + raw.body.bytes.size)
  have hraw : raw.body.ptr.toNat + raw.body.bytes.size ≤
      Wasm.Core.Harness.rawTargetPages request *
        (64 * Wasm.Core.Exec.Ki) := by
    simpa [request, Wasm.requestOfInvocation, Gemm.toWasmInvocation,
      Gemm.RawInvocationBody.toWasm, Wasm.Core.Harness.rawTargetPages,
      raw.lawful.1] using hrawCover
  unfold initialMemoryLength
  exact (Nat.max_le).2 ⟨Nat.le_trans hstatic
    (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)),
    Nat.le_trans hraw
      (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))⟩

private theorem map_resolvedMemoryExport? (name : Wasm.Core.Name)
    (entries : List Wasm.Core.Exec.ExportInst) :
    Option.map Subtype.val (Wasm.resolvedMemoryExport? name entries) =
      Wasm.findMemoryExport? name entries := by
  unfold Wasm.resolvedMemoryExport?
  split <;> simp_all

private theorem map_resolvedFunctionExport? (name : Wasm.Core.Name)
    (entries : List Wasm.Core.Exec.ExportInst) :
    Option.map Subtype.val (Wasm.resolvedFunctionExport? name entries) =
      Wasm.findFunctionExport? name entries := by
  unfold Wasm.resolvedFunctionExport?
  split <;> simp_all

/-- The public proof-carrying closed-instantiation wrapper succeeds on every
directly compiled plan and retains the two canonical resolved exports. -/
theorem compile_instantiateClosed?_some {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (hvalid : Wasm.validateUnder P (compile checked) = true) :
    ∃ instantiated,
      Wasm.instantiateClosed? P (compile checked) hvalid = some instantiated ∧
      instantiated.1.1.frame.mod.exports =
        [{ name := Wasm.Core.memoryExportName, addr := .mem 0 },
         { name := Wasm.Core.gemmExportName, addr := .func 0 }] := by
  obtain ⟨core, hcore, hexports⟩ := moduleOf_instantiateA?_some
    (envOf checked.inputSig checked.plan)
    (bodyCode (envOf checked.inputSig checked.plan) checked.inputSig.scratch
      checked.plan)
  have hcore' : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (compile checked).core [] = some core := by
    simpa [compile_core, compileCore] using hcore
  have hcoreCore : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (compileCore checked) [] = some core := by
    simpa [compile_core] using hcore'
  let instantiated : Wasm.ClosedInstantiationResult (compile checked) :=
    ⟨core, Wasm.Core.Exec.instantiateA?_sound_of_closed_module
      (Wasm.validateUnder_sound hvalid).1
      (Wasm.Core.Module.imports_eq_nil_of_admittedBy
        (Wasm.validateUnder_sound hvalid).2) hcore', hcore'⟩
  refine ⟨instantiated, ?_, hexports⟩
  unfold instantiated Wasm.instantiateClosed?
  cases hcoreCore
  rfl

/-- The exact cost-retaining public initializer succeeds for every direct
compiler result and every lawful invocation.  No execution conclusion is
stored in the module or source certificate: this theorem runs the ordinary
allocator and both ordinary export searches through their proof-carrying
public wrappers. -/
theorem compile_initialization_costed_succeeds {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) :
    ∃ initialization,
      Wasm.initialGemmInvocationCosted P (compile checked)
          (Gemm.toWasmInvocation G raw) = .ok initialization := by
  let hvalid := compile_validateUnder checked
  obtain ⟨instantiated, hinstantiated, hexports⟩ :=
    compile_instantiateClosed?_some checked hvalid
  cases hmemory : Wasm.resolvedMemoryExport?
      (Wasm.requestOfInvocation (compile checked)
        (Gemm.toWasmInvocation G raw)).memoryExportName
      instantiated.1.1.frame.mod.exports with
  | none =>
      rw [hexports] at hmemory
      simp [Wasm.requestOfInvocation, Wasm.resolvedMemoryExport?,
        Wasm.findMemoryExport?] at hmemory
  | some memoryExport =>
      cases hfunction : Wasm.resolvedFunctionExport?
          (Wasm.requestOfInvocation (compile checked)
            (Gemm.toWasmInvocation G raw)).gemmExportName
          instantiated.1.1.frame.mod.exports with
      | none =>
          rw [hexports] at hfunction
          by_cases hnames : Wasm.Core.memoryExportName =
              Wasm.Core.gemmExportName
          · simp [Wasm.requestOfInvocation, Wasm.resolvedFunctionExport?,
              Wasm.findFunctionExport?, hnames] at hfunction
          · simp [Wasm.requestOfInvocation, Wasm.resolvedFunctionExport?,
              Wasm.findFunctionExport?, hnames] at hfunction
      | some functionExport =>
          have hmemoryAddress : memoryExport.1 = 0 := by
            have hvalue := congrArg (Option.map Subtype.val) hmemory
            rw [map_resolvedMemoryExport?] at hvalue
            simp only [Option.map_some] at hvalue
            generalize memoryExport.1 = address at hvalue ⊢
            rw [hexports] at hvalue
            simpa [Wasm.requestOfInvocation, Wasm.findMemoryExport?,
              Wasm.Core.memoryExportName_matches,
              Wasm.Core.gemmExportName_matches] using hvalue.symm
          have hfunctionAddress : functionExport.1 = 0 := by
            have hvalue := congrArg (Option.map Subtype.val) hfunction
            rw [map_resolvedFunctionExport?] at hvalue
            simp only [Option.map_some] at hvalue
            generalize functionExport.1 = address at hvalue ⊢
            rw [hexports] at hvalue
            simpa [Wasm.requestOfInvocation, Wasm.findFunctionExport?,
              Wasm.Core.memoryExportName_matches,
              Wasm.Core.gemmExportName_matches] using hvalue.symm
          let environment := envOf checked.inputSig checked.plan
          let body := bodyCode environment checked.inputSig.scratch checked.plan
          obtain ⟨functionCore, hfunctionCore, hfunctionType⟩ :=
            moduleOf_instantiateA?_function_type environment body
          have hfunctionCore' : Wasm.Core.Exec.instantiateA?
              ({} : Wasm.Core.Exec.Store) (compile checked).core [] =
                some functionCore := by
            simpa [compile_core, compileCore, environment, body] using
              hfunctionCore
          have hfunctionCoreEq : functionCore = instantiated.1 :=
            Option.some.inj (hfunctionCore'.symm.trans instantiated.2.2)
          subst functionCore
          have hready : Wasm.Core.Harness.GemmFunctionReady
              { request := Wasm.requestOfInvocation (compile checked)
                  (Gemm.toWasmInvocation G raw)
                memoryAddr := memoryExport.1
                gemmAddr := functionExport.1 }
              instantiated.1.1.store := by
            simpa [Wasm.Core.Harness.GemmFunctionReady,
              hfunctionAddress] using hfunctionType
          obtain ⟨memoryCore, hmemoryCore, hmoduleMems, hstoreMems⟩ :=
            moduleOf_instantiateA?_memory environment body
          have hmemoryCore' : Wasm.Core.Exec.instantiateA?
              ({} : Wasm.Core.Exec.Store) (compile checked).core [] =
                some memoryCore := by
            simpa [compile_core, compileCore, environment, body] using
              hmemoryCore
          have hmemoryCoreEq : memoryCore = instantiated.1 :=
            Option.some.inj (hmemoryCore'.symm.trans instantiated.2.2)
          subst memoryCore
          have represented := of_decide_eq_true checked.coreRepresentable
          have hpages := represented.2.1
          rw [P.lawful.maxPages] at hpages
          have henvPages : environment.pages ≤ 65536 := by
            rw [show environment.pages =
                checked.plan.coreLayoutPages checked.inputSig by
              simpa [environment] using
                DirectValidation.DirectTyping.envOf_pages_eq
                  checked.inputSig checked.plan]
            exact hpages
          obtain ⟨grown, installedBytes, installedState, hgrow, hsplice,
              hinstall, hinstalledMems, hinstalledFuncs, hinstalledFrame⟩ :=
            installRaw_initialCompilerMemory
              (Wasm.requestOfInvocation (compile checked)
                (Gemm.toWasmInvocation G raw))
              instantiated.1.1 environment.pages henvPages
              hmoduleMems hstoreMems
          have hinstallReady : Wasm.Core.Harness.RawInstallReady
              { request := Wasm.requestOfInvocation (compile checked)
                  (Gemm.toWasmInvocation G raw)
                memoryAddr := memoryExport.1
                gemmAddr := functionExport.1 }
              instantiated.1.1 := by
            rw [hmemoryAddress, hfunctionAddress]
            simp [Wasm.Core.Harness.RawInstallReady, hinstall]
          exact Wasm.initialGemmInvocationCosted_success_of hvalid
            hinstantiated hmemory hfunction hready hinstallReady

/-- Erasing only the initialization labels retains the identical successful
public pre-start configuration. -/
theorem compile_initialization_succeeds {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) :
    ∃ initial,
      Wasm.initialGemmInvocation P (compile checked)
          (Gemm.toWasmInvocation G raw) = .ok initial := by
  obtain ⟨initialization, hinitialization⟩ :=
    compile_initialization_costed_succeeds checked raw
  exact ⟨initialization.initial,
    Wasm.costed_initialization_erase hinitialization⟩

/-- Inverting the executable initializer exposes the precise raw Harness
configuration allocated by the direct compiler.  Both public export addresses
are computed to zero; the theorem does not infer them from a caller-provided
harness. -/
theorem compile_initialization_raw_shape {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    ∃ core,
      Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
          (compile checked).core [] = some core ∧
      initial.1 = .beforeEntry
        { request := Wasm.requestOfInvocation (compile checked)
            (Gemm.toWasmInvocation G raw)
          memoryAddr := 0
          gemmAddr := 0 }
        core := by
  let environment := envOf checked.inputSig checked.plan
  let body := bodyCode environment checked.inputSig.scratch checked.plan
  obtain ⟨core, hshape⟩ := moduleOf_instantiateA?_shape environment body
  have hcore := hshape.1
  have hexports := hshape.2.2.2.2.2.2.2
  have hcore' : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (compile checked).core [] = some core := by
    simpa [compile_core, compileCore, environment, body] using hcore
  refine ⟨core, hcore', ?_⟩
  unfold Wasm.initialGemmInvocation at hplain
  simp only [Wasm.initialGemmInvocationCosted,
    compile_validateUnder, ↓reduceDIte] at hplain
  unfold Wasm.instantiateClosed? at hplain
  split at hplain
  · cases hplain
  · rename_i _ instantiated _
    have hinstantiated : instantiated.1 = core :=
      Option.some.inj (instantiated.2.2.symm.trans hcore')
    have hinstantiatedExports : instantiated.1.1.frame.mod.exports =
        [{ name := Wasm.Core.memoryExportName, addr := .mem 0 },
         { name := Wasm.Core.gemmExportName, addr := .func 0 }] := by
      rw [hinstantiated]
      exact hexports
    split at hplain
    · cases hplain
    · rename_i _ memoryExport hmemory
      have hmemoryAddress : memoryExport.1 = 0 := by
        have hvalue := congrArg (Option.map Subtype.val) hmemory
        rw [map_resolvedMemoryExport?] at hvalue
        simp only [Option.map_some] at hvalue
        generalize memoryExport.1 = address at hvalue ⊢
        rw [hinstantiatedExports] at hvalue
        simpa [Wasm.requestOfInvocation, Wasm.findMemoryExport?,
          Wasm.Core.memoryExportName_matches,
          Wasm.Core.gemmExportName_matches] using hvalue.symm
      split at hplain
      · cases hplain
      · rename_i _ functionExport hfunction
        have hfunctionAddress : functionExport.1 = 0 := by
          have hvalue := congrArg (Option.map Subtype.val) hfunction
          rw [map_resolvedFunctionExport?] at hvalue
          simp only [Option.map_some] at hvalue
          generalize functionExport.1 = address at hvalue ⊢
          rw [hinstantiatedExports] at hvalue
          simpa [Wasm.requestOfInvocation, Wasm.findFunctionExport?,
            Wasm.Core.memoryExportName_matches,
            Wasm.Core.gemmExportName_matches] using hvalue.symm
        by_cases hready : Wasm.Core.Harness.GemmFunctionReady
            { request := Wasm.requestOfInvocation (compile checked)
                (Gemm.toWasmInvocation G raw)
              memoryAddr := memoryExport.1
              gemmAddr := functionExport.1 }
            instantiated.1.1.store
        · rw [dif_pos hready] at hplain
          by_cases hinstallReady : Wasm.Core.Harness.RawInstallReady
              { request := Wasm.requestOfInvocation (compile checked)
                  (Gemm.toWasmInvocation G raw)
                memoryAddr := memoryExport.1
                gemmAddr := functionExport.1 }
              instantiated.1.1
          · rw [dif_pos hinstallReady] at hplain
            simp only [Except.map, Except.ok.injEq] at hplain
            have hinitial := congrArg Subtype.val hplain.symm
            simpa [hmemoryAddress, hfunctionAddress, hinstantiated] using hinitial
          · rw [dif_neg hinstallReady] at hplain
            cases hplain
        · rw [dif_neg hready] at hplain
          cases hplain

/-- The executable initializer's concrete pre-start state has no residual
start code and contains exactly the zero-filled singleton memory allocated at
the compiler's proved-small initial page count. -/
theorem compile_initialization_store_shape {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    let environment := envOf checked.inputSig checked.plan
    ∃ core,
      Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
        (compile checked).core [] = some core ∧
      initial.1 = .beforeEntry
        { request := Wasm.requestOfInvocation (compile checked)
            (Gemm.toWasmInvocation G raw)
          memoryAddr := 0
          gemmAddr := 0 }
        core ∧
      core.2 = [] ∧
      core.1.frame.mod.mems = [0] ∧
      core.1.store.mems = [initialCompilerMemory environment.pages] ∧
      environment.pages ≤ 65536 := by
  let environment := envOf checked.inputSig checked.plan
  let body := bodyCode environment checked.inputSig.scratch checked.plan
  obtain ⟨core, hcore, hinitial⟩ :=
    compile_initialization_raw_shape checked raw hplain
  obtain ⟨shapeCore, hshape⟩ :=
    moduleOf_instantiateA?_shape environment body
  have hshapeCore := hshape.1
  have hcode := hshape.2.1
  obtain ⟨memoryCore, hmemoryCore, hmoduleMems, hstoreMems⟩ :=
    moduleOf_instantiateA?_memory environment body
  have hshapeCore' : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (compile checked).core [] = some shapeCore := by
    simpa [compile_core, compileCore, environment, body] using hshapeCore
  have hmemoryCore' : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (compile checked).core [] = some memoryCore := by
    simpa [compile_core, compileCore, environment, body] using hmemoryCore
  have hshapeEq : shapeCore = core :=
    Option.some.inj (hshapeCore'.symm.trans hcore)
  have hmemoryEq : memoryCore = core :=
    Option.some.inj (hmemoryCore'.symm.trans hcore)
  subst shapeCore
  subst memoryCore
  have represented := of_decide_eq_true checked.coreRepresentable
  have hpages := represented.2.1
  rw [P.lawful.maxPages] at hpages
  have henvPages : environment.pages ≤ 65536 := by
    rw [show environment.pages = checked.plan.coreLayoutPages checked.inputSig by
      simpa [environment] using
        DirectValidation.DirectTyping.envOf_pages_eq
          checked.inputSig checked.plan]
    exact hpages
  exact ⟨core, hcore, hinitial, hcode, hmoduleMems, hstoreMems, henvPages⟩

/-- The unique raw-install transition immediately following successful direct
compiler initialization exposes an entry store that agrees exactly with the
independent GNAF initial machine on every source-visible byte. -/
theorem compile_installRaw_entry_matches {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    let environment := envOf checked.inputSig checked.plan
    let request := Wasm.requestOfInvocation (compile checked)
      (Gemm.toWasmInvocation G raw)
    let harness : Wasm.Core.Harness.Harness :=
      { request := request, memoryAddr := 0, gemmAddr := 0 }
    ∃ (core : Wasm.Core.Exec.Config) (installedState : Wasm.Core.Exec.State)
        (entry : Wasm.ObservableStore),
      initial.1 = .beforeEntry harness core ∧
      Wasm.Core.Harness.StepA initial.1
        (.installRaw 0 request.rawPtr.val request.rawLen.val
          environment.pages
          (Wasm.Core.Harness.rawTargetPages request - environment.pages))
        (.readyToEnter harness installedState) ∧
      Wasm.Core.Harness.observeStore harness installedState.store = some entry ∧
      (installedState.store.funcs[0]?).map Wasm.Core.Exec.FuncInst.code =
        some (.func
          { typeidx := coreU32 0
            locals := List.replicate environment.declaredLocals
              { valtype := .num .i64 }
            body := Wasm.Core.InstrSeq.ofList
              (bodyCode environment checked.inputSig.scratch checked.plan) }) ∧
      (installedState.store.funcs[0]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) ∧
      MemoryMatches (initialMachine checked raw) entry := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  let harness : Wasm.Core.Harness.Harness :=
    { request := request, memoryAddr := 0, gemmAddr := 0 }
  obtain ⟨core, hcore, hinitial, hcode, hmoduleMems, hstoreMems, hpages⟩ :=
    compile_initialization_store_shape checked raw hplain
  have hinitial' : initial.1 = .beforeEntry harness core := by
    simpa [harness, request] using hinitial
  obtain ⟨grown, installedBytes, installedState, hgrow, hsplice,
      hinstall, hinstalledMems, hinstalledFuncs, _⟩ :=
    installRaw_initialCompilerMemory request core.1 environment.pages hpages
      hmoduleMems hstoreMems
  obtain ⟨functionCore, hfunctionCore, hfunction⟩ :=
    moduleOf_instantiateA?_function environment
      (bodyCode environment checked.inputSig.scratch checked.plan)
  have hfunctionCore' : Wasm.Core.Exec.instantiateA?
      ({} : Wasm.Core.Exec.Store) (compile checked).core [] =
        some functionCore := by
    simpa [compile_core, compileCore, environment] using hfunctionCore
  have hfunctionEq : functionCore = core :=
    Option.some.inj (hfunctionCore'.symm.trans hcore)
  subst functionCore
  have hinstalledFunction :
      (installedState.store.funcs[0]?).map Wasm.Core.Exec.FuncInst.code =
        some (.func
          { typeidx := coreU32 0
            locals := List.replicate environment.declaredLocals
              { valtype := .num .i64 }
            body := Wasm.Core.InstrSeq.ofList
              (bodyCode environment checked.inputSig.scratch checked.plan) }) := by
    rw [hinstalledFuncs]
    exact hfunction
  obtain ⟨typeCore, htypeCore, htype⟩ :=
    moduleOf_instantiateA?_function_type environment
      (bodyCode environment checked.inputSig.scratch checked.plan)
  have htypeCore' : Wasm.Core.Exec.instantiateA?
      ({} : Wasm.Core.Exec.Store) (compile checked).core [] = some typeCore := by
    simpa [compile_core, compileCore, environment] using htypeCore
  have htypeEq : typeCore = core :=
    Option.some.inj (htypeCore'.symm.trans hcore)
  subst typeCore
  have hinstalledType :
      (installedState.store.funcs[0]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) := by
    rw [hinstalledFuncs]
    exact htype
  obtain ⟨canonicalGrown, hcanonicalGrow, hcanonicalBytes⟩ :=
    grow_initialCompilerMemory request environment.pages hpages
  have hcanonicalEq : canonicalGrown = grown :=
    Option.some.inj (hcanonicalGrow.symm.trans hgrow)
  subst canonicalGrown
  rw [hcanonicalBytes] at hsplice
  have hsplice' : Wasm.Core.Exec.spliceAt?
      (List.replicate
        (Nat.max environment.pages (Wasm.Core.Harness.rawTargetPages request) *
          (64 * Wasm.Core.Exec.Ki))
        (⟨0, by decide⟩ : Wasm.Core.Byte))
      raw.body.ptr.toNat raw.body.bytes.toList.length
      (raw.body.bytes.toList.map Wasm.invocationByte) = some installedBytes := by
    simpa [request, Wasm.requestOfInvocation, Gemm.toWasmInvocation,
      Gemm.RawInvocationBody.toWasm, Foundation.Bytes.byteArray_toList,
      raw.lawful.1] using hsplice
  have hbytes := installedBytes_matches_source raw.body.bytes.toList
    raw.body.ptr.toNat (initialMemoryLength checked raw)
    (Nat.max environment.pages (Wasm.Core.Harness.rawTargetPages request) *
      (64 * Wasm.Core.Exec.Ki)) installedBytes
    (by simpa [Foundation.Bytes.byteArray_toList] using
      raw_window_le_initialMemoryLength checked raw)
    (initialMemoryLength_le_runtime checked raw) hsplice'
  let entry : Wasm.ObservableStore := { bytes := installedBytes }
  have hmatches : MemoryMatches (initialMachine checked raw) entry := by
    simpa [MemoryMatches, Machine.byteImage, entry, initialMachine,
      Foundation.Bytes.byteArray_toList] using hbytes
  have hobserve : Wasm.Core.Harness.observeStore harness
      installedState.store = some entry := by
    simp [Wasm.Core.Harness.observeStore, harness, hinstalledMems, entry]
  have hcore : core = (core.1, []) := by
    cases core
    simp_all
  refine ⟨core, installedState, entry, hinitial', ?_, hobserve,
    hinstalledFunction, hinstalledType, hmatches⟩
  rw [hinitial', hcore]
  exact Wasm.Core.Harness.StepA.installRaw hinstall

/-- Public typed-carrier spelling of `compile_installRaw_entry_matches`: the
raw installer is a genuine `Wasm.Step`, and its reachable ready state retains
the exact source-entry memory relation. -/
theorem compile_public_installRaw_entry_matches {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    let environment := envOf checked.inputSig checked.plan
    let request := Wasm.requestOfInvocation (compile checked)
      (Gemm.toWasmInvocation G raw)
    let harness : Wasm.Core.Harness.Harness :=
      { request := request, memoryAddr := 0, gemmAddr := 0 }
    ∃ (next : Wasm.Config) (installedState : Wasm.Core.Exec.State)
        (entry : Wasm.ObservableStore),
      Wasm.Step initial
        (.installRaw 0 request.rawPtr.val request.rawLen.val
          environment.pages
          (Wasm.Core.Harness.rawTargetPages request - environment.pages)) next ∧
      next.1 = .readyToEnter harness installedState ∧
      Wasm.Core.Harness.observeStore harness installedState.store = some entry ∧
      (installedState.store.funcs[0]?).map Wasm.Core.Exec.FuncInst.code =
        some (.func
          { typeidx := coreU32 0
            locals := List.replicate environment.declaredLocals
              { valtype := .num .i64 }
            body := Wasm.Core.InstrSeq.ofList
              (bodyCode environment checked.inputSig.scratch checked.plan) }) ∧
      (installedState.store.funcs[0]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) ∧
      MemoryMatches (initialMachine checked raw) entry := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  let harness : Wasm.Core.Harness.Harness :=
    { request := request, memoryAddr := 0, gemmAddr := 0 }
  obtain ⟨core, installedState, entry, _, hstep, hobserve, hfunction, htype,
      hmatches⟩ :=
    compile_installRaw_entry_matches checked raw hplain
  let event : Wasm.Event :=
    .installRaw 0 request.rawPtr.val request.rawLen.val environment.pages
      (Wasm.Core.Harness.rawTargetPages request - environment.pages)
  let next : Wasm.Config :=
    Wasm.Core.Harness.TypedConfig.successor initial event
      (.readyToEnter harness installedState) hstep
  exact ⟨next, installedState, entry, hstep, rfl, hobserve, hfunction, htype,
    hmatches⟩

/-- Every successfully initialized direct compilation takes the real raw
installation edge and then the real exported-function entry edge.  At the
entry boundary the public store matches the independent source machine and the
invoked function is the compiler's exact emitted body. -/
theorem compile_public_reaches_function_entry {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    let environment := envOf checked.inputSig checked.plan
    let request := Wasm.requestOfInvocation (compile checked)
      (Gemm.toWasmInvocation G raw)
    let harness : Wasm.Core.Harness.Harness :=
      { request := request, memoryAddr := 0, gemmAddr := 0 }
    ∃ (ready after : Wasm.Config) (installedState : Wasm.Core.Exec.State)
        (invoked : Wasm.Core.Exec.Config) (entry : Wasm.ObservableStore),
      Wasm.Step initial
        (.installRaw 0 request.rawPtr.val request.rawLen.val
          environment.pages
          (Wasm.Core.Harness.rawTargetPages request - environment.pages)) ready ∧
      ready.1 = .readyToEnter harness installedState ∧
      Wasm.Core.Harness.invokeResult? harness installedState.store =
        some invoked ∧
      Wasm.Step ready (.enterGemm 0) after ∧
      after.1 = .afterEntry harness installedState.store invoked ∧
      Wasm.Core.Harness.observeStore harness installedState.store = some entry ∧
      (installedState.store.funcs[0]?).map Wasm.Core.Exec.FuncInst.code =
        some (.func
          { typeidx := coreU32 0
            locals := List.replicate environment.declaredLocals
              { valtype := .num .i64 }
            body := Wasm.Core.InstrSeq.ofList
              (bodyCode environment checked.inputSig.scratch checked.plan) }) ∧
      (installedState.store.funcs[0]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) ∧
      MemoryMatches (initialMachine checked raw) entry := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  let harness : Wasm.Core.Harness.Harness :=
    { request := request, memoryAddr := 0, gemmAddr := 0 }
  obtain ⟨ready, installedState, entry, hinstall, hready, hobserve,
      hfunction, htype, hmatches⟩ :=
    compile_public_installRaw_entry_matches checked raw hplain
  have htype' :
      (installedState.store.funcs[harness.gemmAddr]?).bind
          (fun function => Wasm.Core.expandDt function.type) =
        some (.func
          (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
          (Wasm.Core.ValTypes.ofList [.num .i32])) := by
    simpa [harness] using htype
  obtain ⟨invoked, hinvoked⟩ :=
    invokeResult?_exists_of_gemm_type htype'
  have henterRaw : Wasm.Core.Harness.StepA ready.1 (.enterGemm 0)
      (.afterEntry harness installedState.store invoked) := by
    rw [hready]
    simpa [harness] using
      (Wasm.Core.Harness.StepA.enterGemm
        (Wasm.Core.Harness.invokeResult?_sound hinvoked))
  let after : Wasm.Config :=
    Wasm.Core.Harness.TypedConfig.successor ready (.enterGemm 0)
      (.afterEntry harness installedState.store invoked) henterRaw
  exact ⟨ready, after, installedState, invoked, entry, hinstall, hready,
    hinvoked, henterRaw, rfl, hobserve, hfunction, htype, hmatches⟩

/-- The first post-entry Core reduction opens the emitted function body under
the exact one-result frame/label prescribed by the public call rule.  Together
with `compile_public_reaches_function_entry`, this discharges the complete
initialization/install/invoke prefix of the compiler simulation. -/
theorem compile_public_steps_into_emitted_body {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    let environment := envOf checked.inputSig checked.plan
    let request := Wasm.requestOfInvocation (compile checked)
      (Gemm.toWasmInvocation G raw)
    let harness : Wasm.Core.Harness.Harness :=
      { request := request, memoryAddr := 0, gemmAddr := 0 }
    let emittedFunction : Wasm.Core.Func :=
      { typeidx := coreU32 0
        locals := List.replicate environment.declaredLocals
          { valtype := .num .i64 }
        body := Wasm.Core.InstrSeq.ofList
          (bodyCode environment checked.inputSig.scratch checked.plan) }
    ∃ (ready after bodyState : Wasm.Config)
        (installedState : Wasm.Core.Exec.State)
        (function : Wasm.Core.Exec.FuncInst) (entry : Wasm.ObservableStore)
        (coreEvent : Wasm.Core.Exec.Event),
      Wasm.Step initial
        (.installRaw 0 request.rawPtr.val request.rawLen.val
          environment.pages
          (Wasm.Core.Harness.rawTargetPages request - environment.pages)) ready ∧
      Wasm.Step ready (.enterGemm 0) after ∧
      Wasm.Step after (.coreAfterEntry coreEvent) bodyState ∧
      bodyState.1 = .afterEntry harness installedState.store
        (⟨installedState.store, { mod := {} }⟩,
          [.frame 1
            { locals := harness.args.map some ++
                emittedFunction.locals.map
                  (fun lc => Wasm.Core.Exec.default_ lc.valtype)
              mod := function.mod }
            [.label 1 []
              (Wasm.Core.Exec.plains emittedFunction.body.toList)]]) ∧
      Wasm.Core.Harness.observeStore harness installedState.store = some entry ∧
      MemoryMatches (initialMachine checked raw) entry := by
  let environment := envOf checked.inputSig checked.plan
  let request := Wasm.requestOfInvocation (compile checked)
    (Gemm.toWasmInvocation G raw)
  let harness : Wasm.Core.Harness.Harness :=
    { request := request, memoryAddr := 0, gemmAddr := 0 }
  let emittedFunction : Wasm.Core.Func :=
    { typeidx := coreU32 0
      locals := List.replicate environment.declaredLocals
        { valtype := .num .i64 }
      body := Wasm.Core.InstrSeq.ofList
        (bodyCode environment checked.inputSig.scratch checked.plan) }
  obtain ⟨ready, after, installedState, invoked, entry, hinstall, _,
      hinvoked, henter, hafter, hobserve, hfunctionCode, hfunctionType,
      hmatches⟩ := compile_public_reaches_function_entry checked raw hplain
  cases hlookup : installedState.store.funcs[0]? with
  | none => simp [hlookup] at hfunctionCode
  | some function =>
      have hcode : function.code = .func emittedFunction := by
        simpa [hlookup, emittedFunction] using hfunctionCode
      have htype : Wasm.Core.expandDt function.type =
          some (.func
            (Wasm.Core.ValTypes.ofList [.num .i32, .num .i32])
            (Wasm.Core.ValTypes.ofList [.num .i32])) := by
        simpa [hlookup] using hfunctionType
      have hlookup' :
          installedState.store.funcs[harness.gemmAddr]? = some function := by
        simpa [harness] using hlookup
      have hinvokedExact := invokeResult?_eq_of_gemm_type hlookup' htype
      have hinvokedShape : invoked =
          (⟨installedState.store, { mod := {} }⟩,
            Wasm.Core.Exec.vals harness.args ++
              [.addrref (.funcAddr harness.gemmAddr),
               .plain (.callRef (.defd function.type))]) :=
        Option.some.inj (hinvoked.symm.trans hinvokedExact)
      subst invoked
      let coreEvent : Wasm.Core.Exec.Event :=
        .read .callRefFunc
          (Wasm.Core.Exec.sourcePlains
            (Wasm.Core.Exec.vals harness.args ++
              [.addrref (.funcAddr harness.gemmAddr),
               .plain (.callRef (.defd function.type))]))
      have hcore := invoke_callRefFunc_step hlookup' htype hcode
      let entered : Wasm.Core.Exec.Config :=
        (⟨installedState.store, { mod := {} }⟩,
          [.frame 1
            { locals := harness.args.map some ++
                emittedFunction.locals.map
                  (fun lc => Wasm.Core.Exec.default_ lc.valtype)
              mod := function.mod }
            [.label 1 []
              (Wasm.Core.Exec.plains emittedFunction.body.toList)]])
      have hcore' : Wasm.Core.Exec.StepA
          (⟨installedState.store, { mod := {} }⟩,
            Wasm.Core.Exec.vals harness.args ++
              [.addrref (.funcAddr harness.gemmAddr),
               .plain (.callRef (.defd function.type))])
          coreEvent entered := by
        simpa [entered, emittedFunction, coreEvent] using hcore
      have hbodyRaw : Wasm.Core.Harness.StepA after.1
          (.coreAfterEntry coreEvent)
          (.afterEntry harness installedState.store entered) := by
        rw [hafter]
        exact .coreAfter hcore' (by rfl) (by simp [entered])
      let bodyState : Wasm.Config :=
        Wasm.Core.Harness.TypedConfig.successor after
          (.coreAfterEntry coreEvent)
          (.afterEntry harness installedState.store entered) hbodyRaw
      exact ⟨ready, after, bodyState, installedState, function, entry,
        coreEvent, hinstall, henter, hbodyRaw, rfl, hobserve, hmatches⟩

/-- A successful plain initialization of a compiler result is the erasure of
one exact cost-retaining initialization observation with the same initial
configuration.  This is the inversion direction used by `Wasm.Run`, whose
surface intentionally exposes only the plain initializer. -/
theorem compile_costed_initialization_of_plain {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) {initial : Wasm.Config}
    (hplain : Wasm.initialGemmInvocation P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initial) :
    ∃ initialization,
      Wasm.initialGemmInvocationCosted P (compile checked)
          (Gemm.toWasmInvocation G raw) = .ok initialization ∧
        initialization.initial = initial := by
  unfold Wasm.initialGemmInvocation at hplain
  cases hcosted : Wasm.initialGemmInvocationCosted P (compile checked)
      (Gemm.toWasmInvocation G raw) with
  | error failure =>
      rw [hcosted] at hplain
      simp [Except.map] at hplain
  | ok initialization =>
      rw [hcosted] at hplain
      simp only [Except.map, Except.ok.injEq] at hplain
      exact ⟨initialization, rfl, hplain⟩

end WasmGemmGnaf.GNAF
