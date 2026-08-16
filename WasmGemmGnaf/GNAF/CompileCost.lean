import WasmGemmGnaf.GNAF.CompileScalarRuntime
import WasmGemmGnaf.Wasm.Core.CostForcedExecution
import WasmGemmGnaf.Wasm.Core.HarnessFunctional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Exact cost of the admitted direct compiler image

This file relates the independent invocation-indexed source formula in
`CheckedPlan.certifiedCost` to the concrete initialization and execution events
of the direct public-Core image.  The formula contains no evaluator result or
proof witness.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectScalarCost

/-- The source structural status-step count is exactly the length of the
ordered assignment list consumed by the scalar runtime simulation. -/
theorem statusAssignments_length (plan : Plan) :
    (DirectScalar.statusAssignments plan).length =
      CheckedPlan.compiledStatusSteps plan := by
  induction plan with
  | seq first second ihFirst ihSecond =>
      simp [DirectScalar.statusAssignments, CheckedPlan.compiledStatusSteps,
        ihFirst, ihSecond]
  | allocScratch _ body ih | opaqueProcess _ body ih =>
      simpa [DirectScalar.statusAssignments,
        CheckedPlan.compiledStatusSteps] using ih
  | setStatus => rfl
  | nop | classifyRaw | dispatchLayout | branch | pack | unpack | storeReg |
      loadReg | loopNest | loopReg | tiled | reduce | setReg | scalarOp |
      vectorOp | emitTable | tableLoad | buildOutput => rfl

/-- Every retained source status assignment contributes exactly one live
constant operand to the initial emitted body; its matching `local.set` and the
fixed epilogue contribute no live slot until they execute. -/
theorem statusAssignments_liveSlots (environment : CompileEnv)
    (plan : Plan) :
    ((Wasm.Core.Exec.plains (DirectScalar.statusCode environment plan)).map
      Wasm.adminLiveSlots).sum =
        (DirectScalar.statusAssignments plan).length := by
  rw [DirectScalar.statusCode_eq_flatMap]
  induction DirectScalar.statusAssignments plan with
  | nil => rfl
  | cons value rest ih =>
      rw [List.flatMap_cons]
      rw [show Wasm.Core.Exec.plains
          ([constL value, localSet environment.statusLocal] ++
            rest.flatMap (fun value =>
              [constL value, localSet environment.statusLocal])) =
          Wasm.Core.Exec.plains
              [constL value, localSet environment.statusLocal] ++
            Wasm.Core.Exec.plains
              (rest.flatMap (fun value =>
                [constL value, localSet environment.statusLocal])) by
        exact List.map_append]
      rw [List.map_append, List.sum_append, ih]
      simp [Wasm.Core.Exec.plains, Wasm.adminLiveSlots, constL, localSet]
      omega

/-- At function entry the complete emitted body therefore exposes exactly one
live administrative operand per retained status assignment.  The final
`local.get` and conversion are not values until their respective rules fire. -/
theorem bodyCode_liveSlots {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    ((Wasm.Core.Exec.plains
      (bodyCode (envOf checked.inputSig checked.plan)
        checked.inputSig.scratch checked.plan)).map
      Wasm.adminLiveSlots).sum =
        CheckedPlan.compiledStatusSteps checked.plan := by
  rw [DirectScalar.bodyCode_eq_statusCode]
  rw [show Wasm.Core.Exec.plains
      (DirectScalar.statusCode (envOf checked.inputSig checked.plan)
          checked.plan ++
        [localGet (envOf checked.inputSig checked.plan).statusLocal,
          wrapI64]) =
      Wasm.Core.Exec.plains
          (DirectScalar.statusCode (envOf checked.inputSig checked.plan)
            checked.plan) ++
        Wasm.Core.Exec.plains
          [localGet (envOf checked.inputSig checked.plan).statusLocal,
            wrapI64] by exact List.map_append]
  rw [List.map_append, List.sum_append,
    statusAssignments_liveSlots, statusAssignments_length]
  simp [Wasm.Core.Exec.plains, Wasm.adminLiveSlots, localGet, wrapI64]

/-- The source-only initial-memory expression is definitionally the byte
extent used by the compiler environment. -/
theorem env_byteSize_eq_compiledInitialMemoryBytes {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    (envOf checked.inputSig checked.plan).byteSize =
      checked.compiledInitialMemoryBytes := by
  simp [envOf, CompileEnv.byteSize, CompileEnv.outLenAddr,
    CompileEnv.statusAddr, CompileEnv.tableBase, CompileEnv.scratchBase,
    CheckedPlan.compiledInitialMemoryBytes]

/-- Consequently the module's declared minimum is the exact source-computed
initial page count. -/
theorem env_pages_eq_compiledInitialPages {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    (envOf checked.inputSig checked.plan).pages =
      checked.compiledInitialPages := by
  simp [CompileEnv.pages, CheckedPlan.compiledInitialPages,
    env_byteSize_eq_compiledInitialMemoryBytes]

/-- The source-only local count is the exact compiler declaration count. -/
theorem env_declaredLocals_eq_compiledDeclaredLocals {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    (envOf checked.inputSig checked.plan).declaredLocals =
      checked.compiledDeclaredLocals := by
  rfl

/-- Splicing an in-bounds byte window into a singleton page-aligned memory
preserves its exact page count.  This is the resource-snapshot bridge used
after the Harness grows and installs a public raw invocation. -/
theorem storeMemoryPages_singleton_spliceAt?
    {memory : Wasm.Core.Exec.MemInst}
    {installedBytes replacement : List Wasm.Core.Byte}
    {store : Wasm.Core.Exec.Store} {offset pages : Nat}
    (hmemory : memory.bytes.length =
      pages * (64 * Wasm.Core.Exec.Ki))
    (hsplice : Wasm.Core.Exec.spliceAt? memory.bytes offset
      replacement.length replacement = some installedBytes)
    (hmems : store.mems = [{ memory with bytes := installedBytes }]) :
    Wasm.storeMemoryPages store = pages := by
  unfold Wasm.Core.Exec.spliceAt? at hsplice
  split at hsplice
  next hbound =>
    have hinstalled : installedBytes =
        memory.bytes.take offset ++ replacement ++
          memory.bytes.drop (offset + replacement.length) :=
      Option.some.inj hsplice.symm
    have hlen : installedBytes.length = memory.bytes.length := by
      rw [hinstalled]
      simpa only [Wasm.spliceAt, List.append_assoc] using
        Wasm.spliceAt_length memory.bytes offset replacement hbound
    unfold Wasm.storeMemoryPages
    rw [hmems]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    rw [hlen, hmemory]
    have hpageSize : 0 < 64 * Wasm.Core.Exec.Ki := by decide
    rw [Nat.mul_comm]
    exact Nat.mul_div_right pages hpageSize
  next => contradiction

/-- The concrete Harness grow-and-splice facts therefore expose exactly the
larger of the compiler's declared minimum and the invocation's required page
extent in the installed singleton store. -/
theorem storeMemoryPages_installedRaw
    (request : Wasm.Core.Harness.Request) (pages : Nat)
    {grown : Wasm.Core.Exec.MemInst}
    {installedBytes : List Wasm.Core.Byte}
    {store : Wasm.Core.Exec.Store}
    (hgrown : grown.bytes = List.replicate
      (Nat.max pages (Wasm.Core.Harness.rawTargetPages request) *
        (64 * Wasm.Core.Exec.Ki)) ⟨0, by decide⟩)
    (hsplice : Wasm.Core.Exec.spliceAt? grown.bytes request.rawPtr.val
      request.rawLen.val request.rawBytes = some installedBytes)
    (hmems : store.mems = [{ grown with bytes := installedBytes }]) :
    Wasm.storeMemoryPages store =
      Nat.max pages (Wasm.Core.Harness.rawTargetPages request) := by
  apply storeMemoryPages_singleton_spliceAt?
      (memory := grown) (installedBytes := installedBytes)
      (replacement := request.rawBytes) (offset := request.rawPtr.val)
      (pages := Nat.max pages (Wasm.Core.Harness.rawTargetPages request))
      (store := store)
  · rw [hgrown]
    simp
  · simpa [request.rawLength] using hsplice
  · exact hmems

/-- The freshly instantiated direct module has the exact empty-stack,
singleton-memory resource snapshot used by initialization costing. -/
theorem moduleOf_instantiateA?_snapshot (env : CompileEnv)
    (body : List Wasm.Core.Instr) (layout : Wasm.GcLayoutConstants)
    (harness : Wasm.Core.Harness.Harness) {core : Wasm.Core.Exec.Config}
    (hcore : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (moduleOf env body) [] = some core)
    (hpages : env.pages ≤ 65536) :
    Wasm.snapshotRaw layout (.beforeEntry harness core) =
      { liveValueSlots := 0
        memoryPages := env.pages
        tableSize := 0
        liveGcBytes := 0 } := by
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
    Wasm.Core.Exec.globalsxa, Wasm.Core.Exec.tablesxa, coreU32] at hcore
  subst core
  simp [Wasm.snapshotRaw, Wasm.rawConfigState?, Wasm.rawConfigInstrs,
    Wasm.storeMemoryPages, Wasm.storeTableSize, Wasm.storeGcLiveBytes]
  have hpages64 : env.pages < 2 ^ 64 := by omega
  rw [show (coreU64 env.pages).val = env.pages by
    simp [coreU64, Nat.mod_eq_of_lt hpages64]]
  have hpageSize : 0 < 64 * Wasm.Core.Exec.Ki := by decide
  rw [Nat.mul_comm]
  exact Nat.mul_div_right env.pages hpageSize

/-- Closed source formula for the direct module's six deterministic
initialization subevents and its allocated-memory snapshot. -/
def initializationCost (profile : Wasm.Profile)
    {G : Gemm.Problem profile} (checked : CheckedPlan profile G) :
    Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      instantiationSteps := 6
      wasmRuleSteps := profile.costTableBody.ruleStepUnit * 6
      peakPages := checked.compiledInitialPages }

/-- The cumulative part of `count` deterministic initialization subevents. -/
def initializationEventsCost (table : Wasm.CostTableBody) (count : Nat) :
    Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      instantiationSteps := count
      wasmRuleSteps := table.ruleStepUnit * count }

/-- Two dynamic vectors are equal when all sixteen named coordinates agree. -/
theorem dynamicVector_ext {left right : Cost.DynamicVector}
    (h : ∀ coordinate : Cost.DynamicCoordinate,
      coordinate.value left = coordinate.value right) :
    left = right := by
  apply Cost.DynamicVector.componentwiseLE_antisymm
  · intro coordinate
    exact Nat.le_of_eq (h coordinate)
  · intro coordinate
    exact Nat.le_of_eq (h coordinate).symm

/-- Folding initialization subevents depends exactly on their count, because
their distinct payloads affect allocation provenance but have the same pinned
cost contribution. -/
theorem foldl_initializationEventCost (table : Wasm.CostTableBody)
    (events : List Wasm.CostedInitializationEvent)
    (accumulated : Cost.DynamicVector) :
    events.foldl (fun accumulated event =>
        Cost.sequentialCompose accumulated
          (Wasm.initializationEventCost table event)) accumulated =
      Cost.sequentialCompose accumulated
        (initializationEventsCost table events.length) := by
  induction events generalizing accumulated with
  | nil =>
      exact (Cost.sequentialCompose_zero_right accumulated).symm
  | cons event rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      apply dynamicVector_ext
      intro coordinate
      cases coordinate <;>
        simp [Cost.DynamicCoordinate.value, Wasm.initializationEventCost,
          initializationEventsCost,
          Cost.sequentialCompose, Cost.DynamicVector.zero, Nat.mul_add] <;>
        omega

/-- The direct module has exactly one type, one memory, one function, two
exports and the final Harness-frame construction event. -/
theorem compile_initializationEvents_length {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) :
    (Wasm.Core.Harness.initializationEvents (compile checked).core).length = 6 := by
  rw [Wasm.Core.Harness.initializationEvents_length]
  simp [compile_core, compileCore, moduleOf]

/-- Every successful direct-compiler initialization carries exactly the six
allocation charges and the initial singleton-memory page peak stated by the
source formula. -/
theorem compile_initialization_cost_exact {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation)
    {initialization : Wasm.InitializationObservation P}
    (hinitialization : Wasm.initialGemmInvocationCosted P (compile checked)
      (Gemm.toWasmInvocation G raw) = .ok initialization) :
    initialization.cost = initializationCost P checked := by
  rw [initialization.costExact]
  obtain ⟨request, hrequest, _, hevents, hconfigs⟩ :=
    Wasm.costed_initialization_sound hinitialization
  have hplain := Wasm.costed_initialization_erase hinitialization
  let environment := envOf checked.inputSig checked.plan
  let body := bodyCode environment checked.inputSig.scratch checked.plan
  obtain ⟨core, hcore, hinitial, _, _, _, hpages⟩ :=
    compile_initialization_store_shape checked raw hplain
  have hcore' : Wasm.Core.Exec.instantiateA? ({} : Wasm.Core.Exec.Store)
      (moduleOf environment body) [] = some core := by
    simpa [compile_core, compileCore, environment, body] using hcore
  have hrequestSnapshot :
      Wasm.snapshotOf P.costTableBody.layout request = default := by
    simp [Wasm.snapshotOf, hrequest, Wasm.snapshotRaw,
      Wasm.rawConfigState?]
  have hinitialSnapshot :
      Wasm.snapshotOf P.costTableBody.layout initialization.initial =
        { liveValueSlots := 0
          memoryPages := environment.pages
          tableSize := 0
          liveGcBytes := 0 } := by
    change Wasm.snapshotRaw P.costTableBody.layout initialization.initial.1 = _
    rw [hinitial]
    exact moduleOf_instantiateA?_snapshot environment body
      P.costTableBody.layout _ hcore' hpages
  have hdefaultSnapshot : (default : Wasm.ConfigResourceSnapshot) =
      { liveValueSlots := 0
        memoryPages := 0
        tableSize := 0
        liveGcBytes := 0 } := rfl
  have henvironmentPages : environment.pages = checked.compiledInitialPages := by
    simpa [environment] using env_pages_eq_compiledInitialPages checked
  rw [hevents, hconfigs]
  unfold Wasm.Cost.foldInitialization Wasm.initializationSnapshots
  simp only [Foundation.NonemptyCanonicalList.elements]
  rw [foldl_initializationEventCost]
  rw [compile_initializationEvents_length checked]
  apply dynamicVector_ext
  intro coordinate
  cases coordinate <;>
    simp [Cost.DynamicCoordinate.value, initializationEventsCost,
      initializationCost, hrequestSnapshot, hinitialSnapshot,
      hdefaultSnapshot, henvironmentPages,
      Wasm.peakOverConfigs, Wasm.snapshotPeak,
      Cost.sequentialCompose, Cost.DynamicVector.zero,
      Cost.ComponentwiseMax] <;>
    omega

/-- Closed source formula for the emitted Harness/Core path after fresh
initialization. -/
def executionCost (profile : Wasm.Profile)
    {G : Gemm.Problem profile} (checked : CheckedPlan profile G)
    (raw : G.RawInvocation) : Cost.DynamicVector :=
  let statusSteps := CheckedPlan.compiledStatusSteps checked.plan
  let initialPages := checked.compiledInitialPages
  let targetPages := Wasm.pagesFor (raw.body.ptr.toNat + raw.body.len.toNat)
  let grownPages := targetPages - initialPages
  { Cost.DynamicVector.zero with
      dispatchSteps := 5
      preparationSteps :=
        profile.costTableBody.installationPreparationUnit
      wasmRuleSteps := profile.costTableBody.ruleStepUnit * (statusSteps + 8)
      scalarOps := 1
      bytesWritten :=
        profile.costTableBody.installedByteWriteUnit * raw.body.len.toNat
      memoryGrowPages := grownPages
      peakStackValues :=
        checked.compiledDeclaredLocals + 4 + max statusSteps 1
      peakPages := initialPages + grownPages
      outputBytes := 4 }

/-- The independently stated initialization and execution formulae compose to
the public source `certifiedCost` definition coordinate by coordinate. -/
theorem compose_formula_eq_certifiedCost {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation) :
    Cost.sequentialCompose (initializationCost P checked)
        (executionCost P checked raw) =
      checked.certifiedCost raw := by
  apply dynamicVector_ext
  intro coordinate
  cases coordinate <;>
    simp [Cost.DynamicCoordinate.value, initializationCost, executionCost,
      CheckedPlan.certifiedCost,
      Cost.sequentialCompose, Cost.DynamicVector.zero, Nat.mul_add] <;>
    omega

/-- Once the emitted Harness path is shown locally target- and cost-forced,
the public costed execution relation has exactly the independent source
formula.  This bridge deliberately accepts an operational forcing proof,
rather than a second evaluator-produced cost witness. -/
theorem compile_cost_exact_of_charged {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G)
    (raw : G.RawInvocation)
    (initialization : Wasm.InitializationObservation P)
    {initial : Wasm.Config}
    (costed : Wasm.CostedExecutionObservation P initial)
    (hrun : Wasm.CostedExecutionFor P (compile checked)
      (Gemm.toWasmInvocation G raw) initialization costed)
    {final : Wasm.Core.Harness.Config}
    (forced : Wasm.Core.Harness.ChargedForcedTargets P initial.1
      (executionCost P checked raw) final) :
    Cost.sequentialCompose initialization.cost costed.cost =
      checked.certifiedCost raw := by
  obtain ⟨hinitialization, _, _, hcostedRun⟩ := hrun
  rw [compile_initialization_cost_exact checked raw hinitialization]
  rw [costed.costExact]
  rw [forced.foldTrace_eq hcostedRun]
  exact compose_formula_eq_certifiedCost checked raw

end DirectScalarCost

end WasmGemmGnaf.GNAF
