import WasmGemmGnaf.Wasm.Core.CompleteSuccessors
import WasmGemmGnaf.Wasm.Core.TypedRuntimeMatch

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core

namespace Harness.TypedConfig

/-- Matcher completeness from an explicit compatible runtime store. -/
theorem refMatchCompleteAt_of_storeOrigins (config : TypedConfig)
    {state : Exec.State}
    (horigin : Exec.StoreTypeOriginsA state.store
      (Exec.allocTypes config.raw.module.types)) :
    Exec.RefMatchCompleteAt
      (Exec.allocTypes config.raw.module.types).length state := by
  have hrequest := config.2.requestValid
  obtain ⟨rawTypes, htypes⟩ := hrequest.typesOk
  intro reference target href
  exact Exec.refMatchesN_complete_of_allocated hrequest.1 htypes horigin href

end Harness.TypedConfig

namespace Harness

/-- Matcher completeness from a validated request and an explicit compatible
runtime store.  Stating this independently of `TypedConfig` lets the executable
phase split recurse directly on the raw harness configuration. -/
theorem Request.Valid.refMatchCompleteAt_of_storeOrigins {request : Request}
    (hrequest : request.Valid) {state : Exec.State}
    (horigin : Exec.StoreTypeOriginsA state.store
      (Exec.allocTypes request.module.types)) :
    Exec.RefMatchCompleteAt
      (Exec.allocTypes request.module.types).length state := by
  obtain ⟨rawTypes, htypes⟩ := hrequest.typesOk
  intro reference target href
  exact Exec.refMatchesN_complete_of_allocated hrequest.1 htypes horigin href

/-! ## Executable fresh initialization -/

/-- A checked source module with no imports has an empty semantic import
sequence as well. -/
theorem moduleTypeImports_eq_nil_of_module {module : Module}
    {moduleType : ModuleType} (hmodule : Module_okA module moduleType)
    (himports : module.imports = []) : moduleType.imports = [] := by
  cases hmodule
  simp_all [SeqLen₂, Context.closModuleType, substAllModuleType,
    substModuleType]
  apply List.eq_nil_of_length_eq_zero
  omega

/-- Local spelling retained for the successor proofs; AMD-019 defines the
canonical computations at the Harness execution boundary. -/
abbrev findMemoryExportAddress? := initialMemoryExportAddress?

/-- Local spelling retained for the successor proofs. -/
abbrev findFunctionExportAddress? := initialFunctionExportAddress?

theorem findMemoryExportAddress?_sound {name : Name}
    {entries : List Exec.ExportInst} {address : Exec.MemAddr}
    (h : findMemoryExportAddress? name entries = some address) :
    ({ name := name, addr := .mem address } : Exec.ExportInst) ∈ entries := by
  induction entries with
  | nil => simp [findMemoryExportAddress?] at h
  | cons entry entries ih =>
      rcases entry with ⟨entryName, externalAddress⟩
      by_cases hname : entryName = name
      · subst entryName
        cases externalAddress with
        | tag _ | global _ | table _ | func _ =>
            simp [findMemoryExportAddress?] at h
            exact List.mem_cons_of_mem _ (ih h)
        | mem found =>
            simp [findMemoryExportAddress?] at h
            subst found
            exact List.mem_cons_self
      · simp [findMemoryExportAddress?, hname] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem findFunctionExportAddress?_sound {name : Name}
    {entries : List Exec.ExportInst} {address : Exec.FuncAddr}
    (h : findFunctionExportAddress? name entries = some address) :
    ({ name := name, addr := .func address } : Exec.ExportInst) ∈ entries := by
  induction entries with
  | nil => simp [findFunctionExportAddress?] at h
  | cons entry entries ih =>
      rcases entry with ⟨entryName, externalAddress⟩
      by_cases hname : entryName = name
      · subst entryName
        cases externalAddress with
        | tag _ | global _ | mem _ | table _ =>
            simp [findFunctionExportAddress?] at h
            exact List.mem_cons_of_mem _ (ih h)
        | func found =>
            simp [findFunctionExportAddress?] at h
            subst found
            exact List.mem_cons_self
      · simp [findFunctionExportAddress?, hname] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem findMemoryExportAddress?_exists_of_mem {name : Name}
    {entries : List Exec.ExportInst} {address : Exec.MemAddr}
    (h : ({ name := name, addr := .mem address } : Exec.ExportInst) ∈ entries) :
    ∃ found, findMemoryExportAddress? name entries = some found := by
  induction entries with
  | nil => simp at h
  | cons entry entries ih =>
      simp only [List.mem_cons] at h
      rcases h with heq | htail
      · subst entry
        exact ⟨address, by simp [findMemoryExportAddress?]⟩
      · rcases entry with ⟨entryName, externalAddress⟩
        by_cases hname : entryName = name
        · subst entryName
          cases externalAddress with
          | mem found => exact ⟨found, by simp [findMemoryExportAddress?]⟩
          | tag _ | global _ | table _ | func _ =>
              obtain ⟨found, hfound⟩ := ih htail
              exact ⟨found, by simp [findMemoryExportAddress?, hfound]⟩
        · obtain ⟨found, hfound⟩ := ih htail
          exact ⟨found, by simp [findMemoryExportAddress?, hname, hfound]⟩

theorem findFunctionExportAddress?_exists_of_mem {name : Name}
    {entries : List Exec.ExportInst} {address : Exec.FuncAddr}
    (h : ({ name := name, addr := .func address } : Exec.ExportInst) ∈ entries) :
    ∃ found, findFunctionExportAddress? name entries = some found := by
  induction entries with
  | nil => simp at h
  | cons entry entries ih =>
      simp only [List.mem_cons] at h
      rcases h with heq | htail
      · subst entry
        exact ⟨address, by simp [findFunctionExportAddress?]⟩
      · rcases entry with ⟨entryName, externalAddress⟩
        by_cases hname : entryName = name
        · subst entryName
          cases externalAddress with
          | func found => exact ⟨found, by simp [findFunctionExportAddress?]⟩
          | tag _ | global _ | mem _ | table _ =>
              obtain ⟨found, hfound⟩ := ih htail
              exact ⟨found, by simp [findFunctionExportAddress?, hfound]⟩
        · obtain ⟨found, hfound⟩ := ih htail
          exact ⟨found, by simp [findFunctionExportAddress?, hname, hfound]⟩

/-- The sole executable fresh-initialization candidate.  Failure is represented
by the empty list and is excluded from the public typed carrier by the checked
request-readiness certificate. -/
def initializationSuccessors (request : Request) : List (Event × Config) :=
  match Exec.instantiateA? ({} : Exec.Store) request.module [] with
  | none => []
  | some core =>
      match findMemoryExportAddress? request.memoryExportName
          core.1.frame.mod.exports with
      | none => []
      | some memoryAddress =>
          match findFunctionExportAddress? request.gemmExportName
              core.1.frame.mod.exports with
          | none => []
          | some functionAddress =>
              let harness : Harness :=
                { request := request
                  memoryAddr := memoryAddress
                  gemmAddr := functionAddress }
              [(.initialize (initializationEvents request.module),
                .beforeEntry harness core)]

/-- A computed fresh-initialization candidate is an independent relational
Harness transition. -/
theorem mem_initializationSuccessors_stepA {request : Request}
    (valid : request.Valid) {event : Event} {next : Config}
    (hmem : (event, next) ∈ initializationSuccessors request) :
    StepA (.initializing request) event next := by
  rcases valid with ⟨_, validRest⟩
  rcases validRest with ⟨moduleValidity, validRest⟩
  obtain ⟨moduleType, moduleOk⟩ := moduleValidity
  rcases validRest with ⟨moduleImports, readiness⟩
  have moduleTypeImports :=
    moduleTypeImports_eq_nil_of_module moduleOk moduleImports
  unfold initializationSuccessors at hmem
  cases hcore : Exec.instantiateA? ({} : Exec.Store) request.module [] with
  | none => simp [hcore] at hmem
  | some core =>
      cases hmemory : findMemoryExportAddress? request.memoryExportName
          core.1.frame.mod.exports with
      | none => simp [hcore, hmemory] at hmem
      | some memoryAddress =>
          cases hfunction : findFunctionExportAddress? request.gemmExportName
              core.1.frame.mod.exports with
          | none => simp [hcore, hmemory, hfunction] at hmem
          | some functionAddress =>
              simp only [hcore, hmemory, hfunction, List.mem_singleton,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl⟩
              apply StepA.instantiate
              apply InitializesA.mk
              · apply Exec.instantiateA?_sound_of_module moduleOk
                · simp [SeqLen₂, moduleTypeImports]
                · intro index address externType haddress htype
                  simp [moduleTypeImports] at htype
                · exact hcore
              · exact ⟨findMemoryExportAddress?_sound hmemory,
                  findFunctionExportAddress?_sound hfunction⟩
              · simp [initializationCandidate?, hcore,
                  findMemoryExportAddress?, findFunctionExportAddress?,
                  hmemory, hfunction]

/-- Every checked request makes the executable initialization list nonempty. -/
theorem initializationSuccessors_nonempty {request : Request}
    (valid : request.Valid) :
    ∃ edge, edge ∈ initializationSuccessors request := by
  rcases valid with ⟨_, validRest⟩
  rcases validRest with ⟨moduleValidity, validRest⟩
  rcases validRest with ⟨moduleImports, readiness⟩
  rcases readiness with
    ⟨core, memoryAddress, functionAddress, hcore, hmemory,
      hfunction, _, _⟩
  refine ⟨(.initialize (initializationEvents request.module),
      .beforeEntry
        { request := request, memoryAddr := memoryAddress,
          gemmAddr := functionAddress } core), ?_⟩
  simp [initializationSuccessors, hcore, hmemory, hfunction]

/-- Lift executable Core edges through the normal pre-entry classifier. -/
def beforeCoreSuccessors (harness : Harness) :
    List (Exec.Event × Exec.Config) → List (Event × Config) :=
  List.filterMap fun edge =>
    match liftBeforeCore harness edge.1 edge.2 with
    | none => none
    | some next => some (.coreBeforeEntry edge.1, next)

/-- Lift executable Core edges while a pre-entry trap cause propagates. -/
def trappingBeforeCoreSuccessors (harness : Harness) (trap : Trap) :
    List (Exec.Event × Exec.Config) → List (Event × Config) :=
  List.map fun edge =>
    (.coreBeforeEntry edge.1,
      liftTrappingBeforeCore harness trap edge.2)

/-- Lift executable Core edges through the normal post-entry classifier. -/
def afterCoreSuccessors (harness : Harness) (entry : Exec.Store) :
    List (Exec.Event × Exec.Config) → List (Event × Config) :=
  List.filterMap fun edge =>
    match liftAfterCore harness entry edge.1 edge.2 with
    | none => none
    | some next => some (.coreAfterEntry edge.1, next)

/-- Lift executable Core edges while a post-entry trap cause propagates. -/
def trappingAfterCoreSuccessors (harness : Harness) (entry : Exec.Store)
    (trap : Trap) :
    List (Exec.Event × Exec.Config) → List (Event × Config) :=
  List.map fun edge =>
    (.coreAfterEntry edge.1,
      liftTrappingAfterCore harness entry trap edge.2)

theorem mem_beforeCoreSuccessors_iff {harness : Harness}
    {edges : List (Exec.Event × Exec.Config)} {event : Event} {next : Config} :
    (event, next) ∈ beforeCoreSuccessors harness edges ↔
      ∃ coreEvent coreNext,
        (coreEvent, coreNext) ∈ edges ∧
        event = .coreBeforeEntry coreEvent ∧
        liftBeforeCore harness coreEvent coreNext = some next := by
  constructor
  · intro hmem
    simp only [beforeCoreSuccessors, List.mem_filterMap] at hmem
    obtain ⟨⟨coreEvent, coreNext⟩, hedge, heq⟩ := hmem
    cases hlift : liftBeforeCore harness coreEvent coreNext with
    | none => simp [hlift] at heq
    | some lifted =>
        simp [hlift] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨coreEvent, coreNext, hedge, rfl, hlift⟩
  · rintro ⟨coreEvent, coreNext, hedge, rfl, hlift⟩
    simp only [beforeCoreSuccessors, List.mem_filterMap]
    exact ⟨(coreEvent, coreNext), hedge, by simp [hlift]⟩

theorem mem_trappingBeforeCoreSuccessors_iff {harness : Harness}
    {trap : Trap} {edges : List (Exec.Event × Exec.Config)}
    {event : Event} {next : Config} :
    (event, next) ∈ trappingBeforeCoreSuccessors harness trap edges ↔
      ∃ coreEvent coreNext,
        (coreEvent, coreNext) ∈ edges ∧
        event = .coreBeforeEntry coreEvent ∧
        next = liftTrappingBeforeCore harness trap coreNext := by
  constructor
  · intro hmem
    simp only [trappingBeforeCoreSuccessors, List.mem_map] at hmem
    obtain ⟨⟨coreEvent, coreNext⟩, hedge, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact ⟨coreEvent, coreNext, hedge, heq.1.symm, heq.2.symm⟩
  · rintro ⟨coreEvent, coreNext, hedge, rfl, rfl⟩
    simp only [trappingBeforeCoreSuccessors, List.mem_map]
    exact ⟨(coreEvent, coreNext), hedge, rfl⟩

theorem mem_afterCoreSuccessors_iff {harness : Harness}
    {entry : Exec.Store} {edges : List (Exec.Event × Exec.Config)}
    {event : Event} {next : Config} :
    (event, next) ∈ afterCoreSuccessors harness entry edges ↔
      ∃ coreEvent coreNext,
        (coreEvent, coreNext) ∈ edges ∧
        event = .coreAfterEntry coreEvent ∧
        liftAfterCore harness entry coreEvent coreNext = some next := by
  constructor
  · intro hmem
    simp only [afterCoreSuccessors, List.mem_filterMap] at hmem
    obtain ⟨⟨coreEvent, coreNext⟩, hedge, heq⟩ := hmem
    cases hlift : liftAfterCore harness entry coreEvent coreNext with
    | none => simp [hlift] at heq
    | some lifted =>
        simp [hlift] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨coreEvent, coreNext, hedge, rfl, hlift⟩
  · rintro ⟨coreEvent, coreNext, hedge, rfl, hlift⟩
    simp only [afterCoreSuccessors, List.mem_filterMap]
    exact ⟨(coreEvent, coreNext), hedge, by simp [hlift]⟩

theorem mem_trappingAfterCoreSuccessors_iff {harness : Harness}
    {entry : Exec.Store} {trap : Trap}
    {edges : List (Exec.Event × Exec.Config)}
    {event : Event} {next : Config} :
    (event, next) ∈ trappingAfterCoreSuccessors harness entry trap edges ↔
      ∃ coreEvent coreNext,
        (coreEvent, coreNext) ∈ edges ∧
        event = .coreAfterEntry coreEvent ∧
        next = liftTrappingAfterCore harness entry trap coreNext := by
  constructor
  · intro hmem
    simp only [trappingAfterCoreSuccessors, List.mem_map] at hmem
    obtain ⟨⟨coreEvent, coreNext⟩, hedge, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact ⟨coreEvent, coreNext, hedge, heq.1.symm, heq.2.symm⟩
  · rintro ⟨coreEvent, coreNext, hedge, rfl, rfl⟩
    simp only [trappingAfterCoreSuccessors, List.mem_map]
    exact ⟨(coreEvent, coreNext), hedge, rfl⟩

/-- The deterministic raw-byte installation edge, when all partial updates
compute. -/
def installRawSuccessors (harness : Harness) (state : Exec.State) :
    List (Event × Config) :=
  match installRaw? harness state with
  | none => []
  | some (previousPages, grownPages, next) =>
      [(.installRaw harness.memoryAddr harness.request.rawPtr.val
          harness.request.rawLen.val previousPages grownPages,
        .readyToEnter harness next)]

/-- The two released ABI arguments have their exact Core numeric types. -/
theorem Harness.args_val_ok (harness : Harness) (store : Exec.Store) :
    SeqAll₂ (fun value type => Exec.Val_okA store value type) harness.args
      [.num .i32, .num .i32] := by
  letI : Exec.ExecutionAuthority := Exec.amendedExecutionAuthority
  intro index value type hvalue htype
  cases index with
  | zero =>
      simp [Harness.args] at hvalue htype
      subst value
      subst type
      exact .num .mk
  | succ index =>
      cases index with
      | zero =>
          simp [Harness.args] at hvalue htype
          subst value
          subst type
          exact .num .mk
      | succ index => simp [Harness.args] at hvalue

/-- Executable invocation result for the released two-i32 ABI. -/
def invokeResult? (harness : Harness) (store : Exec.Store) :
    Option Exec.Config :=
  match store.funcs[harness.gemmAddr]? with
  | none => none
  | some function =>
      match expandDt function.type with
      | some (.func (.cons (.num .i32) (.cons (.num .i32) .nil)) codomain) =>
          some (⟨store, { mod := {} }⟩,
            Exec.vals harness.args ++
              [.addrref (.funcAddr harness.gemmAddr),
                .plain (.callRef (.defd function.type))])
      | _ => none

theorem invokeResult?_sound {harness : Harness} {store : Exec.Store}
    {core : Exec.Config} (h : invokeResult? harness store = some core) :
    Exec.InvokeA store harness.gemmAddr harness.args core := by
  unfold invokeResult? at h
  cases hfunction : store.funcs[harness.gemmAddr]? with
  | none => simp [hfunction] at h
  | some function =>
      simp only [hfunction] at h
      cases hexpand : expandDt function.type with
      | none => simp [hexpand] at h
      | some expanded =>
          simp only [hexpand] at h
          cases expanded with
          | array _ | struct _ => simp at h
          | func domain codomain =>
              cases domain <;> try simp at h
              rename_i first tail
              cases first <;> try simp at h
              rename_i numType
              cases numType <;> try simp at h
              cases tail <;> try simp at h
              rename_i second remaining
              cases second <;> try simp at h
              rename_i secondNumType
              cases secondNumType <;> try simp at h
              cases remaining <;> try simp at h
              rcases h with ⟨rfl, rfl⟩
              letI : Exec.ExecutionAuthority := Exec.amendedExecutionAuthority
              exact .mk hfunction (.mk hexpand) rfl
                (harness.args_val_ok store)

/-- The unique entry-boundary edge when invocation premises compute. -/
def enterGemmSuccessors (harness : Harness) (state : Exec.State) :
    List (Event × Config) :=
  match invokeResult? harness state.store with
  | none => []
  | some invoked =>
      [(.enterGemm harness.gemmAddr,
        .afterEntry harness state.store invoked)]

theorem mem_enterGemmSuccessors_stepA (harness : Harness)
    (state : Exec.State) (event : Event) (next : Config)
    (hmem : (event, next) ∈ enterGemmSuccessors harness state) :
    StepA (.readyToEnter harness state) event next := by
  unfold enterGemmSuccessors at hmem
  cases hinvoke : invokeResult? harness state.store with
  | none => simp [hinvoke] at hmem
  | some invoked =>
      simp only [hinvoke, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact .enterGemm (invokeResult?_sound hinvoke)

theorem invokeResult?_complete {harness : Harness} {store : Exec.Store}
    {core : Exec.Config}
    (hinvoke : Exec.InvokeA store harness.gemmAddr harness.args core) :
    invokeResult? harness store = some core := by
  cases hinvoke with
  | @mk function domain codomain hfunction hexpand hlength hvalues =>
      cases hexpand with
      | mk hexpand =>
      cases domain with
      | nil =>
          change 2 = 0 at hlength
          omega
      | cons first tail =>
          cases tail with
          | nil =>
              change 2 = 1 at hlength
              omega
          | cons second remaining =>
              have hremaining : remaining = .nil := by
                cases remaining with
                | nil => rfl
                | cons third more =>
                    change 2 = (first :: second :: third :: more.toList).length
                      at hlength
                    simp only [List.length_cons] at hlength
                    omega
              subst remaining
              have hfirst : Exec.Val_okA store
                  (.num ⟨.i32, harness.request.rawPtr⟩) first :=
                hvalues 0 _ _ (by simp [Harness.args])
                  (by simp [ValTypes.toList])
              have hsecond : Exec.Val_okA store
                  (.num ⟨.i32, harness.request.rawLen⟩) second :=
                hvalues 1 _ _ (by simp [Harness.args])
                  (by simp [ValTypes.toList])
              cases hfirst with
              | num hnumberFirst =>
                  cases hnumberFirst
                  cases hsecond with
                  | num hnumberSecond =>
                      cases hnumberSecond
                      simp [invokeResult?, hfunction, hexpand]

theorem enterGemm_mem_successors {harness : Harness} {state : Exec.State}
    {core : Exec.Config}
    (hinvoke : Exec.InvokeA state.store harness.gemmAddr harness.args core) :
    ((.enterGemm harness.gemmAddr,
      .afterEntry harness state.store core) ∈
        enterGemmSuccessors harness state) := by
  have hinvoked := invokeResult?_complete hinvoke
  unfold enterGemmSuccessors
  rw [hinvoked]
  simp

/-- Recognize the one-value normal return shape. -/
def returnAfterSuccessors (harness : Harness) (entry : Exec.Store)
    (core : Exec.Config) : List (Event × Config) :=
  match core.2 with
  | [instruction] =>
      match Exec.adminToVal instruction with
      | none => []
      | some value =>
          [(.returnAfterEntry, .returned harness entry value core.1)]
  | _ => []

/-- Recognize an uncaught pre-entry exception and retain its allocated value. -/
def throwBeforeSuccessors (harness : Harness) (core : Exec.Config) :
    List (Event × Config) :=
  match core.2 with
  | [.addrref (.exnAddr address), .plain .throwRef] =>
      match core.1.exninst[address]? with
      | none => []
      | some exception =>
          [(.throwBeforeEntry address,
            .thrownBeforeEntry harness address exception core.1)]
  | _ => []

/-- Post-entry uncaught-exception counterpart. -/
def throwAfterSuccessors (harness : Harness) (entry : Exec.Store)
    (core : Exec.Config) : List (Event × Config) :=
  match core.2 with
  | [.addrref (.exnAddr address), .plain .throwRef] =>
      match core.1.exninst[address]? with
      | none => []
      | some exception =>
          [(.throwAfterEntry address,
            .thrownAfterEntry harness entry address exception core.1)]
  | _ => []

/-- Every Core edge from one typed Harness phase. -/
def coreSuccessorsForRequest (request : Request) (valid : request.Valid)
    (core : Exec.Config)
    (compatible : Exec.CompatibleConfigTypeOriginsA
      (Exec.allocTypes request.module.types) core) :
    List (Exec.Event × Exec.Config) :=
  Exec.compatibleSuccessors (Exec.allocTypes request.module.types)
    (Exec.allocTypes request.module.types).length
    (fun candidate candidateCompatible =>
      valid.refMatchCompleteAt_of_storeOrigins candidateCompatible.1)
    core compatible

theorem mem_coreSuccessorsForRequest_iff_stepA (request : Request)
    (valid : request.Valid)
    (core : Exec.Config)
    (compatible : Exec.CompatibleConfigTypeOriginsA
      (Exec.allocTypes request.module.types) core)
    (event : Exec.Event) (next : Exec.Config) :
    (event, next) ∈ coreSuccessorsForRequest request valid core compatible ↔
      Exec.StepA core event next := by
  unfold coreSuccessorsForRequest
  exact Exec.mem_compatibleSuccessors_iff_stepA _ _ _ _ _

theorem mem_installRawSuccessors_stepA (harness : Harness)
    (state : Exec.State) (event : Event) (next : Config)
    (hmem : (event, next) ∈ installRawSuccessors harness state) :
    StepA (.beforeEntry harness (state, [])) event next := by
  unfold installRawSuccessors at hmem
  cases hinstall : installRaw? harness state with
  | none => simp [hinstall] at hmem
  | some result =>
      rcases result with ⟨previousPages, grownPages, nextState⟩
      simp only [hinstall, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact .installRaw hinstall

theorem installRaw_mem_successors {harness : Harness} {state next : Exec.State}
    {previousPages grownPages : Nat}
    (hinstall : installRaw? harness state =
      some (previousPages, grownPages, next)) :
    ((.installRaw harness.memoryAddr harness.request.rawPtr.val
        harness.request.rawLen.val previousPages grownPages,
      .readyToEnter harness next) ∈ installRawSuccessors harness state) := by
  simp [installRawSuccessors, hinstall]

theorem mem_returnAfterSuccessors_iff_stepA (harness : Harness)
    (entry : Exec.Store) (core : Exec.Config) (event : Event) (next : Config) :
    (event, next) ∈ returnAfterSuccessors harness entry core ↔
      (event = .returnAfterEntry ∧
        StepA (.afterEntry harness entry core) event next) := by
  constructor
  · intro hmem
    rcases core with ⟨state, instructions⟩
    unfold returnAfterSuccessors at hmem
    cases instructions with
    | nil => simp at hmem
    | cons instruction rest =>
        cases rest with
        | cons nextInstruction tail => simp at hmem
        | nil =>
            cases hvalue : Exec.adminToVal instruction with
            | none => simp [hvalue] at hmem
            | some value =>
                simp only [hvalue, List.mem_singleton, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl⟩
                have hinstruction := Exec.toAdmin_of_adminToVal hvalue
                subst instruction
                exact ⟨rfl, .returnAfter⟩
  · rintro ⟨rfl, hstep⟩
    cases hstep with
    | returnAfter =>
        simp [returnAfterSuccessors, Exec.adminToVal_toAdmin]

theorem mem_throwBeforeSuccessors_iff_stepA (harness : Harness)
    (core : Exec.Config) (event : Event) (next : Config) :
    (event, next) ∈ throwBeforeSuccessors harness core ↔
      (∃ address, event = .throwBeforeEntry address ∧
        StepA (.beforeEntry harness core) event next) := by
  constructor
  · intro hmem
    rcases core with ⟨state, instructions⟩
    unfold throwBeforeSuccessors at hmem
    split at hmem <;> try simp at hmem
    rename_i address hshape
    change instructions =
      [.addrref (.exnAddr address), .plain .throwRef] at hshape
    subst instructions
    cases hlookup : state.exninst[address]? with
    | none => simp [hlookup] at hmem
    | some exception =>
        simp only [hlookup, List.mem_singleton, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨address, rfl, .throwBefore hlookup⟩
  · rintro ⟨address, rfl, hstep⟩
    cases hstep with
    | throwBefore hlookup => simp [throwBeforeSuccessors, hlookup]

theorem mem_throwAfterSuccessors_iff_stepA (harness : Harness)
    (entry : Exec.Store) (core : Exec.Config) (event : Event) (next : Config) :
    (event, next) ∈ throwAfterSuccessors harness entry core ↔
      (∃ address, event = .throwAfterEntry address ∧
        StepA (.afterEntry harness entry core) event next) := by
  constructor
  · intro hmem
    rcases core with ⟨state, instructions⟩
    unfold throwAfterSuccessors at hmem
    split at hmem <;> try simp at hmem
    rename_i address hshape
    change instructions =
      [.addrref (.exnAddr address), .plain .throwRef] at hshape
    subst instructions
    cases hlookup : state.exninst[address]? with
    | none => simp [hlookup] at hmem
    | some exception =>
        simp only [hlookup, List.mem_singleton, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨address, rfl, .throwAfter hlookup⟩
  · rintro ⟨address, rfl, hstep⟩
    cases hstep with
    | throwAfter hlookup => simp [throwAfterSuccessors, hlookup]

/-- Exact executable Harness edges for every post-instantiation phase.  The
initializing phase is added only after its separate relational functionality
proof is available. -/
def postInitializationSuccessorsRaw (config : Config)
    (origins : config.RuntimeTypeOriginsA)
    (valid : config.request.Valid) :
    List (Event × Config) :=
  match config with
  | .initializing _ => []
  | .beforeEntry harness core =>
      beforeCoreSuccessors harness
          (coreSuccessorsForRequest harness.request valid core origins) ++
        (match core.2 with
        | [] => installRawSuccessors harness core.1
        | _ => []) ++
        throwBeforeSuccessors harness core
  | .trappingBeforeEntry harness trap core =>
      trappingBeforeCoreSuccessors harness trap
        (coreSuccessorsForRequest harness.request valid core origins)
  | .readyToEnter harness state => enterGemmSuccessors harness state
  | .afterEntry harness entry core =>
      afterCoreSuccessors harness entry
          (coreSuccessorsForRequest harness.request valid core origins) ++
        returnAfterSuccessors harness entry core ++
        throwAfterSuccessors harness entry core
  | .trappingAfterEntry harness entry trap core =>
      trappingAfterCoreSuccessors harness entry trap
        (coreSuccessorsForRequest harness.request valid core origins)
  | .returned _ _ _ _ | .trappedBeforeEntry _ _ _ |
      .trappedAfterEntry _ _ _ _ | .thrownBeforeEntry _ _ _ _ |
      .thrownAfterEntry _ _ _ _ _ => []

def postInitializationSuccessors (config : TypedConfig) :
    List (Event × Config) :=
  postInitializationSuccessorsRaw config.raw config.2.runtimeTypeOriginsA
    config.2.requestValid

theorem mem_postInitializationSuccessorsRaw_stepA {config : Config}
    (origins : config.RuntimeTypeOriginsA) (valid : config.request.Valid)
    {event : Event} {next : Config}
    (hmem : (event, next) ∈
      postInitializationSuccessorsRaw config origins valid) :
    StepA config event next := by
  cases config with
  | initializing request =>
      simp [postInitializationSuccessorsRaw] at hmem
  | beforeEntry harness core =>
      rcases core with ⟨state, instructions⟩
      simp only [postInitializationSuccessorsRaw, List.mem_append] at hmem
      rcases hmem with (hcore | hinstall) | hthrow
      · rw [mem_beforeCoreSuccessors_iff] at hcore
        obtain ⟨coreEvent, coreNext, hedge, rfl, hlift⟩ := hcore
        apply (stepA_coreBefore_iff harness (state, instructions)
          coreEvent next).mpr
        refine ⟨coreNext, ?_, hlift⟩
        exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          (state, instructions) origins coreEvent coreNext).mp hedge
      · cases instructions with
        | nil => exact mem_installRawSuccessors_stepA harness state event next hinstall
        | cons instruction rest => simp at hinstall
      · obtain ⟨address, hevent, hstep⟩ :=
          (mem_throwBeforeSuccessors_iff_stepA harness
            (state, instructions) event next).mp hthrow
        exact hstep
  | trappingBeforeEntry harness trap core =>
      simp only [postInitializationSuccessorsRaw] at hmem
      rw [mem_trappingBeforeCoreSuccessors_iff] at hmem
      obtain ⟨coreEvent, coreNext, hedge, rfl, rfl⟩ := hmem
      apply (stepA_trappingBefore_iff harness trap core coreEvent _).mpr
      refine ⟨coreNext, ?_, rfl⟩
      exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid core
        origins coreEvent coreNext).mp hedge
  | readyToEnter harness state =>
      simp only [postInitializationSuccessorsRaw] at hmem
      exact mem_enterGemmSuccessors_stepA harness state event next hmem
  | afterEntry harness entry core =>
      simp only [postInitializationSuccessorsRaw, List.mem_append] at hmem
      rcases hmem with (hcore | hreturn) | hthrow
      · rw [mem_afterCoreSuccessors_iff] at hcore
        obtain ⟨coreEvent, coreNext, hedge, rfl, hlift⟩ := hcore
        apply (stepA_coreAfter_iff harness entry core coreEvent next).mpr
        refine ⟨coreNext, ?_, hlift⟩
        exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid core
          origins coreEvent coreNext).mp hedge
      · obtain ⟨hevent, hstep⟩ :=
          (mem_returnAfterSuccessors_iff_stepA harness entry core
            event next).mp hreturn
        exact hstep
      · obtain ⟨address, hevent, hstep⟩ :=
          (mem_throwAfterSuccessors_iff_stepA harness entry core
            event next).mp hthrow
        exact hstep
  | trappingAfterEntry harness entry trap core =>
      simp only [postInitializationSuccessorsRaw] at hmem
      rw [mem_trappingAfterCoreSuccessors_iff] at hmem
      obtain ⟨coreEvent, coreNext, hedge, rfl, rfl⟩ := hmem
      apply (stepA_trappingAfter_iff harness entry trap core coreEvent _).mpr
      refine ⟨coreNext, ?_, rfl⟩
      exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid core
        origins coreEvent coreNext).mp hedge
  | returned harness entry value state =>
      simp [postInitializationSuccessorsRaw] at hmem
  | trappedBeforeEntry harness trap state =>
      simp [postInitializationSuccessorsRaw] at hmem
  | trappedAfterEntry harness entry trap state =>
      simp [postInitializationSuccessorsRaw] at hmem
  | thrownBeforeEntry harness address exception state =>
      simp [postInitializationSuccessorsRaw] at hmem
  | thrownAfterEntry harness entry address exception state =>
      simp [postInitializationSuccessorsRaw] at hmem

theorem mem_postInitializationSuccessors_stepA {config : TypedConfig}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ postInitializationSuccessors config) :
    StepA config.raw event next :=
  mem_postInitializationSuccessorsRaw_stepA
    config.2.runtimeTypeOriginsA config.2.requestValid hmem

theorem stepA_mem_postInitializationSuccessorsRaw {config : Config}
    (origins : config.RuntimeTypeOriginsA) (valid : config.request.Valid)
    {event : Event} {next : Config}
    (hphase : ∀ request, config ≠ .initializing request)
    (hstep : StepA config event next) :
    (event, next) ∈ postInitializationSuccessorsRaw config origins valid := by
  cases hstep with
  | @instantiate request target hinitializes =>
      exact False.elim (hphase request rfl)
  | @coreBefore harness source target coreEvent hcore hcause htarget =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_beforeCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftBeforeCore, hcause, isRawTrap_eq_true_iff, htarget]
  | @coreBeforeTrap harness source target coreEvent cause hcore hcause htarget =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_beforeCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftBeforeCore, hcause, isRawTrap_eq_true_iff, htarget]
  | @coreBeforeTrapFinal harness source state coreEvent cause hcore hcause =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_beforeCoreSuccessors_iff]
      refine ⟨coreEvent, (state, [.trap]), ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent (state, [.trap])).mpr hcore
      · simp [liftBeforeCore, hcause, isRawTrap]
  | @coreTrappingBefore harness trap source target coreEvent hcore htarget =>
      simp only [postInitializationSuccessorsRaw]
      rw [mem_trappingBeforeCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftTrappingBeforeCore, isRawTrap_eq_true_iff, htarget]
  | @coreTrappingBeforeFinal harness trap source state coreEvent hcore =>
      simp only [postInitializationSuccessorsRaw]
      rw [mem_trappingBeforeCoreSuccessors_iff]
      refine ⟨coreEvent, (state, [.trap]), ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent (state, [.trap])).mpr hcore
      · simp [liftTrappingBeforeCore, isRawTrap]
  | @installRaw harness source target previousPages grownPages hinstall =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      exact Or.inl (Or.inr (installRaw_mem_successors hinstall))
  | @enterGemm harness state core hinvoke =>
      simp only [postInitializationSuccessorsRaw]
      exact enterGemm_mem_successors hinvoke
  | @coreAfter harness entry source target coreEvent hcore hcause htarget =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_afterCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftAfterCore, hcause, isRawTrap_eq_true_iff, htarget]
  | @coreAfterTrap harness entry source target coreEvent cause hcore hcause htarget =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_afterCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftAfterCore, hcause, isRawTrap_eq_true_iff, htarget]
  | @coreAfterTrapFinal harness entry source state coreEvent cause hcore hcause =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inl
      rw [mem_afterCoreSuccessors_iff]
      refine ⟨coreEvent, (state, [.trap]), ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent (state, [.trap])).mpr hcore
      · simp [liftAfterCore, hcause, isRawTrap]
  | @coreTrappingAfter harness entry trap source target coreEvent hcore htarget =>
      simp only [postInitializationSuccessorsRaw]
      rw [mem_trappingAfterCoreSuccessors_iff]
      refine ⟨coreEvent, target, ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent target).mpr hcore
      · simp [liftTrappingAfterCore, isRawTrap_eq_true_iff, htarget]
  | @coreTrappingAfterFinal harness entry trap source state coreEvent hcore =>
      simp only [postInitializationSuccessorsRaw]
      rw [mem_trappingAfterCoreSuccessors_iff]
      refine ⟨coreEvent, (state, [.trap]), ?_, rfl, ?_⟩
      · exact (mem_coreSuccessorsForRequest_iff_stepA harness.request valid
          source origins coreEvent (state, [.trap])).mpr hcore
      · simp [liftTrappingAfterCore, isRawTrap]
  | @returnAfter harness entry state value =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inl
      apply Or.inr
      exact (mem_returnAfterSuccessors_iff_stepA harness entry
        (state, Exec.vals [value]) .returnAfterEntry
        (.returned harness entry value state)).mpr ⟨rfl, .returnAfter⟩
  | @throwBefore harness state address exception hlookup =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inr
      exact (mem_throwBeforeSuccessors_iff_stepA harness
        (state, [.addrref (.exnAddr address), .plain .throwRef])
        (.throwBeforeEntry address)
        (.thrownBeforeEntry harness address exception state)).mpr
          ⟨address, rfl, .throwBefore hlookup⟩
  | @throwAfter harness entry state address exception hlookup =>
      simp only [postInitializationSuccessorsRaw, List.mem_append]
      apply Or.inr
      exact (mem_throwAfterSuccessors_iff_stepA harness entry
        (state, [.addrref (.exnAddr address), .plain .throwRef])
        (.throwAfterEntry address)
        (.thrownAfterEntry harness entry address exception state)).mpr
          ⟨address, rfl, .throwAfter hlookup⟩

theorem stepA_mem_postInitializationSuccessors {config : TypedConfig}
    {event : Event} {next : Config}
    (hphase : ∀ request, config.raw ≠ .initializing request)
    (hstep : StepA config.raw event next) :
    (event, next) ∈ postInitializationSuccessors config :=
  stepA_mem_postInitializationSuccessorsRaw config.2.runtimeTypeOriginsA
    config.2.requestValid hphase hstep

/-! ## Complete raw and proof-carrying Harness successor lists -/

/-- Fresh-initialization candidates at exactly the initializing phase. -/
def initializationSuccessorsFor : Config → List (Event × Config) := fun config =>
  match config with
  | .initializing request => initializationSuccessors request
  | _ => []

theorem mem_initializationSuccessorsFor_stepA {config : Config}
    (valid : config.request.Valid) {event : Event} {next : Config}
    (hmem : (event, next) ∈ initializationSuccessorsFor config) :
    StepA config event next := by
  cases config with
  | initializing request =>
      exact mem_initializationSuccessors_stepA valid
        (by simpa [initializationSuccessorsFor] using hmem)
  | beforeEntry | trappingBeforeEntry | readyToEnter | afterEntry |
      trappingAfterEntry | returned | trappedBeforeEntry | trappedAfterEntry |
      thrownBeforeEntry | thrownAfterEntry =>
      simp [initializationSuccessorsFor] at hmem

/-- Exact executable candidates for every phase of a checked Harness
configuration, including fresh initialization. -/
def rawSuccessors (config : Config) (origins : config.RuntimeTypeOriginsA)
    (valid : config.request.Valid) : List (Event × Config) :=
  initializationSuccessorsFor config ++
    postInitializationSuccessorsRaw config origins valid

theorem mem_rawSuccessors_stepA {config : Config}
    (origins : config.RuntimeTypeOriginsA) (valid : config.request.Valid)
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ rawSuccessors config origins valid) :
    StepA config event next := by
  simp only [rawSuccessors, List.mem_append] at hmem
  rcases hmem with hinitialization | hpost
  · exact mem_initializationSuccessorsFor_stepA valid hinitialization
  · exact mem_postInitializationSuccessorsRaw_stepA origins valid hpost

/-- Every authority Harness transition from a checked raw configuration occurs
in the executable list.  AMD-019 supplies fresh-target functionality; every
post-initialization phase was already enumerated directly. -/
theorem stepA_mem_rawSuccessors
    {config : Config} (origins : config.RuntimeTypeOriginsA)
    (valid : config.request.Valid) {event : Event} {next : Config}
    (hstep : StepA config event next) :
    (event, next) ∈ rawSuccessors config origins valid := by
  by_cases hinitializing : ∃ request, config = .initializing request
  · obtain ⟨request, rfl⟩ := hinitializing
    have hevent : event = .initialize (initializationEvents request.module) :=
      (stepA_initializing_iff request event next).mp hstep |>.1
    subst event
    obtain ⟨⟨candidateEvent, candidateNext⟩, hcandidate⟩ :=
      initializationSuccessors_nonempty valid
    have hcandidateStep := mem_initializationSuccessors_stepA valid hcandidate
    have hcandidateEvent :
        candidateEvent = .initialize (initializationEvents request.module) :=
      (stepA_initializing_iff request candidateEvent candidateNext).mp
        hcandidateStep |>.1
    subst candidateEvent
    have hcandidateInit : InitializesA request candidateNext :=
      (stepA_initializing_iff request
        (.initialize (initializationEvents request.module)) candidateNext).mp
          hcandidateStep |>.2
    have hnextInit : InitializesA request next :=
      (stepA_initializing_iff request
        (.initialize (initializationEvents request.module)) next).mp hstep |>.2
    have hnext : candidateNext = next :=
      InitializesA.target_functional hcandidateInit hnextInit
    subst candidateNext
    simp only [rawSuccessors, List.mem_append]
    exact Or.inl (by simpa [initializationSuccessorsFor] using hcandidate)
  · simp only [rawSuccessors, List.mem_append]
    apply Or.inr
    apply stepA_mem_postInitializationSuccessorsRaw origins valid
    · intro request heq
      exact hinitializing ⟨request, heq⟩
    · exact hstep

/-! ### Proof-carrying public successors -/

/-- Attach the preservation proof to every raw successor of a public typed
configuration.  `List.attach` supplies exactly the membership proof consumed by
`TypedConfig.successor`; no progress or successor claim is stored in the public
carrier. -/
def typedSuccessors (config : TypedConfig) : List (Event × TypedConfig) :=
  (rawSuccessors config.raw config.2.runtimeTypeOriginsA
      config.2.requestValid).attach.map fun edge =>
    (edge.1.1,
      config.successor edge.1.1 edge.1.2
        (mem_rawSuccessors_stepA config.2.runtimeTypeOriginsA
          config.2.requestValid edge.2))

/-- Every proof-carrying executable successor is an authority Harness step. -/
theorem mem_typedSuccessors_stepA {config : TypedConfig}
    {event : Event} {next : TypedConfig}
    (hmem : (event, next) ∈ typedSuccessors config) :
    TypedStep config event next := by
  unfold typedSuccessors at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨edge, _, heq⟩ := hmem
  rcases edge with ⟨⟨rawEvent, rawNext⟩, hraw⟩
  simp only at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact mem_rawSuccessors_stepA config.2.runtimeTypeOriginsA
    config.2.requestValid hraw

/-- Every public typed Harness transition occurs in the proof-carrying
executable successor list. -/
theorem stepA_mem_typedSuccessors
    {config : TypedConfig} {event : Event} {next : TypedConfig}
    (hstep : TypedStep config event next) :
    (event, next) ∈ typedSuccessors config := by
  have hraw : (event, next.1) ∈ rawSuccessors config.raw
      config.2.runtimeTypeOriginsA config.2.requestValid :=
    stepA_mem_rawSuccessors config.2.runtimeTypeOriginsA
      config.2.requestValid hstep
  unfold typedSuccessors
  apply List.mem_map.mpr
  refine ⟨⟨(event, next.1), hraw⟩, ?_, ?_⟩
  · simp
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

end Harness

end WasmGemmGnaf.Wasm.Core
