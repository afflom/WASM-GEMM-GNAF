import WasmGemmGnaf.Wasm.Core.HarnessReadiness

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Harness

/-- The executable fresh-initialization candidate selected by a checked
request carries the checked GEMM function ABI. -/
theorem Request.Valid.initializationSuccessor_gemmReady {request : Request}
    (valid : request.Valid) {event : Event} {next : Config}
    (hmem : (event, next) ∈ initializationSuccessors request) :
    next.GemmReady := by
  rcases valid with ⟨_, ⟨_, _, core, memoryAddress, functionAddress,
    hcore, hmemory, hfunction, hready, _⟩⟩
  simp [initializationSuccessors, hcore, hmemory, hfunction] at hmem
  rcases hmem with ⟨rfl, rfl⟩
  exact hready

/-- Every reachable post-initialization Harness configuration retains the
computed GEMM function ABI established by its checked request. -/
theorem Config.WellTyped.gemmReady_of_not_initializing {config : Config}
    (typed : config.WellTyped)
    (hnot : ∀ request, config ≠ .initializing request) :
    config.GemmReady := by
  rcases typed with ⟨request, trace, valid, steps⟩
  cases steps with
  | refl => exact False.elim (hnot request rfl)
  | @cons first middle final event tail firstStep rest =>
      obtain ⟨edge, hedge⟩ := initializationSuccessors_nonempty valid
      rcases edge with ⟨candidateEvent, candidate⟩
      have candidateStep :
          StepA (.initializing request) candidateEvent candidate :=
        mem_initializationSuccessors_stepA valid hedge
      have candidateInit : InitializesA request candidate :=
        (stepA_initializing_iff request candidateEvent candidate).mp
          candidateStep |>.2
      have firstInit : InitializesA request middle :=
        (stepA_initializing_iff request event middle).mp firstStep |>.2
      have hmiddle : candidate = middle :=
        InitializesA.target_functional candidateInit firstInit
      have candidateReady : candidate.GemmReady :=
        valid.initializationSuccessor_gemmReady hedge
      rw [hmiddle] at candidateReady
      exact rest.preserveGemmReady candidateReady

/-- A positive checked GEMM ABI lookup computes the executable invocation
configuration used by the successor enumerator. -/
theorem invokeResult?_exists_of_gemmFunctionReady {harness : Harness}
    {store : Exec.Store} (ready : GemmFunctionReady harness store) :
    ∃ core, invokeResult? harness store = some core := by
  unfold GemmFunctionReady at ready
  rw [Option.bind_eq_some_iff] at ready
  obtain ⟨function, hfunction, hexpand⟩ := ready
  refine ⟨(⟨store, { mod := {} }⟩,
      Exec.vals harness.args ++
        [.addrref (.funcAddr harness.gemmAddr),
          .plain (.callRef (.defd function.type))]), ?_⟩
  simp [invokeResult?, hfunction, hexpand, ValTypes.ofList]

namespace TypedConfig

/-- Any exhibited raw authority transition from a public source supplies a
proof-carrying executable successor. -/
theorem successors_nonempty_of_rawStep {config : TypedConfig}
    {event : Event} {rawNext : Config}
    (step : StepA config.raw event rawNext) :
    ∃ edge, edge ∈ typedSuccessors config := by
  let next : TypedConfig := config.successor event rawNext step
  refine ⟨(event, next), ?_⟩
  exact stepA_mem_typedSuccessors step

/-- Every reachable initializing phase has the single checked executable
fresh-instantiation successor. -/
theorem initializing_successors_nonempty {config : TypedConfig}
    {request : Request} (heq : config.raw = .initializing request) :
    ∃ edge, edge ∈ typedSuccessors config := by
  have valid := config.2.requestValid
  change config.raw.request.Valid at valid
  rw [heq] at valid
  obtain ⟨⟨event, rawNext⟩, hmem⟩ :=
    initializationSuccessors_nonempty valid
  have step : StepA config.raw event rawNext := by
    rw [heq]
    exact mem_initializationSuccessors_stepA valid hmem
  exact successors_nonempty_of_rawStep step

/-- Once the checked raw-install computation has been transported to the
normal pre-entry return state, the Harness exposes its exact install edge. -/
theorem beforeEntryEmpty_successors_nonempty {config : TypedConfig}
    {harness : Harness} {state : Exec.State}
    (heq : config.raw = .beforeEntry harness (state, []))
    (ready : RawInstallReady harness state) :
    ∃ edge, edge ∈ typedSuccessors config := by
  obtain ⟨previousPages, grownPages, rawNext, hinstall⟩ :=
    ready.exists_result
  have step : StepA config.raw
      (.installRaw harness.memoryAddr harness.request.rawPtr.val
        harness.request.rawLen.val previousPages grownPages)
      (.readyToEnter harness rawNext) := by
    rw [heq]
    exact .installRaw hinstall
  exact successors_nonempty_of_rawStep step

/-- A reachable entry-boundary configuration always has its computed
`enterGemm` successor.  The proof uses the request's checked ABI equality and
ordinary function-store preservation; it stores no progress conclusion in the
public carrier. -/
theorem readyToEnter_successors_nonempty {config : TypedConfig}
    {harness : Harness} {state : Exec.State}
    (heq : config.raw = .readyToEnter harness state) :
    ∃ edge, edge ∈ typedSuccessors config := by
  have hnot : ∀ request, config.raw ≠ .initializing request := by
    intro request hbad
    rw [heq] at hbad
    cases hbad
  have ready : config.raw.GemmReady :=
    config.2.gemmReady_of_not_initializing hnot
  rw [heq] at ready
  change GemmFunctionReady harness state.store at ready
  obtain ⟨core, hinvoke⟩ := invokeResult?_exists_of_gemmFunctionReady ready
  have hraw : StepA config.raw (.enterGemm harness.gemmAddr)
      (.afterEntry harness state.store core) := by
    rw [heq]
    exact .enterGemm (invokeResult?_sound hinvoke)
  exact successors_nonempty_of_rawStep hraw

end TypedConfig

end WasmGemmGnaf.Wasm.Core.Harness
