import WasmGemmGnaf.Wasm.Core.InstantiationOrigins
import WasmGemmGnaf.Wasm.Core.RuntimeMatchComplete
import WasmGemmGnaf.Wasm.Core.ReadSuccessors
import WasmGemmGnaf.Wasm.Core.TypedHarness

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core

namespace Exec

/-- Fresh amended instantiation establishes the complete allocated runtime
origin invariant, including every administrative instruction emitted for
element/data/start initialization. -/
theorem InstantiateA.configTypeOriginsA {module : Module} {core : Config}
    (h : InstantiateA ({} : Store) module [] core) :
    ConfigTypeOriginsA (allocTypes module.types) core := by
  refine ⟨h.storeTypeOriginsA, h.frameTypes_eq_allocTypes, ?_⟩
  cases h
  simp

/-- The empty-frame invocation bootstrap is compatible with the validated
module's allocated runtime type vector. -/
theorem InvokeA.compatibleConfigTypeOriginsA {store : Store}
    {address : FuncAddr} {arguments : List Val} {core : Config}
    {dts : List DefType} (horigin : StoreTypeOriginsA store dts)
    (h : InvokeA store address arguments core) :
    CompatibleConfigTypeOriginsA dts core := by
  cases h
  refine ⟨horigin, Or.inl rfl, ?_⟩
  simp [AdminInstrsTypesA, AdminInstrTypesA]

end Exec

namespace Harness

/-- The store retained by every post-instantiation harness phase.  The initial
request has no runtime store yet. -/
def Config.runtimeStore? : Config → Option Exec.Store
  | .initializing _ => none
  | .beforeEntry _ core | .trappingBeforeEntry _ _ core |
      .afterEntry _ _ core | .trappingAfterEntry _ _ _ core =>
      some core.1.store
  | .readyToEnter _ state | .returned _ _ _ state |
      .trappedBeforeEntry _ _ state | .trappedAfterEntry _ _ _ state |
      .thrownBeforeEntry _ _ _ state | .thrownAfterEntry _ _ _ _ state =>
      some state.store

/-- Runtime type origins for every harness phase.  Active Core configurations
carry the empty-frame-compatible invariant; terminal and boundary states need
only the store component consumed by executable reference matching. -/
def Config.RuntimeTypeOriginsA : Config → Prop
  | .initializing _ => True
  | .beforeEntry harness core | .trappingBeforeEntry harness _ core |
      .afterEntry harness _ core | .trappingAfterEntry harness _ _ core =>
      Exec.CompatibleConfigTypeOriginsA
        (Exec.allocTypes harness.request.module.types) core
  | .readyToEnter harness state | .returned harness _ _ state |
      .trappedBeforeEntry harness _ state |
      .trappedAfterEntry harness _ _ state |
      .thrownBeforeEntry harness _ _ state |
      .thrownAfterEntry harness _ _ _ state =>
      Exec.StoreTypeOriginsA state.store
        (Exec.allocTypes harness.request.module.types)

theorem installRaw?_preserveStoreTypeOriginsA {harness : Harness}
    {source target : Exec.State} {previousPages grownPages : Nat}
    {dts : List DefType}
    (horigin : Exec.StoreTypeOriginsA source.store dts)
    (hinstall : installRaw? harness source =
      some (previousPages, grownPages, target)) :
    Exec.StoreTypeOriginsA target.store dts := by
  unfold installRaw? at hinstall
  cases haddress : source.frame.mod.mems[0]? with
  | none => simp [haddress] at hinstall
  | some memoryAddress =>
      by_cases heq : memoryAddress = harness.memoryAddr
      · cases hmemory : source.store.mems[harness.memoryAddr]? with
        | none => simp [haddress, heq, hmemory] at hinstall
        | some memory =>
            cases hgrow : Exec.growMem memory
                (rawGrowthPages harness.request memory) with
            | none => simp [haddress, heq, hmemory, hgrow] at hinstall
            | some grownMemory =>
                cases hgrown : source.withMemInst idx0 grownMemory with
                | none =>
                    simp [haddress, heq, hmemory, hgrow, hgrown] at hinstall
                | some grownState =>
                    cases hbytes : grownState.withMem idx0
                        harness.request.rawPtr.val harness.request.rawLen.val
                        harness.request.rawBytes with
                    | none =>
                        simp [haddress, heq, hmemory, hgrow, hgrown, hbytes]
                          at hinstall
                    | some installedState =>
                        simp [haddress, heq, hmemory, hgrow, hgrown, hbytes]
                          at hinstall
                        rcases hinstall with ⟨rfl, rfl, rfl⟩
                        exact (horigin.preserve_withMemInst hgrown).preserve_withMem
                          hbytes
      · simp [haddress, heq] at hinstall

theorem StepA.preserveRuntimeTypeOriginsA {source target : Config}
    {event : Event} (step : StepA source event target)
    (hsource : source.RuntimeTypeOriginsA) :
    target.RuntimeTypeOriginsA := by
  cases step with
  | instantiate hinitializes =>
      cases hinitializes with
      | mk hinstantiate _ =>
          exact hinstantiate.configTypeOriginsA.compatible
  | coreBefore hstep _ _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreBeforeTrap hstep _ _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreBeforeTrapFinal hstep _ =>
      exact (hstep.preserveCompatibleConfigTypeOriginsA hsource).1
  | coreTrappingBefore hstep _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreTrappingBeforeFinal hstep =>
      exact (hstep.preserveCompatibleConfigTypeOriginsA hsource).1
  | @installRaw harness state targetState previousPages grownPages hinstall =>
      exact installRaw?_preserveStoreTypeOriginsA hsource.1 hinstall
  | enterGemm hinvoke =>
      exact hinvoke.compatibleConfigTypeOriginsA hsource
  | coreAfter hstep _ _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreAfterTrap hstep _ _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreAfterTrapFinal hstep _ =>
      exact (hstep.preserveCompatibleConfigTypeOriginsA hsource).1
  | coreTrappingAfter hstep _ =>
      exact hstep.preserveCompatibleConfigTypeOriginsA hsource
  | coreTrappingAfterFinal hstep =>
      exact (hstep.preserveCompatibleConfigTypeOriginsA hsource).1
  | returnAfter => exact hsource.1
  | throwBefore => exact hsource.1
  | throwAfter => exact hsource.1

/-- The runtime-origin invariant is preserved by every finite harness run. -/
theorem StepsA.preserveRuntimeTypeOriginsA {source target : Config}
    {trace : List Event} (steps : StepsA source trace target)
    (hsource : source.RuntimeTypeOriginsA) :
    target.RuntimeTypeOriginsA := by
  induction steps with
  | refl => exact hsource
  | cons head _ ih => exact ih (head.preserveRuntimeTypeOriginsA hsource)

/-- The module-validity witness carried by a public request contains the
checked semantic expansion of its complete source type section. -/
theorem Request.Valid.typesOk {request : Request} (h : request.Valid) :
    ∃ dts : List DefType,
      Types_okA Context.empty request.module.types dts := by
  rcases h with ⟨_, hrest⟩
  rcases hrest with ⟨hmodule, _⟩
  obtain ⟨moduleType, hmodule⟩ := hmodule
  cases hmodule with
  | mk htypes _ => exact ⟨_, htypes⟩

/-- Reachability from a validated request establishes runtime type origins at
every public harness phase. -/
theorem Config.WellTyped.runtimeTypeOriginsA {config : Config}
    (h : config.WellTyped) : config.RuntimeTypeOriginsA := by
  rcases h with ⟨request, trace, _, steps⟩
  exact steps.preserveRuntimeTypeOriginsA (by trivial)

/-- A public configuration retains the validation witness for its own request
through every harness phase. -/
theorem Config.WellTyped.requestValid {config : Config}
    (h : config.WellTyped) : config.request.Valid := by
  rcases h with ⟨request, trace, valid, steps⟩
  have heq : config.request = request := by simpa using steps.request_eq
  rw [heq]
  exact valid

/-- Project the store-origin component from any post-instantiation phase. -/
theorem Config.RuntimeTypeOriginsA.storeTypeOriginsA {config : Config}
    {store : Exec.Store} (h : config.RuntimeTypeOriginsA)
    (hstore : config.runtimeStore? = some store) :
    Exec.StoreTypeOriginsA store
      (Exec.allocTypes config.module.types) := by
  cases config <;>
    simp_all [Config.RuntimeTypeOriginsA, Config.runtimeStore?, Config.module,
      Config.request] <;>
    subst_vars <;>
    first | exact h.1 | exact h

namespace TypedConfig

/-- Every raw Core state sharing the runtime store of a public typed harness
configuration has a complete executable reference matcher.  The certificate
is independent of the active frame, so recursive instruction-context descent
uses the same checked allocation and store proof. -/
theorem refMatchCompleteAt (config : TypedConfig) {state : Exec.State}
    (hstore : config.raw.runtimeStore? = some state.store) :
    Exec.RefMatchCompleteAt
      (Exec.allocTypes config.raw.module.types).length state := by
  have hrequest := config.2.requestValid
  obtain ⟨rawTypes, htypes⟩ := hrequest.typesOk
  have horigins := config.2.runtimeTypeOriginsA
  have hstoreOrigin := horigins.storeTypeOriginsA hstore
  intro reference target href
  exact Exec.refMatchesN_complete_of_allocated hrequest.1 htypes hstoreOrigin
    href

end TypedConfig

end Harness

end WasmGemmGnaf.Wasm.Core
