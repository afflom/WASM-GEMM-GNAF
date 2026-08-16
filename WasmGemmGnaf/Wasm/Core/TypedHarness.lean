/-
  Proof-carrying public configurations for the amended Core harness.

  Raw Core states admit malformed stores for which executable reference
  matching is intentionally incomplete.  The public carrier therefore keeps
  only configurations reached from a syntactically representable,
  declaratively validated request.  This is an ordinary reachability/typing
  invariant; it stores no progress, successor-completeness, or termination
  conclusion.
-/
import WasmGemmGnaf.Wasm.Core.HarnessExecution

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Harness

/-- The checked evidence from which a public invocation may start.  Besides
source syntax and amended module validation, the released machine is closed
and the ordinary executable initializer has already demonstrated that fresh
instantiation and both required export lookups succeed.  These are computation
equalities and list memberships, not an assumed progress or completeness
proposition; callers still construct them by running the initializer and keep
failure explicit. -/
def Request.Valid (request : Request) : Prop :=
  request.module.types.all TypeDef.isSyn = true ∧
    (∃ moduleType, Module_okA request.module moduleType) ∧
    request.module.imports = [] ∧
    ∃ core memoryAddress functionAddress,
        Exec.instantiateA? ({} : Exec.Store) request.module [] = some core ∧
        initialMemoryExportAddress? request.memoryExportName
          core.1.frame.mod.exports = some memoryAddress ∧
        initialFunctionExportAddress? request.gemmExportName
          core.1.frame.mod.exports = some functionAddress ∧
        GemmFunctionReady
          { request := request, memoryAddr := memoryAddress,
            gemmAddr := functionAddress }
          core.1.store ∧
        RawInstallReady
          { request := request, memoryAddr := memoryAddress,
            gemmAddr := functionAddress }
          core.1

/-- A raw harness configuration belongs to the public machine exactly when it
is reachable from a validated request's unique initial phase. -/
def Config.WellTyped (config : Config) : Prop :=
  ∃ (request : Request) (trace : List Event),
    request.Valid ∧ StepsA (.initializing request) trace config

/-- A public configuration carries its validation/reachability derivation. -/
def TypedConfig : Type := { config : Config // config.WellTyped }

namespace TypedConfig

/-- Erase the proof-carrying public carrier to the authority harness state. -/
def raw (config : TypedConfig) : Config := config.1

instance : Coe TypedConfig Config := ⟨raw⟩

/-- The validated initial phase is a public configuration. -/
def initializing (request : Request) (valid : request.Valid) : TypedConfig :=
  ⟨.initializing request, request, [], valid, .refl _⟩

end TypedConfig

/-- Append one authority step to a finite trace. -/
theorem StepsA.snoc {initial config next : Config} {trace : List Event}
    {event : Event} (steps : StepsA initial trace config)
    (step : StepA config event next) :
    StepsA initial (trace ++ [event]) next := by
  induction steps with
  | refl _ => simpa using StepsA.cons step (.refl next)
  | cons head tail ih =>
      exact .cons head (ih step)

/-- Concatenate two authority traces. -/
theorem StepsA.append {initial middle final : Config}
    {leftTrace rightTrace : List Event}
    (left : StepsA initial leftTrace middle)
    (right : StepsA middle rightTrace final) :
    StepsA initial (leftTrace ++ rightTrace) final := by
  induction left with
  | refl _ => simpa using right
  | cons head tail ih => exact .cons head (ih right)

/-- The public typing/reachability invariant is preserved by every finite
authority trace. -/
theorem StepsA.preserveWellTyped {config next : Config} {trace : List Event}
    (steps : StepsA config trace next) (typed : config.WellTyped) :
    next.WellTyped := by
  obtain ⟨request, initialTrace, valid, reaches⟩ := typed
  exact ⟨request, initialTrace ++ trace, valid, reaches.append steps⟩

/-- The public typing/reachability invariant is preserved by every authority
step. -/
theorem StepA.preserveWellTyped {config next : Config} {event : Event}
    (step : StepA config event next) (typed : config.WellTyped) :
    next.WellTyped := by
  obtain ⟨request, trace, valid, steps⟩ := typed
  exact ⟨request, trace ++ [event], valid, steps.snoc step⟩

/-- Lift one raw authority step between public configurations. -/
def TypedStep (config : TypedConfig) (event : Event)
    (next : TypedConfig) : Prop :=
  StepA config.1 event next.1

/-- Attach the preserved typing proof to a raw successor. -/
def TypedConfig.successor (config : TypedConfig) (event : Event)
    (next : Config) (step : StepA config.1 event next) : TypedConfig :=
  ⟨next, step.preserveWellTyped config.2⟩

end WasmGemmGnaf.Wasm.Core.Harness
