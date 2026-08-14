/-
  Wasm/Core/HarnessExecution.lean --- the released Core invocation spine.

  The raw Core relation reduces `(State, instr*)`.  A released invocation also
  has a phase protocol: instantiate a fresh module, run its initialization and
  start code, install the raw bytes only after normal start completion, capture
  the entry store exactly once, invoke the exported `gemm`, and retain whether
  a terminal trap or exception occurred before or after that boundary.

  The sum-shaped configuration below makes the entry-store invariant
  structural: no before-entry constructor contains one and every after-entry
  constructor contains exactly one.  This is the internal Core carrier.  It is
  intentionally not aliased to the legacy subset `Wasm.Config`; the final
  namespace migration must expose this carrier directly after moving that
  subset under `Wasm.Subset`.
-/
import WasmGemmGnaf.Wasm.Core.EventExecution
import WasmGemmGnaf.Wasm.Core.Instantiation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Harness

open Exec

/-- Core index zero without importing the profile-facing module. -/
def idx0 : MemIdx := ⟨0, two_pow_pos 32⟩

/-- Core pages required to contain a byte extent. -/
def requiredPages (bytes : Nat) : Nat :=
  (bytes + (64 * Ki) - 1) / (64 * Ki)

/-- The release-facing data needed for one fresh raw invocation.  Export names
remain data at this internal layer; the released profile binds them to the
checked Core names `memory` and `gemm`. -/
structure Request where
  module : Module
  memoryExportName : Name
  gemmExportName : Name
  rawPtr : U32
  rawLen : U32
  rawBytes : List Byte
  rawLength : rawLen.val = rawBytes.length
  rawAddressBound : rawPtr.val + rawLen.val ≤ 2 ^ 32
  rawPageBound : requiredPages (rawPtr.val + rawLen.val) ≤ 65536
  deriving DecidableEq

instance : Inhabited Request where
  default :=
    { module := default
      memoryExportName := default
      gemmExportName := default
      rawPtr := ⟨0, two_pow_pos 32⟩
      rawLen := ⟨0, two_pow_pos 32⟩
      rawBytes := []
      rawLength := rfl
      rawAddressBound := by decide
      rawPageBound := by decide }

/-- Export addresses resolved in the freshly instantiated module instance. -/
structure Harness where
  request : Request
  memoryAddr : MemAddr
  gemmAddr : FuncAddr
  deriving DecidableEq, Inhabited

/-- A typed trap records the exact Core rule event that created it. -/
structure Trap where
  cause : Exec.Event
  deriving DecidableEq, Repr, Inhabited

/-- The two required exported addresses are captured from the module instance,
not supplied by a host lookup outside the semantics. -/
def ResolvesExports (mm : ModuleInst) (h : Harness) : Prop :=
  { name := h.request.memoryExportName, addr := .mem h.memoryAddr } ∈ mm.exports ∧
  { name := h.request.gemmExportName, addr := .func h.gemmAddr } ∈ mm.exports

/-- The released ABI arguments `(rawPtr, rawLen)` as Core values. -/
def Harness.args (h : Harness) : List Val :=
  [.num ⟨.i32, h.request.rawPtr⟩, .num ⟨.i32, h.request.rawLen⟩]

/-- One phase-safe released-machine configuration. -/
inductive Config where
  /-- A raw request before Core allocation/instantiation.  The sole transition
  out of this constructor fixes the released initial store to `{}`. -/
  | initializing (request : Request)
  /-- Element/data initialization and the optional start call execute here. -/
  | beforeEntry (harness : Harness) (core : Exec.Config)
  /-- An intrinsic Core rule created a trap under an administrative context;
  subsequent Core propagation steps remain explicit and retain its cause. -/
  | trappingBeforeEntry (harness : Harness) (trap : Trap) (core : Exec.Config)
  /-- Start returned normally and raw bytes have been installed; `gemm` has not
  yet been invoked and the entry store has not yet been captured. -/
  | readyToEnter (harness : Harness) (state : State)
  /-- The entry store is captured and the exported invocation is executing. -/
  | afterEntry (harness : Harness) (entryStore : Store) (core : Exec.Config)
  /-- The after-entry counterpart of `trappingBeforeEntry`. -/
  | trappingAfterEntry (harness : Harness) (entryStore : Store) (trap : Trap)
      (core : Exec.Config)
  | returned (harness : Harness) (entryStore : Store) (value : Val)
      (finalState : State)
  | trappedBeforeEntry (harness : Harness) (trap : Trap) (finalState : State)
  | trappedAfterEntry (harness : Harness) (entryStore : Store) (trap : Trap)
      (finalState : State)
  | thrownBeforeEntry (harness : Harness) (exceptionAddr : ExnAddr)
      (exceptionValue : ExnInst) (finalState : State)
  | thrownAfterEntry (harness : Harness) (entryStore : Store)
      (exceptionAddr : ExnAddr) (exceptionValue : ExnInst) (finalState : State)

/-- Every harness configuration retains the exact request that created it.
This projection is total by construction, including terminal states, so later
typing/provenance judgments never need to guess a source module from a raw
runtime store. -/
def Config.request : Config → Request
  | .initializing request => request
  | .beforeEntry harness _ | .trappingBeforeEntry harness _ _ |
      .readyToEnter harness _ | .afterEntry harness _ _ |
      .trappingAfterEntry harness _ _ _ | .returned harness _ _ _ |
      .trappedBeforeEntry harness _ _ | .trappedAfterEntry harness _ _ _ |
      .thrownBeforeEntry harness _ _ _ | .thrownAfterEntry harness _ _ _ _ =>
      harness.request

/-- The exact source module of every harness configuration. -/
def Config.module (config : Config) : Module := config.request.module

/-- Coarse phase tags carried by every event. -/
inductive Phase where
  | beforeEntry
  | entryBoundary
  | afterEntry
  deriving DecidableEq, Repr, Inhabited

/-- Deterministic subevents of fresh Core instantiation, in allocation order.
The payloads are exactly the quantities consumed by initialization charging. -/
inductive InitializationEvent where
  | closeType (index : Nat)
  | allocTag (index : Nat)
  | evalGlobal (index exprInstrs : Nat)
  | allocGlobal (index : Nat)
  | allocMemory (index initialPages initialBytes : Nat)
  | evalTable (index exprInstrs : Nat)
  | allocTable (index initialElements : Nat)
  | allocFunction (index locals bodyInstrs : Nat)
  | allocData (index bytes : Nat)
  | evalElem (index exprs exprInstrs : Nat)
  | allocElem (index elements : Nat)
  | allocExport (index : Nat)
  | constructHarnessFrame (hasStart : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The exact deterministic event expansion for the allocation/static-
initialization part of `InstantiateA`. -/
def initializationEvents (m : Module) : List InitializationEvent :=
  (m.types.zipIdx.map fun p => .closeType p.2) ++
  (m.tags.zipIdx.map fun p => .allocTag p.2) ++
  (m.globals.zipIdx.flatMap fun p =>
    [.evalGlobal p.2 p.1.init.toList.length, .allocGlobal p.2]) ++
  (m.mems.zipIdx.map fun p =>
    .allocMemory p.2 p.1.memtype.lim.min.val
      (p.1.memtype.lim.min.val * (64 * Ki))) ++
  (m.tables.zipIdx.flatMap fun p =>
    [.evalTable p.2 p.1.init.toList.length,
      .allocTable p.2 p.1.tabletype.lim.min.val]) ++
  (m.funcs.zipIdx.map fun p =>
    .allocFunction p.2 p.1.locals.length p.1.body.toList.length) ++
  (m.datas.zipIdx.map fun p => .allocData p.2 p.1.bytes.length) ++
  (m.elems.zipIdx.flatMap fun p =>
    [.evalElem p.2 p.1.init.length (p.1.init.map fun e => e.toList.length).sum,
      .allocElem p.2 p.1.init.length]) ++
  (m.exports.zipIdx.map fun p => .allocExport p.2) ++
  [.constructHarnessFrame m.start.isSome]

private theorem sum_map_two {α : Type} (xs : List α) :
    (xs.map fun _ => 2).sum = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]; omega

theorem initializationEvents_length (m : Module) :
    (initializationEvents m).length =
      m.types.length + m.tags.length + 2 * m.globals.length + m.mems.length +
      2 * m.tables.length + m.funcs.length + m.datas.length +
      2 * m.elems.length + m.exports.length + 1 := by
  simp [initializationEvents, List.length_flatMap, sum_map_two]
  omega

/-- Exact released-machine events.  Core events retain their complete rule
identity; harness events retain every operand used by cost charging. -/
inductive Event where
  | initialize (events : List InitializationEvent)
  | coreBeforeEntry (event : Exec.Event)
  | installRaw (memory : MemAddr) (offset bytes : Nat)
  | enterGemm (func : FuncAddr)
  | coreAfterEntry (event : Exec.Event)
  | returnAfterEntry
  | throwBeforeEntry (exception : ExnAddr)
  | throwAfterEntry (exception : ExnAddr)
  deriving DecidableEq, Repr, Inhabited

/-- The phase of an emitted event. -/
def Event.phase : Event → Phase
  | .initialize _ | .coreBeforeEntry _ | .installRaw _ _ _ |
      .throwBeforeEntry _ => .beforeEntry
  | .enterGemm _ => .entryBoundary
  | .coreAfterEntry _ | .returnAfterEntry | .throwAfterEntry _ => .afterEntry

/-- Pure rules that create a trap rather than merely propagate an existing
one through an administrative context. -/
def pureIntrinsicTrap : PureRule → Bool
  | .unreachable | .refAsNonNullNull | .i31GetNull | .unopTrap | .binopTrap
  | .cvtopTrap | .vunopTrap | .vbinopTrap | .vternopTrap => true
  | _ => false

/-- Store-reading rules that create a trap. -/
def readIntrinsicTrap : ReadRule → Bool
  | .callRefNull | .returnCallRefFrameNull | .throwRefNull
  | .tableGetOob | .tableFillOob | .tableCopyOob | .tableInitOob
  | .loadNumOob | .loadPackOob | .vloadOob | .vloadPackOob
  | .vloadSplatOob | .vloadZeroOob | .vloadLaneOob
  | .memoryFillOob | .memoryCopyOob | .memoryInitOob | .refCastFail
  | .structGetNull | .arrayNewElemOob | .arrayNewDataOob | .arrayGetNull
  | .arrayGetOob | .arrayLenNull | .arrayFillNull | .arrayFillOob
  | .arrayCopyNull1 | .arrayCopyNull2 | .arrayCopyOob1 | .arrayCopyOob2
  | .arrayInitElemNull | .arrayInitElemOob1 | .arrayInitElemOob2
  | .arrayInitDataNull | .arrayInitDataOob1 | .arrayInitDataOob2 => true
  | _ => false

/-- The exact inner rule event that first creates a trap. -/
def coreTrapCause? : Exec.Event → Option Exec.Event
  | e@(.pure pe _) => if pureIntrinsicTrap pe.rule then some e else none
  | e@(.read rule _) => if readIntrinsicTrap rule then some e else none
  | .ctxtInstrs _ _ inner | .ctxtLabel _ inner | .ctxtFrame _ inner =>
      coreTrapCause? inner
  | e@(.tableSetOob _) | e@(.storeNumOob _ _) | e@(.storePackOob _ _)
  | e@(.vstoreOob _ _) | e@(.vstoreLaneOob _ _) | e@(.structSetNull _ _)
  | e@(.arraySetNull _) | e@(.arraySetOob _) => some e
  | _ => none

/-- The first trap-creating Core event in a harness trace.  Administrative
trap-propagation events do not overwrite the cause. -/
def traceTrap? : List Event → Option Trap
  | [] => none
  | .coreBeforeEntry e :: trace | .coreAfterEntry e :: trace =>
      match coreTrapCause? e with
      | some cause => some { cause := cause }
      | none => traceTrap? trace
  | _ :: trace => traceTrap? trace

/-- Executable recognition of the outermost administrative trap. -/
def isRawTrap : List AdminInstr → Bool
  | [.trap] => true
  | _ => false

@[simp] theorem isRawTrap_eq_true_iff (is : List AdminInstr) :
    isRawTrap is = true ↔ is = [.trap] := by
  cases is with
  | nil => simp [isRawTrap]
  | cons i is =>
      cases i <;> cases is <;> simp [isRawTrap]

/-- Lift one Core step from the normal pre-entry phase.  A newly classified
trap enters a cause-carrying propagation state (or lands terminally when the
Core target is already the raw trap); an unclassified raw trap is rejected as
an unreachable propagation state with no originating cause. -/
def liftBeforeCore (h : Harness) (event : Exec.Event)
    (c' : Exec.Config) : Option Config :=
  match coreTrapCause? event with
  | none =>
      if isRawTrap c'.2 then none else some (.beforeEntry h c')
  | some cause =>
      if isRawTrap c'.2 then
        some (.trappedBeforeEntry h { cause := cause } c'.1)
      else some (.trappingBeforeEntry h { cause := cause } c')

/-- Lift one Core step from the normal post-entry phase. -/
def liftAfterCore (h : Harness) (entry : Store) (event : Exec.Event)
    (c' : Exec.Config) : Option Config :=
  match coreTrapCause? event with
  | none =>
      if isRawTrap c'.2 then none else some (.afterEntry h entry c')
  | some cause =>
      if isRawTrap c'.2 then
        some (.trappedAfterEntry h entry { cause := cause } c'.1)
      else some (.trappingAfterEntry h entry { cause := cause } c')

/-- Propagation after a cause has been recorded keeps every Core transition
and consumes the cause only when the raw trap reaches the outermost level. -/
def liftTrappingBeforeCore (h : Harness) (trap : Trap)
    (c' : Exec.Config) : Config :=
  if isRawTrap c'.2 then .trappedBeforeEntry h trap c'.1
  else .trappingBeforeEntry h trap c'

/-- Post-entry counterpart of `liftTrappingBeforeCore`. -/
def liftTrappingAfterCore (h : Harness) (entry : Store) (trap : Trap)
    (c' : Exec.Config) : Config :=
  if isRawTrap c'.2 then .trappedAfterEntry h entry trap c'.1
  else .trappingAfterEntry h entry trap c'

/-- Fresh instantiation reaches the pre-start phase.  Empty imports are fixed
by the released profile; no host environment remains as a parameter. -/
inductive InitializesA (request : Request) : Config → Prop where
  | mk {core : Exec.Config} {memory : MemAddr} {gemm : FuncAddr} :
      InstantiateA ({} : Store) request.module [] core →
      ResolvesExports core.1.frame.mod
        { request := request, memoryAddr := memory, gemmAddr := gemm } →
      InitializesA request
        (.beforeEntry
          { request := request, memoryAddr := memory, gemmAddr := gemm } core)

/-- One released harness/Core transition.  This relation is independent of an
executable successor list. -/
inductive StepA : Config → Event → Config → Prop where
  | instantiate {request : Request} {c : Config} :
      InitializesA request c →
      StepA (.initializing request)
        (.initialize (initializationEvents request.module)) c
  | coreBefore {h : Harness} {c c' : Exec.Config} {event : Exec.Event} :
      Exec.StepA c event c' → coreTrapCause? event = none →
      c'.2 ≠ [.trap] →
      StepA (.beforeEntry h c) (.coreBeforeEntry event) (.beforeEntry h c')
  | coreBeforeTrap {h : Harness} {c c' : Exec.Config}
      {event cause : Exec.Event} :
      Exec.StepA c event c' →
      coreTrapCause? event = some cause →
      c'.2 ≠ [.trap] →
      StepA (.beforeEntry h c) (.coreBeforeEntry event)
        (.trappingBeforeEntry h { cause := cause } c')
  | coreBeforeTrapFinal {h : Harness} {c : Exec.Config} {z : State}
      {event cause : Exec.Event} :
      Exec.StepA c event (z, [.trap]) →
      coreTrapCause? event = some cause →
      StepA (.beforeEntry h c) (.coreBeforeEntry event)
        (.trappedBeforeEntry h { cause := cause } z)
  | coreTrappingBefore {h : Harness} {trap : Trap} {c c' : Exec.Config}
      {event : Exec.Event} :
      Exec.StepA c event c' → c'.2 ≠ [.trap] →
      StepA (.trappingBeforeEntry h trap c) (.coreBeforeEntry event)
        (.trappingBeforeEntry h trap c')
  | coreTrappingBeforeFinal {h : Harness} {trap : Trap} {c : Exec.Config}
      {z : State} {event : Exec.Event} :
      Exec.StepA c event (z, [.trap]) →
      StepA (.trappingBeforeEntry h trap c) (.coreBeforeEntry event)
        (.trappedBeforeEntry h trap z)
  | installRaw {h : Harness} {z z' : State} :
      z.frame.mod.mems[0]? = some h.memoryAddr →
      z.withMem idx0 h.request.rawPtr.val h.request.rawLen.val h.request.rawBytes = some z' →
      StepA (.beforeEntry h (z, []))
        (.installRaw h.memoryAddr h.request.rawPtr.val h.request.rawLen.val)
        (.readyToEnter h z')
  | enterGemm {h : Harness} {z : State} {core : Exec.Config} :
      InvokeA z.store h.gemmAddr h.args core →
      StepA (.readyToEnter h z) (.enterGemm h.gemmAddr)
        (.afterEntry h z.store core)
  | coreAfter {h : Harness} {entry : Store} {c c' : Exec.Config}
      {event : Exec.Event} :
      Exec.StepA c event c' → coreTrapCause? event = none →
      c'.2 ≠ [.trap] →
      StepA (.afterEntry h entry c) (.coreAfterEntry event)
        (.afterEntry h entry c')
  | coreAfterTrap {h : Harness} {entry : Store} {c c' : Exec.Config}
      {event cause : Exec.Event} :
      Exec.StepA c event c' →
      coreTrapCause? event = some cause →
      c'.2 ≠ [.trap] →
      StepA (.afterEntry h entry c) (.coreAfterEntry event)
        (.trappingAfterEntry h entry { cause := cause } c')
  | coreAfterTrapFinal {h : Harness} {entry : Store} {c : Exec.Config}
      {z : State} {event cause : Exec.Event} :
      Exec.StepA c event (z, [.trap]) →
      coreTrapCause? event = some cause →
      StepA (.afterEntry h entry c) (.coreAfterEntry event)
        (.trappedAfterEntry h entry { cause := cause } z)
  | coreTrappingAfter {h : Harness} {entry : Store} {trap : Trap}
      {c c' : Exec.Config} {event : Exec.Event} :
      Exec.StepA c event c' → c'.2 ≠ [.trap] →
      StepA (.trappingAfterEntry h entry trap c) (.coreAfterEntry event)
        (.trappingAfterEntry h entry trap c')
  | coreTrappingAfterFinal {h : Harness} {entry : Store} {trap : Trap}
      {c : Exec.Config} {z : State} {event : Exec.Event} :
      Exec.StepA c event (z, [.trap]) →
      StepA (.trappingAfterEntry h entry trap c) (.coreAfterEntry event)
        (.trappedAfterEntry h entry trap z)
  | returnAfter {h : Harness} {entry : Store} {z : State} {v : Val} :
      StepA (.afterEntry h entry (z, vals [v])) .returnAfterEntry
        (.returned h entry v z)
  | throwBefore {h : Harness} {z : State} {a : ExnAddr} {ex : ExnInst} :
      z.exninst[a]? = some ex →
      StepA (.beforeEntry h (z, [.addrref (.exnAddr a), .plain .throwRef]))
        (.throwBeforeEntry a) (.thrownBeforeEntry h a ex z)
  | throwAfter {h : Harness} {entry : Store} {z : State} {a : ExnAddr}
      {ex : ExnInst} :
      z.exninst[a]? = some ex →
      StepA (.afterEntry h entry
          (z, [.addrref (.exnAddr a), .plain .throwRef]))
        (.throwAfterEntry a) (.thrownAfterEntry h entry a ex z)

/-- Exact pre-entry lift of a labelled Core transition.  This is the
classifier-exhaustiveness boundary: every newly intrinsic trap has exactly the
cause carried by its Core event, while a cause-free raw propagation step is
absent. -/
theorem stepA_coreBefore_iff (h : Harness) (c : Exec.Config)
    (event : Exec.Event) (next : Config) :
    StepA (.beforeEntry h c) (.coreBeforeEntry event) next ↔
      ∃ c', Exec.StepA c event c' ∧
        liftBeforeCore h event c' = some next := by
  constructor
  · intro hs
    cases hs with
    | coreBefore hstep hcause hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftBeforeCore, hcause, isRawTrap_eq_true_iff, hnot]
    | coreBeforeTrap hstep hcause hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftBeforeCore, hcause, isRawTrap_eq_true_iff, hnot]
    | coreBeforeTrapFinal hstep hcause =>
        refine ⟨_, hstep, ?_⟩
        simp [liftBeforeCore, hcause, isRawTrap]
  · rintro ⟨⟨z, is⟩, hstep, hlift⟩
    cases hcause : coreTrapCause? event with
    | none =>
        cases htrap : isRawTrap is with
        | false =>
            have hnot : is ≠ [.trap] := by
              intro heq
              subst is
              simp [isRawTrap] at htrap
            simp [liftBeforeCore, hcause, htrap] at hlift
            subst next
            exact .coreBefore hstep hcause hnot
        | true => simp [liftBeforeCore, hcause, htrap] at hlift
    | some cause =>
        cases htrap : isRawTrap is with
        | false =>
            have hnot : is ≠ [.trap] := by
              intro heq
              subst is
              simp [isRawTrap] at htrap
            simp [liftBeforeCore, hcause, htrap] at hlift
            subst next
            exact .coreBeforeTrap hstep hcause hnot
        | true =>
            have heq : is = [.trap] := (isRawTrap_eq_true_iff is).mp htrap
            subst is
            simp [liftBeforeCore, hcause, isRawTrap] at hlift
            subst next
            exact .coreBeforeTrapFinal hstep hcause

/-- Exact post-entry lift of a labelled Core transition. -/
theorem stepA_coreAfter_iff (h : Harness) (entry : Store) (c : Exec.Config)
    (event : Exec.Event) (next : Config) :
    StepA (.afterEntry h entry c) (.coreAfterEntry event) next ↔
      ∃ c', Exec.StepA c event c' ∧
        liftAfterCore h entry event c' = some next := by
  constructor
  · intro hs
    cases hs with
    | coreAfter hstep hcause hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftAfterCore, hcause, isRawTrap_eq_true_iff, hnot]
    | coreAfterTrap hstep hcause hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftAfterCore, hcause, isRawTrap_eq_true_iff, hnot]
    | coreAfterTrapFinal hstep hcause =>
        refine ⟨_, hstep, ?_⟩
        simp [liftAfterCore, hcause, isRawTrap]
  · rintro ⟨⟨z, is⟩, hstep, hlift⟩
    cases hcause : coreTrapCause? event with
    | none =>
        cases htrap : isRawTrap is with
        | false =>
            have hnot : is ≠ [.trap] := by
              intro heq
              subst is
              simp [isRawTrap] at htrap
            simp [liftAfterCore, hcause, htrap] at hlift
            subst next
            exact .coreAfter hstep hcause hnot
        | true => simp [liftAfterCore, hcause, htrap] at hlift
    | some cause =>
        cases htrap : isRawTrap is with
        | false =>
            have hnot : is ≠ [.trap] := by
              intro heq
              subst is
              simp [isRawTrap] at htrap
            simp [liftAfterCore, hcause, htrap] at hlift
            subst next
            exact .coreAfterTrap hstep hcause hnot
        | true =>
            have heq : is = [.trap] := (isRawTrap_eq_true_iff is).mp htrap
            subst is
            simp [liftAfterCore, hcause, isRawTrap] at hlift
            subst next
            exact .coreAfterTrapFinal hstep hcause

/-- Every pre-entry propagation transition is retained and preserves the
recorded intrinsic cause until the raw outer trap is reached. -/
theorem stepA_trappingBefore_iff (h : Harness) (trap : Trap)
    (c : Exec.Config) (event : Exec.Event) (next : Config) :
    StepA (.trappingBeforeEntry h trap c) (.coreBeforeEntry event) next ↔
      ∃ c', Exec.StepA c event c' ∧
        liftTrappingBeforeCore h trap c' = next := by
  constructor
  · intro hs
    cases hs with
    | coreTrappingBefore hstep hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftTrappingBeforeCore, isRawTrap_eq_true_iff, hnot]
    | coreTrappingBeforeFinal hstep =>
        refine ⟨_, hstep, ?_⟩
        simp [liftTrappingBeforeCore, isRawTrap]
  · rintro ⟨⟨z, is⟩, hstep, hlift⟩
    cases htrap : isRawTrap is with
    | false =>
        have hnot : is ≠ [.trap] := by
          intro heq
          subst is
          simp [isRawTrap] at htrap
        simp [liftTrappingBeforeCore, htrap] at hlift
        subst next
        exact .coreTrappingBefore hstep hnot
    | true =>
        have heq : is = [.trap] := (isRawTrap_eq_true_iff is).mp htrap
        subst is
        simp [liftTrappingBeforeCore, isRawTrap] at hlift
        subst next
        exact .coreTrappingBeforeFinal hstep

/-- Post-entry counterpart of `stepA_trappingBefore_iff`. -/
theorem stepA_trappingAfter_iff (h : Harness) (entry : Store) (trap : Trap)
    (c : Exec.Config) (event : Exec.Event) (next : Config) :
    StepA (.trappingAfterEntry h entry trap c) (.coreAfterEntry event) next ↔
      ∃ c', Exec.StepA c event c' ∧
        liftTrappingAfterCore h entry trap c' = next := by
  constructor
  · intro hs
    cases hs with
    | coreTrappingAfter hstep hnot =>
        refine ⟨_, hstep, ?_⟩
        simp [liftTrappingAfterCore, isRawTrap_eq_true_iff, hnot]
    | coreTrappingAfterFinal hstep =>
        refine ⟨_, hstep, ?_⟩
        simp [liftTrappingAfterCore, isRawTrap]
  · rintro ⟨⟨z, is⟩, hstep, hlift⟩
    cases htrap : isRawTrap is with
    | false =>
        have hnot : is ≠ [.trap] := by
          intro heq
          subst is
          simp [isRawTrap] at htrap
        simp [liftTrappingAfterCore, htrap] at hlift
        subst next
        exact .coreTrappingAfter hstep hnot
    | true =>
        have heq : is = [.trap] := (isRawTrap_eq_true_iff is).mp htrap
        subst is
        simp [liftTrappingAfterCore, isRawTrap] at hlift
        subst next
        exact .coreTrappingAfterFinal hstep

/-- A finite released run with its exact phase-tagged trace. -/
inductive StepsA : Config → List Event → Config → Prop where
  | refl (c : Config) : StepsA c [] c
  | cons {c c' c'' : Config} {event : Event} {trace : List Event} :
      StepA c event c' → StepsA c' trace c'' →
      StepsA c (event :: trace) c''

/-- A harness transition cannot change the originating request/module. -/
theorem StepA.request_eq {config event next}
    (hstep : StepA config event next) : next.request = config.request := by
  cases hstep with
  | instantiate hinit => cases hinit; rfl
  | coreBefore | coreBeforeTrap | coreBeforeTrapFinal |
      coreTrappingBefore | coreTrappingBeforeFinal | installRaw | enterGemm |
      coreAfter | coreAfterTrap | coreAfterTrapFinal | coreTrappingAfter |
      coreTrappingAfterFinal | returnAfter | throwBefore | throwAfter => rfl

/-- Request identity is invariant over every finite harness execution. -/
theorem StepsA.request_eq {config trace next}
    (hsteps : StepsA config trace next) : next.request = config.request := by
  induction hsteps with
  | refl => rfl
  | cons hstep _ ih => exact ih.trans hstep.request_eq

/-- Successful initialization emits exactly the deterministic expansion above;
the event list cannot be paired with a different instantiation derivation. -/
theorem stepA_initializing_iff (request : Request) (event : Event) (c : Config) :
    StepA (.initializing request) event c ↔
      event = .initialize (initializationEvents request.module) ∧
        InitializesA request c := by
  constructor
  · intro hs
    cases hs with
    | instantiate hi => exact ⟨rfl, hi⟩
  · rintro ⟨rfl, hi⟩
    exact .instantiate hi

/-- Entry-store presence is a projection of the configuration constructor. -/
def Config.entryStore? : Config → Option Store
  | .initializing _ | .beforeEntry _ _ | .trappingBeforeEntry _ _ _ |
      .readyToEnter _ _ |
      .trappedBeforeEntry _ _ _ |
      .thrownBeforeEntry _ _ _ _ => none
  | .afterEntry _ entry _ | .trappingAfterEntry _ entry _ _ |
      .returned _ entry _ _ |
      .trappedAfterEntry _ entry _ _ | .thrownAfterEntry _ entry _ _ _ => some entry

/-- The entry boundary installs exactly the store of the ready state. -/
theorem StepA.enter_entryStore {h : Harness} {z : State} {core : Exec.Config}
    (_hi : InvokeA z.store h.gemmAddr h.args core) :
    Config.entryStore? (.afterEntry h z.store core) = some z.store := by
  rfl

/-- Before-entry Core work and byte installation cannot fabricate an entry
snapshot. -/
theorem StepA.before_target_entry_none {c c' : Config} {event : Event}
    (hs : StepA c event c') (hp : event.phase = .beforeEntry) :
    c'.entryStore? = none := by
  cases hs <;> simp [Event.phase, Config.entryStore?] at hp ⊢
  case instantiate hinit => cases hinit; rfl

/-- After crossing the boundary, every nonterminal and terminal successor
retains the same entry snapshot. -/
theorem StepA.after_entry_preserved {h : Harness} {entry : Store}
    {core : Exec.Config} {event : Event} {c' : Config}
    (hs : StepA (.afterEntry h entry core) event c') :
    c'.entryStore? = some entry := by
  cases hs <;> rfl

/-- Trap propagation after entry retains the same entry snapshot at every
intermediate and terminal configuration. -/
theorem StepA.trappingAfter_entry_preserved {h : Harness} {entry : Store}
    {trap : Trap} {core : Exec.Config} {event : Event} {c' : Config}
    (hs : StepA (.trappingAfterEntry h entry trap core) event c') :
    c'.entryStore? = some entry := by
  cases hs <;> rfl

/-- Trap propagation before entry cannot fabricate an entry snapshot. -/
theorem StepA.trappingBefore_target_entry_none {h : Harness} {trap : Trap}
    {core : Exec.Config} {event : Event} {c' : Config}
    (hs : StepA (.trappingBeforeEntry h trap core) event c') :
    c'.entryStore? = none := by
  cases hs <;> rfl

/-- No transition can cross the entry boundary a second time. -/
theorem StepA.no_reenter {h : Harness} {entry : Store} {core : Exec.Config}
    {event : Event} {c' : Config}
    (hs : StepA (.afterEntry h entry core) event c') :
    event ≠ .enterGemm h.gemmAddr := by
  cases hs <;> simp

/-- A cause-carrying after-entry propagation state also cannot cross the
entry boundary again. -/
theorem StepA.trappingAfter_no_reenter {h : Harness} {entry : Store}
    {trap : Trap} {core : Exec.Config} {event : Event} {c' : Config}
    (hs : StepA (.trappingAfterEntry h entry trap core) event c') :
    event ≠ .enterGemm h.gemmAddr := by
  cases hs <;> simp

/-! ## Structural terminal partition -/

/-- Normal termination of the exported call.  The value is the exact Core
value retained by the terminal configuration. -/
inductive Halt : Config → Val → Prop where
  | returned (h : Harness) (entry : Store) (value : Val) (finalState : State) :
      Halt (.returned h entry value finalState) value

/-- A terminal trap, preserving whether the entry boundary was crossed and
the exact intrinsic Core event that caused the trap. -/
inductive Trapped : Config → Trap → Prop where
  | beforeEntry (h : Harness) (trap : Trap) (finalState : State) :
      Trapped (.trappedBeforeEntry h trap finalState) trap
  | afterEntry (h : Harness) (entry : Store) (trap : Trap)
      (finalState : State) :
      Trapped (.trappedAfterEntry h entry trap finalState) trap

/-- A terminal uncaught exception, with the exact allocated exception value. -/
inductive Thrown : Config → ExnInst → Prop where
  | beforeEntry (h : Harness) (address : ExnAddr) (value : ExnInst)
      (finalState : State) :
      Thrown (.thrownBeforeEntry h address value finalState) value
  | afterEntry (h : Harness) (entry : Store) (address : ExnAddr)
      (value : ExnInst) (finalState : State) :
      Thrown (.thrownAfterEntry h entry address value finalState) value

/-- The exact terminal predicate of the released harness. -/
def IsTerminal (config : Config) : Prop :=
  (∃ value, Halt config value) ∨
  (∃ trap, Trapped config trap) ∨
  (∃ exceptionValue, Thrown config exceptionValue)

/-- Terminality is decidable solely from the phase-safe configuration
constructor; no semantic search or timeout is involved. -/
def terminal (config : Config) : Decidable (IsTerminal config) := by
  cases config with
  | initializing request =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | beforeEntry h core =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | trappingBeforeEntry h trap core =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | readyToEnter h state =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | afterEntry h entry core =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | trappingAfterEntry h entry trap core =>
      apply isFalse
      rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h
  | returned h entry value finalState =>
      exact isTrue (Or.inl ⟨value, .returned h entry value finalState⟩)
  | trappedBeforeEntry h trap finalState =>
      exact isTrue (Or.inr (Or.inl ⟨trap, .beforeEntry h trap finalState⟩))
  | trappedAfterEntry h entry trap finalState =>
      exact isTrue
        (Or.inr (Or.inl ⟨trap, .afterEntry h entry trap finalState⟩))
  | thrownBeforeEntry h address value finalState =>
      exact isTrue
        (Or.inr (Or.inr ⟨value, .beforeEntry h address value finalState⟩))
  | thrownAfterEntry h entry address value finalState =>
      exact isTrue
        (Or.inr (Or.inr
          ⟨value, .afterEntry h entry address value finalState⟩))

/-- The three terminal judgments are exhaustive and mutually constructor-
disjoint.  This is the concrete Core harness instance of SPEC section 7.1's
terminal law. -/
theorem terminal_iff_halt_trap_or_throw (config : Config) :
    IsTerminal config ↔
      ((∃ value, Halt config value) ∨
       (∃ trap, Trapped config trap) ∨
       (∃ exceptionValue, Thrown config exceptionValue)) := by
  rfl

/-! ## Exact terminal observations -/

/-- ABI-visible bytes of the exported memory. -/
structure ObservableStore where
  bytes : List Byte
  deriving DecidableEq, Repr, Inhabited

/-- The closed release profile admits no externally visible non-memory
effects. -/
structure ObservableEffects where
  deriving DecidableEq, Repr, Inhabited

theorem ObservableEffects.subsingleton (a b : ObservableEffects) : a = b := by
  cases a; cases b; rfl

def ObservableEffects.none : ObservableEffects := {}

/-- Projection of the exact exported memory instance. -/
def observeStore (h : Harness) (s : Store) : Option ObservableStore :=
  (s.mems[h.memoryAddr]?).map fun m => { bytes := m.bytes }

/-- Exact outcomes required by SPEC section 7.4.  Before-entry terminal
constructors cannot carry an entry snapshot; all three after-entry outcomes
must carry exactly one. -/
inductive ExecutionObservation where
  | returned (trace : List Event) (gemmEntryObservableStore : ObservableStore)
      (value : Val) (finalObservableStore : ObservableStore)
      (effects : ObservableEffects)
  | trappedBeforeEntry (trace : List Event)
      (trap : Trap) (finalObservableStore : ObservableStore)
      (effects : ObservableEffects)
  | trappedAfterEntry (trace : List Event)
      (gemmEntryObservableStore : ObservableStore)
      (trap : Trap) (finalObservableStore : ObservableStore)
      (effects : ObservableEffects)
  | thrownBeforeEntry (trace : List Event) (exceptionValue : ExnInst)
      (finalObservableStore : ObservableStore) (effects : ObservableEffects)
  | thrownAfterEntry (trace : List Event)
      (gemmEntryObservableStore : ObservableStore) (exceptionValue : ExnInst)
      (finalObservableStore : ObservableStore) (effects : ObservableEffects)

/-- A terminal configuration and trace determine an exact observation through
the exported-memory projection. -/
inductive Observes : List Event → Config → ExecutionObservation → Prop where
  | returned {trace : List Event} {h : Harness} {entry : Store} {v : Val}
      {z : State} {entryObs finalObs : ObservableStore} :
      observeStore h entry = some entryObs →
      observeStore h z.store = some finalObs →
      Observes trace (.returned h entry v z)
        (.returned trace entryObs v finalObs .none)
  | trappedBefore {trace : List Event} {h : Harness} {z : State}
      {trap : Trap} {finalObs : ObservableStore} :
      traceTrap? trace = some trap →
      observeStore h z.store = some finalObs →
      Observes trace (.trappedBeforeEntry h trap z)
        (.trappedBeforeEntry trace trap finalObs .none)
  | trappedAfter {trace : List Event} {h : Harness} {entry : Store}
      {z : State} {trap : Trap} {entryObs finalObs : ObservableStore} :
      traceTrap? trace = some trap →
      observeStore h entry = some entryObs →
      observeStore h z.store = some finalObs →
      Observes trace (.trappedAfterEntry h entry trap z)
        (.trappedAfterEntry trace entryObs trap finalObs .none)
  | thrownBefore {trace : List Event} {h : Harness} {a : ExnAddr}
      {ex : ExnInst} {z : State} {finalObs : ObservableStore} :
      observeStore h z.store = some finalObs →
      Observes trace (.thrownBeforeEntry h a ex z)
        (.thrownBeforeEntry trace ex finalObs .none)
  | thrownAfter {trace : List Event} {h : Harness} {entry : Store}
      {a : ExnAddr} {ex : ExnInst} {z : State}
      {entryObs finalObs : ObservableStore} :
      observeStore h entry = some entryObs →
      observeStore h z.store = some finalObs →
      Observes trace (.thrownAfterEntry h entry a ex z)
        (.thrownAfterEntry trace entryObs ex finalObs .none)

/-- Finite execution from a fresh request to one exact terminal observation. -/
inductive FiniteExecution (initial : Config) : ExecutionObservation → Prop where
  | mk {trace : List Event} {terminal : Config} {observation : ExecutionObservation} :
      StepsA initial trace terminal → Observes trace terminal observation →
      FiniteExecution initial observation

end WasmGemmGnaf.Wasm.Core.Harness
