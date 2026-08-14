/-
  Theorems: the formal WebAssembly layer.

  This module is an INDEX, not a source of new mathematics.  Every declaration
  below restates a proposition already proved in `WasmGemmGnaf/Wasm/` and closes
  it by `exact`-ing the original.  Restating rather than `export`ing is
  deliberate: the proposition is written out here in full, so SPEC §15's
  required-name list can be checked against the *statements* in one place
  instead of trusting that a re-exported name still says what it used to say.

  ## Exact public-Core SPEC §15 declarations indexed here

  * `Wasm.decode_sound`
  * `Wasm.decode_complete`

  Both are stated over the public representable `Wasm.Module`, the amended
  decoder, and `Wasm.Core.Binary.BmoduleA`.  The newly required exact public
  `Wasm.encode_decode_roundtrip` is proved in `Wasm/CoreBackEnd.lean`; it is not
  re-indexed by this module.

  The other declarations in this file are proved facts about the legacy
  `Wasm.Subset` validator, execution relation, fuel explorer, costed semantics,
  or adequacy map.  They remain useful internal results, but their names do not
  make them public amended-Core SPEC §15 discharges.  In particular, the
  required public-Core validator biconditional, progress theorem, successor and
  bounded-explorer results, costed erasure/initialization results, and authority
  map over every amended rule remain outstanding.  `just required` is the live
  compiled ledger.

  The §15 list also retains `validate_bool_iff` as an explicitly weak legacy
  subset name.  Its theorem below has exactly that scope; it is not the public
  amended-Core validator biconditional.

  ## Additional proved results indexed here

  `subset_encode_decode_roundtrip`, `subset_decode_is_encode`,
  `subset_decode_error_or_encode`, `successors_nodup`,
  `fault_decoding_ne_instantiation`
  (with the two injectivity halves), `costed_run_iff_plain_run`,
  `wasm_cost_table_total`, `terminal_iff_halt_trap_or_throw`,
  `validation_preservation`, `initialConfig_configWellTyped`,
  `initialConfig_instantiates`.

  `validation_preservation` carries the invariant hypothesis `hwelltyped`, but
  it too is a theorem about the legacy subset machine rather than public Core.

  Same-named subset results elsewhere in `WasmGemmGnaf/Wasm/` remain scoped to
  that legacy machine and receive no release credit.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Declarative
import WasmGemmGnaf.Wasm.Validate
import WasmGemmGnaf.Wasm.Step
import WasmGemmGnaf.Wasm.Soundness
import WasmGemmGnaf.Wasm.Fault
import WasmGemmGnaf.Wasm.Fuel
import WasmGemmGnaf.Wasm.Erasure
import WasmGemmGnaf.Wasm.Adequacy

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

/-! ## The SUBSET codec: decode/encode round trip

These three are about `Wasm.Subset`, the codec of `Wasm/Binary.lean`.  They are
not the SPEC §15 public front-end theorems.  The release predicates under
`Universal/` have not yet migrated off this codec, but `Artifact/Emit.lean` now
uses the public amended-Core encoder.  These results say nothing about that
public format. -/

/-- **Round trip.**  Decoding an encoded module returns exactly that module. -/
theorem subset_encode_decode_roundtrip (m : Wasm.Subset.Module) :
    Wasm.Subset.decode (Wasm.Subset.encode m) = .ok m :=
  Wasm.Subset.encode_decode_roundtrip m

/-- **Subset decoder soundness.**  A byte string that decodes at all is the
encoding of the module it decodes to, so a malformed input never yields a wrong
module. -/
theorem subset_decode_is_encode {b : ByteArray} {m : Wasm.Subset.Module}
    (h : Wasm.Subset.decode b = .ok m) : b = Wasm.Subset.encode m :=
  Wasm.Subset.decode_is_encode h

/-- **Subset decoder totality.**  Every byte string either produces a typed
fault or produces the unique module whose encoding it is. -/
theorem subset_decode_error_or_encode (b : ByteArray) :
    (∃ f : Wasm.DecodeFault, Wasm.Subset.decode b = .error f) ∨
    (∃ m : Wasm.Subset.Module, Wasm.Subset.decode b = .ok m ∧ b = Wasm.Subset.encode m) :=
  Wasm.Subset.decode_error_or_encode b

/-! ## Binary format: the amended Core 3.0 grammar

`Wasm.decode` is the Core 3.0 decoder of `Wasm/Core/Decode.lean` and
`Wasm.DeclarativeBinaryRelation` projects the public representable carrier to
its Core AST and applies the amended binary grammar
`Wasm.Core.Binary.BmoduleA`;
see `Wasm/CoreFrontEnd.lean` for why the names moved. -/

/-- **SPEC §15, `Wasm.decode_sound`.**  Everything the executable Core 3.0
decoder accepts is derivable in `Wasm.DeclarativeBinaryRelation`, the amended
binary grammar with the registered authority repairs propagated through it. -/
theorem decode_sound {b : ByteArray} {m : Wasm.Module}
    (h : Wasm.decode b = .ok m) : Wasm.DeclarativeBinaryRelation b m :=
  Wasm.decode_sound h

/-- **SPEC §15, `Wasm.decode_complete`.**  Everything derivable in
`Wasm.DeclarativeBinaryRelation` the executable Core 3.0 decoder accepts,
returning exactly the module the derivation synthesized. -/
theorem decode_complete {b : ByteArray} {m : Wasm.Module}
    (h : Wasm.DeclarativeBinaryRelation b m) : Wasm.decode b = .ok m :=
  Wasm.decode_complete h

/-! ## Validation -/

/-- The executable validator decides the declarative validity judgment of this
repository's Wasm subset. -/
theorem validate_bool_iff (m : Wasm.Subset.Module) :
    Wasm.validate m = true ↔ Wasm.DeclarativelyValid m :=
  Wasm.validate_bool_iff m

/-- The legacy subset validation equivalence.  Its proposition is not the
public amended-Core `Wasm.validate_iff_declarative` obligation. -/
theorem validate_iff_declarative (m : Wasm.Subset.Module) :
    Wasm.validate m = true ↔ Wasm.DeclarativelyValid m :=
  Wasm.validate_iff_declarative m

/-! ## Reduction: the executable successor enumeration is the relation -/

/-- On the legacy subset machine, executable successor enumeration is exactly
the reduction relation.  The public amended-Core obligation remains open. -/
theorem mem_successors_iff_step (c : Wasm.Config) (e : Wasm.Event) (c' : Wasm.Config) :
    (e, c') ∈ Wasm.successors c ↔ Wasm.Step c e c' :=
  Wasm.mem_successors_iff_step c e c'

/-- The successor enumeration is duplicate free, so counting successors counts
distinct reducts. -/
theorem successors_nodup (c : Wasm.Config) : (Wasm.successors c).Nodup :=
  Wasm.successors_nodup c

/-! ## The bounded explorer covers every maximal branch -/

/-- On the legacy subset machine, when
`Wasm.exploreAll` answers `complete`, the observations it carries contain
*every* finite execution of the initial configuration — with no hypothesis on
the trace length.  This is strictly stronger than
`Wasm.runFuel_complete_with_bound`, whose conclusion is conditional on
`observation.trace.length ≤ bound`: the `complete` constructor is reachable only
when no branch of `initial` is still running after `bound + 1` steps, which
makes the bound a proved property of `initial` rather than a restriction on the
runs being covered. -/
theorem bounded_tree_covers_every_branch {bound : Nat} {initial : Wasm.Config}
    {obs : List Wasm.ExecutionObservation}
    {cov : Wasm.CoversEveryMaximalFiniteBranch bound initial obs}
    (hcomplete : Wasm.exploreAll bound initial = .complete obs cov)
    {o : Wasm.ExecutionObservation} (hrun : Wasm.FiniteExecution initial o) :
    o ∈ obs :=
  Wasm.bounded_tree_covers_every_branch hcomplete hrun

/-! ## Progress and preservation for the modelled machine -/

/-- A well-typed configuration of a valid legacy subset module has halted,
trapped, thrown, or can still take a step.  This is not public-Core progress.

`Wasm.ConfigWellTyped` is the syntactic typing invariant of
`WasmGemmGnaf/Wasm/Soundness.lean`, stated in the declarative judgment of
`Wasm/Validate.lean`; it mentions neither `Wasm.Step` nor `Wasm.successors` nor
`Config.status`, so it cannot smuggle this conclusion in.  It is preserved by
reduction (`validation_preservation`) and established by `Wasm.initialConfig`
(`initialConfig_configWellTyped`).  The scope is the modelled subset, and the
one restriction the modelled `Wasm.Step` forces — a branch to a function's
implicit outermost label has no reduction rule, so the invariant admits only
frame-local branches — is stated in that file's header. -/
theorem validation_progress {module : Wasm.Subset.Module} {config : Wasm.Config}
    (hvalid : Wasm.DeclarativelyValid module)
    (hconfig : Wasm.ConfigInstantiates module config)
    (hwelltyped : Wasm.ConfigWellTyped config) :
    (∃ outcome, Wasm.Halt config outcome) ∨
    (∃ trap, Wasm.Trapped config trap) ∨
    (∃ exceptionValue, Wasm.Thrown config exceptionValue) ∨
    (Wasm.successors config).Nonempty :=
  Wasm.validation_progress hvalid hconfig hwelltyped

/-- On the legacy subset machine, a configuration is terminal exactly when it
has halted, trapped, or thrown. -/
theorem terminal_iff_halt_trap_or_throw (config : Wasm.Config) :
    config.IsTerminal ↔
      ((∃ outcome, Wasm.Halt config outcome) ∨
        (∃ trap, Wasm.Trapped config trap) ∨
        (∃ exceptionValue, Wasm.Thrown config exceptionValue)) :=
  Wasm.isTerminal_iff_halt_trapped_thrown config

/-- The legacy subset preservation result, with the invariant hypothesis
`hwelltyped`.  It does not establish preservation for the public Core machine. -/
theorem validation_preservation {module : Wasm.Subset.Module} {config : Wasm.Config}
    {event : Wasm.Event} {next : Wasm.Config}
    (hvalid : Wasm.DeclarativelyValid module)
    (hstep : Wasm.Step config event next)
    (hconfig : Wasm.ConfigInstantiates module config)
    (hwelltyped : Wasm.ConfigWellTyped config) :
    Wasm.ConfigWellTyped next :=
  Wasm.validation_preservation hvalid hstep hconfig hwelltyped

/-- **The invariant is reachable, not empty.**  The configuration the machine
starts in is well typed. -/
theorem initialConfig_configWellTyped {m : Wasm.Subset.Module} {raw : Wasm.RawInvocation}
    {c : Wasm.Config} (h : Wasm.initialConfig m raw = .ok c)
    (hstart : Wasm.StartFrameLocal m) : Wasm.ConfigWellTyped c :=
  Wasm.initialConfig_configWellTyped h hstart

/-- The configuration the machine starts in instantiates the module it was built
from. -/
theorem initialConfig_instantiates {m : Wasm.Subset.Module} {raw : Wasm.RawInvocation}
    {c : Wasm.Config} (h : Wasm.initialConfig m raw = .ok c)
    (hlocal : Wasm.GemmFrameLocal m) : Wasm.ConfigInstantiates m c :=
  Wasm.initialConfig_instantiates h hlocal

/-! ## Fault disjointness -/

/-- The two failure domains of `Wasm.Fault` are disjoint: a decoding failure can
never be silently reported as an instantiation failure. -/
theorem fault_decoding_ne_instantiation
    (a : Wasm.DecodeFault) (b : Wasm.InstantiationFault) :
    Wasm.Fault.decoding a ≠ Wasm.Fault.instantiation b :=
  Wasm.Fault.decoding_ne_instantiation a b

/-- The decoding injection loses no information. -/
theorem fault_decoding_injective {a b : Wasm.DecodeFault}
    (h : Wasm.Fault.decoding a = Wasm.Fault.decoding b) : a = b :=
  Wasm.Fault.decoding_injective h

/-- The instantiation injection loses no information. -/
theorem fault_instantiation_injective {a b : Wasm.InstantiationFault}
    (h : Wasm.Fault.instantiation a = Wasm.Fault.instantiation b) : a = b :=
  Wasm.Fault.instantiation_injective h

/-! ## Cost erasure -/

/-- The `DEV-001` amended erasure law for the legacy subset machine.  A costed
run of `costedTrace` holds exactly when the ordinary run of
`eraseCosts costedTrace` holds *and* `costedTrace` is a labelling the machine
produces.  The side condition is necessary: without it the backward direction is
false, because `costedTrace` is universally quantified. -/
theorem costed_erase_iff_plain_run {P : Wasm.Profile} {module : Wasm.Subset.Module}
    {invocation : Wasm.RawInvocation} {costedTrace : List Wasm.CostedEvent}
    {observation : Wasm.ExecutionObservation} :
    Wasm.CostedRun P module invocation costedTrace observation ↔
      (Wasm.Run module invocation (Wasm.eraseCosts costedTrace) observation ∧
        Wasm.CostedLabelling module invocation costedTrace) :=
  Wasm.costed_erase_iff_plain_run

/-- Cost instrumentation is transparent on the legacy subset machine, with no
side condition: an observation is reachable by a costed run exactly when it is
reachable by the ordinary run of its own trace. -/
theorem costed_run_iff_plain_run {P : Wasm.Profile} {module : Wasm.Subset.Module}
    {invocation : Wasm.RawInvocation} {observation : Wasm.ExecutionObservation} :
    (∃ costedTrace : List Wasm.CostedEvent,
        Wasm.CostedRun P module invocation costedTrace observation) ↔
      Wasm.Run module invocation observation.trace observation :=
  Wasm.costed_run_iff_plain_run

/-! ## Cost-table totality -/

/-- Every legacy subset costed event has exactly one contribution.  This does
not establish exact coverage of the amended Core event universe. -/
theorem wasm_cost_table_total (t : Wasm.CostTableBody) (event : Wasm.CostedEvent) :
    ∃ contribution : Cost.DynamicVector,
      Wasm.EventContribution t event contribution ∧
        ∀ other : Cost.DynamicVector,
          Wasm.EventContribution t event other → other = contribution :=
  Wasm.wasm_cost_table_total t event

/-! ## The legacy adequacy map's pinned revision identity -/

/-- The current adequacy map is identity-bound to the *vendored* revision, and
every rule identifier enabled by that legacy map has exactly one mapped Lean
declaration.

The first conjunct binds the profile, the conformance map and the vendored tree
record of `Wasm/Revision.lean` to one commit, carries the digest of
`vendor/wasm-spec/SHA256SUMS` — the digest of digests over all 374 vendored
files — and supplies the injectivity of both canonical identities, so a
different revision, or a single different vendored byte, gives a different
identity.  Lean does not read the tree: `xtask vendor` recomputes that digest
from the bytes on disk and fails the gate if the literal has drifted, and `M13`
plants a mutated `SHA256SUMS` on a copy and requires the check to reject it.

The remaining conjuncts are the one-to-one property: each enabled identifier has
exactly one fully qualified Lean declaration name, exactly one row in the map and
exactly one vendored anchor; distinct enabled identifiers never share a
declaration; and a rejected identifier has no declaration, no anchor and no row.

It does **not** bind every enabled amended Core decoder, validator, runtime,
execution, and harness rule required by the public release profile.  Therefore
it does not discharge SPEC §15's public
`Wasm.profile_matches_pinned_revision`; `WS-004` remains open.  It also does not
claim that Lean derives vendored rule bodies from bytes. -/
theorem profile_matches_pinned_revision (profile : Wasm.Profile) :
    (profile.body.revisionCommit = Wasm.core3AdequacyMap.revisionCommit ∧
      Wasm.core3AdequacyMap.revisionCommit = Wasm.core3Revision.commit ∧
      Wasm.core3AdequacyMap.vendorTree = Wasm.core3VendoredTree ∧
      Wasm.core3AdequacyMap.vendorTree.commit =
        Wasm.core3AdequacyMap.revisionCommit ∧
      Wasm.core3AdequacyMap.vendorTree.manifestSha256 =
        Wasm.core3VendorManifestSha256 ∧
      (∀ r : Wasm.RevisionBody,
        Wasm.RevisionBody.identity r =
            Wasm.RevisionBody.identity Wasm.core3Revision ↔
          r = Wasm.core3Revision) ∧
      (∀ t : Wasm.VendoredTreeBody,
        Wasm.VendoredTreeBody.identity t =
            Wasm.VendoredTreeBody.identity Wasm.core3AdequacyMap.vendorTree ↔
          t = Wasm.core3AdequacyMap.vendorTree)) ∧
    (∀ id : Wasm.PinnedCoreRuleId, Wasm.PinnedCoreRuleId.RuleEnabled id →
      (∃ name : String,
        Wasm.PinnedCoreRuleId.fullDeclaration? id = some name ∧
        ∀ other : String,
          Wasm.PinnedCoreRuleId.fullDeclaration? id = some other → other = name) ∧
      (∃ row : Wasm.AdequacyRow,
        (row ∈ Wasm.core3AdequacyMap.rows ∧ row.ruleId = id.ruleId) ∧
        ∀ other : Wasm.AdequacyRow,
          other ∈ Wasm.core3AdequacyMap.rows →
            other.ruleId = id.ruleId → other = row) ∧
      (∃ anchor : String,
        Wasm.PinnedCoreRuleId.vendorAnchor? id = some anchor ∧
        ∀ other : String,
          Wasm.PinnedCoreRuleId.vendorAnchor? id = some other →
            other = anchor)) ∧
    (∀ a b : Wasm.PinnedCoreRuleId,
      Wasm.PinnedCoreRuleId.RuleEnabled a → Wasm.PinnedCoreRuleId.RuleEnabled b →
        Wasm.PinnedCoreRuleId.fullDeclaration? a =
            Wasm.PinnedCoreRuleId.fullDeclaration? b →
          a = b) ∧
    (∀ id : Wasm.PinnedCoreRuleId, ¬ Wasm.PinnedCoreRuleId.RuleEnabled id →
      Wasm.PinnedCoreRuleId.leanDeclaration? id = none ∧
      Wasm.PinnedCoreRuleId.vendorAnchor? id = none ∧
      id.ruleId ∉ Wasm.core3AdequacyMap.rows.map Wasm.AdequacyRow.ruleId) :=
  Wasm.profile_matches_pinned_revision profile

end WasmGemmGnaf.Theorems
