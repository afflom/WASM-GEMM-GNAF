/-
  Exact proposition bindings for the SPEC §15 required declarations.

  ## The defect this module exists to remove

  `xtask claims required` derives the SPEC §15 inventory from `SPEC.md` and asks
  the COMPILED environment whether each name exists and what its axiom closure
  is.  That is a check on a NAME.  An external audit put it exactly:

  > The repository's reported 36/58 remains inflated.  Its checker verifies names
  > rather than exact proposition types; its own M12 test demonstrates that a
  > matching-name `Nat := 0` is counted as discharged.

  That was accurate.  Every number this repository has published about SPEC §15
  rested on a check that a declaration named `Wasm.validation_progress` with type
  `Nat` would have passed.

  What follows is the fix, and it is the same discipline `Conformance/Schema.lean`
  applies one layer down: each required declaration is RESTATED in full and the
  restatement is closed by `:= @Name` — a definitional coercion.  If the
  declaration's real type is not defeq to the stated proposition, this file does
  not elaborate.  A tactic proof would establish only propositional equivalence
  and would defeat the entire point, so `xtask signature` rejects any binding not
  closed by `:= @Name`.

  ## What the tool checks, and what it cannot

  Machine-checked here:

    * the declaration exists, and its type is DEFINITIONALLY the proposition
      written below (Lean's elaborator decides this, not a string comparison);
    * every name `xtask claims required` counts discharged has a binding
      (`xtask signature` fails otherwise, and `required.rs` refuses to count an
      unbound name);
    * where `SPEC.md` states the theorem in a fenced `lean` block, the docstring
      quotes that block VERBATIM — `xtask signature` re-reads `SPEC.md` and
      compares, so a SPEC edit that changes a required statement breaks this file
      instead of silently passing.

  NOT machine-checked, and nothing here pretends otherwise: that the proposition
  written below IS what SPEC means, wherever SPEC states no fenced theorem.
  Twenty-nine of SPEC §15's fifty-eight names have no fenced statement anywhere in
  `SPEC.md`; of the thirty-nine bound below, twenty quote a verbatim SPEC block
  and nineteen quote governing prose instead.  For the second nineteen a reader
  closes the last step.  That residual is real and is the same one `Schema.lean`
  has.

  ## Three kinds of binding

  `-- spec-signature:` — the declaration carries SPEC's proposition.  Counts as
  discharged.

  `-- spec-signature-amended:` — the declaration carries a proposition that
  differs from SPEC's literal text, under a deviation filed in
  `model/spec-deviations.json`, whose id the marker cites.  `xtask signature`
  checks that the id exists.  Does NOT count as discharged.

  The gap an AMENDED binding discloses can point either way, and after SPEC's
  §24 amendment log it does.  It used to mean only "the repository proves
  something other than the literal text, because the literal text is false".
  Since `AMD-003` corrected SPEC §12.5 to the *stronger* scope-free form, the
  surviving AMENDED binding means the opposite: SPEC now asks for more than the
  declaration wearing the required name proves.  Either way the binding pins the
  proposition that IS carried, and either way it does not count.

  `-- spec-signature-weaker:` — the declaration is strictly weaker than SPEC's
  literal text and no deviation is filed.  The binding still pins the weaker
  proposition so it cannot drift, and names it as weaker in the tool's output.
  Does NOT count as discharged.

  The last two exist so that a disclosed gap is recorded in a form a machine
  reads, rather than looking like a binding somebody forgot to write.  Neither
  can inflate a number: only `spec-signature` counts.
-/
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Declarative
import WasmGemmGnaf.Wasm.Soundness
import WasmGemmGnaf.Wasm.Step
import WasmGemmGnaf.Wasm.PublicSuccessors
import WasmGemmGnaf.Wasm.PublicFuel
import WasmGemmGnaf.Wasm.Erasure
import WasmGemmGnaf.Wasm.CoreErasure
import WasmGemmGnaf.Wasm.CostedExplore
import WasmGemmGnaf.Wasm.Adequacy
import WasmGemmGnaf.Gemm.ABI
import WasmGemmGnaf.Gemm.Classify
import WasmGemmGnaf.Gemm.Reference
import WasmGemmGnaf.Cost.Aggregate
import WasmGemmGnaf.Cost.Event
import WasmGemmGnaf.Cost.Proper
import WasmGemmGnaf.GNAF.Normalize
import WasmGemmGnaf.Artifact.Emit
import WasmGemmGnaf.Universal.Evaluate
import WasmGemmGnaf.Universal.Argmin
import WasmGemmGnaf.Universal.EnumerateInputs
import WasmGemmGnaf.Universal.Partition
import WasmGemmGnaf.Universal.Sublevel
import WasmGemmGnaf.Atlas.Dependency
import WasmGemmGnaf.Atlas.Lifecycle
import WasmGemmGnaf.Atlas.Rebuild
import WasmGemmGnaf.Atlas.Reconstruct
import WasmGemmGnaf.Atlas.SemanticClosure

set_option autoImplicit false

namespace WasmGemmGnaf.Conformance

/-! ## 1. Wasm (SPEC §15, thirteen declarations) -/

/--
**SPEC §7.3**, quoted verbatim:

```lean
theorem decode_sound
    (h : Wasm.decode bytes = .ok module) :
  Wasm.DeclarativeBinaryRelation bytes module
```

No deviation: `bytes` and `module` are auto-bound implicits in SPEC's spelling
and explicit implicits here.

TYPE OF `module`, disclosed because it MOVED.  SPEC leaves `module` auto-bound
and states no type for it; §7.2 fixes the reading — "The decoder SHALL recognize
the complete pinned Core 3.0 binary grammar" — so `module` is the public
representable carrier `Wasm.Module`, whose `.core` field is a `Wasm.Core.Module`,
and `Wasm.decode` is the Core 3.0 decoder of
`Wasm/Core/Decode.lean`.  Until this tranche both denoted the SUBSET codec of
`Wasm/Binary.lean`, and `xtask independence` demoted this name as CIRCULAR
because the subset proof routed through the subset encoder.  The subset codec
survives as `Wasm.Subset.*`; nothing in the import graph of this theorem
contains an encoder.
-/
-- spec-signature: Wasm.decode_sound
theorem decode_sound_signature :
    ∀ {bytes : ByteArray} {module : Wasm.Module},
      Wasm.decode bytes = .ok module → Wasm.DeclarativeBinaryRelation bytes module :=
  @Wasm.decode_sound

/--
**SPEC §7.3**, quoted verbatim:

```lean
theorem decode_complete
    (h : Wasm.DeclarativeBinaryRelation bytes module) :
  Wasm.decode bytes = .ok module
```

No deviation.  `module` is a `Wasm.Module` for the reason recorded on
`decode_sound_signature` above.
-/
-- spec-signature: Wasm.decode_complete
theorem decode_complete_signature :
    ∀ {bytes : ByteArray} {module : Wasm.Module},
      Wasm.DeclarativeBinaryRelation bytes module → Wasm.decode bytes = .ok module :=
  @Wasm.decode_complete

/--
**SPEC §7.3 and §15**, quoted verbatim:

```lean
theorem encode_decode_roundtrip (module : Wasm.Module) :
  Wasm.decode (Wasm.encode module) = .ok module
```

EXACT. The public encoder is computational and complete on the representable
amended-Core carrier; the theorem uses the independent amended binary grammar.
-/
-- spec-signature: Wasm.encode_decode_roundtrip
theorem encode_decode_roundtrip_signature :
    ∀ (module : Wasm.Module),
      Wasm.decode (Wasm.encode module) = .ok module :=
  @Wasm.encode_decode_roundtrip

/-
**SPEC §7.3 and §15**, quoted verbatim:

```lean
theorem validate_bool_iff (module : Wasm.Module) :
  Wasm.validate module = true ↔ Wasm.DeclarativelyValid module
```

UNBOUND.  The former legacy-subset declaration was removed when the public
names were migrated to the amended-Core carrier.  Omission is intentional
until the exact public theorem above is kernel checked.
-/

/--
**SPEC §7.3 and §15.**  Public amended-Core validation preservation.

```lean
theorem validation_preservation
    (hvalid : Wasm.DeclarativelyValid module)
    (hstep : Wasm.Step config event next)
    (hconfig : Wasm.ConfigInstantiates module config) :
  Wasm.ConfigWellTyped next
```
-/
-- spec-signature: Wasm.validation_preservation
theorem validation_preservation_signature :
    ∀ {module : Wasm.Module} {config : Wasm.Config}
      {event : Wasm.Event} {next : Wasm.Config},
      Wasm.DeclarativelyValid module →
      Wasm.Step config event next →
      Wasm.ConfigInstantiates module config →
      Wasm.ConfigWellTyped next :=
  @Wasm.validation_preservation

/-
**SPEC §7.3**, quoted verbatim:

```lean
theorem validation_progress
    (hvalid : Wasm.DeclarativelyValid module)
    (hconfig : Wasm.ConfigInstantiates module config)
    (hwelltyped : Wasm.ConfigWellTyped config) :
  (∃ outcome, Wasm.Halt config outcome) ∨
  (∃ trap, Wasm.Trapped config trap) ∨
  (∃ exceptionValue, Wasm.Thrown config exceptionValue) ∨
  (Wasm.successors config).Nonempty
```

UNBOUND.  The former legacy-subset declaration was removed when the public
names were migrated to the amended-Core carrier.  Omission is intentional
until the exact public progress theorem above is kernel checked.
-/

/--
**SPEC §7.1**, quoted verbatim:

```lean
theorem mem_successors_iff_step :
  (event, next) ∈ M.successors config ↔ M.Step config event next
```

Here `Wasm.Config` is the proof-carrying validated/reachable amended-Core
Harness configuration, `Wasm.Step` is the corresponding authority relation,
and `Wasm.successors` is its exhaustive executable enumeration.
-/
-- spec-signature: Wasm.mem_successors_iff_step
theorem mem_successors_iff_step_signature :
    ∀ (config : Wasm.Config) (event : Wasm.Event) (next : Wasm.Config),
      (event, next) ∈ Wasm.successors config ↔ Wasm.Step config event next :=
  @Wasm.mem_successors_iff_step

/--
**SPEC §7.4** states this one in prose, not in a fenced block:

> Soundness SHALL map every returned observation to a relational execution.
> Completeness SHALL prove that every relational branch of length at most the
> bound occurs in the tree, and that `complete` contains every maximal branch.

Here `Wasm.Config` is the proof-carrying validated/reachable amended-Core
Harness configuration.  When `exploreAll` answers `complete`, the executable
absence of any prefix of length `bound + 1` removes the length hypothesis, so
the returned tree contains every relational finite branch (and hence every
finite maximal branch).
-/
-- spec-signature: Wasm.bounded_tree_covers_every_branch
theorem bounded_tree_covers_every_branch_signature :
    ∀ {bound : Nat} {initial : Wasm.Config}
      {obs : List Wasm.ExecutionObservation}
      {cov : Wasm.CoversEveryMaximalFiniteBranch bound initial obs},
      Wasm.exploreAll bound initial = Wasm.ExecutionTreeResult.complete obs cov →
      ∀ {o : Wasm.ExecutionObservation}, Wasm.FiniteExecution initial o → o ∈ obs :=
  @Wasm.bounded_tree_covers_every_branch

/--
**SPEC §7.4**, quoted verbatim:

```lean
theorem runFuel_sound
    (hmember : Wasm.TreeContains (Wasm.exploreAll bound initial) observation) :
  Wasm.FiniteExecution initial observation
```

The executable tree enumerates the proof-carrying public amended-Core Harness
successors, and membership is mapped back to the corresponding relational
finite execution.
-/
-- spec-signature: Wasm.runFuel_sound
theorem runFuel_sound_signature :
    ∀ {bound : Nat} {initial : Wasm.Config} {observation : Wasm.ExecutionObservation},
      Wasm.TreeContains (Wasm.exploreAll bound initial) observation →
      Wasm.FiniteExecution initial observation :=
  @Wasm.runFuel_sound

/--
**SPEC §7.4**, quoted verbatim:

```lean
theorem runFuel_complete_with_bound
    (hrun : Wasm.FiniteExecution initial observation)
    (hlen : observation.trace.length ≤ bound) :
  Wasm.TreeContains (Wasm.exploreAll bound initial) observation
```

This completeness theorem quantifies over the proof-carrying public
amended-Core Harness machine and follows every successor admitted by its exact
executable/relational successor equivalence.
-/
-- spec-signature: Wasm.runFuel_complete_with_bound
theorem runFuel_complete_with_bound_signature :
    ∀ {bound : Nat} {initial : Wasm.Config} {observation : Wasm.ExecutionObservation},
      Wasm.FiniteExecution initial observation →
      observation.trace.length ≤ bound →
      Wasm.TreeContains (Wasm.exploreAll bound initial) observation :=
  @Wasm.runFuel_complete_with_bound

/--
**SPEC §7.5**, quoted verbatim, as amended by `AMD-002` (SPEC §24):

```lean
theorem costed_erase_iff_plain_run :
  Wasm.CostedRun P module invocation costedTrace observation ↔
    (Wasm.Run module invocation (eraseCosts costedTrace) observation ∧
     Wasm.CostedLabelling module invocation costedTrace)
```

The FORMULA amendment is exact.  This binding was `spec-signature-amended`
under `DEV-001` while SPEC stated the bare biconditional.  SPEC has since been
corrected: the literal text was **proved false**, for every profile, by
`Wasm.not_costed_erase_iff_plain_run`
in `Wasm/Erasure.lean`.  The witness is a module that passes `Wasm.validate`
together with a costed trace whose erasure is exactly the plain trace of a
maximal run of that module, and which differs from the machine's own labelling
in one payload — the installed byte count of the harness transition — that
`Wasm.CostedEvent.erase` discards (`Wasm.erase_enterGemm_eq`).  The old
right-hand side holds of it (`Counterexample.minimal_run`) and the left-hand
side does not (`Counterexample.minimal_not_costedRun`), so no theorem of the
superseded shape exists and the amendment is the strongest true form.

The side condition is a condition on LABELS alone: `Wasm.CostedLabelling`
mentions no observation, no store and no terminal status, so it does not smuggle
the conclusion into the hypothesis.  The forward direction is strictly stronger
than the superseded text (`CostedRun` now yields the plain run *and* that the
labelling is machine-produced), and SPEC §7.5 additionally requires
`Wasm.costed_run_iff_plain_run`, which carries the intent with no side condition
at all.

The CARRIER is now exact: `module` is the public amended-Core `Wasm.Module`,
`invocation` is profile-indexed, configurations are validated/reachable public
Harness configurations, and cost labels contain the exact public Harness event
whose contribution is computed by the profile.  `DEV-001` stays on file because
its refutation explains the amended formula.
-/
-- spec-signature: Wasm.costed_erase_iff_plain_run
theorem costed_erase_iff_plain_run_signature :
    ∀ {P : Wasm.Profile} {module : Wasm.Module} {invocation : Wasm.Invocation P}
      {costedTrace : List Wasm.CostedEvent} {observation : Wasm.ExecutionObservation},
      Wasm.CostedRun P module invocation costedTrace observation ↔
        (Wasm.Run module invocation (Wasm.eraseCosts costedTrace) observation ∧
         Wasm.CostedLabelling module invocation costedTrace) :=
  @Wasm.costed_erase_iff_plain_run

/--
**SPEC §7.5**, quoted verbatim:

```lean
theorem costed_initialization_erase
    (h : Wasm.initialGemmInvocationCosted P module invocation =
      .ok initialization) :
  Wasm.initialGemmInvocation P module invocation = .ok initialization.initial
```

EXACT.  The profile is passed explicitly to both public initializers, the
module is the public amended-Core carrier, and the retained observation is
`Wasm.InitializationObservation P`.  The plain endpoint is the erasure of the
same public computation, not a separately implemented subset machine.
-/
-- spec-signature: Wasm.costed_initialization_erase
theorem costed_initialization_erase_signature :
    ∀ {P : Wasm.Profile} {module : Wasm.Module} {invocation : Wasm.Invocation P}
      {initialization : Wasm.InitializationObservation P},
      Wasm.initialGemmInvocationCosted P module invocation = .ok initialization →
      Wasm.initialGemmInvocation P module invocation = .ok initialization.initial :=
  @Wasm.costed_initialization_erase

/--
**SPEC §7.1** states this one in prose, not in a fenced block:

> `profile_matches_pinned_revision` means that the concrete model and map are
> identity-bound to the vendored revision and that every enabled vendored rule
> has exactly one mapped Lean declaration.  It does not claim that Lean can
> derive English prose from bytes.

The proposition below binds the public profile and vendored-tree identities,
then ranges over the generated finite index of every syntax, opcode,
validation, execution, and numeric obligation extracted from the pinned
SpecTec sources.  Every enabled row has one unique compiled declaration alias,
map row, and source anchor; every rejected row has none.  `just core` regenerates
the 1,291-row inventory byte-for-byte and elaborates every alias.  M13 tests the
vendored-content identity boundary and M14 tests the extraction, marker, and
compiled-declaration coverage boundary.
-/
-- spec-signature: Wasm.profile_matches_pinned_revision
theorem profile_matches_pinned_revision_signature :
    ∀ (profile : Wasm.Profile),
      (profile.body.revisionCommit = Wasm.core3AdequacyMap.revisionCommit ∧
       Wasm.core3AdequacyMap.revisionCommit = Wasm.core3Revision.commit ∧
       Wasm.core3AdequacyMap.vendorTree = Wasm.core3VendoredTree ∧
       Wasm.core3AdequacyMap.vendorTree.commit = Wasm.core3AdequacyMap.revisionCommit ∧
       Wasm.core3AdequacyMap.vendorTree.manifestSha256 = Wasm.core3VendorManifestSha256 ∧
       (∀ r : Wasm.RevisionBody,
          r.identity = Wasm.core3Revision.identity ↔ r = Wasm.core3Revision) ∧
       ∀ t : Wasm.VendoredTreeBody,
         t.identity = Wasm.core3AdequacyMap.vendorTree.identity ↔
           t = Wasm.core3AdequacyMap.vendorTree) ∧
      (∀ id : Wasm.PinnedCoreRuleId,
         id.RuleEnabled →
         (∃ name, id.fullDeclaration? = some name ∧
            ∀ other : String, id.fullDeclaration? = some other → other = name) ∧
         (∃ row, (row ∈ Wasm.core3AdequacyMap.rows ∧ row.ruleId = id.ruleId) ∧
            ∀ other : Wasm.AdequacyRow,
              other ∈ Wasm.core3AdequacyMap.rows → other.ruleId = id.ruleId → other = row) ∧
         ∃ anchor, id.vendorAnchor? = some anchor ∧
           ∀ other : String, id.vendorAnchor? = some other → other = anchor) ∧
      (∀ a b : Wasm.PinnedCoreRuleId,
         a.RuleEnabled → b.RuleEnabled → a.fullDeclaration? = b.fullDeclaration? → a = b) ∧
      ∀ id : Wasm.PinnedCoreRuleId,
        ¬ id.RuleEnabled →
        id.leanDeclaration? = none ∧
        id.vendorAnchor? = none ∧
        ¬ id.ruleId ∈ List.map Wasm.AdequacyRow.ruleId Wasm.core3AdequacyMap.rows :=
  @Wasm.profile_matches_pinned_revision

/-! ## 2. Gemm (SPEC §15, ten declarations) -/

/--
**SPEC §8.4**, quoted verbatim:

```lean
theorem classify_total (raw : problem.RawInvocation) :
  ∃ classification, Gemm.classify problem raw = classification
```

DEVIATION (domain), disclosed and in the widening direction: SPEC quantifies over
`problem.RawInvocation`, which §8.3 defines as `Gemm.RawInvocation P` — a body
paired with a lawfulness proof.  The repository's classifier is a function of the
profile and the PROOF-FREE body, so this theorem quantifies over
`Gemm.RawInvocationBody P`, of which every `Gemm.RawInvocation P` carries one.
Every SPEC instance is therefore an instance of this, and unlawful bodies are
covered too.
-/
-- spec-signature: Gemm.classify_total
theorem classify_total_signature :
    ∀ {P : Wasm.Profile} (raw : Gemm.RawInvocationBody P),
      ∃ classification, Gemm.classify P raw = classification :=
  @Gemm.classify_total

/--
**SPEC §8.4** states this one in prose, not in a fenced block:

> `Accepts` … SHALL be total over raw invocations.

SPEC's nearest fenced statement is the weaker `valid_reference_nonempty`, which
assumes `Gemm.classify problem raw = .valid invocation`.  The repository proves
the unconditional totality the prose asks for, with no classification hypothesis.
-/
-- spec-signature: Gemm.reference_total
theorem reference_total_signature :
    ∀ {P : Wasm.Profile} (problem : Gemm.Problem P) (raw : Gemm.RawInvocation P),
      ∃ observation, Gemm.Reference.Accepts problem raw observation :=
  @Gemm.reference_total

/--
**SPEC §8.4** states this one as an instance, not a theorem:

> ```lean
> instance problem_input_fintype : Fintype problem.RawInvocation
> ```

and **SPEC §10.3** item 2:

> Raw invocations within the ABI/memory profile are finite and exactly
> enumerable or covered by proved symbolic partitions.

DEVIATIONS, both disclosed: SPEC indexes by the problem, the repository by the
profile (`§8.3`: `Gemm.Problem.RawInvocation problem := Gemm.RawInvocation P`, so
these coincide); and `Fintype` is `Foundation.Fintype`, this development having
no Mathlib.

SPEC §4 forbids `Classical.choice` in an executable witness, so the axiom
closure of this declaration is decisive and is audited separately by
`xtask claims required` — `M12` is its falsifier.
-/
-- spec-signature: Gemm.valid_input_finite
abbrev valid_input_finite_signature :
    ∀ (P : Wasm.Profile), Foundation.Fintype (Gemm.ValidRawInvocation P) :=
  @Gemm.valid_input_finite

/--
**SPEC §8.4** `instance problem_input_fintype : Fintype problem.RawInvocation`,
and **SPEC §10.3** item 2, as for `valid_input_finite` above.  This is the
instance over the complete raw carrier: SPEC §8.3 requires that "all byte strings
of every representable length participate, including malformed headers", so this
one, and not `valid_input_finite`, is what the competitor universe rests on.

Same two disclosed deviations: profile-indexed rather than problem-indexed, and
`Foundation.Fintype`.
-/
-- spec-signature: Gemm.raw_input_finite
abbrev raw_input_finite_signature :
    ∀ (P : Wasm.Profile), Foundation.Fintype (Gemm.RawInvocation P) :=
  @Gemm.raw_input_finite

/--
**SPEC §8.3**, quoted verbatim:

```lean
theorem raw_invocation_roundtrip (raw : Gemm.RawInvocation P) :
  Gemm.decodeRawInvocation P (Gemm.encodeRawInvocation raw) = .ok raw
```

No deviation.
-/
-- spec-signature: Gemm.raw_invocation_roundtrip
theorem raw_invocation_roundtrip_signature :
    ∀ {P : Wasm.Profile} (raw : Gemm.RawInvocation P),
      Gemm.decodeRawInvocation P (Gemm.encodeRawInvocation raw) = .ok raw :=
  @Gemm.raw_invocation_roundtrip

/--
**SPEC §8.3**, quoted verbatim:

```lean
theorem raw_invocation_surjective
    (ptr len : UInt32) (bytes : ByteArray)
    (hlen : bytes.size = len.toNat)
    (hrange : ptr.toNat + len.toNat ≤ 2^P.addressBits)
    (hpages : pagesFor (ptr.toNat + len.toNat) ≤ P.maxPages) :
  ∃ raw : Gemm.RawInvocation P,
    raw.body.ptr = ptr ∧ raw.body.len = len ∧ raw.body.bytes = bytes
```

DEVIATION (spelling only): SPEC writes `pagesFor` unqualified; it is
`Wasm.pagesFor`.

This is the anti-narrowing theorem: it is what stops the raw carrier being
quietly restricted to inputs the implementation likes.
-/
-- spec-signature: Gemm.raw_invocation_surjective
theorem raw_invocation_surjective_signature :
    ∀ {P : Wasm.Profile} (ptr len : UInt32) (bytes : ByteArray),
      bytes.size = len.toNat →
      ptr.toNat + len.toNat ≤ 2 ^ P.addressBits →
      Wasm.pagesFor (ptr.toNat + len.toNat) ≤ P.maxPages →
      ∃ raw : Gemm.RawInvocation P,
        raw.body.ptr = ptr ∧ raw.body.len = len ∧ raw.body.bytes = bytes :=
  @Gemm.raw_invocation_surjective

/--
**SPEC §8.3** states this one in prose, not in a fenced block:

> `Gemm/ABI.lean` SHALL fix exact byte offsets, integer endianness, descriptor
> encoding, matrix regions, output region, and status encoding.

with the header layout fixed by the 256-byte table in that section.  The
roundtrip is what makes that table a bijection on well-formed headers rather
than a comment.
-/
-- spec-signature: Gemm.abi_roundtrip
theorem abi_roundtrip_signature :
    ∀ (h : Gemm.RawHeader), Gemm.decodeHeader (Gemm.encodeHeader h) = some h :=
  @Gemm.abi_roundtrip

/--
**SPEC §8.3** states this one in prose, not in a fenced block:

> Every byte-level well-formed descriptor whose views fit memory and whose tag
> combination appears above SHALL classify as valid unless it violates the
> explicitly enumerated alias or resource predicate.

The repository's proposition writes "byte-level well-formed, tag combination
appears above, and does not violate the enumerated predicates" out as the exact
conjunction of hypotheses the classifier is defined against.
-/
-- spec-signature: Gemm.classifier_exact_domain
theorem classifier_exact_domain_signature :
    ∀ {P : Wasm.Profile} (raw : Gemm.RawInvocationBody P) (h : Gemm.RawHeader),
      Gemm.decodeHeader raw.bytes = some h →
      Gemm.headerMalformed h = none →
      Gemm.tagUnsupported h = none →
      Gemm.headerCompatible h →
      Gemm.dimensionsRepresentable h →
      Gemm.DescriptorWellFormed (Gemm.descriptorOf h) (Gemm.windowOf P raw) →
      Gemm.ResourceOk P raw →
      ∃ invocation, Gemm.classify P raw = Gemm.Classification.valid invocation :=
  @Gemm.classifier_exact_domain

/--
**SPEC §8.3** states this one in prose, not in a fenced block:

> Required anti-vacuity theorems SHALL provide a nonzero `1×1×1` witness for
> every mandatory scalar-kind × compatible arithmetic-mode × transpose ×
> layout-class combination, and SHALL prove that the full C range and status are
> observable.

This binding is the first half of that sentence.  The mandatory combinations are
`Gemm.mandatoryCases`; for each, the witness classifies as `valid`, decodes to a
header with exactly that case's tags and transposes, has `1×1×1` shape, enters
with `C = 0`, and computes a NONZERO reference element with status `0`.  A
vacuous witness — one whose reference element were zero, or whose input were
rejected — would not satisfy this.
-/
-- spec-signature: Gemm.mandatory_family_nonzero_witnesses
theorem mandatory_family_nonzero_witnesses_signature :
    ∀ (P : Wasm.Profile) (c : Gemm.MandatoryCase),
      c ∈ Gemm.mandatoryCases →
      ∃ (raw : Gemm.RawInvocation P) (inv : Gemm.ValidInvocation P) (h : Gemm.RawHeader),
        Gemm.classify P raw.body = Gemm.Classification.valid inv ∧
        Gemm.decodeHeader raw.body.bytes = some h ∧
        h.aTag.toNat = c.kind.tag ∧
        h.bTag.toNat = c.kind.tag ∧
        h.cTag.toNat = c.kind.tag ∧
        h.accTag.toNat = c.acc.tag ∧
        h.modeTag.toNat = c.mode.tag ∧
        (Gemm.descriptorOf h).transposeA = c.transposeA ∧
        (Gemm.descriptorOf h).transposeB = c.transposeB ∧
        (Gemm.descriptorOf h).shapeC = { batch := 1, rows := 1, cols := 1 } ∧
        Gemm.cBitsAt (Gemm.descriptorOf h) (Gemm.entryStore raw.body)
            { b := 0, i := 0, j := 0 } = 0 ∧
        Gemm.referenceElem (Gemm.descriptorOf h) (Gemm.entryStore raw.body)
            { b := 0, i := 0, j := 0 } = Gemm.oneBits c.kind ∧
        Gemm.oneBits c.kind ≠ 0 ∧
        Gemm.referenceStatus raw.body = 0 :=
  @Gemm.mandatory_family_nonzero_witnesses

/--
**SPEC §8.3**, the second half of the anti-vacuity sentence quoted above:

> … and SHALL prove that the full C range and status are observable.

and **SPEC §8.3** again, on what "observable" means:

> C and status-detail are fully observable.

The repository's proposition: for an accepted reference observation of a valid
raw input, the semantic outcome is `returned` with exactly the reference status,
and EVERY byte of the invocation extent lying in the C region or the
status-detail region equals the reference final store at that index.  A masked
or partially reported C would not satisfy this.
-/
-- spec-signature: Gemm.observation_covers_status_and_full_c
theorem observation_covers_status_and_full_c_signature :
    ∀ {P : Wasm.Profile} (problem : Gemm.Problem P) (raw : Gemm.RawInvocation P)
      {o : Wasm.ExecutionObservation},
      Gemm.refValid raw.body = true →
      Gemm.Reference.Accepts problem raw o →
      ∃ e f,
        Gemm.semanticFor problem raw o =
          Gemm.SemanticOutcome.returned (Gemm.referenceStatus raw.body) e f ∧
        ∀ i : Nat,
          i < raw.body.len.toNat →
          ((Gemm.regionsOfRaw raw.body).c.Mem i ∨
           (Gemm.regionsOfRaw raw.body).statusDetail.Mem i) →
          f i = Gemm.referenceFinalStore raw.body i :=
  @Gemm.observation_covers_status_and_full_c

/-! ## 3. Cost (SPEC §15, three declarations) -/

/--
**SPEC §9.3** states this one in prose, not in a fenced block:

> The implementation SHALL prove `evaluation.cost.static.moduleBytes =
> bytes.size`, positive accounting for every semantic transition and module/store
> byte, finiteness of every coordinate sublevel, and completeness of the
> byte/input/execution enumerators induced by `boundOfScore`.

> ```lean
> def Cost.ExactAggregateCost
>     {Raw : Type} [Fintype Raw]
>     (P : Wasm.Profile) (bytes : ByteArray) (module : Wasm.Module)
>     (repetitions : Nat) (dynamicFor : Raw → Cost.DynamicVector)
>     (cost : Cost.CompleteSystemCost) : Prop
> ```
-/
-- spec-signature: Cost.module_bytes_exact
theorem module_bytes_exact_signature :
    ∀ {Raw : Type} [Foundation.Fintype Raw]
      {P : Wasm.Profile} {bytes : ByteArray} {module : Wasm.Module}
      {repetitions : Nat}
      {dynamicFor : Raw → Cost.DynamicVector} {cost : Cost.CompleteSystemCost},
      Cost.ExactAggregateCost P bytes module repetitions dynamicFor cost →
      cost.static.moduleBytes = bytes.size :=
  @Cost.module_bytes_exact

/--
**SPEC §9.3** states this one in prose, not in a fenced block:

> The implementation SHALL prove … positive accounting for every semantic
> transition and module/store byte …

The repository's proposition: composing an event's charge onto a running vector
raises the total by at least that event's weight.  No transition can be free, so
no competitor can be credited with an unaccounted step.
-/
-- spec-signature: Cost.transition_accounting_positive
theorem transition_accounting_positive_signature :
    ∀ (v : Cost.DynamicVector) (e : Cost.Event),
      v.total + e.weight ≤ (Cost.sequentialCompose v e.charge).total :=
  @Cost.transition_accounting_positive

/--
**SPEC §9.3** states this one in prose, not in a fenced block:

> The implementation SHALL prove … finiteness of every coordinate sublevel …

and **SPEC §10.2**:

> it SHALL prove that every possible competitor capable of beating the known
> baseline lies in a finite, exactly checkable cost sublevel.

DEVIATION (generality), disclosed and in the widening direction: SPEC §9.3
indexes `Cost.ProperObjective` by `(P : Wasm.Profile) (G : Gemm.Problem P)`; the
repository's is polymorphic in both index types.  Every SPEC instance is an
instance of this.
-/
-- spec-signature: Cost.objective_sublevel_finite
theorem objective_sublevel_finite_signature :
    ∀ {Profile Problem : Type} {P : Profile} {G : Problem}
      (objective : Cost.ProperObjective P G) (u : Nat) (c : Cost.CompleteSystemCost),
      objective.score c ≤ u → c ∈ Cost.sublevelEnumeration u :=
  @Cost.objective_sublevel_finite

/-! ## 4. GNAF and the emitter (SPEC §15, three declarations) -/

/--
**SPEC §11.3**, quoted verbatim:

```lean
theorem normalize_semantics (plan : GNAF.CheckedPlan P G) :
  GNAF.Eval (GNAF.normalize plan) = GNAF.Eval plan
```

DEVIATION (domain), disclosed and in the widening direction: SPEC quantifies over
`GNAF.CheckedPlan P G`; the repository proves it for every `GNAF.Plan`, of which a
`CheckedPlan` carries one (`GNAF/Typing.lean`: `CheckedPlan.plan`).  Every SPEC
instance is therefore an instance of this.  The repository's `CheckedPlan` is
indexed by signatures rather than by `(P, G)`, which is why the general form is
the one stated.
-/
-- spec-signature: GNAF.normalize_semantics
theorem normalize_semantics_signature :
    ∀ (p : GNAF.Plan), GNAF.Eval (GNAF.normalize p) = GNAF.Eval p :=
  @GNAF.normalize_semantics

/--
**SPEC §11.3**, quoted verbatim:

```lean
theorem normalize_cost_le (plan : GNAF.CheckedPlan P G) :
  GNAF.certifiedCost (GNAF.normalize plan) ≤ GNAF.certifiedCost plan
```

DEVIATIONS, both disclosed: the same widening from `CheckedPlan P G` to `Plan` as
for `normalize_semantics`; and `GNAF.certifiedCost p` is written `p.certifiedCost`
here, which is the same function (`GNAF/Plan.lean`).
-/
-- spec-signature: GNAF.normalize_cost_le
theorem normalize_cost_le_signature :
    ∀ (p : GNAF.Plan), (GNAF.normalize p).certifiedCost ≤ p.certifiedCost :=
  @GNAF.normalize_cost_le

/--
**SPEC §11.4**, quoted verbatim:

```lean
theorem decode_emit : Wasm.decode (Artifact.emit m) = .ok m
```

EXACT.  `m` is auto-bound in SPEC's spelling and universally quantified here.
`Wasm.Module` is the carrier of amended Core 3.0 ASTs that have a declarative
binary derivation.  `Artifact.emit` uses the independently verified amended
Core encoder, and `Artifact.decode_emit` composes its grammar soundness with
the public decoder's grammar completeness.
-/
-- spec-signature: Artifact.decode_emit
theorem decode_emit_signature :
    ∀ (m : Wasm.Module), Wasm.decode (Artifact.emit m) = .ok m :=
  @Artifact.decode_emit

/-! ## 5. Universal (SPEC §15, twelve declarations) -/

/--
**SPEC §10.3**, quoted verbatim:

```lean
theorem possible_winner_within_sublevel
    (hc : ProfileValid P competitorBytes)
    (cEval : SystemEvaluation P G competitorBytes)
    (heval : SystemEvaluationRel P G competitorBytes cEval)
    (hcorrect : Correct G cEval)
    (hfeasible : Feasible G cEval)
    (hbetter : O.score cEval.cost ≤ O.score bEval.cost) :
  WithinSublevel (O.boundOfScore (O.score bEval.cost)) competitorBytes cEval
```

DEVIATIONS, all disclosed:

* SPEC's `P G` pair is bundled by the repository as `S : Universal.Setting P`,
  carrying the costed semantics, the costed machine and the problem, so
  `SystemEvaluation P G bytes` is written `SystemEvaluation S bytes`.
* `SystemEvaluationRel` gains a `D : Universal.Decider S` parameter, which SPEC
  leaves as a fixed `Universal.evaluate`.  It is universally quantified here, so
  the repository's statement is the stronger one: it holds for EVERY evaluator,
  not for one privileged evaluator.
* The theorem carries a `Foundation.Fintype (Gemm.RawInvocation P)` instance
  argument that SPEC's statement does not.  It is discharged by
  `Gemm.raw_input_finite`, itself SPEC §15 required and present, so the
  hypothesis is not an escape hatch; it is still an added hypothesis and is named
  here rather than hidden.
* Binder ORDER differs from SPEC's listing.  Every SPEC hypothesis appears, none
  is added beyond the instance named above, and the conclusion is unchanged.
All module-bearing propositions now quantify over the public amended-Core
`Wasm.Module`.  The bundled-setting and fixed-evaluator presentation changes
above do not narrow any SPEC hypothesis or conclusion.
-/
-- spec-signature: Universal.possible_winner_within_sublevel
theorem possible_winner_within_sublevel_signature :
    ∀ {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]
      {S : Universal.Setting P} {D : Universal.Decider S}
      (O : Cost.ProperObjective P S.problem)
      {baselineBytes competitorBytes : ByteArray}
      (bEval : Universal.SystemEvaluation S baselineBytes),
      Universal.ProfileValid P competitorBytes →
      ∀ cEval : Universal.SystemEvaluation S competitorBytes,
        Universal.SystemEvaluationRel S D competitorBytes cEval →
        Universal.Correct cEval →
        Universal.Feasible cEval →
        O.score cEval.cost ≤ O.score bEval.cost →
        Universal.WithinSublevel (O.boundOfScore (O.score bEval.cost))
          competitorBytes cEval :=
  @Universal.possible_winner_within_sublevel

/--
**SPEC §10.3** item 1, in prose:

> Byte strings within the module-size bound are finite and exactly enumerable.

and **SPEC §9.3**:

> … completeness of the byte/input/execution enumerators induced by
> `boundOfScore`.

The repository's proposition is the completeness half: every byte string no
longer than the bound is IN the enumeration.  It is the direction that matters —
soundness of an enumerator cannot make coverage false, incompleteness can.
-/
-- spec-signature: Universal.byte_enumerator_complete
theorem byte_enumerator_complete_signature :
    ∀ {bound : Nat} {bytes : ByteArray},
      bytes.size ≤ bound → bytes ∈ Universal.byteEnumerator bound :=
  @Universal.byte_enumerator_complete

/--
**SPEC §10.3** item 2, in prose:

> Raw invocations within the ABI/memory profile are finite and exactly
> enumerable or covered by proved symbolic partitions.

and **SPEC §9.3** on enumerator completeness, as quoted for
`byte_enumerator_complete`.

The repository's proposition is unconditional: EVERY raw invocation of the
profile occurs in the enumeration, with no size or shape side condition.
-/
-- spec-signature: Universal.input_enumerator_complete
theorem input_enumerator_complete_signature :
    ∀ {P : Wasm.Profile} (G : Gemm.Problem P) (raw : Gemm.RawInvocation P),
      raw ∈ Universal.enumerateInputs P G :=
  @Universal.input_enumerator_complete

/--
**SPEC §10.3**, governing prose:

> Runs within the step and state bounds are finite.

and:

> Decoder, validator, reference acceptance, resource use, and exact trace cost
> are decidable on that finite carrier.

SPEC lists `Universal.execution_checker_sound` without a separate fenced
formula.  The bound proposition here is the public checker's exact local
reflection boundary: a completed answer retains both the fresh-initialization
equality and the completed all-successor-tree equality that constructed it.
-/
-- spec-signature: Universal.execution_checker_sound
theorem execution_checker_sound_signature :
    ∀ {P : Wasm.Profile} {S : Universal.Setting P} {module : Wasm.Module}
      {raw : Gemm.RawInvocation P}
      {evaluation : Universal.InputEvaluation S module raw},
      Universal.executionChecker S module raw = .complete evaluation →
      Wasm.initialGemmInvocationCosted P module
          (Universal.toWasmInvocation raw) = .ok evaluation.initialization ∧
      ∃ coverage,
        S.machine.exploreAllCosted S.problem.maxSteps evaluation.initial =
          .complete evaluation.observations coverage :=
  @Universal.execution_checker_sound

/--
**SPEC §10.3**, governing prose:

> Runs within the step and state bounds are finite.

and:

> Every sublevel module is checked, or a proof certificate covers its exact
> canonical partition.

SPEC lists `Universal.execution_checker_complete_within_sublevel` without a
separate fenced formula.  The completeness direction below says that successful
fresh initialization plus a completed tree at the problem's exact bound is
returned by the checker as an `InputEvaluation`; no oracle or extra coverage
premise over byte strings is accepted.
-/
-- spec-signature: Universal.execution_checker_complete_within_sublevel
theorem execution_checker_complete_within_sublevel_signature :
    ∀ {P : Wasm.Profile} {S : Universal.Setting P} {module : Wasm.Module}
      {raw : Gemm.RawInvocation P}
      {initialization : Universal.InitializationObservation P}
      {observations : Foundation.NonemptyCanonicalFrontier
        (Universal.CostedExecutionObservation P initialization.initial)}
      {coverage : Universal.CostedCoverage P S.problem.maxSteps
        initialization.initial observations},
      Wasm.initialGemmInvocationCosted P module
          (Universal.toWasmInvocation raw) = .ok initialization →
      S.machine.exploreAllCosted S.problem.maxSteps initialization.initial =
          .complete observations coverage →
      ∃ evaluation : Universal.InputEvaluation S module raw,
        Universal.executionChecker S module raw = .complete evaluation :=
  @Universal.execution_checker_complete_within_sublevel

/--
**SPEC §10.1**, quoted verbatim:

```lean
theorem system_evaluation_rel_sound
    (hrel : SystemEvaluationRel P G bytes evaluation) :
  (Correct G evaluation ↔ SemanticCorrect P G bytes) ∧
  (Feasible G evaluation ↔ SemanticWithinResources P G bytes)
```

DEVIATIONS (spelling), all disclosed and as for
`possible_winner_within_sublevel`: `P G` is bundled as `S : Universal.Setting P`,
and `SystemEvaluationRel` carries the empty canonical-evaluator token
`D : Universal.Decider S` explicitly, universally quantified.  The token has no
callback or data field; the relation calls `Universal.evaluate` directly.  The
constructive finite evaluator also carries the globally discharged
`Foundation.Fintype (Gemm.RawInvocation P)` instance explicitly.
-/
-- spec-signature: Universal.system_evaluation_rel_sound
theorem system_evaluation_rel_sound_signature :
    ∀ {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]
      {S : Universal.Setting P} {D : Universal.Decider S}
      {bytes : ByteArray} {evaluation : Universal.SystemEvaluation S bytes},
      Universal.SystemEvaluationRel S D bytes evaluation →
      (Universal.Correct evaluation ↔ Universal.SemanticCorrect S bytes) ∧
      (Universal.Feasible evaluation ↔
        Universal.SemanticWithinResources S bytes) :=
  @Universal.system_evaluation_rel_sound

/--
**SPEC §10.1**, quoted verbatim:

```lean
theorem system_evaluation_rel_complete
    (hprofile : ProfileValid P bytes)
    (hcorrect : SemanticCorrect P G bytes)
    (hresources : SemanticWithinResources P G bytes) :
  ∃ evaluation : SystemEvaluation P G bytes,
    SystemEvaluationRel P G bytes evaluation
```

DEVIATIONS (spelling), all disclosed and as for the two neighboring
reflection theorems: `P G` is bundled as `S : Universal.Setting P`, and
`SystemEvaluationRel` carries the empty canonical-evaluator token
`D : Universal.Decider S` explicitly.  The constructive finite evaluator also
carries the globally discharged `Foundation.Fintype
(Gemm.RawInvocation P)` instance explicitly.
-/
-- spec-signature: Universal.system_evaluation_rel_complete
theorem system_evaluation_rel_complete_signature :
    ∀ {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]
      {S : Universal.Setting P} {D : Universal.Decider S}
      {bytes : ByteArray},
      Universal.ProfileValid P bytes →
      Universal.SemanticCorrect S bytes →
      Universal.SemanticWithinResources S bytes →
      ∃ evaluation : Universal.SystemEvaluation S bytes,
        Universal.SystemEvaluationRel S D bytes evaluation :=
  @Universal.system_evaluation_rel_complete

/--
**SPEC §10.1**, quoted verbatim:

```lean
theorem system_evaluation_rel_functional
    (ha : SystemEvaluationRel P G bytes a)
    (hb : SystemEvaluationRel P G bytes b) :
  a = b
```

DEVIATIONS (spelling), both disclosed and both as for
`possible_winner_within_sublevel`: `P G` is bundled as `S : Universal.Setting P`,
and `SystemEvaluationRel` carries the evaluator `D : Universal.Decider S`
explicitly, universally quantified.

This is the third of SPEC §10.1's three reflection theorems.  Soundness and
completeness above are exact as well.  The quantified evaluation carries the
public amended-Core module and decoder.
-/
-- spec-signature: Universal.system_evaluation_rel_functional
theorem system_evaluation_rel_functional_signature :
    ∀ {P : Wasm.Profile} {S : Universal.Setting P} {D : Universal.Decider S}
      {bytes : ByteArray} {a b : Universal.SystemEvaluation S bytes},
      Universal.SystemEvaluationRel S D bytes a →
      Universal.SystemEvaluationRel S D bytes b →
      a = b :=
  @Universal.system_evaluation_rel_functional

/--
**SPEC §10.4** states this one through the `PartitionResult` constructors rather
than as a named theorem.  The governing text:

> `incomplete` propagates to `SolveResult.incomplete` and blocks release.

The repository's proposition is the dichotomy that makes that sentence
enforceable: for any bytes denoted by the root partition, either the bytes are
RESOLVED, or some leaf denoting them is answered `incomplete` with an explicit
coverage gap.  There is no third outcome in which coverage is claimed without
either a resolution or a recorded gap.

DEVIATION (disclosed): the theorem carries a
`Foundation.Fintype (Gemm.RawInvocation P)` instance argument, discharged by
`Gemm.raw_input_finite`.
-/
-- spec-signature: Universal.partition_cover_complete
theorem partition_cover_complete_signature :
    ∀ {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]
      {scope : Universal.PartitionScope P}
      (strategy : Universal.PartitionStrategy scope)
      (root : Universal.PartitionBody scope) (bytes : ByteArray),
      root.Denotes bytes →
      Universal.Resolved scope bytes ∨
        ∃ leaf gap, leaf.Denotes bytes ∧
          strategy leaf = Universal.PartitionResult.incomplete gap :=
  @Universal.partition_cover_complete

/-! ## 6. Atlas (SPEC §15, ten declarations) -/

/--
**SPEC §12.5** step 2, in prose:

> compute the least new semantic closure;

and **SPEC §12.1**:

> Optimizer conclusions such as "best," "dominated," or "selected" SHALL NOT be
> premises in semantic closure.

The repository's proposition is LEASTNESS in full: the computed closure is
closed under the rule set, contains the input facts, and is contained in every
`S` with those two properties.  "Least" is proved, not asserted by naming a
function `semanticClosure`.
-/
-- spec-signature: Atlas.semantic_closure_least
theorem semantic_closure_least_signature :
    ∀ (R : Atlas.SemanticRuleSet) (A : Atlas.SemanticFacts),
      Atlas.Closure.ClosedFacts R (Atlas.semanticClosure R A) ∧
      Atlas.Closure.FactSub A (Atlas.semanticClosure R A) ∧
      ∀ S : Atlas.SemanticJudgment → Prop,
        Atlas.Closure.ClosedUnder R S →
        (∀ x : Atlas.SemanticJudgment, A x = true → S x) →
        ∀ x : Atlas.SemanticJudgment, Atlas.semanticClosure R A x = true → S x :=
  @Atlas.semantic_closure_least

/--
**SPEC §12.3**, quoted verbatim in full — the section states no fenced theorem:

> Every certificate SHALL list its exact object, edge, profile, problem,
> objective, and partition dependencies.  Adding or changing an edge invalidates
> the complete transitive impact cone before any new seal.  Unaffected
> certificates may be reused only with a verified transition warrant.

The repository's proposition is the second sentence: if a certificate depends on
an object that REACHES any changed object along the exact dependency edges, that
certificate's id is in the impact cone.  No certificate can survive a change it
transitively depends on.
-/
-- spec-signature: Atlas.invalidation_complete
theorem invalidation_complete_signature :
    ∀ (b : Atlas.StateBody) (changed : List Foundation.CanonicalObjectId)
      (c : Atlas.CertificateEntry),
      c ∈ b.certificates.entries →
      ∀ d : Foundation.CanonicalObjectId,
        d ∈ Atlas.certificateDependencies b c →
        ∀ t : Foundation.CanonicalObjectId,
          t ∈ changed →
          Atlas.Reaches (Atlas.exactDependencyEdges b) d t →
          c.certificateId ∈ Atlas.impactCone (Atlas.exactDependencyEdges b) changed :=
  @Atlas.invalidation_complete

/--
**SPEC §12.5**, quoted verbatim, as amended by `AMD-003` (SPEC §24):

```lean
theorem incremental_eq_full_rebuild
    (hcoherent : Atlas.Coherent state.body)
    (hupdate : (Atlas.accumulate budget state delta).result = .complete successor) :
  Atlas.canonicalize successor.body =
    Atlas.canonicalize
      (Atlas.semanticRebuildBodyWith state.body.scope
        (state.body.declarationBase ∪ delta.declarations))
```

The superseded scope-free statement rebuilt through
`Atlas.semanticRebuildBody` and is kernel-refuted by
`Atlas.not_incremental_eq_full_rebuild`. `AMD-003` repaired the target by
rebuilding through `semanticRebuildBodyWith` in the state's own scope and by
requiring coherence. The declaration below now carries that exact amended
proposition under the required name.
-/
-- spec-signature: Atlas.incremental_eq_full_rebuild
theorem incremental_eq_full_rebuild_signature :
    ∀ {budget : Atlas.BuildBudget} {state : Atlas.UnsealedState} {delta : Atlas.Delta}
      {successor : Atlas.UnsealedState},
      Atlas.Coherent state.body →
      (Atlas.accumulate budget state delta).result = .complete successor →
      Atlas.canonicalize successor.body =
        Atlas.canonicalize
          (Atlas.semanticRebuildBodyWith state.body.scope
            (state.body.declarationBase ∪ delta.declarations)) :=
  @Atlas.incremental_eq_full_rebuild

/--
**SPEC §12.1**, quoted verbatim — the section states no fenced theorem for this
name:

> The deterministic checkers define `canonicalSealCheckResultId` by storing the
> complete checker input, result, and retained preimages in canonical form.

and, on what the seal identity is taken over:

> proof-free `SealCertificateBody` records the checked certificate-object
> identities, `SealCertificate` proves that body/core, and `sealId` identifies
> only `(core, certificate.body)`.

with **SPEC §20.2** item 10:

> The Atlas seal reconstructs from retained canonical objects.

The repository's proposition is that a *verifier* — a function whose ONLY input
is the seal identity, `Atlas.SealIdentity`, one
`ObjectId (SealCore × SealCertificateBody)` — reconstructs

1. exactly the retained preimage list of the sealed state, and
2. for every identity the seal's own `retentionRoot` records, the exact bytes
   retained for it, proved to be a member of the state's retained graph.

The distinction this binding exists to keep: `Atlas.sealVerifierPreimages` is
handed no state, no object graph, no preimage and no proof.  A "reconstruction"
given the preimages and checking that they hash correctly would be a statement
about the CALLER; this one opens the seal identity into the proof-free
`SealCertificateBody`, reads the recorded `retentionCheckResultId` out of it,
opens THAT identity into the checker record, and returns the record's
preimages.  Both openings are total executable readers proved to be left
inverses of the canonical encoders (`Atlas.…R_inverts` in `Atlas/Reconstruct.lean`),
so the content is effectiveness, not the schemas' injectivity.

SPEC §12.1's proof-free/resolved distinction is preserved: everything
reconstructed is a proof-free body (`SealCertificateBody`, `SealCheckResultBody`,
`PreimageEntry`).  The verifier never produces an `Atlas.SealCertificate` or an
`Atlas.UnsealedState`, both of which carry proofs; the resolved objects appear
only on the right of the equations, as what the reconstruction is compared
against.

**Not a coverage claim.**  Every reconstructed byte string comes from
`state.retainedObjects.graph.preimages`, a finite list the seal itself records.
Nothing here quantifies over `ByteArray`, competitors, partitions or optimality,
and a seal retaining three objects satisfies it exactly as one retaining a
million does.  `Atlas.universalCoverCompleteCheck_scope_blind` is untouched and
`Atlas.seal_implies_universal_coverage` remains absent.
-/
-- spec-signature: Atlas.seal_verifier_reconstructs_every_preimage
theorem seal_verifier_reconstructs_every_preimage_signature :
    ∀ sealed : Atlas.SealedState,
      Atlas.sealVerifierPreimages sealed.sealId =
          some sealed.state.retainedObjects.graph.preimages ∧
        ∀ id ∈ sealed.core.retentionRoot.retainedIds,
          ∃ preimage : ByteArray,
            Atlas.sealVerifierPreimage sealed.sealId id = some preimage ∧
            Atlas.PreimageEntry.mk id preimage ∈
              sealed.state.retainedObjects.graph.preimages :=
  @Atlas.seal_verifier_reconstructs_every_preimage

/--
**SPEC §16**, quoted verbatim:

```lean
theorem lifecycle_prefix_conservation
    {body : Atlas.LifecycleTraceBody}
    {trace : Atlas.ResolvedLifecycleTrace body}
    {algorithm : Atlas.LifecycleAlgorithmTag}
    (evaluation : Atlas.LifecycleEvaluation trace algorithm) :
  evaluation.total =
    Cost.sumLifecycle (evaluation.prefixes.map (·.cost))
```

DEVIATION (spelling only): `evaluation.prefixes` is a canonical list, so its
elements are reached as `.elements` and mapped with `List.map`.

This is the theorem that stops a lifecycle total being anything other than the
fold of its own prefixes — no unaccounted build work.
-/
-- spec-signature: Atlas.lifecycle_prefix_conservation
theorem lifecycle_prefix_conservation_signature :
    ∀ {body : Atlas.LifecycleTraceBody} {trace : Atlas.ResolvedLifecycleTrace body}
      {algorithm : Atlas.LifecycleAlgorithmTag}
      (evaluation : Atlas.LifecycleEvaluation trace algorithm),
      evaluation.total =
        Cost.sumLifecycle (List.map (fun r => r.cost) evaluation.prefixes.elements) :=
  @Atlas.lifecycle_prefix_conservation

/--
**SPEC §16**, quoted verbatim:

```lean
theorem lifecycle_native_bound
    {body : Atlas.LifecycleTraceBody}
    {trace : Atlas.ResolvedLifecycleTrace body}
    (evaluation : Atlas.LifecycleEvaluation trace .nativeIncremental) :
  evaluation.total ≤
    Atlas.nativeLifecycleBound Release.primitiveCostTable evaluation.size
```

No deviation.  `≤` is `Cost.LifecycleVector.ComponentwiseLE` via the `LE`
instance in `Cost/Lifecycle.lean`: all seventeen coordinates at once, no trade
between them.

`Release.primitiveCostTable` is pinned in `Cost/Lifecycle.lean` — not in
`Artifact/Release.lean`, because SPEC §10.1's firewall forbids `Cost/` from
importing upward and `Atlas/Lifecycle.lean` must state the bound over it.  Every
coefficient is `1`, the componentwise-minimal positive table SPEC §16 admits, so
the binding cannot be satisfied by inflating a constant;
`Atlas.lifecycle_native_bound_of_positive` proves the same inequality for every
positive table, and `Release.primitiveCostTable_minimal` records that the pinned
table is dominated by all of them.

What the bound constrains is machine-checked, not asserted:
`Atlas.lifecycle_native_bound_attained` proves fourteen of the seventeen
coordinates hold with *equality*, and `Atlas.lifecycle_native_bound_slack` gives
the exact slack on the remaining three (the logarithmic canonicalization factor,
the threefold index bracket, and the request bytes the query bracket adds).  All
three are slack in the shape of SPEC §16's polynomial, not in a coefficient.
-/
-- spec-signature: Atlas.lifecycle_native_bound
theorem lifecycle_native_bound_signature :
    ∀ {body : Atlas.LifecycleTraceBody} {trace : Atlas.ResolvedLifecycleTrace body}
      (evaluation : Atlas.LifecycleEvaluation trace .nativeIncremental),
      evaluation.total ≤
        Atlas.nativeLifecycleBound Release.primitiveCostTable evaluation.size :=
  @Atlas.lifecycle_native_bound

/--
**SPEC §16**, quoted verbatim:

```lean
theorem lifecycle_full_rebuild_comparator_exact
    {body : Atlas.LifecycleTraceBody}
    {trace : Atlas.ResolvedLifecycleTrace body}
    (evaluation : Atlas.LifecycleEvaluation trace .nativeIncremental) :
  Atlas.regretAgainst .canonicalFullRebuildAtEverySeal evaluation =
    Cost.truncatedDifference
      evaluation.total
      (Atlas.canonicalFullRebuildEvaluation trace).total
```

The theorem holds by `rfl`, and `Atlas.lifecycle_full_rebuild_comparator_exact`
says so in its own docstring rather than reading as a deep result.  What the
binding buys is exactly what a definitional coercion can buy: it pins
`Atlas.regretAgainst` at the canonical tag to the truncated difference of this
evaluation's total and the total of `Atlas.canonicalFullRebuildEvaluation` **of
the same trace**.  A later edit that redirected the comparator to a different
evaluation, inserted slack, or compared against a stored number would stop this
file elaborating.

Nothing here claims the regret is zero or bounded; SPEC §16's competitive claim
is a separate obligation.
-/
-- spec-signature: Atlas.lifecycle_full_rebuild_comparator_exact
theorem lifecycle_full_rebuild_comparator_exact_signature :
    ∀ {body : Atlas.LifecycleTraceBody} {trace : Atlas.ResolvedLifecycleTrace body}
      (evaluation : Atlas.LifecycleEvaluation trace .nativeIncremental),
      Atlas.regretAgainst .canonicalFullRebuildAtEverySeal evaluation =
        Cost.truncatedDifference evaluation.total
          (Atlas.canonicalFullRebuildEvaluation trace).total :=
  @Atlas.lifecycle_full_rebuild_comparator_exact

end WasmGemmGnaf.Conformance
