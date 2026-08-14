/-
  Theorems: the release theorem, at the strength it actually has.

  This module is an INDEX over `Artifact/Release.lean`.  It exists so that the
  *conditional* nature of the release result is visible at the top level rather
  than buried under a chain of abbreviations: every hypothesis is written out in
  the statement, and the scope the statement is about is collected into a single
  checkable conjunction.

  ## What is proved here

  | name | content |
  |---|---|
  | `Theorems.release_scope_identities` | every profile / problem / setting / objective identity equation of the release instance, in one conjunction |
  | `Theorems.release_seam_nondegenerate` | the constructed subset `Release.seam` charges every event, charges every validation, budgets every coordinate, and its machine completes with a nonempty frontier |

  ## WHAT IS NOT PROVED HERE, AND USED TO BE

  The release theorem.  `Theorems.release_decider_answers_admissible`,
  `release_globalOptimal_of_nonempty`, `release_globalOptimal_of_admissible`,
  `release_obligation_reduction`, `release_lower_bound_clause`,
  `release_tie_break_clause`, `release_competitor_universe_inhabited`,
  `release_decider_answers_admissible_at_seam`,
  `release_globalOptimal_of_nonempty_at_seam` and
  `release_globalOptimal_of_witness_semantics` were all stated against
  `Release.decider`, the `noncomputable` `Classical.choice` evaluator that an
  external audit ruled a non-conforming discharge of **UV-003**.  That evaluator
  and every result depending on it are deleted; §2 records the reasoning.

  **UV-003 is open and this repository states no `Universal.GlobalOptimal`
  result at the release scope.**

  ## THE NAME IS HONEST, AND HERE IS WHY IT HAS TO BE

  `Artifact.released_wasm_gemm_gnaf_global_optimal` is **not declared here and is
  not declared anywhere in this repository**.  SPEC §15 forbids that name from
  taking `Coverage`, `LowerBound`, `Correct`, `FaithfulWasm`, `CompilerCorrect`
  or `GlobalOptimal` as parameters, so it cannot be stated as a conditional.  It
  cannot be stated at all right now: with `Release.decider` deleted there is no
  decider at the release scope to index `Universal.GlobalOptimal` by.  A
  conditional theorem wearing the unconditional theorem's name would make every
  downstream citation false, and no amount of surrounding prose would repair
  it.

  ## EVERY HYPOTHESIS THAT REMAINS

  1. `[Foundation.Fintype (Gemm.RawInvocation Release.wasmProfile)]` — SPEC
     §8.4's `problem_input_fintype`.  A global instance exists in
     `Universal/EnumerateInputs.lean`, but the compiled axiom audit reaches
     `Classical.choice`.  Because this is an executable enumeration witness,
     SPEC §4 does not credit it; `UV-004` and the three associated required
     names remain outstanding until that dependency is removed.
  2. `(seam : Release.Seam)` — constructed for the current subset machine.
     `Release.seam` is a closed
     term: `Release.semantics` (`Release.costEvent` plus `Wasm.validationCost`
     and `Wasm.instantiatedStaticBytes`), `Release.machine`
     (`Wasm.releaseCostedMachine`, the real all-branch costed explorer), and
     `Release.limit` (five coordinates pinned by SPEC §8.2, the other eleven at
     the profile maximum the pinned costed-step budget implies).
     `Theorems.release_seam_nondegenerate` proves it is not the fake seam — the
     cost model is not free, validation is not free, no coordinate is budgeted
     at zero, and the machine returns a completed **nonempty** frontier on a
     real module.  Two disclosures travel with it and are stated in §4:
     `Release.costEvent` is a *lower bound* on the SPEC §7.5 contribution law,
     and `Release.witnessModule` is not a GEMM implementation.
  3. **The decider.**  SPEC §10.1's implemented finite decoder, validator, input
     enumerator and all-branch explorer, as a `Universal.Decider`.  It does not
     exist here.  It used to be faked by `Release.decider`; see §2.  **UV-003.**
  4. `hne` — nonemptiness of the admissible, evaluated set.  Still open, and now
     not even statable in the form the deleted theorems used, because that form
     mentioned the decider.  No byte sequence is proved `ProfileValid ∧
     SemanticCorrect ∧ SemanticWithinResources` anywhere in this repository, and
     none is asserted to be.  The former subset-emitted witness and its
     byte-indexed `Universal.SystemEvaluation` have been omitted; the current
     GNAF compiler does not produce a public Core module.
  5. The disclosed profile deviation: `Release.wasmProfile` is
     `Wasm.unitWitnessProfile`, not SPEC §7.2's release literal.  Its cost table
     is `Wasm.canonicalCostTableUnits`; the audit rows exactly cover the local
     legacy `Wasm.RuleId` and `Wasm.InitEventId` enumerations, and their
     contributions agree with this repository's own contribution law
     (`Wasm.canonicalCostTable_charges_exactly`).  Those identifiers are not a
     complete enumeration of the amended Core rule universe, however, and the
     rows are not built from or cross-checked against a vendored Core 3.0
     conformance map.  Thus the former empty-row defect is repaired only for the
     legacy subset machinery; release-wide CO-006 remains open for both complete
     amended-Core coverage and external provenance.

  `Release.decider` no longer exists (§2).  Nothing selects a byte sequence at
  the release scope, so `Artifact.released_bytes_equal_selection` (`O-4`) is not
  merely undischarged — it has no selection to be about.

  Every declaration in this file is a proved theorem.  There is no `sorry`, no
  `admit`, no project axiom, no `native_decide`, no `unsafe`, no `partial`.
-/
import WasmGemmGnaf.Artifact.Release

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

open WasmGemmGnaf

/-! ## 1. The scope the release theorem is about

One conjunction, all `rfl`-or-near-`rfl`, so that "which profile, which problem,
which objective" is checkable in a single place instead of being reassembled
from a dozen files.  The four `ruleRows`/`initializationRows` conjuncts establish
an exact, duplicate-free cover of the local legacy `Wasm.RuleId` and
`Wasm.InitEventId` enumerations, with every such rule resolving to a row.  They
do not establish the complete amended-Core coverage required by SPEC §7.5. -/

/--
  **The release scope, stated in full.**

  Reading, in order: the profile body is the canonical Core 3.0 wasm32 body at
  the pinned revision commit over `Wasm.canonicalCostTableUnits`; the address
  model is 32-bit with the 65536-page limit; the cost table is the *units*
  table, and its audit rows are an exact duplicate-free cover of every local
  legacy `Wasm.RuleId` and every harness initialization event; this is not a
  complete amended-Core rule cover.  Decoding costs one unit per byte plus one
  terminal unit; the problem is
  `Gemm.canonicalWGNGv1ProblemBody` at `workloadRepetitions = 1` with the
  `2 ^ 320` costed step budget; the setting forwards exactly those numbers, adds
  nothing to `Gemm.Reference.Accepts` and narrows nothing in the raw-invocation
  carrier; and the objective is `Cost.canonicalObjectiveBody` — weight one on
  every coordinate, unsigned byte-lexicographic tie order, score the plain
  coordinate sum.
-/
theorem release_scope_identities (seam : Release.Seam) :
    -- the profile (SPEC §7.2), including the disclosed deviation
    Release.wasmProfile.body =
        Wasm.canonicalCore3Wasm32ProfileBody Wasm.core3RevisionCommit
          Wasm.canonicalCostTableUnits ∧
    Release.wasmProfile.body.addressBits = 32 ∧
    Release.wasmProfile.body.maxPages = 65536 ∧
    Release.wasmProfile.costTableBody = Wasm.canonicalCostTableUnits ∧
    Release.wasmProfile.costTableBody.ruleRows.map Wasm.CostRuleRow.ruleId =
        Wasm.RuleId.all.map Wasm.RuleId.name ∧
    (Release.wasmProfile.costTableBody.ruleRows.map
      Wasm.CostRuleRow.ruleId).Nodup ∧
    (∀ r : Wasm.RuleId,
      (Release.wasmProfile.costTableBody.rowFor? r.name).isSome) ∧
    Release.wasmProfile.costTableBody.initializationRows.map
        Wasm.CostRuleRow.ruleId =
      Wasm.InitEventId.all.map Wasm.InitEventId.name ∧
    (∀ bytes : ByteArray,
      Release.wasmProfile.costTableBody.decodeCost bytes = bytes.size + 1) ∧
    -- the problem (SPEC §8.3)
    Release.gemmProblem.body =
        Gemm.canonicalWGNGv1ProblemBody Release.wasmProfile.body
          (workloadRepetitions := 1) ∧
    Release.gemmProblem.workloadRepetitions = 1 ∧
    Release.gemmProblem.maxSteps = 2 ^ 320 ∧
    -- the setting (SPEC §10.1)
    (Release.setting seam).problem = Release.problem seam ∧
    (Release.setting seam).problem.maxSteps = 2 ^ 320 ∧
    (Release.setting seam).problem.workloadRepetitions = 1 ∧
    (Release.setting seam).problem.RawInvocation =
        Gemm.RawInvocation Release.wasmProfile ∧
    (∀ (raw : Gemm.RawInvocation Release.wasmProfile)
        (observation : Wasm.ExecutionObservation),
      (Release.setting seam).problem.Accepts raw observation ↔
        Gemm.Reference.Accepts Release.gemmProblem raw observation) ∧
    -- the objective (SPEC §9.3)
    (Release.costObjective seam).body = Cost.canonicalObjectiveBody ∧
    (∀ co : Cost.ArtifactCoordinate,
      (Release.costObjective seam).body.weight co = 1) ∧
    (Release.costObjective seam).body.tieOrder = .unsignedByteLexicographic ∧
    (∀ c : Cost.CompleteSystemCost,
      (Release.costObjective seam).score c = Cost.CanonicalObjective.score c) :=
  ⟨Release.wasmProfile_body,
   Release.wasmProfile_addressBits,
   Release.wasmProfile_maxPages,
   Release.wasmProfile_costTableBody,
   Release.wasmProfile_ruleRows_exact_cover.1,
   Release.wasmProfile_ruleRows_nodup,
   Release.wasmProfile_covers_every_rule,
   Release.wasmProfile_ruleRows_exact_cover.2,
   Release.wasmProfile_decodeCost,
   Release.gemmProblem_canonical,
   Release.gemmProblem_workloadRepetitions,
   Release.gemmProblem_maxSteps,
   Release.setting_problem seam,
   Release.setting_maxSteps seam,
   Release.setting_workloadRepetitions seam,
   Release.setting_rawInvocation seam,
   Release.setting_accepts seam,
   Release.costObjective_body seam,
   Release.costObjective_weights_one seam,
   Release.costObjective_tieOrder seam,
   Release.costObjective_score seam⟩

/-! ## 2 AND 3. THE RELEASE THEOREM — REMOVED

`Theorems.release_decider_answers_admissible`,
`Theorems.release_globalOptimal_of_nonempty`,
`Theorems.release_globalOptimal_of_admissible`,
`Theorems.release_obligation_reduction`,
`Theorems.release_lower_bound_clause`,
`Theorems.release_tie_break_clause` and
`Theorems.release_competitor_universe_inhabited` stood here, and
`Theorems.release_decider_answers_admissible_at_seam`,
`Theorems.release_globalOptimal_of_nonempty_at_seam` and
`Theorems.release_globalOptimal_of_witness_semantics` stood in §4.

Every one of them was stated against `Release.decider`: a `noncomputable`
one-field wrapper around `Release.evaluateClassically`, which assumed `Nonempty
(Universal.SystemEvaluation …)` and extracted an inhabitant by
`Classical.choice`.  It decoded nothing, validated nothing, enumerated no input
and explored no branch.  An external audit ruled that a non-conforming discharge
of **UV-003**, and SPEC §19 / §6.3 exclude noncomputable definitions from the
release path in the first place.

`Release.decider` and `Release.evaluateClassically` are deleted, so these
results are deleted with them.  They are **absent**, not weakened, not renamed
and not retained behind a checker; and no replacement evaluator over the witness
semantics is offered, because a differently-spelled substitution for the
implemented explorer is the same non-conformance.

**UV-003 is open, and this repository states no `Universal.GlobalOptimal`
result at the release scope.**  Closing it means implementing SPEC §10.1's
finite decoder, validator, input enumerator and all-branch explorer as a
`Universal.Decider (Release.setting Release.seam)` and proving
`Universal.DeciderAnswersAdmissible` of *that*.  The scope identities of §1 and
the subset seam non-degeneracy of §4 are unaffected: neither mentions a
decider. -/

/-! ## 4. The subset seam is constructed

Everything in §2 and §3 takes `(seam : Release.Seam)` as an argument.  Until
`Release.seam` existed, nothing inhabited that type, so every one of those
statements was an implication whose *type-level* antecedent might have been
unsatisfiable.

`Artifact/Release.lean` §5 now builds one:

* `Release.semantics` — `Release.costEvent` (the pinned per-rule row that each
  plain event determines on its own), `Wasm.validationCost`,
  `Wasm.instantiatedStaticBytes`;
* `Release.machine` — `Wasm.releaseCostedMachine`, the real all-branch costed
  explorer of `Wasm/CostedExplore.lean`;
* `Release.limit` — five coordinates pinned verbatim by
  `Gemm.releaseResourceContract`, eleven supplied at the profile maximum the
  pinned costed-step budget implies (`Release.limit_pinned`,
  `Release.limit_unpinned` say which are which).

The statements below are about that constructed seam.  **Two disclosures travel
with them.**  `Release.costEvent` is a *lower bound* on SPEC §7.5's contribution
law, not the law: a plain `Wasm.Event` does not carry the transferred byte
count, the grow delta or the installed byte count, so
`Release.costEvent_le_eventContribution` is an inequality and not an equation.
And `Release.witnessModule` — the module on which the machine is proved to
complete — is the smallest module `GNAF.moduleOf` emits, whose `gemm` returns
the constant `0`; it is **not** `Artifact.baselineModule` and it computes no
product.  See `Artifact/Release.lean` §5.9 for why the compiled GEMM witness
cannot be discharged here. -/

/--
  **Non-degeneracy of the constructed seam.**

  Five facts, in one conjunction: some event's charge is not the zero vector
  (and is exactly the pinned dispatch row); *every* event is charged at least
  one rule step; every module costs at least one validation step; every one of
  the sixteen resource coordinates has a positive budget; and on
  `Release.witnessModule` the costed machine both initializes and returns a
  completed, nonempty, canonically ordered frontier — at *every* raw invocation.

  The last conjunct rules out a `Seam` whose machine answers
  `.initializationFailure` unconditionally.  It does not construct a
  byte-indexed `Universal.SystemEvaluation`; that additionally needs the omitted
  compiler-to-public-Core emission path.
-/
theorem release_seam_nondegenerate :
    (∃ e : Wasm.Event,
        (Release.seam.semantics.costEvent e).charge ≠ Cost.DynamicVector.zero ∧
        (Release.seam.semantics.costEvent e).charge =
          Wasm.dispatchCharge Release.wasmProfile.costTableBody) ∧
    (∀ e : Wasm.Event,
      0 < (Release.seam.semantics.costEvent e).charge.wasmRuleSteps) ∧
    (∀ m : Wasm.Subset.Module, 0 < Release.seam.semantics.validationSteps m) ∧
    (∀ dc : Cost.DynamicCoordinate, 0 < dc.value Release.seam.limit) ∧
    (∀ raw : Gemm.RawInvocation Release.wasmProfile,
      Release.seam.machine.initialGemmInvocationCosted Release.witnessModule
          (Universal.toWasmInvocation raw) =
        .ok { initial := Release.witnessInitial raw
              cost := Wasm.initializationCost Release.wasmProfile
                        Release.witnessModule } ∧
      ∃ (frontier : Foundation.NonemptyCanonicalFrontier
            (Universal.CostedExecutionObservation Release.semantics
              (Release.witnessInitial raw)))
        (coverage : Universal.CostedCoverage Release.semantics
            (Release.setting Release.seam).problem.maxSteps
            (Release.witnessInitial raw) frontier),
        Release.seam.machine.exploreAllCosted
            (Release.setting Release.seam).problem.maxSteps
            (Release.witnessInitial raw) = .complete frontier coverage) :=
  ⟨Release.seam_costEvent_not_zero, Release.seam_costEvent_charge_pos,
   Release.seam_validationSteps_pos, Release.limit_pos,
   Release.seam_machine_completes⟩

end WasmGemmGnaf.Theorems
