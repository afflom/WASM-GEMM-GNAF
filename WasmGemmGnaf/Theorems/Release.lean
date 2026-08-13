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
  | `Theorems.release_seam_nondegenerate` | **GO-008**: the constructed `Release.seam` charges every event, charges every validation, budgets every coordinate, and its machine completes with a nonempty frontier |
  | `Theorems.release_systemEvaluation_inhabited` | **GO-008's headline**: `Universal.SystemEvaluation` at the constructed setting is inhabited on a `ProfileValid` closed literal |

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
     §8.4's `problem_input_fintype`.  This is now **discharged**, globally and
     constructively, by `Gemm.raw_input_finite` in
     `Universal/EnumerateInputs.lean`; §4's section header still binds it
     because the statements there were written before the instance existed, and
     it is satisfied rather than assumed.
  2. `(seam : Release.Seam)` — **CLOSED (GO-008)**.  `Release.seam` is a closed
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
     none is asserted to be.  Two of the four conjuncts are theorems on one
     closed literal, `Release.witnessBytes`: `Release.witness_profileValid`
     (profile validity) and `Theorems.release_systemEvaluation_inhabited` (the
     `Universal.SystemEvaluation` inhabitant).  `Universal.SemanticWithinResources`
     is unproved for it and `Universal.SemanticCorrect` is **false** for it — the
     witness module's `gemm` returns the constant `0`.  `Artifact/Baseline.lean`
     proves profile validity for the compiled GEMM witness
     (`Artifact.baseline_profileValid`); its `SemanticCorrect` is
     `GNAF.compile_refines`, omitted under `BI-002`/`O-6`.
  5. The disclosed profile deviation: `Release.wasmProfile` is
     `Wasm.unitWitnessProfile`, not SPEC §7.2's release literal — the cost table
     is `Wasm.canonicalCostTableUnits`, whose eight units, canonical GC widths
     and audit rows are the canonical release values, but which is *not* built
     by `Wasm.buildCanonicalCostTable` from a vendored Core 3.0 conformance map,
     because neither that function nor that map exists here.  What CO-006
     reported — empty `ruleRows` and `initializationRows`, so that `rowFor?`
     returned `none` for every rule — is closed: the rows are now an exact,
     duplicate-free cover of `Wasm.RuleId` and `Wasm.InitEventId`, and
     `release_scope_identities` asserts that cover rather than asserting
     emptiness.  What remains open is only the *provenance* of the row
     contributions: they are proved equal to this repository's own contribution
     law (`Wasm.canonicalCostTable_charges_exactly`), not cross-checked against
     an external conformance map.

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
from a dozen files.  The four `ruleRows`/`initializationRows` conjuncts are the
machine-checked cost-profile statement SPEC §7.5 requires of
`buildCanonicalCostTable`'s argument — an exact, duplicate-free cover, with
every rule resolving to a row; they are part of the scope statement, not a
footnote to it. -/

/--
  **The release scope, stated in full.**

  Reading, in order: the profile body is the canonical Core 3.0 wasm32 body at
  the pinned revision commit over `Wasm.canonicalCostTableUnits`; the address
  model is 32-bit with the 65536-page limit; the cost table is the *units*
  table, and its audit rows are an exact duplicate-free cover of every pinned
  Core rule identifier and every harness initialization event; decoding costs
  one unit per byte plus one terminal unit; the problem is
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
`Universal.DeciderAnswersAdmissible` of *that*.  The scope identities of §1, the
seam non-degeneracy of §4 and the evaluation inhabitant of §4 are unaffected:
none of them mentions a decider. -/

/-! ## 4. The seam is constructed (GO-008)

Everything in §2 and §3 takes `(seam : Release.Seam)` as an argument.  Until
`Release.seam` existed, nothing inhabited that type, so every one of those
statements was an implication whose *type-level* antecedent might have been
unsatisfiable — and the nonemptiness antecedent `hne` was worse than open, it
was not even known to be satisfiable at any seam.

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

  The last conjunct is the one that matters: a `Seam` whose machine answered
  `.initializationFailure` unconditionally would typecheck and would leave
  `Universal.SystemEvaluation` uninhabited, which is exactly the degenerate
  inhabitant this theorem rules out.
-/
theorem release_seam_nondegenerate :
    (∃ e : Wasm.Event,
        (Release.seam.semantics.costEvent e).charge ≠ Cost.DynamicVector.zero ∧
        (Release.seam.semantics.costEvent e).charge =
          Wasm.dispatchCharge Release.wasmProfile.costTableBody) ∧
    (∀ e : Wasm.Event,
      0 < (Release.seam.semantics.costEvent e).charge.wasmRuleSteps) ∧
    (∀ m : Wasm.Module, 0 < Release.seam.semantics.validationSteps m) ∧
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

section AtSeam

variable [Foundation.Fintype (Gemm.RawInvocation Release.wasmProfile)]

/--
  **GO-008's headline, at top level.**

  `Universal.SystemEvaluation` at the *constructed* release setting is
  inhabited, on a closed byte literal that is also `Universal.ProfileValid`.

  This is what defeats vacuity.  It does **not** say the literal is
  `Universal.Admissible`: `Universal.SemanticCorrect` demands
  `Gemm.Reference.Accepts` at every raw invocation, which is false for a module
  whose `gemm` returns `0`, and is not claimed.  Two of the four conjuncts of
  the release antecedent are now theorems on one literal; two are not.
-/
theorem release_systemEvaluation_inhabited :
    ∃ bytes : ByteArray,
      Universal.ProfileValid Release.wasmProfile bytes ∧
      Nonempty (Universal.SystemEvaluation (Release.setting Release.seam) bytes) :=
  ⟨Release.witnessBytes, Release.witness_profileValid,
    ⟨Release.witnessSystemEvaluation⟩⟩

end AtSeam

end WasmGemmGnaf.Theorems
