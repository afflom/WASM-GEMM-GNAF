import WasmGemmGnaf.Atlas.Attention
import WasmGemmGnaf.Atlas.Rebuild
import WasmGemmGnaf.Universal.Partition
import WasmGemmGnaf.Artifact.Release

set_option autoImplicit false

/-!
# Atlas: optimum-relevant attention coverage (SPEC §12.2)

SPEC §12.2 requires

```lean
theorem attention_no_optimum_relevant_false_negative
    {profile : Wasm.Profile}
    {problem : Gemm.Problem profile}
    {objective : Cost.ProperObjective profile problem}
    {state : Atlas.UnsealedState}
    {core : Atlas.SealCore}
    {candidateBytes : ByteArray}
    {evaluation : Universal.SystemEvaluation profile problem candidateBytes}
    (hsealed : Atlas.SealCertificate state core)
    (hprofile : Wasm.ProfileId profile = core.profileId)
    (hproblem : Gemm.ProblemId problem = core.problemId)
    (hobjective : Cost.ObjectiveId objective = core.objectiveId)
    (hc : Universal.ProfileValid profile candidateBytes)
    (heval : Universal.SystemEvaluationRel profile problem candidateBytes evaluation)
    (hscore : objective.score evaluation.cost ≤ core.baselineScore) :
  Atlas.AttentionContains core candidateBytes ∨
  Atlas.HasSoundExclusionCertificate core candidateBytes evaluation
```

`Atlas.AttentionContains` and `Atlas.HasSoundExclusionCertificate` are used there
and defined nowhere in SPEC.  Both are defined below, but the refutation does not
rest on those definitions — see "Why it is false".

**That statement is false, and this file proves it false.**  The required name is
therefore *absent* from this repository; `DEV-005` in `model/spec-deviations.json`
records the refutation, and the intended content is proved here under the
different name `Atlas.attention_no_declared_optimum_relevant_false_negative`.

## Why it is false

`Atlas.SealCertificate` is the conjunction of seven *deterministic checkers*
(`Atlas/Certificate.lean`), each a `Bool` function of the recorded state and the
recorded core.  Not one of them mentions a byte string, a decoder, a semantics or
a cost.  In particular `Atlas.attentionCompleteCheck` asks only that every object
the state *records* is routed by some indexed signature; it is satisfied — with
every root empty — by a state that has recorded nothing at all.

SPEC's statement, on the other hand, quantifies over **every** `candidateBytes`
whose evaluated score is within the core's baseline.  Nothing links the two.  So
seal an Atlas that declared nothing, hand it a candidate that really is
profile-valid, really has a `Universal.SystemEvaluation`, and really scores at
the baseline, and the disjunction has no way to hold: the attention root lists no
signature and the certificate root lists no certificate.

`Atlas.attention_no_optimum_relevant_false_negative_is_false` proves exactly
that, and it does so **parametrically in the two predicates SPEC leaves
undefined**.  It assumes only

* an attention record that indexes *no* signature contains no candidate, and
* a certificate store that stores *no* certificate identity supplies no
  *retained* exclusion certificate (SPEC §12.2: an omission "is legal only when a
  **retained** proof shows …"),

so no choice of `Atlas.AttentionContains` / `Atlas.HasSoundExclusionCertificate`
satisfying those two minimal honesty conditions can make SPEC's statement true.
The refutation cannot be an artefact of definitions chosen to make it easy.

## The two vacuity traps, and how they are guarded

**Trap 1 — a vacuous relevance predicate.**  `Atlas.OptimumRelevant` is SPEC's own
hypothesis conjunction, made into a definition: profile validity, the three scope
bindings, and the existence of an *evaluated* system evaluation whose objective
score is within the core's baseline.  It is proved inhabited by a concrete
witness — `Atlas.witness_optimumRelevant`, at `Release.witnessBytes`, whose
`Universal.ProfileValid` is `Release.witness_profileValid` and whose
`Universal.SystemEvaluation` is `Release.witnessSystemEvaluation`, both of them
theorems of `Artifact/Release.lean` and neither of them assumed here.  The
positive theorem therefore fires on a real candidate, and
`Atlas.declared_witness_is_routed` exhibits the index actually returning it.

**Trap 2 — defining relevance through the index.**  `OptimumRelevant` mentions no
attention index, no `attend`, no signature and no `AttentionContains`; it is a
function of the objective, the candidate bytes and the decider alone.  Conversely
`Atlas.AttentionContains` is defined from the *core's recorded signature list*
and the candidate's own canonical applicability signature (`Atlas.attentionEntryOf`
already fixes that signature to be the declaration's own bytes), so the link
between "the state indexes it" and "`attend` returns it" is a theorem
(`Atlas.attentionRoutes_of_indexesCandidate`,
`Atlas.attentionContains_of_attentionRoutes`) and not a definition.  Neither
direction is `rfl`.

## What is proved here

| name | content |
|---|---|
| `Atlas.NoOptimumRelevantFalseNegative` | SPEC §12.2's statement, written out, parameterised by the two predicates SPEC does not define |
| `Atlas.attention_no_optimum_relevant_false_negative_is_false` | **it is FALSE**, for every pair of predicates meeting two minimal honesty conditions |
| `Atlas.honesty_conditions_satisfiable` | those two conditions are satisfiable, so the line above is not a vacuous conditional |
| `Atlas.attention_no_optimum_relevant_false_negative_is_false_for_listed_grounds` | false again with the retention requirement dropped, under SPEC's three listed exclusion grounds |
| `Atlas.attention_no_optimum_relevant_false_negative_is_false_at_every_evaluator` | false at *every* evaluator that evaluates the witness bytes, not only at the one this file builds |
| `Atlas.undeclared_witness_is_missed` | the witness: an optimum-relevant candidate, a sealed core, an empty attention root, an empty certificate root |
| `Atlas.no_listed_exclusion_ground_for_witness` | and none of SPEC's three exclusion grounds holds of it |
| `Atlas.blind_attend_empty` | the miss is at the level of `attend` itself: the blind Atlas routes nothing, at any request |
| `Atlas.attention_no_declared_optimum_relevant_false_negative` | the intended content: a *declared* optimum-relevant candidate is never a false negative |
| `Atlas.declared_witness_is_routed` | non-vacuity: the same real candidate, declared, is routed by `attend` and contained in the sealed core |
| `Atlas.attentionRoutes_of_indexesCandidate` | the routing mechanism itself drops nothing it indexes |
| `Atlas.attentionContains_of_attentionRoutes` | and a sealed core records the signature of everything `attend` returns |
| `Atlas.sealCertificateAt` | a rebuilt state seals at *every* baseline score; no checker reads `baselineScore` |

## The residual obligation, named

The intended theorem adds two hypotheses and no others: that the state is
`Atlas.Coherent`, and that the candidate is in its declaration base.  The second
is the gap, and it is precisely SPEC §10.5's universal coverage obligation stated
at the Atlas boundary: nothing in this repository proves that every profile-valid
byte string reaches the declaration base.
`Atlas.attention_no_optimum_relevant_false_negative_is_false` is the
machine-checked statement that the seal does **not** discharge it.

## A note on the import direction

This module imports `WasmGemmGnaf.Artifact.Release`, which is one SPEC §5 layer
above `Atlas`.  It does so only to reach the *witness data* — a byte literal, a
profile-validity theorem and a `Universal.SystemEvaluation` — that no lower layer
constructs.  Nothing here is imported *back* into the Atlas proper: no other
Atlas module depends on this one, and the SPEC §10.1 firewall (which protects
`Foundation`, `Wasm`, `Gemm`, `Cost` and the extensional `Universal` definitions
from the artifact) is untouched.
-/

namespace WasmGemmGnaf.Atlas

open WasmGemmGnaf.Foundation

/-! ## 1. What "attention contains the candidate" means

`Atlas.attentionEntryOf` (`Atlas/Delta.lean`) already fixes the canonical
applicability signature of a declaration: "its own bytes are its applicability
signature".  These three definitions read that convention back off, so a
candidate's signature and identity are functions of its bytes and of nothing
else. -/

/-- The canonical applicability signature of a candidate: its own bytes, exactly
as `Atlas.attentionEntryOf` indexes them. -/
def candidateSignature (candidateBytes : ByteArray) : ByteArray := candidateBytes

/-- The canonical semantic identity of a candidate, exactly as
`Atlas.objectEntryOf` records it. -/
def candidateObjectId (candidateBytes : ByteArray) : CanonicalObjectId :=
  declId candidateBytes

/-- The request that demands exactly the candidate's applicability signature. -/
def candidateRequest (candidateBytes : ByteArray) : RequestSignature :=
  ⟨[candidateSignature candidateBytes]⟩

/--
**SPEC §12.2**, `Atlas.AttentionContains`.

A `SealCore` carries the attention index only through `attentionRoot`, which SPEC
§12.1 fixes as "the exact list of indexed request signatures".  So what a *core*
can say about a candidate is that the signature under which the candidate would
be indexed is one of the signatures the seal commits to.

This is deliberately the *weak* reading: the strictly stronger `attend`-level
reading implies it on any sealed state
(`Atlas.attentionContains_of_attentionRoutes`).  The refutation of §6 does not
depend on this definition at all — it is parametric in the predicate — so this
definition is used only to state the positive result of §7 and to witness that
the refutation's honesty condition is satisfiable.
-/
def AttentionContains (core : SealCore) (candidateBytes : ByteArray) : Prop :=
  candidateSignature candidateBytes ∈ core.attentionRoot.signatures

/-- The strong, state-level reading: `attend` really returns the candidate's
identity on the request that demands the candidate's signature. -/
def AttentionRoutes (s : StateBody) (candidateBytes : ByteArray) : Prop :=
  CanonicalSet.Mem (attend s (candidateRequest candidateBytes))
    (candidateObjectId candidateBytes)

/-- The state indexes the candidate: some entry carries the candidate's own
applicability signature and routes the candidate's own identity. -/
def IndexesCandidate (s : StateBody) (candidateBytes : ByteArray) : Prop :=
  ∃ e ∈ s.attentionIndex.entries,
    e.signature = candidateSignature candidateBytes ∧
    candidateObjectId candidateBytes ∈ e.targets

/-- **The routing mechanism drops nothing it indexes.**  Not `rfl`: it goes
through `attend`'s filter, its `flatMap` and its duplicate removal. -/
theorem attentionRoutes_of_indexesCandidate {s : StateBody} {candidateBytes : ByteArray}
    (h : IndexesCandidate s candidateBytes) : AttentionRoutes s candidateBytes := by
  obtain ⟨e, he, hsig, ht⟩ := h
  refine (attend_mem_iff s (candidateRequest candidateBytes)
    (candidateObjectId candidateBytes)).mpr ⟨e, he, ?_, ht⟩
  refine (RequestSignature.applies_iff _ _).mpr ?_
  rw [hsig]
  exact List.mem_cons_self

/-- A sealed core's attention root lists exactly the signatures of the state's
index entries.  Extracted from the deterministic checker, not assumed. -/
theorem attentionCoverage_signatures {state : UnsealedState} {core : SealCore}
    (h : VerifiesAttentionCoverage state core) :
    core.attentionRoot.signatures =
      state.body.attentionIndex.entries.map (·.signature) := by
  simp only [VerifiesAttentionCoverage, attentionCompleteCheck, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rw [h.1.1.1]
  exact h.1.1.2

/-- **A sealed core records the signature of everything `attend` returns.**  The
strong reading implies the weak one, so a refutation of the weak one refutes
every reading in between. -/
theorem attentionContains_of_attentionRoutes {state : UnsealedState} {core : SealCore}
    (hseal : VerifiesAttentionCoverage state core) {candidateBytes : ByteArray}
    (h : AttentionRoutes state.body candidateBytes) :
    AttentionContains core candidateBytes := by
  obtain ⟨e, he, happ, _⟩ :=
    (attend_mem_iff state.body (candidateRequest candidateBytes)
      (candidateObjectId candidateBytes)).mp h
  have hsig : e.signature = candidateSignature candidateBytes := by
    have hmem := (RequestSignature.applies_iff _ _).mp happ
    simpa [candidateRequest] using hmem
  rw [AttentionContains, attentionCoverage_signatures hseal, ← hsig]
  exact List.mem_map_of_mem he

/-! ## 2. Optimum relevance, defined from the objective and nothing else

SPEC's hypothesis conjunction, as a definition.  It mentions no attention index,
no `attend`, no signature and no seal check — only profile validity, the three
scope bindings the theorem requires, and an *evaluated* system evaluation whose
score is within the core's recorded baseline. -/

/--
**Optimum relevance** (SPEC §12.2's hypotheses, named).

`candidateBytes` is optimum-relevant to `core` when it is profile valid, the core
commits to this profile, problem and objective, and the decider answers with a
system evaluation whose objective score does not exceed the core's baseline —
i.e. exactly the candidates SPEC §12.2 forbids attention to miss.
-/
def OptimumRelevant {P : Wasm.Profile} {S : Universal.Setting P}
    (D : Universal.Decider S) (problem : Gemm.Problem P)
    (objective : Cost.ProperObjective P S.problem)
    (core : SealCore) (candidateBytes : ByteArray) : Prop :=
  Universal.ProfileValid P candidateBytes ∧
  Wasm.ProfileId P = core.profileId ∧
  Gemm.ProblemId problem = core.problemId ∧
  Cost.ObjectiveId objective = core.objectiveId ∧
  ∃ evaluation : Universal.SystemEvaluation S candidateBytes,
    Universal.SystemEvaluationRel S D candidateBytes evaluation ∧
    objective.score evaluation.cost ≤ core.baselineScore

/-! ## 3. Sealed states at an arbitrary baseline score

`Atlas/Rebuild.lean` seals a rebuilt state at `baselineScore = 0`.  None of the
seven checkers reads `baselineScore`, so the same state seals at *any* baseline —
which is what lets a counterexample choose the baseline the candidate attains. -/

/-- The rebuilt core, at an arbitrary baseline score. -/
def coreAt (scope : Scope) (decls : CanonicalDeclarationSet) (baseline : Nat) : SealCore :=
  { derivedCore scope decls with baselineScore := baseline }

@[simp] theorem coreAt_attentionRoot (scope : Scope) (decls : CanonicalDeclarationSet)
    (baseline : Nat) :
    (coreAt scope decls baseline).attentionRoot = ⟨decls.declarations⟩ := rfl

@[simp] theorem coreAt_certificateRoot (scope : Scope) (decls : CanonicalDeclarationSet)
    (baseline : Nat) :
    (coreAt scope decls baseline).certificateRoot = ⟨[]⟩ := rfl

@[simp] theorem coreAt_baselineScore (scope : Scope) (decls : CanonicalDeclarationSet)
    (baseline : Nat) : (coreAt scope decls baseline).baselineScore = baseline := rfl

/-- **A rebuilt state seals at every baseline score.**  Every field is discharged
by a proved checker result of `Atlas/Rebuild.lean`; none is assumed. -/
def sealCertificateAt (scope : Scope) (decls : CanonicalDeclarationSet) (baseline : Nat) :
    SealCertificate (derivedState scope decls) (coreAt scope decls baseline) where
  body := canonicalSealCertificateBody (derivedState scope decls) (coreAt scope decls baseline)
  bodyValid := verifies_canonicalSealCertificateBody _ _ rfl
  coreBindsState := ⟨rfl, rfl, rfl, rfl⟩
  closureLeast := derivedState_closureLeastCheck scope decls
  attentionComplete := derivedState_attentionCompleteCheck scope decls
  dependenciesComplete := derivedState_dependenciesCompleteCheck scope decls
  universalCoverComplete := derivedState_universalCoverCompleteCheck scope decls
  envelopeExact := derivedState_envelopeExactCheck scope decls
  certificatesSound := derivedState_certificatesSoundCheck scope decls
  retentionComplete := derivedState_retentionCompleteCheck scope decls

/-! ## 4. A real optimum-relevant candidate

`Release.witnessBytes` is a closed byte literal; `Release.witness_profileValid`
and `Release.witnessSystemEvaluation` are theorems of `Artifact/Release.lean`.
The only thing constructed here is a decider that answers with that evaluation,
which is what `Universal.SystemEvaluationRel` needs and what SPEC §10.1's
`Universal.evaluate` would supply. -/

/-- A decider at the constructed release setting that answers `.complete` with
the *already proved* witness evaluation.  It decides nothing else; it exists so
that `Universal.SystemEvaluationRel` — which is a statement about an evaluator —
has an evaluator to be about.  The evaluation it returns is
`Release.witnessSystemEvaluation`, every field of which is a theorem. -/
def witnessDecider : Universal.Decider (Release.setting Release.seam) where
  evaluate bytes :=
    if h : bytes = Release.witnessBytes then
      Eq.mpr
        (congrArg (Universal.EvaluationResult (Release.setting Release.seam)) h)
        (Universal.EvaluationResult.complete Release.witnessSystemEvaluation)
    else
      Universal.EvaluationResult.profileFailure ⟨declId ByteArray.empty, 0, []⟩

theorem witnessDecider_evaluates :
    Universal.SystemEvaluationRel (Release.setting Release.seam) witnessDecider
      Release.witnessBytes Release.witnessSystemEvaluation :=
  dif_pos rfl

/-- The release scope, as an `Atlas.Scope`: the three canonical identities the
seal core must commit to. -/
def releaseScope : Scope where
  objectiveId := Cost.ObjectiveId (Release.costObjective Release.seam)
  profileId := Wasm.ProfileId Release.wasmProfile
  problemId := Gemm.ProblemId Release.gemmProblem

/-- The witness candidate's exact objective score. -/
def witnessScore : Nat :=
  (Release.costObjective Release.seam).score Release.witnessSystemEvaluation.cost

/-- An Atlas that declared nothing. -/
def blindDecls : CanonicalDeclarationSet := ⟨[]⟩

/-- An Atlas that declared exactly the witness candidate. -/
def declaredDecls : CanonicalDeclarationSet := ⟨[Release.witnessBytes]⟩

/-- **The relevance predicate is inhabited.**  At the release scope, and at a
baseline the candidate attains, `Release.witnessBytes` is optimum-relevant to the
sealed core — for *every* declaration base, so the blind Atlas of §6 and the
declaring Atlas of §7 face the same real candidate. -/
theorem witness_optimumRelevant (decls : CanonicalDeclarationSet) :
    OptimumRelevant witnessDecider Release.gemmProblem
      (Release.costObjective Release.seam) (coreAt releaseScope decls witnessScore)
      Release.witnessBytes :=
  ⟨Release.witness_profileValid, rfl, rfl, rfl,
    Release.witnessSystemEvaluation, witnessDecider_evaluates, Nat.le_refl _⟩

/-! ## 5. Sound exclusion, in SPEC's own three grounds

SPEC §12.2: "an omitted candidate or partition is legal only when a **retained**
proof shows that it is empty, cannot beat the current bound, or is exactly
reconstructible elsewhere."  Those are three grounds and a retention requirement.
Both are transcribed here.

These definitions exist for two reasons.  First, they show the honesty conditions
of §6 are *satisfiable*, so the parametric refutation is not a conditional with
unsatisfiable antecedents.  Second, they let §6 record the stronger fact that
none of SPEC's three listed grounds holds of the counterexample candidate even
before the retention requirement is applied. -/

/-- SPEC §12.2's three legal grounds for omitting a candidate. -/
inductive ExclusionGround
  /-- The candidate denotes nothing. -/
  | empty
  /-- Its exact score cannot reach the core's recorded baseline. -/
  | cannotBeatBound
  /-- An attended candidate reconstructs it exactly. -/
  | reconstructibleElsewhere
  deriving DecidableEq

/--
**Soundness of an exclusion ground**: what would have to be *true* for the
corresponding omission to be legal.  Each clause is the semantic content of one
of SPEC's three grounds, taken at the objective the core commits to.

Note what is *not* here: inadmissibility.  SPEC §12.2 lists three grounds and
this transcribes those three.  A reader who takes "it is empty" to also cover a
profile-valid candidate that fails `Universal.SemanticCorrect` is reading a
fourth ground into the sentence; under that reading
`Atlas.no_listed_exclusion_ground_for_witness` and
`Atlas.attention_no_optimum_relevant_false_negative_is_false_for_listed_grounds`
do not apply.  `Atlas.attention_no_optimum_relevant_false_negative_is_false` is
unaffected by the question: the counterexample seal retains no certificate of any
kind, so no *retained* proof of any ground — listed or not — exists in it.
-/
def SoundExclusion {P : Wasm.Profile} {S : Universal.Setting P} (core : SealCore)
    (candidateBytes : ByteArray)
    (evaluation : Universal.SystemEvaluation S candidateBytes) :
    ExclusionGround → Prop
  | .empty => ¬ Universal.ProfileValid P candidateBytes
  | .cannotBeatBound => ∀ objective : Cost.ProperObjective P S.problem,
      Cost.ObjectiveId objective = core.objectiveId →
        core.baselineScore < objective.score evaluation.cost
  | .reconstructibleElsewhere => ∃ other : ByteArray, other ≠ candidateBytes ∧
      AttentionContains core other ∧
      ∃ e : Universal.SystemEvaluation S other,
        e.module = evaluation.module ∧ e.cost = evaluation.cost

/--
**SPEC §12.2**, `Atlas.HasSoundExclusionCertificate`.

The candidate's exclusion certificate is retained by the seal — its subject
identity is one of the identities the certificate root commits to — and the
ground it rests on is sound.  This is the *permissive* reading: it asks only that
the store retain something identified by the candidate, not that the store's
entry be inspected, so any stricter definition implies it.
-/
def HasSoundExclusionCertificate {P : Wasm.Profile} {S : Universal.Setting P}
    (core : SealCore) (candidateBytes : ByteArray)
    (evaluation : Universal.SystemEvaluation S candidateBytes) : Prop :=
  candidateObjectId candidateBytes ∈ core.certificateRoot.certificateIds ∧
    ∃ ground : ExclusionGround, SoundExclusion core candidateBytes evaluation ground

/-- An attention record that indexes no signature contains no candidate. -/
theorem not_attentionContains_of_no_signature {core : SealCore} {candidateBytes : ByteArray}
    (h : core.attentionRoot.signatures = []) : ¬ AttentionContains core candidateBytes := by
  rw [AttentionContains, h]
  simp

/-- A certificate store that retains no certificate identity supplies no
retained exclusion certificate. -/
theorem not_hasSoundExclusionCertificate_of_no_certificate {P : Wasm.Profile}
    {S : Universal.Setting P} {core : SealCore} {candidateBytes : ByteArray}
    {evaluation : Universal.SystemEvaluation S candidateBytes}
    (h : core.certificateRoot.certificateIds = []) :
    ¬ HasSoundExclusionCertificate core candidateBytes evaluation := by
  rintro ⟨hmem, -⟩
  rw [h] at hmem
  simp at hmem

/--
**Not one of SPEC's three listed grounds holds of the counterexample candidate.**

* `empty` — the candidate is profile valid (`Release.witness_profileValid`).
* `cannotBeatBound` — its score *is* the core's baseline, so it ties the bound
  rather than exceeding it; this is the hardest case for an index to be allowed
  to drop.
* `reconstructibleElsewhere` — the core attends nothing, so nothing reconstructs
  it.

See `Atlas.SoundExclusion` for the disclosure about a fourth, unlisted ground.
-/
theorem no_listed_exclusion_ground_for_witness (ground : ExclusionGround) :
    ¬ SoundExclusion (coreAt releaseScope blindDecls witnessScore) Release.witnessBytes
        Release.witnessSystemEvaluation ground := by
  cases ground with
  | empty => exact fun h => h Release.witness_profileValid
  | cannotBeatBound =>
      intro h
      exact Nat.lt_irrefl _ (h (Release.costObjective Release.seam) rfl)
  | reconstructibleElsewhere =>
      rintro ⟨_other, -, hcontains, -⟩
      exact not_attentionContains_of_no_signature rfl hcontains

/-! ## 6. SPEC §12.2's statement is false -/

/--
**SPEC §12.2's `attention_no_optimum_relevant_false_negative`**, written out in
the repository's spelling and parameterised by the two predicates SPEC names but
does not define.

Two spellings differ from SPEC's display, both already disclosed for the
`Universal` family in `Conformance/RequiredSignatures.lean`: SPEC's
`profile, problem` pair is bundled as `S : Universal.Setting P`, so
`Universal.SystemEvaluation profile problem bytes` is written
`Universal.SystemEvaluation S bytes`; and `Universal.SystemEvaluationRel` carries
its evaluator `D` explicitly.  Both are *universally* quantified here, so this
proposition is the stronger one — it would have to hold at every setting and
every evaluator.
-/
def NoOptimumRelevantFalseNegative
    (Contains : SealCore → ByteArray → Prop)
    (Excluded : (P : Wasm.Profile) → (S : Universal.Setting P) → SealCore →
      (bytes : ByteArray) → Universal.SystemEvaluation S bytes → Prop) : Prop :=
  ∀ (P : Wasm.Profile) (S : Universal.Setting P) (D : Universal.Decider S)
    (problem : Gemm.Problem P) (objective : Cost.ProperObjective P S.problem)
    (state : UnsealedState) (core : SealCore) (candidateBytes : ByteArray)
    (evaluation : Universal.SystemEvaluation S candidateBytes),
    SealCertificate state core →
    Wasm.ProfileId P = core.profileId →
    Gemm.ProblemId problem = core.problemId →
    Cost.ObjectiveId objective = core.objectiveId →
    Universal.ProfileValid P candidateBytes →
    Universal.SystemEvaluationRel S D candidateBytes evaluation →
    objective.score evaluation.cost ≤ core.baselineScore →
    Contains core candidateBytes ∨ Excluded P S core candidateBytes evaluation

/--
**The witness for the refutation.**

A sealed Atlas that declared nothing, at the release scope, at the baseline the
witness candidate attains:

* the candidate is optimum-relevant to the core — profile valid, evaluated, and
  at the baseline;
* the core's attention root indexes **no** signature;
* the core's certificate root stores **no** certificate identity.

The seal is not weakened to arrange this: `Atlas.sealCertificateAt` discharges
all seven deterministic checkers.
-/
theorem undeclared_witness_is_missed :
    OptimumRelevant witnessDecider Release.gemmProblem
        (Release.costObjective Release.seam)
        (coreAt releaseScope blindDecls witnessScore) Release.witnessBytes ∧
      (coreAt releaseScope blindDecls witnessScore).attentionRoot.signatures = [] ∧
      (coreAt releaseScope blindDecls witnessScore).certificateRoot.certificateIds = [] ∧
      ¬ AttentionContains (coreAt releaseScope blindDecls witnessScore)
          Release.witnessBytes :=
  ⟨witness_optimumRelevant blindDecls, rfl, rfl, by
    simp [AttentionContains, coreAt, derivedCore, blindDecls]⟩

/-- **The blind Atlas routes nothing, at any request.**  The miss is at the level
of `attend` itself and not only at the level of the core's recorded root: the
index has no entry, so no request routes anything. -/
theorem blind_attend_empty (request : RequestSignature) (x : CanonicalObjectId) :
    ¬ CanonicalSet.Mem (attend (derivedState releaseScope blindDecls).body request) x := by
  intro hx
  obtain ⟨e, he, -, -⟩ :=
    (attend_mem_iff (derivedState releaseScope blindDecls).body request x).mp hx
  simp [derivedState, unsealedFromBody, semanticRebuildBodyWith, derivedBody,
    blindDecls] at he

/-- In particular the blind Atlas does not route the optimum-relevant witness. -/
theorem blind_not_attentionRoutes_witness :
    ¬ AttentionRoutes (derivedState releaseScope blindDecls).body Release.witnessBytes :=
  blind_attend_empty _ _

/--
**SPEC §12.2's `attention_no_optimum_relevant_false_negative` is FALSE.**

Stated parametrically in the two predicates SPEC leaves undefined, under the two
minimal honesty conditions any definition of them must satisfy:

* `hContains` — an attention record that indexes no signature at all contains no
  candidate.  `Atlas.AttentionRoot` is, by SPEC §12.1, "the exact list of indexed
  request signatures"; a definition violating this would report a candidate as
  attended by an index that names nothing.
* `hExcluded` — a certificate store that stores no certificate identity supplies
  no *retained* exclusion certificate.  SPEC §12.2: an omitted candidate "is
  legal only when a **retained** proof shows that it is empty, cannot beat the
  current bound, or is exactly reconstructible elsewhere."

No pair of predicates satisfying those two conditions makes SPEC's statement
true.  The refutation is therefore not an artefact of definitions chosen to make
it easy, and it cannot be repaired by redefining `AttentionContains` or
`HasSoundExclusionCertificate`: it can only be repaired by adding a hypothesis
that links the seal to the byte universe — which is SPEC §10.5's universal
coverage obligation, and is exactly the hypothesis §7 adds.

The two conditions are satisfiable: `Atlas.honesty_conditions_satisfiable` proves
this file's own `Atlas.AttentionContains` and
`Atlas.HasSoundExclusionCertificate` meet them.
-/
theorem attention_no_optimum_relevant_false_negative_is_false
    (Contains : SealCore → ByteArray → Prop)
    (Excluded : (P : Wasm.Profile) → (S : Universal.Setting P) → SealCore →
      (bytes : ByteArray) → Universal.SystemEvaluation S bytes → Prop)
    (hContains : ∀ (core : SealCore) (bytes : ByteArray),
      core.attentionRoot.signatures = [] → ¬ Contains core bytes)
    (hExcluded : ∀ (P : Wasm.Profile) (S : Universal.Setting P) (core : SealCore)
      (bytes : ByteArray) (evaluation : Universal.SystemEvaluation S bytes),
      core.certificateRoot.certificateIds = [] →
      ¬ Excluded P S core bytes evaluation) :
    ¬ NoOptimumRelevantFalseNegative Contains Excluded := by
  intro hall
  have hdisj := hall Release.wasmProfile (Release.setting Release.seam) witnessDecider
    Release.gemmProblem (Release.costObjective Release.seam)
    (derivedState releaseScope blindDecls) (coreAt releaseScope blindDecls witnessScore)
    Release.witnessBytes Release.witnessSystemEvaluation
    (sealCertificateAt releaseScope blindDecls witnessScore)
    rfl rfl rfl Release.witness_profileValid witnessDecider_evaluates (Nat.le_refl _)
  rcases hdisj with h | h
  · exact hContains _ _ rfl h
  · exact hExcluded _ _ _ _ _ rfl h

/-- **The honesty conditions are satisfiable**, so the refutation above is not a
conditional with an unsatisfiable antecedent: this file's own definitions meet
both. -/
theorem honesty_conditions_satisfiable :
    (∀ (core : SealCore) (bytes : ByteArray),
        core.attentionRoot.signatures = [] → ¬ AttentionContains core bytes) ∧
      (∀ (P : Wasm.Profile) (S : Universal.Setting P) (core : SealCore)
        (bytes : ByteArray) (evaluation : Universal.SystemEvaluation S bytes),
        core.certificateRoot.certificateIds = [] →
        ¬ HasSoundExclusionCertificate core bytes evaluation) :=
  ⟨fun _ _ h => not_attentionContains_of_no_signature h,
   fun _ _ _ _ _ h => not_hasSoundExclusionCertificate_of_no_certificate h⟩

/--
**The same refutation without the retention requirement**, under the reading that
SPEC §12.2's three listed grounds are the legal ones.

Here `hExcluded` asks only that "soundly excluded" entail one of SPEC's three
grounds actually holding — the certificate need not be retained, need not exist,
and need not be inspectable.  The statement still fails, because
`Atlas.no_listed_exclusion_ground_for_witness` shows that of the three grounds,
one is contradicted by profile validity, one by the candidate tying the baseline,
and one by the core attending nothing.

The disclosure of `Atlas.SoundExclusion` applies to this theorem and not to
`Atlas.attention_no_optimum_relevant_false_negative_is_false`.
-/
theorem attention_no_optimum_relevant_false_negative_is_false_for_listed_grounds
    (Contains : SealCore → ByteArray → Prop)
    (Excluded : (P : Wasm.Profile) → (S : Universal.Setting P) → SealCore →
      (bytes : ByteArray) → Universal.SystemEvaluation S bytes → Prop)
    (hContains : ∀ (core : SealCore) (bytes : ByteArray),
      core.attentionRoot.signatures = [] → ¬ Contains core bytes)
    (hExcluded : ∀ (P : Wasm.Profile) (S : Universal.Setting P) (core : SealCore)
      (bytes : ByteArray) (evaluation : Universal.SystemEvaluation S bytes),
      Excluded P S core bytes evaluation →
      ∃ ground : ExclusionGround, SoundExclusion core bytes evaluation ground) :
    ¬ NoOptimumRelevantFalseNegative Contains Excluded := by
  intro hall
  have hdisj := hall Release.wasmProfile (Release.setting Release.seam) witnessDecider
    Release.gemmProblem (Release.costObjective Release.seam)
    (derivedState releaseScope blindDecls) (coreAt releaseScope blindDecls witnessScore)
    Release.witnessBytes Release.witnessSystemEvaluation
    (sealCertificateAt releaseScope blindDecls witnessScore)
    rfl rfl rfl Release.witness_profileValid witnessDecider_evaluates (Nat.le_refl _)
  rcases hdisj with h | h
  · exact hContains _ _ rfl h
  · obtain ⟨ground, hground⟩ := hExcluded _ _ _ _ _ h
    exact no_listed_exclusion_ground_for_witness ground hground

/--
**The refutation does not depend on the chosen evaluator.**

`Universal.SystemEvaluationRel` is a statement about an evaluator, so the
counterexample has to name one; `Atlas.witnessDecider` is that name.  This
theorem removes the objection that the choice is doing the work: take *any*
`Universal.Decider` at the constructed release setting that evaluates the witness
bytes at all — SPEC §10.1's `Universal.evaluate` among them, once it exists —
and the statement still fails.  The reason is
`Universal.systemEvaluation_subsingleton`: an evaluator that completes on these
bytes has no choice about *what* it answers.

`Release.seam_machine_completes` proves the constructed machine does complete on
the witness module at every raw invocation, so this is not an empty hypothesis
about a hypothetical evaluator either.
-/
theorem attention_no_optimum_relevant_false_negative_is_false_at_every_evaluator
    (D : Universal.Decider (Release.setting Release.seam))
    (hD : ∃ e : Universal.SystemEvaluation (Release.setting Release.seam)
        Release.witnessBytes,
      Universal.SystemEvaluationRel (Release.setting Release.seam) D
        Release.witnessBytes e)
    (Contains : SealCore → ByteArray → Prop)
    (Excluded : (P : Wasm.Profile) → (S : Universal.Setting P) → SealCore →
      (bytes : ByteArray) → Universal.SystemEvaluation S bytes → Prop)
    (hContains : ∀ (core : SealCore) (bytes : ByteArray),
      core.attentionRoot.signatures = [] → ¬ Contains core bytes)
    (hExcluded : ∀ (P : Wasm.Profile) (S : Universal.Setting P) (core : SealCore)
      (bytes : ByteArray) (evaluation : Universal.SystemEvaluation S bytes),
      core.certificateRoot.certificateIds = [] →
      ¬ Excluded P S core bytes evaluation) :
    ¬ NoOptimumRelevantFalseNegative Contains Excluded := by
  intro hall
  have hrel := Universal.systemEvaluationRel_of_exists hD Release.witnessSystemEvaluation
  have hdisj := hall Release.wasmProfile (Release.setting Release.seam) D
    Release.gemmProblem (Release.costObjective Release.seam)
    (derivedState releaseScope blindDecls) (coreAt releaseScope blindDecls witnessScore)
    Release.witnessBytes Release.witnessSystemEvaluation
    (sealCertificateAt releaseScope blindDecls witnessScore)
    rfl rfl rfl Release.witness_profileValid hrel (Nat.le_refl _)
  rcases hdisj with h | h
  · exact hContains _ _ rfl h
  · exact hExcluded _ _ _ _ _ rfl h

/-! ## 7. The intended content

The residual hypothesis, stated rather than hidden: the candidate was *declared*
to the Atlas, and the state is coherent (`Atlas.Coherent`, i.e. its semantic half
is exactly what its declaration base derives — preserved by every update, and
established by every rebuild).  Under it, and under every one of SPEC's own
hypotheses, the candidate is routed by `attend` and contained in the sealed
core. -/

/--
**No declared optimum-relevant candidate is a false negative.**

Every hypothesis of SPEC §12.2's statement, plus exactly two more:
`Atlas.Coherent state.body`, and membership of the candidate in the state's
declaration base.  The conclusion is strictly stronger than SPEC's disjunction —
the left disjunct is proved outright, in both its weak (core-level) and strong
(`attend`-level) readings, so no exclusion certificate is needed and none is
offered.

`hdeclared` is the gap, and it is the one
`Atlas.attention_no_optimum_relevant_false_negative_is_false` proves load
bearing.  It is *not* an assumption that the index already contains the
candidate: it says only that the candidate reached the Atlas as a declaration,
after which the indexing is derived (`Atlas.attentionEntryOf`) and the routing
proved.  What is not proved anywhere in this repository — and what the refutation
shows the seal cannot supply — is that every profile-valid byte string is
declared.  That is SPEC §10.5's universal coverage obligation.

`hcoherent` is the standing well-formedness condition of `Atlas/Update.lean`: the
state's semantic half is exactly what its declaration base derives.  No
counterexample to dropping it is offered here; it is what makes the attention
index a function of the declaration base at all, it is established by every
rebuild (`Atlas.rebuild_coherent`) and preserved by every update
(`Atlas.semanticApplyBody_coherent`), and it is the same hypothesis `DEV-004`
found load bearing for rebuild equivalence.
-/
theorem attention_no_declared_optimum_relevant_false_negative
    {P : Wasm.Profile} {S : Universal.Setting P} {D : Universal.Decider S}
    {problem : Gemm.Problem P} {objective : Cost.ProperObjective P S.problem}
    {state : UnsealedState} {core : SealCore} {candidateBytes : ByteArray}
    {evaluation : Universal.SystemEvaluation S candidateBytes}
    (hsealed : SealCertificate state core)
    (hprofile : Wasm.ProfileId P = core.profileId)
    (hproblem : Gemm.ProblemId problem = core.problemId)
    (hobjective : Cost.ObjectiveId objective = core.objectiveId)
    (hc : Universal.ProfileValid P candidateBytes)
    (heval : Universal.SystemEvaluationRel S D candidateBytes evaluation)
    (hscore : objective.score evaluation.cost ≤ core.baselineScore)
    (hcoherent : Coherent state.body)
    (hdeclared : candidateBytes ∈ state.body.declarationBase.declarations) :
    OptimumRelevant D problem objective core candidateBytes ∧
      AttentionRoutes state.body candidateBytes ∧
      AttentionContains core candidateBytes := by
  have hentries : state.body.attentionIndex.entries =
      state.body.declarationBase.declarations.map attentionEntryOf :=
    congrArg (fun b => b.attentionIndex.entries) hcoherent
  have hindexed : IndexesCandidate state.body candidateBytes := by
    refine ⟨attentionEntryOf candidateBytes, ?_, rfl, ?_⟩
    · rw [hentries]
      exact List.mem_map_of_mem hdeclared
    · exact List.mem_cons_self
  have hroutes : AttentionRoutes state.body candidateBytes :=
    attentionRoutes_of_indexesCandidate hindexed
  exact ⟨⟨hc, hprofile, hproblem, hobjective, evaluation, heval, hscore⟩, hroutes,
    attentionContains_of_attentionRoutes hsealed.attentionComplete hroutes⟩

/--
**Non-vacuity of §6.**

The same real candidate as §5 — `Release.witnessBytes`, profile valid by
`Release.witness_profileValid`, evaluated by `Release.witnessSystemEvaluation`,
at a baseline it attains — declared to the Atlas this time.  The index returns
it: `attend` routes its canonical identity, and the sealed core contains its
canonical signature.

So `Atlas.OptimumRelevant` is inhabited, and the theorem of §6 is not a statement
about an empty class.
-/
theorem declared_witness_is_routed :
    OptimumRelevant witnessDecider Release.gemmProblem
        (Release.costObjective Release.seam)
        (coreAt releaseScope declaredDecls witnessScore) Release.witnessBytes ∧
      AttentionRoutes (derivedState releaseScope declaredDecls).body
        Release.witnessBytes ∧
      AttentionContains (coreAt releaseScope declaredDecls witnessScore)
        Release.witnessBytes :=
  attention_no_declared_optimum_relevant_false_negative
    (sealCertificateAt releaseScope declaredDecls witnessScore)
    rfl rfl rfl Release.witness_profileValid witnessDecider_evaluates (Nat.le_refl _)
    (derivedBody_coherent releaseScope declaredDecls) List.mem_cons_self

end WasmGemmGnaf.Atlas
