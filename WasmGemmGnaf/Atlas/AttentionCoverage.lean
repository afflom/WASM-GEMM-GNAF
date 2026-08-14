import WasmGemmGnaf.Atlas.Attention
import WasmGemmGnaf.Atlas.Rebuild
import WasmGemmGnaf.Universal.EnumerateInputs
import WasmGemmGnaf.Universal.Partition

set_option autoImplicit false

/-!
# Atlas: optimum-relevant attention coverage (SPEC §12.2)

This module contains the Atlas-local definitions and proofs that do not depend on
a concrete release artifact.  It relates declaration bytes to attention
signatures and object identities, proves that `attend` routes every indexed
candidate, and proves that a coherent Atlas routes every optimum-relevant
candidate present in its declaration base.

The declaration-base hypothesis is explicit.  Showing that every profile-valid
byte string reaches that base remains SPEC §10.5's separate all-byte coverage
obligation; an attention seal alone does not supply it.
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
(`Atlas.attentionContains_of_attentionRoutes`).
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

/-- **A sealed core records the signature of everything `attend` returns.** -/
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
seven checkers reads `baselineScore`, so the same state seals at *any* baseline. -/

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

/-! ## 4. Sound exclusion, in SPEC's own three grounds

SPEC §12.2: "an omitted candidate or partition is legal only when a **retained**
proof shows that it is empty, cannot beat the current bound, or is exactly
reconstructible elsewhere."  Those are three grounds and a retention requirement.
Both are transcribed here. -/

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

/-! ## 5. The all-byte statement as a proposition -/

/--
The all-byte form of `attention_no_optimum_relevant_false_negative`, written out
in the repository's spelling and parameterised by its containment and exclusion
predicates.

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

/-- The two empty-root honesty conditions follow from the concrete containment
and retained-certificate definitions. -/
theorem honesty_conditions_satisfiable :
    (∀ (core : SealCore) (bytes : ByteArray),
        core.attentionRoot.signatures = [] → ¬ AttentionContains core bytes) ∧
      (∀ (P : Wasm.Profile) (S : Universal.Setting P) (core : SealCore)
        (bytes : ByteArray) (evaluation : Universal.SystemEvaluation S bytes),
        core.certificateRoot.certificateIds = [] →
        ¬ HasSoundExclusionCertificate core bytes evaluation) :=
  ⟨fun _ _ h => not_attentionContains_of_no_signature h,
   fun _ _ _ _ _ h => not_hasSoundExclusionCertificate_of_no_certificate h⟩

/-! ## 6. Declared-candidate coverage

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

`hdeclared` is not an assumption that the index already contains the candidate:
it says only that the candidate reached the Atlas as a declaration, after which
the indexing is derived (`Atlas.attentionEntryOf`) and the routing proved.  What
is not proved here is that every profile-valid byte string is declared.  That is
SPEC §10.5's universal coverage obligation.

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

end WasmGemmGnaf.Atlas
