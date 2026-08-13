/-
  The Atlas lifecycle: traces, strategy-indexed prefix evaluations, and the
  native lifecycle cost polynomial.
  Normative source: SPEC.md section 16 (the lifecycle half).

  SCOPE — read this before citing anything here.

  This file supplies the lifecycle carrier and accounting SPEC 16 makes
  normative: `LifecycleTraceBody` with its canonical identity,
  `ResolvedLifecycleTrace`, `LifecycleSizeVector`, `LifecycleAlgorithmTag`,
  `LifecyclePrefixResult`, `LifecycleEvaluation`, and `Atlas.nativeLifecycleBound`.

  Two things about it are load bearing and easy to get wrong, so they are
  spelled out.

  1. **Every verifier here is a recomputation, never a stored conclusion.**
     `VerifiesExactLifecyclePrefix` says the recorded before/after state
     identities, selected delta, optional seal and query-result identities are
     *exactly* what replaying the trace under the named strategy produces;
     `VerifiesLifecyclePrefixCost` and `VerifiesLifecycleSize` say the same of
     the charged cost and the size vector.  No structure field asserts that a
     bound holds, that two strategies agree, or that a lifecycle is optimal.

  2. **`lifecycle_native_bound` is PROVED, over a pinned release table.**  An
     earlier version of this note recorded it as omitted because the inequality
     "is false for an arbitrary primitive-cost table … which is a property of a
     *release* table this repository has not pinned."  The first clause was
     right; the second was the fix, not the obstacle.  SPEC 16 states the
     theorem over `Release.primitiveCostTable`, so that table is now pinned in
     `Cost/Lifecycle.lean` — every coefficient `1`, the componentwise-minimal
     positive table SPEC allows — and the inequality is proved over it, with
     `lifecycle_native_bound_of_positive` establishing it for *every* positive
     table so that nothing rests on the choice.  `lifecycle_native_bound_attained`
     and `lifecycle_native_bound_slack` then say exactly which fourteen
     coordinates are attained with equality and exactly how loose the other
     three are.

  3. **`lifecycle_incremental_semantics_eq_full_rebuild` is OMITTED because it
     is FALSE**, and that is proved here rather than argued:
     `not_lifecycle_incremental_semantics_eq_full_rebuild` refutes SPEC 16's
     literal statement.  `ResolvedLifecycleTrace` carries no coherence
     obligation on its initial state, and an incoherent start is observed
     differently by the two strategies at prefix `0`.  The theorem is proved
     under exactly the missing hypothesis, as
     `lifecycle_incremental_semantics_eq_full_rebuild_of_coherent`, which does
     *not* wear SPEC's name; no binding in
     `Conformance/RequiredSignatures.lean` claims that name.

  The comparator half of SPEC 16 is closed:
  `Atlas.canonicalFullRebuildEvaluation` is a total constructor with no
  hypothesis, `Atlas.regretAgainst` is defined by cases on the comparator tag,
  and `Atlas.lifecycle_full_rebuild_comparator_exact` is proved.  See the
  "## Omissions" section at the end of the file for what remains open and why.

  Every declaration in this file is either a definition or a kernel-checked
  theorem.  Nothing is assumed: no placeholder proof, no project axiom, and no
  compiled-evaluation decision procedure appears anywhere below.
-/
import WasmGemmGnaf.Atlas.Query
import WasmGemmGnaf.Atlas.Attention
import WasmGemmGnaf.Cost.Lifecycle

set_option autoImplicit false

namespace WasmGemmGnaf.Atlas

open WasmGemmGnaf.Foundation

/-! ## A canonical finite set of naturals (SPEC 16, `CanonicalFinset Nat`) -/

/-- A finite set of naturals in canonical form: strictly ascending, hence
duplicate free and uniquely determined by its membership. -/
structure CanonicalNatFinset where
  /-- The elements, strictly ascending. -/
  elements : List Nat
  /-- They really are strictly ascending. -/
  ascending : List.Pairwise (· < ·) elements

namespace CanonicalNatFinset

/-- The empty canonical finite set. -/
def empty : CanonicalNatFinset := ⟨[], List.Pairwise.nil⟩

@[simp] theorem empty_elements : empty.elements = [] := rfl

/-- Membership. -/
def Mem (s : CanonicalNatFinset) (n : Nat) : Prop := n ∈ s.elements

instance : Membership Nat CanonicalNatFinset where
  mem s n := Mem s n

instance decidableMem (s : CanonicalNatFinset) (n : Nat) : Decidable (Mem s n) :=
  inferInstanceAs (Decidable (n ∈ s.elements))

/-- A canonical finite set is duplicate free. -/
theorem nodup (s : CanonicalNatFinset) : s.elements.Nodup :=
  s.ascending.imp (fun h => Nat.ne_of_lt h)

theorem eq_of_elements_eq {a b : CanonicalNatFinset} (h : a.elements = b.elements) :
    a = b := by
  cases a; cases b; cases h; rfl

end CanonicalNatFinset

/-! ## The lifecycle trace body (SPEC 16) -/

/--
  **SPEC 16**, `Atlas.LifecycleTraceBody`: the first-order, canonically encoded
  release input that names one lifecycle.

  `CanonicalList DeltaId` and `CanonicalList RequestId` are the *schedules* of a
  trace, so their canonical order is the trace order, not the byte order; they
  are therefore plain lists, and `ResolvedLifecycleTrace.resolvesDeltas` pins
  them to the resolved objects position by position.
-/
structure LifecycleTraceBody where
  /-- Schema version. -/
  version : Nat
  /-- The pinned profile identity. -/
  profileId : ProfileId
  /-- The pinned problem identity. -/
  problemId : ProblemId
  /-- The pinned objective identity. -/
  objectiveId : ObjectiveId
  /-- The identity of the state the lifecycle starts from. -/
  initialStateId : StateIdentity
  /-- The delta schedule, in trace order. -/
  deltaIds : List Foundation.DeltaId
  /-- The request schedule, in trace order. -/
  requestIds : List RequestId
  /-- The prefix ordinal each request is answered after. -/
  requestAfterPrefixes : List Nat
  /-- The prefix ordinals at which the state is sealed. -/
  sealAfterPrefixes : CanonicalNatFinset
  /-- The number of deltas in the trace. -/
  horizon : Nat

namespace LifecycleTraceBody

/-- The flattening used to build the canonical encoder. -/
def toTuple (b : LifecycleTraceBody) :
    Nat × CanonicalObjectId × CanonicalObjectId × CanonicalObjectId ×
      CanonicalObjectId × List CanonicalObjectId × List CanonicalObjectId ×
      List Nat × List Nat × Nat :=
  (b.version, b.profileId, b.problemId, b.objectiveId, b.initialStateId,
   b.deltaIds, b.requestIds, b.requestAfterPrefixes,
   b.sealAfterPrefixes.elements, b.horizon)

theorem toTuple_injective : Function.Injective toTuple := by
  intro a b h
  obtain ⟨v₁, p₁, q₁, o₁, s₁, d₁, r₁, ra₁, ⟨se₁, ha₁⟩, hz₁⟩ := a
  obtain ⟨v₂, p₂, q₂, o₂, s₂, d₂, r₂, ra₂, ⟨se₂, ha₂⟩, hz₂⟩ := b
  simp only [toTuple, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h
  subst e1; subst e2; subst e3; subst e4; subst e5
  subst e6; subst e7; subst e8; subst e9; subst e10
  rfl

/-- The canonical prefix-free encoding of a lifecycle trace body. -/
def bytes (b : LifecycleTraceBody) : List UInt8 :=
  Bytes.pairBytes Bytes.natBytes
   (Bytes.pairBytes CanonicalObjectId.bytes
    (Bytes.pairBytes CanonicalObjectId.bytes
     (Bytes.pairBytes CanonicalObjectId.bytes
      (Bytes.pairBytes CanonicalObjectId.bytes
       (Bytes.pairBytes Enc.idList
        (Bytes.pairBytes Enc.idList
         (Bytes.pairBytes Enc.natList
          (Bytes.pairBytes Enc.natList Bytes.natBytes)))))))) b.toTuple

theorem bytes_prefixFree : Bytes.PrefixFree bytes :=
  (Bytes.pairBytes_prefixFree Bytes.natBytes_prefixFree
   (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
    (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
     (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
      (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
       (Bytes.pairBytes_prefixFree Enc.idList_prefixFree
        (Bytes.pairBytes_prefixFree Enc.idList_prefixFree
         (Bytes.pairBytes_prefixFree Enc.natList_prefixFree
          (Bytes.pairBytes_prefixFree Enc.natList_prefixFree
            Bytes.natBytes_prefixFree))))))))).comp toTuple_injective

/-- The frozen canonical schema of a lifecycle trace body. -/
def identitySchema : CanonicalSchema LifecycleTraceBody :=
  CanonicalSchema.ofPrefixFree 1 CanonicalDomainTag.atlasState
    (leafTag 9 "Atlas.LifecycleTraceBody") (leafTag_size_pos 9 _)
    bytes bytes_prefixFree

/-- Every canonical identity a trace body references. -/
def referencedObjects (b : LifecycleTraceBody) : List CanonicalObjectId :=
  [b.profileId, b.problemId, b.objectiveId, b.initialStateId] ++
    b.deltaIds ++ b.requestIds

end LifecycleTraceBody

/-- **SPEC 16**, `Atlas.LifecycleTraceIdentity`. -/
abbrev LifecycleTraceIdentity := ObjectId LifecycleTraceBody

/-- **SPEC 16**, `Atlas.LifecycleTraceId`. -/
def LifecycleTraceId (body : LifecycleTraceBody) : LifecycleTraceIdentity :=
  Identity LifecycleTraceBody.identitySchema body

/-- Trace identity is structural comparison, not a digest. -/
theorem LifecycleTraceId_eq_iff {a b : LifecycleTraceBody} :
    LifecycleTraceId a = LifecycleTraceId b ↔ a = b :=
  Identity_eq_iff LifecycleTraceBody.identitySchema

theorem LifecycleTraceId_injective : Function.Injective LifecycleTraceId :=
  fun _ _ h => LifecycleTraceId_eq_iff.mp h

/-! ## Complete preimages of a trace (SPEC 16, `CompleteLifecycleObjectGraph`) -/

/-- **SPEC 16**, `CompleteLifecycleObjectGraph`: every identity the trace body
references resolves in the retained graph.  This mirrors
`Atlas.CompleteObjectGraph` of SPEC 12.1; the completeness field is a side
condition discharged at construction, never a stored conclusion. -/
structure CompleteLifecycleObjectGraph (body : LifecycleTraceBody) where
  /-- The retained graph. -/
  graph : ObjectGraph
  /-- It resolves every referenced identity. -/
  complete : ∀ id ∈ body.referencedObjects, graph.resolves id = true

/-- The canonical complete preimage graph of a trace body: retain exactly the
canonical preimage of every identity it references. -/
def canonicalLifecycleObjectGraph (body : LifecycleTraceBody) :
    CompleteLifecycleObjectGraph body where
  graph := ObjectGraph.ofIds body.referencedObjects
  complete := fun _ hid => ObjectGraph.ofIds_resolves hid

/-! ## Resolved traces (SPEC 16) -/

/-- The canonical identities of a resolved delta schedule. -/
def CanonicalDeltaIds (deltas : List Delta) : List Foundation.DeltaId :=
  deltas.map DeltaId

/-- The canonical identities of a resolved request schedule. -/
def CanonicalRequestIds (requests : List RequestSignature) : List RequestId :=
  requests.map RequestSignatureId

/--
  **SPEC 16**, `Atlas.ResolvedLifecycleTrace`.

  Every `resolves*` field is an equation between recomputed identities and the
  first-order schedule recorded in the body, so a resolved trace cannot name
  objects the body does not.
-/
structure ResolvedLifecycleTrace (body : LifecycleTraceBody) where
  /-- The state the lifecycle starts from. -/
  initialState : UnsealedState
  /-- The resolved deltas, in trace order. -/
  deltas : List Delta
  /-- The resolved requests, in trace order. -/
  requests : List RequestSignature
  /-- The initial state really is the one the body names. -/
  resolvesInitial : initialState.bodyId = body.initialStateId
  /-- The delta schedule really is the one the body names. -/
  resolvesDeltas : CanonicalDeltaIds deltas = body.deltaIds
  /-- The request schedule really is the one the body names. -/
  resolvesRequests : CanonicalRequestIds requests = body.requestIds
  /-- The horizon is the length of the delta schedule. -/
  horizonEq : body.horizon = body.deltaIds.length
  /-- Every request has exactly one scheduled prefix ordinal. -/
  requestScheduleLength :
    body.requestAfterPrefixes.length = body.requestIds.length
  /-- Every scheduled request ordinal is inside the horizon. -/
  requestOrdinalsValid : ∀ ordinal ∈ body.requestAfterPrefixes,
    ordinal ≤ body.horizon
  /-- Every seal ordinal is inside the horizon. -/
  sealOrdinalsValid : ∀ ordinal ∈ body.sealAfterPrefixes.elements,
    ordinal ≤ body.horizon
  /-- Every referenced object is retained. -/
  completePreimages : CompleteLifecycleObjectGraph body

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The resolved trace has exactly `body.horizon` deltas. -/
theorem deltas_length (trace : ResolvedLifecycleTrace body) :
    trace.deltas.length = body.horizon := by
  rw [trace.horizonEq, ← trace.resolvesDeltas, CanonicalDeltaIds, List.length_map]

/-- The resolved trace has exactly as many requests as scheduled ordinals. -/
theorem requests_length (trace : ResolvedLifecycleTrace body) :
    trace.requests.length = body.requestAfterPrefixes.length := by
  rw [trace.requestScheduleLength, ← trace.resolvesRequests, CanonicalRequestIds,
    List.length_map]

/-- The scope the lifecycle runs in: the initial state's own scope. -/
def scope (trace : ResolvedLifecycleTrace body) : Scope :=
  trace.initialState.body.scope

end ResolvedLifecycleTrace

/-! ## Strategies (SPEC 16) -/

/-- **SPEC 16**, `Atlas.LifecycleAlgorithmTag`.  A lifecycle evaluation is
strategy indexed; there is no untagged evaluation whose native and full-rebuild
costs could be interchanged. -/
inductive LifecycleAlgorithmTag
  /-- The native incremental update operator of SPEC 12.5. -/
  | nativeIncremental
  /-- The comparator: a canonical full rebuild at every seal point. -/
  | canonicalFullRebuildAtEverySeal
  deriving DecidableEq, Repr, Inhabited

/-! ## Replaying a trace

Every verifier below is stated against these total, computable replays.  They
are functions of the trace and the strategy alone. -/

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The delta selected at prefix `n`: none at prefix `0` (the initial state),
otherwise the `n-1`-st delta of the schedule. -/
def selectedDelta? (trace : ResolvedLifecycleTrace body) : Nat → Option Delta
  | 0 => none
  | k + 1 => trace.deltas[k]?

@[simp] theorem selectedDelta?_zero (trace : ResolvedLifecycleTrace body) :
    trace.selectedDelta? 0 = none := rfl

/-- The state body reached after applying the first `n` deltas incrementally. -/
def nativeBodyAt (trace : ResolvedLifecycleTrace body) : Nat → StateBody
  | 0 => trace.initialState.body
  | k + 1 =>
      match trace.deltas[k]? with
      | some delta => semanticApplyBody (trace.nativeBodyAt k) delta
      | none => trace.nativeBodyAt k

@[simp] theorem nativeBodyAt_zero (trace : ResolvedLifecycleTrace body) :
    trace.nativeBodyAt 0 = trace.initialState.body := rfl

/-- The declaration base accumulated after `n` prefixes. -/
def accumulatedDeclarations (trace : ResolvedLifecycleTrace body) (n : Nat) :
    CanonicalDeclarationSet :=
  (trace.nativeBodyAt n).declarationBase

/-- The state body the canonical full rebuild reaches after `n` prefixes: the
rebuild of the accumulated declaration base in the trace's own scope. -/
def rebuildBodyAt (trace : ResolvedLifecycleTrace body) (n : Nat) : StateBody :=
  semanticRebuildBodyWith trace.scope (trace.accumulatedDeclarations n)

/-- The state body a named strategy reaches after `n` prefixes. -/
def bodyAt (trace : ResolvedLifecycleTrace body) :
    LifecycleAlgorithmTag → Nat → StateBody
  | .nativeIncremental, n => trace.nativeBodyAt n
  | .canonicalFullRebuildAtEverySeal, n => trace.rebuildBodyAt n

/-- **The two strategies reach the same state on a coherent trace.**  This is
`Atlas.semanticApplyBody_eq_rebuild` of SPEC 12.5, lifted to prefix `0`; it is
not the full observational-equality theorem of SPEC 16, which is omitted. -/
theorem bodyAt_zero_agree (trace : ResolvedLifecycleTrace body)
    (hcoherent : Coherent trace.initialState.body) :
    trace.bodyAt .nativeIncremental 0 = trace.bodyAt .canonicalFullRebuildAtEverySeal 0 := by
  show trace.initialState.body =
    semanticRebuildBodyWith trace.scope trace.initialState.body.declarationBase
  exact hcoherent

/-- Whether prefix `n` is a seal point. -/
def isSealPoint (_trace : ResolvedLifecycleTrace body) (n : Nat) : Bool :=
  decide (n ∈ body.sealAfterPrefixes.elements)

/-- The requests scheduled to be answered after prefix `n`. -/
def scheduledRequests (trace : ResolvedLifecycleTrace body) (n : Nat) :
    List RequestSignature :=
  (body.requestAfterPrefixes.zip trace.requests).filterMap
    (fun p => if p.1 = n then some p.2 else none)

end ResolvedLifecycleTrace

/-! ## Query outcomes and their identities -/

/-- The first-order body of one answered lifecycle query: the state it was
answered against, the request, and the exact routed identities.  Every field is
recomputed by `Atlas.attendTargets`; none is a stored conclusion. -/
structure QueryOutcomeBody where
  /-- The state the query was answered against. -/
  stateId : StateIdentity
  /-- The request. -/
  requestId : RequestId
  /-- The exact routed identities, in index order. -/
  targets : List CanonicalObjectId
  deriving DecidableEq

namespace QueryOutcomeBody

/-- The flattening used to build the canonical encoder. -/
def toTuple (b : QueryOutcomeBody) :
    CanonicalObjectId × CanonicalObjectId × List CanonicalObjectId :=
  (b.stateId, b.requestId, b.targets)

theorem toTuple_injective : Function.Injective toTuple := by
  intro a b h
  cases a; cases b
  simp only [toTuple, Prod.mk.injEq] at h
  simp only [QueryOutcomeBody.mk.injEq]
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The canonical prefix-free encoding of a query outcome. -/
def bytes (b : QueryOutcomeBody) : List UInt8 :=
  Bytes.pairBytes CanonicalObjectId.bytes
    (Bytes.pairBytes CanonicalObjectId.bytes Enc.idList) b.toTuple

theorem bytes_prefixFree : Bytes.PrefixFree bytes :=
  (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
    (Bytes.pairBytes_prefixFree CanonicalObjectId.bytes_prefixFree
      Enc.idList_prefixFree)).comp toTuple_injective

/-- The frozen canonical schema of a query outcome. -/
def identitySchema : CanonicalSchema QueryOutcomeBody :=
  CanonicalSchema.ofPrefixFree 1 CanonicalDomainTag.queryResult
    (leafTag 10 "Atlas.QueryOutcomeBody") (leafTag_size_pos 10 _)
    bytes bytes_prefixFree

end QueryOutcomeBody

/-- The canonical identity of an answered lifecycle query. -/
def QueryOutcomeId (b : QueryOutcomeBody) : QueryResultId :=
  CanonicalObjectId.ofTyped (Identity QueryOutcomeBody.identitySchema b)

theorem QueryOutcomeId_eq_iff {a b : QueryOutcomeBody} :
    QueryOutcomeId a = QueryOutcomeId b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff QueryOutcomeBody.identitySchema

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The exact query outcome of one request at prefix `n` under a strategy. -/
def queryOutcomeAt (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) (n : Nat) (request : RequestSignature) :
    QueryOutcomeBody :=
  { stateId := StateId (trace.bodyAt algorithm n)
    requestId := RequestSignatureId request
    targets := attendTargets (trace.bodyAt algorithm n) request }

/-- The exact query-result identities produced at prefix `n`. -/
def queryResultIdsAt (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) (n : Nat) : List QueryResultId :=
  (trace.scheduledRequests n).map
    (fun request => QueryOutcomeId (trace.queryOutcomeAt algorithm n request))

/-- The exact seal identity produced at prefix `n`, when `n` is a seal point. -/
def sealIdAt (trace : ResolvedLifecycleTrace body)
    (_algorithm : LifecycleAlgorithmTag) (n : Nat) : Option SealIdentity :=
  if trace.isSealPoint n then
    some (derivedSealedState trace.scope (trace.accumulatedDeclarations n)).sealId
  else
    none

end ResolvedLifecycleTrace

/-! ## The exact prefix transition verifier (SPEC 16) -/

/--
  **SPEC 16**, `VerifiesExactLifecyclePrefix`.

  Each prefix verifier binds its strategy, before state, selected delta, after
  state, optional seal and exact query-result identities.  Every conjunct is an
  equation against the replay above, so nothing here can be recorded without
  being recomputable.
-/
def VerifiesExactLifecyclePrefix {body : LifecycleTraceBody}
    (algorithm : LifecycleAlgorithmTag) (trace : ResolvedLifecycleTrace body)
    (prefixOrdinal : Fin (body.horizon + 1))
    (beforeStateId : StateIdentity) (deltaId : Option Foundation.DeltaId)
    (afterStateId : StateIdentity) (sealId : Option SealIdentity)
    (queryResultIds : List QueryResultId) : Prop :=
  beforeStateId = StateId (trace.bodyAt algorithm (prefixOrdinal.val - 1)) ∧
  deltaId = (trace.selectedDelta? prefixOrdinal.val).map DeltaId ∧
  afterStateId = StateId (trace.bodyAt algorithm prefixOrdinal.val) ∧
  sealId = trace.sealIdAt algorithm prefixOrdinal.val ∧
  queryResultIds = trace.queryResultIdsAt algorithm prefixOrdinal.val

/-! ## The exact prefix cost (SPEC 16) -/

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The total size in bytes of a list of canonical declarations. -/
def declarationBytes (l : List ByteArray) : Nat := (l.map ByteArray.size).sum

/-- The genuinely new declarations the selected delta contributes at prefix
`n`. -/
def novelDeclarationsAt (trace : ResolvedLifecycleTrace body) (n : Nat) :
    List ByteArray :=
  match trace.selectedDelta? n with
  | none => []
  | some delta =>
      newDeclarations (trace.nativeBodyAt (n - 1)).declarationBase delta

/-- The declarations a strategy actually canonicalizes at prefix `n`: the novel
ones for the native operator, and — at a seal point — the whole accumulated base
for the canonical full rebuild. -/
def chargedDeclarationsAt (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) (n : Nat) : List ByteArray :=
  match algorithm with
  | .nativeIncremental => trace.novelDeclarationsAt n
  | .canonicalFullRebuildAtEverySeal =>
      if trace.isSealPoint n then (trace.accumulatedDeclarations n).declarations
      else trace.novelDeclarationsAt n

/--
  **SPEC 16**, the exact charge of one lifecycle prefix.

  This is a *definition* of the lifecycle cost model, in the sense SPEC 9.1
  fixes the artifact cost model: it says what is charged, not that any bound
  holds.  Accumulation, closure, indexing, invalidation, sealing, retention and
  query selection are each charged against the work the replay actually
  performs at this prefix.
-/
def prefixCost (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) (n : Nat) : Cost.LifecycleVector :=
  let charged := trace.chargedDeclarationsAt algorithm n
  let novelCount := charged.length
  let chargedBytes := declarationBytes charged
  let retained := declarationBytes (trace.accumulatedDeclarations n).declarations
  let requests := trace.scheduledRequests n
  let routed :=
    (requests.map (fun r => (attendTargets (trace.bodyAt algorithm n) r).length)).sum
  let sealed := trace.isSealPoint n
  { authorityCheckSteps :=
      if n = 0 then
        declarationBytes trace.initialState.body.declarationBase.declarations
      else 0
    canonicalizationSteps := chargedBytes
    canonicalNovelObjects := novelCount
    canonicalNovelEdges := novelCount
    closureSteps := novelCount
    indexSteps := novelCount
    attentionBucketsTouched := novelCount
    dependencyObjectsVisited := novelCount
    partitionSteps := 0
    partitionCellsChanged := 0
    verifierSteps := if sealed then retained else 0
    sealSteps := if sealed then 1 + retained else 0
    querySelectionSteps := requests.length + routed
    migrationSteps := 0
    retainedStateBytes := retained
    peakWorkingBytes := retained + chargedBytes
    artifact := Cost.ArtifactVector.zero }

end ResolvedLifecycleTrace

/-- **SPEC 16**, `Cost.VerifiesLifecyclePrefixCost`: the recorded charge is
exactly the replay's charge. -/
def VerifiesLifecyclePrefixCost {body : LifecycleTraceBody}
    (algorithm : LifecycleAlgorithmTag) (trace : ResolvedLifecycleTrace body)
    (prefixOrdinal : Fin (body.horizon + 1))
    (_beforeStateId : StateIdentity) (_deltaId : Option Foundation.DeltaId)
    (_afterStateId : StateIdentity) (_sealId : Option SealIdentity)
    (_queryResultIds : List QueryResultId) (cost : Cost.LifecycleVector) : Prop :=
  cost = trace.prefixCost algorithm prefixOrdinal.val

/-! ## Prefix results (SPEC 16) -/

/-- **SPEC 16**, `Atlas.LifecyclePrefixResult`. -/
structure LifecyclePrefixResult {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) (algorithm : LifecycleAlgorithmTag) where
  /-- Which prefix this result is about. -/
  prefixOrdinal : Fin (body.horizon + 1)
  /-- The state identity before the prefix. -/
  beforeStateId : StateIdentity
  /-- The delta applied at the prefix, if any. -/
  deltaId : Option Foundation.DeltaId
  /-- The state identity after the prefix. -/
  afterStateId : StateIdentity
  /-- The seal produced at the prefix, if any. -/
  sealId : Option SealIdentity
  /-- The exact query-result identities produced at the prefix. -/
  queryResultIds : List QueryResultId
  /-- The charge of the prefix. -/
  cost : Cost.LifecycleVector
  /-- The transition really is the replay's transition. -/
  exactTransition : VerifiesExactLifecyclePrefix algorithm trace prefixOrdinal
    beforeStateId deltaId afterStateId sealId queryResultIds
  /-- The charge really is the replay's charge. -/
  exactCost : VerifiesLifecyclePrefixCost algorithm trace prefixOrdinal
    beforeStateId deltaId afterStateId sealId queryResultIds cost

namespace LifecyclePrefixResult

variable {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
  {algorithm : LifecycleAlgorithmTag}

/-- The recorded charge is the replay's charge. -/
theorem cost_eq (r : LifecyclePrefixResult trace algorithm) :
    r.cost = trace.prefixCost algorithm r.prefixOrdinal.val := r.exactCost

/-- The recorded after-state identity is the replay's state identity. -/
theorem afterStateId_eq (r : LifecyclePrefixResult trace algorithm) :
    r.afterStateId = StateId (trace.bodyAt algorithm r.prefixOrdinal.val) :=
  r.exactTransition.2.2.1

/-- The recorded query-result identities are the replay's. -/
theorem queryResultIds_eq (r : LifecyclePrefixResult trace algorithm) :
    r.queryResultIds = trace.queryResultIdsAt algorithm r.prefixOrdinal.val :=
  r.exactTransition.2.2.2.2

/-- **Two prefix results for the same ordinal are identical.**  Nothing in a
prefix result is free: the replay determines every field. -/
theorem eq_of_prefixOrdinal_eq {a b : LifecyclePrefixResult trace algorithm}
    (h : a.prefixOrdinal = b.prefixOrdinal) : a = b := by
  obtain ⟨oa, ba, da, aa, sa, qa, ca, ta, ka⟩ := a
  obtain ⟨ob, bb, db, ab, sb, qb, cb, tb, kb⟩ := b
  simp only at h
  subst h
  obtain ⟨t1, t2, t3, t4, t5⟩ := ta
  obtain ⟨u1, u2, u3, u4, u5⟩ := tb
  subst t1; subst t2; subst t3; subst t4; subst t5
  subst u1; subst u2; subst u3; subst u4; subst u5
  have : ca = cb := by rw [ka, kb]
  subst this
  rfl

end LifecyclePrefixResult

/-! ## Prefix-ordered families

SPEC 16 writes `NonemptyCanonicalList (LifecyclePrefixResult …)`.  The canonical
order of a lifecycle family is **prefix order** — SPEC 16 itself fixes the fold
as "natural addition in prefix order" — not the byte order of a schema.  The
carrier below is therefore a nonempty list, and `CoversExactlyEveryPrefix` pins
the order: it forces the ordinals to be exactly `0, 1, …, horizon`, in that
order, with no repetition and nothing missing.  `coversExactlyEveryPrefix_nodup`
and `coversExactlyEveryPrefix_length` prove that the pinning really is that
strong. -/

/-- A nonempty family in prefix order. -/
structure PrefixOrderedList (α : Type) where
  /-- The first element. -/
  head : α
  /-- The remaining elements, in order. -/
  rest : List α

namespace PrefixOrderedList

variable {α : Type}

/-- The elements, in prefix order. -/
def elements (l : PrefixOrderedList α) : List α := l.head :: l.rest

theorem elements_ne_nil (l : PrefixOrderedList α) : l.elements ≠ [] := by
  simp [elements]

@[simp] theorem elements_cons (a : α) (rest : List α) :
    (PrefixOrderedList.mk a rest).elements = a :: rest := rfl

end PrefixOrderedList

/-- **SPEC 16**, `CoversExactlyEveryPrefix`: the family's ordinals are exactly
`0, …, horizon`, in prefix order. -/
def CoversExactlyEveryPrefix {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    (prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)) : Prop :=
  prefixes.elements.map (fun r => r.prefixOrdinal.val) = List.range (body.horizon + 1)

/-- The cover has exactly `horizon + 1` members. -/
theorem coversExactlyEveryPrefix_length {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    {prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)}
    (h : CoversExactlyEveryPrefix prefixes) :
    prefixes.elements.length = body.horizon + 1 := by
  have := congrArg List.length h
  simpa using this

/-- The cover repeats no prefix. -/
theorem coversExactlyEveryPrefix_nodup {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    {prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)}
    (h : CoversExactlyEveryPrefix prefixes) :
    (prefixes.elements.map (fun r => r.prefixOrdinal.val)).Nodup := by
  rw [h]
  exact List.nodup_range

/-- The cover misses no prefix. -/
theorem coversExactlyEveryPrefix_complete {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    {prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)}
    (h : CoversExactlyEveryPrefix prefixes) (n : Nat) (hn : n ≤ body.horizon) :
    ∃ r ∈ prefixes.elements, r.prefixOrdinal.val = n := by
  have hmem : n ∈ prefixes.elements.map (fun r => r.prefixOrdinal.val) := by
    rw [h]
    exact List.mem_range.mpr (Nat.lt_succ_of_le hn)
  obtain ⟨r, hr, hval⟩ := List.mem_map.mp hmem
  exact ⟨r, hr, hval⟩

/-! ## Lifecycle size vectors and the native bound (SPEC 16) -/

/-- **SPEC 16**, `Atlas.LifecycleSizeVector`.  Defined once, in
`Cost/Lifecycle.lean`; this is the Atlas-facing name of the same record. -/
abbrev LifecycleSizeVector := Cost.LifecycleSizeVector

/--
  **SPEC 16**, `Atlas.nativeLifecycleBound`: the fixed componentwise polynomial.

  Authority checking is bounded by `cAuthority * authorityBytesChecked`;
  canonicalization by
  `cCanonicalize * deltaBytes * (log2 (retainedStateBytes + 2) + 1)`; closure by
  `cClosure * closureDerivations`; indexing by `cIndex * (canonicalNovelObjects
  + canonicalNovelEdges + attentionBucketsTouched)`; invalidation by
  `cDependency * dependencyImpactObjects`; partition work by `cPartition *
  partitionCellsChanged`; verification and sealing by their fixed coefficients
  times `certificateBytesChecked`, `sealCount` and the cumulative
  `sealInputBytesScanned`; query work by `cQuery * (queryCount +
  requestBytesChecked + attentionCandidatesVisited)`; migration by `cMigration *
  migrationObjects`.  Artifact work is exactly `size.artifactWork`, and the
  retained-state and peak-working-byte coordinates are passed through, not
  absorbed into constants.

  Defined once, in `Cost/Lifecycle.lean`; this is the Atlas-facing name.
-/
def nativeLifecycleBound (table : Cost.PrimitiveCostTable)
    (size : LifecycleSizeVector) : Cost.LifecycleVector :=
  Cost.nativeLifecycleBound table size

/-- Artifact work is exactly the size vector's artifact work. -/
theorem nativeLifecycleBound_artifact (table : Cost.PrimitiveCostTable)
    (size : LifecycleSizeVector) :
    (nativeLifecycleBound table size).artifact = size.artifactWork := rfl

/-- Retained-state bytes are passed through, not absorbed into a constant. -/
theorem nativeLifecycleBound_retainedStateBytes (table : Cost.PrimitiveCostTable)
    (size : LifecycleSizeVector) :
    (nativeLifecycleBound table size).retainedStateBytes
      = size.retainedStateBytes := rfl

/-- Peak working bytes are passed through, not absorbed into a constant. -/
theorem nativeLifecycleBound_peakWorkingBytes (table : Cost.PrimitiveCostTable)
    (size : LifecycleSizeVector) :
    (nativeLifecycleBound table size).peakWorkingBytes
      = size.peakWorkingBytes := rfl

/--
  **Scope of `nativeLifecycleBound`.**  The polynomial is a function of the
  primitive-cost table and the size vector *only*: two lifecycles with the same
  size vector get the same bound, whatever their traces, strategies or prefix
  costs were.  Consequently no statement about an actual lifecycle total follows
  from this definition alone — that is exactly the content of
  `lifecycle_native_bound`, which is proved below from the exact accounting
  identities of the replay, never read off from here.
-/
theorem nativeLifecycleBound_scope_size_only
    (table : Cost.PrimitiveCostTable) (a b : LifecycleSizeVector) (h : a = b) :
    nativeLifecycleBound table a = nativeLifecycleBound table b := by rw [h]

/-! ## The exact size verifier (SPEC 16) -/

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The exact size vector of a replayed lifecycle family. -/
def lifecycleSize (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag)
    (prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)) :
    LifecycleSizeVector :=
  let ordinals := prefixes.elements.map (fun r => r.prefixOrdinal.val)
  let costs := prefixes.elements.map (fun r => r.cost)
  { horizon := body.horizon
    authorityBytesChecked :=
      declarationBytes trace.initialState.body.declarationBase.declarations
    deltaBytes :=
      (ordinals.map (fun n => declarationBytes (trace.novelDeclarationsAt n))).sum
    requestBytesChecked :=
      (ordinals.map (fun n =>
        ((trace.scheduledRequests n).map
          (fun r => declarationBytes r.tokens)).sum)).sum
    canonicalNovelObjects := (costs.map (·.canonicalNovelObjects)).sum
    canonicalNovelEdges := (costs.map (·.canonicalNovelEdges)).sum
    closureDerivations := (costs.map (·.closureSteps)).sum
    attentionBucketsTouched := (costs.map (·.attentionBucketsTouched)).sum
    dependencyImpactObjects := (costs.map (·.dependencyObjectsVisited)).sum
    partitionCellsChanged := (costs.map (·.partitionCellsChanged)).sum
    certificateBytesChecked := (costs.map (·.verifierSteps)).sum
    retainedStateBytes := Cost.maxOf (costs.map (·.retainedStateBytes))
    sealCount := (ordinals.filter (fun n => trace.isSealPoint n)).length
    sealInputBytesScanned :=
      (ordinals.map (fun n =>
        if trace.isSealPoint n then
          declarationBytes (trace.accumulatedDeclarations n).declarations
        else 0)).sum
    queryCount := (ordinals.map (fun n => (trace.scheduledRequests n).length)).sum
    attentionCandidatesVisited :=
      (ordinals.map (fun n =>
        ((trace.scheduledRequests n).map
          (fun r => (attendTargets (trace.bodyAt algorithm n) r).length)).sum)).sum
    migrationObjects := 0
    peakWorkingBytes := Cost.maxOf (costs.map (·.peakWorkingBytes))
    artifactWork := Cost.ArtifactVector.zero }

end ResolvedLifecycleTrace

/-- **SPEC 16**, `VerifiesLifecycleSize`: the recorded size vector is exactly
the replay's size vector. -/
def VerifiesLifecycleSize {body : LifecycleTraceBody}
    {algorithm : LifecycleAlgorithmTag} (trace : ResolvedLifecycleTrace body)
    (prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm))
    (size : LifecycleSizeVector) : Prop :=
  size = trace.lifecycleSize algorithm prefixes

/-! ## Lifecycle evaluations (SPEC 16) -/

/--
  **SPEC 16**, `Atlas.LifecycleEvaluation`.

  Strategy indexed: `algorithm` is an index of the type, so a native evaluation
  and a full-rebuild evaluation are never interchangeable terms.
-/
structure LifecycleEvaluation {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) (algorithm : LifecycleAlgorithmTag) where
  /-- One result per prefix, in prefix order. -/
  prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)
  /-- They cover exactly every prefix. -/
  exactPrefixCover : CoversExactlyEveryPrefix prefixes
  /-- The size vector. -/
  size : LifecycleSizeVector
  /-- It is exactly the replay's size vector. -/
  sizeExact : VerifiesLifecycleSize trace prefixes size
  /-- The lifecycle total. -/
  total : Cost.LifecycleVector
  /-- It is exactly the frozen fold of the prefix costs, in prefix order. -/
  totalExact : total = Cost.sumLifecycle (prefixes.elements.map (fun r => r.cost))

/--
  **SPEC 16**, `Atlas.lifecycle_prefix_conservation`.

  The lifecycle total is the frozen mixed fold of the prefix costs in prefix
  order — every step/count coordinate summed, `retainedStateBytes` and
  `peakWorkingBytes` taken as componentwise maxima, the empty fold all zero.
  Nothing may be charged to a lifecycle that is not charged to one of its
  prefixes, and nothing charged to a prefix may be dropped.
-/
theorem lifecycle_prefix_conservation {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    (evaluation : LifecycleEvaluation trace algorithm) :
    evaluation.total =
      Cost.sumLifecycle (evaluation.prefixes.elements.map (fun r => r.cost)) :=
  evaluation.totalExact

namespace LifecycleEvaluation

variable {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
  {algorithm : LifecycleAlgorithmTag}

/-- The evaluation covers exactly `horizon + 1` prefixes. -/
theorem prefixes_length (evaluation : LifecycleEvaluation trace algorithm) :
    evaluation.prefixes.elements.length = body.horizon + 1 :=
  coversExactlyEveryPrefix_length evaluation.exactPrefixCover

/-- **Conservation, per coordinate.**  Every prefix's charge on an additively
folded coordinate is dominated by the lifecycle total. -/
theorem prefix_le_total_add_coord (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat)
    (hzero : f Cost.LifecycleVector.zero = 0)
    (hcomb : ∀ a b, f (Cost.LifecycleVector.combine a b) = f a + f b)
    {r : LifecyclePrefixResult trace algorithm}
    (hr : r ∈ evaluation.prefixes.elements) :
    f r.cost ≤ f evaluation.total := by
  rw [evaluation.totalExact]
  exact Cost.le_sumLifecycle_add_coord f hzero hcomb (List.mem_map_of_mem hr)

/-- The same for a maximum-folded coordinate. -/
theorem prefix_le_total_max_coord (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat)
    (hzero : f Cost.LifecycleVector.zero = 0)
    (hcomb : ∀ a b, f (Cost.LifecycleVector.combine a b) = max (f a) (f b))
    {r : LifecyclePrefixResult trace algorithm}
    (hr : r ∈ evaluation.prefixes.elements) :
    f r.cost ≤ f evaluation.total := by
  rw [evaluation.totalExact]
  exact Cost.le_sumLifecycle_max_coord f hzero hcomb (List.mem_map_of_mem hr)

/-- Sealing steps are conserved: no seal's charge escapes the total. -/
theorem sealSteps_le_total (evaluation : LifecycleEvaluation trace algorithm)
    {r : LifecyclePrefixResult trace algorithm}
    (hr : r ∈ evaluation.prefixes.elements) :
    r.cost.sealSteps ≤ evaluation.total.sealSteps :=
  evaluation.prefix_le_total_add_coord _ rfl (fun _ _ => rfl) hr

/-- Retained-state bytes are conserved as a maximum, exactly as SPEC 16's fold
prescribes. -/
theorem retainedStateBytes_le_total (evaluation : LifecycleEvaluation trace algorithm)
    {r : LifecyclePrefixResult trace algorithm}
    (hr : r ∈ evaluation.prefixes.elements) :
    r.cost.retainedStateBytes ≤ evaluation.total.retainedStateBytes :=
  evaluation.prefix_le_total_max_coord _ rfl (fun _ _ => rfl) hr

/-- The recorded size vector is the replay's size vector. -/
theorem size_eq (evaluation : LifecycleEvaluation trace algorithm) :
    evaluation.size = trace.lifecycleSize algorithm evaluation.prefixes :=
  evaluation.sizeExact

/-- **The evaluation is determined by the trace and the strategy.**  Two
evaluations of the same trace under the same strategy that cover the prefixes
identically agree on every prefix result, hence on the total and the size. -/
theorem eq_of_prefixes_eq {a b : LifecycleEvaluation trace algorithm}
    (h : a.prefixes = b.prefixes) : a = b := by
  obtain ⟨pa, ca, sa, ea, ta, ka⟩ := a
  obtain ⟨pb, cb, sb, eb, tb, kb⟩ := b
  simp only at h
  subst h
  have hs : sa = sb := by rw [ea, eb]
  have ht : ta = tb := by rw [ka, kb]
  subst hs; subst ht
  rfl

end LifecycleEvaluation

/-! ## Amortization (SPEC 16)

"An amortized statement SHALL divide only the exact summed numerator by the
explicit positive `body.horizon`; it SHALL retain the nonamortized total and
every prefix result."  The definition below takes the evaluation itself, so
every prefix result and the nonamortized total are retained by construction, and
it is only defined for a positive horizon. -/

/-- The amortized charge of an additively folded coordinate over an explicitly
positive horizon.  The evaluation — hence the nonamortized total and every
prefix result — is retained. -/
def amortized {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
    {algorithm : LifecycleAlgorithmTag}
    (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat) (_hpos : 0 < body.horizon) : Nat :=
  f evaluation.total / body.horizon

/-- The amortized value never exceeds the nonamortized one: division is by a
positive horizon, and the total is retained. -/
theorem amortized_le_total {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat) (hpos : 0 < body.horizon) :
    amortized evaluation f hpos ≤ f evaluation.total :=
  Nat.div_le_self _ _

/-- The amortized value really is the exact summed numerator divided by the
explicit horizon: nothing else is divided. -/
theorem amortized_eq {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {algorithm : LifecycleAlgorithmTag}
    (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat) (hpos : 0 < body.horizon) :
    amortized evaluation f hpos =
      f (Cost.sumLifecycle (evaluation.prefixes.elements.map (fun r => r.cost)))
        / body.horizon := by
  rw [amortized, evaluation.totalExact]

/-! ## The native lifecycle bound (SPEC 16)

`Atlas.lifecycle_native_bound` was omitted from earlier versions of this file on
the ground that the inequality "is false for an arbitrary primitive-cost table
and an arbitrary trace: the coefficients must dominate the per-prefix charges,
which is a property of a *release* table this repository has not pinned."  The
first half of that was right and the second half was the fix rather than an
obstacle: SPEC 16 states the theorem over `Release.primitiveCostTable`, not over
an arbitrary table, so the table is now pinned — in `Cost/Lifecycle.lean`, at the
bottom of the import graph, for the reason its docstring gives — and the
inequality is proved over it.

The pinned table has **every coefficient equal to `1`**, which is the
componentwise-minimal positive table SPEC 16 allows.  The bound is therefore not
true by inflation: `lifecycle_native_bound_of_positive` proves it for *every*
positive table, and `Release.primitiveCostTable_minimal` records that the pinned
one is dominated by all of them.

The real content is the block of exact accounting identities below.  Each one
computes a coordinate of the lifecycle total as a coordinate (or a sum of two
coordinates) of the size vector, using only `CoversExactlyEveryPrefix` — the fact
that the family's ordinals are exactly `0, …, horizon`, once each, in order.  The
inequality then follows coordinate by coordinate from positivity alone.  Because
the identities are equalities, `lifecycle_native_bound_attained` can state
exactly where the bound is tight (fourteen of the seventeen coordinates) and
`lifecycle_native_bound_slack` exactly how loose the other three are. -/

/-- The charges recorded by a prefix family are the replay's charges at that
family's ordinals.  This is `LifecyclePrefixResult.exactCost`, lifted from one
prefix to the family, and it is what lets the whole fold be computed from the
trace alone. -/
theorem prefixCosts_eq {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) (algorithm : LifecycleAlgorithmTag)
    (prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm)) :
    prefixes.elements.map (fun r => r.cost)
      = (prefixes.elements.map (fun r => r.prefixOrdinal.val)).map
          (trace.prefixCost algorithm) := by
  rw [List.map_map]
  exact List.map_congr_left (fun r _ => r.cost_eq)

/-- With the prefix cover, the charges are the replay's charges at
`0, 1, …, horizon`, in that order and once each. -/
theorem prefixCosts_eq_range {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) (algorithm : LifecycleAlgorithmTag)
    (prefixes : PrefixOrderedList (LifecyclePrefixResult trace algorithm))
    (hcover : CoversExactlyEveryPrefix prefixes) :
    prefixes.elements.map (fun r => r.cost)
      = (List.range (body.horizon + 1)).map (trace.prefixCost algorithm) := by
  rw [prefixCosts_eq, hcover]

namespace LifecycleEvaluation

variable {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
  {algorithm : LifecycleAlgorithmTag}

/-! ### Reading a coordinate of the total, and of the size vector, off the replay -/

/-- An additively folded coordinate of the total is the prefix-ordered sum of
that coordinate of the replay's charges. -/
theorem total_add_coord_eq (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat)
    (hzero : f Cost.LifecycleVector.zero = 0)
    (hcomb : ∀ a b, f (Cost.LifecycleVector.combine a b) = f a + f b) :
    f evaluation.total
      = ((List.range (body.horizon + 1)).map
          (fun n => f (trace.prefixCost algorithm n))).sum := by
  rw [evaluation.totalExact, Cost.sumLifecycle_add_coord f hzero hcomb,
    prefixCosts_eq_range trace algorithm evaluation.prefixes evaluation.exactPrefixCover,
    List.map_map]
  rfl

/-- A maximum-folded coordinate of the total is the maximum of that coordinate
of the replay's charges. -/
theorem total_max_coord_eq (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat)
    (hzero : f Cost.LifecycleVector.zero = 0)
    (hcomb : ∀ a b, f (Cost.LifecycleVector.combine a b) = max (f a) (f b)) :
    f evaluation.total
      = Cost.maxOf ((List.range (body.horizon + 1)).map
          (fun n => f (trace.prefixCost algorithm n))) := by
  rw [evaluation.totalExact, Cost.sumLifecycle_max_coord f hzero hcomb,
    prefixCosts_eq_range trace algorithm evaluation.prefixes evaluation.exactPrefixCover,
    List.map_map]
  rfl

/-- A size coordinate that `lifecycleSize` defines as a sum over the family's
charges is the same prefix-ordered sum. -/
theorem size_cost_coord_eq (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat) (g : LifecycleSizeVector → Nat)
    (hg : ∀ p : PrefixOrderedList (LifecyclePrefixResult trace algorithm),
      g (trace.lifecycleSize algorithm p)
        = ((p.elements.map (fun r => r.cost)).map f).sum) :
    g evaluation.size
      = ((List.range (body.horizon + 1)).map
          (fun n => f (trace.prefixCost algorithm n))).sum := by
  rw [evaluation.size_eq, hg,
    prefixCosts_eq_range trace algorithm evaluation.prefixes evaluation.exactPrefixCover,
    List.map_map]
  rfl

/-- The same for a size coordinate defined as a maximum over the charges. -/
theorem size_cost_max_coord_eq (evaluation : LifecycleEvaluation trace algorithm)
    (f : Cost.LifecycleVector → Nat) (g : LifecycleSizeVector → Nat)
    (hg : ∀ p : PrefixOrderedList (LifecyclePrefixResult trace algorithm),
      g (trace.lifecycleSize algorithm p)
        = Cost.maxOf ((p.elements.map (fun r => r.cost)).map f)) :
    g evaluation.size
      = Cost.maxOf ((List.range (body.horizon + 1)).map
          (fun n => f (trace.prefixCost algorithm n))) := by
  rw [evaluation.size_eq, hg,
    prefixCosts_eq_range trace algorithm evaluation.prefixes evaluation.exactPrefixCover,
    List.map_map]
  rfl

/-- A size coordinate that `lifecycleSize` defines as a sum over the family's
*ordinals* is the sum over `0, …, horizon`. -/
theorem size_ordinal_coord_eq (evaluation : LifecycleEvaluation trace algorithm)
    (φ : Nat → Nat) (g : LifecycleSizeVector → Nat)
    (hg : ∀ p : PrefixOrderedList (LifecyclePrefixResult trace algorithm),
      g (trace.lifecycleSize algorithm p)
        = ((p.elements.map (fun r => r.prefixOrdinal.val)).map φ).sum) :
    g evaluation.size = ((List.range (body.horizon + 1)).map φ).sum := by
  rw [evaluation.size_eq, hg, evaluation.exactPrefixCover]

/-- The seal count is the number of sealing prefixes among `0, …, horizon`. -/
theorem size_sealCount_eq (evaluation : LifecycleEvaluation trace algorithm) :
    evaluation.size.sealCount
      = ((List.range (body.horizon + 1)).filter
          (fun n => trace.isSealPoint n)).length := by
  have h : evaluation.size.sealCount
      = ((evaluation.prefixes.elements.map (fun r => r.prefixOrdinal.val)).filter
          (fun n => trace.isSealPoint n)).length := by
    rw [evaluation.size_eq]; rfl
  rw [h, evaluation.exactPrefixCover]

/-! ### The exact accounting identities of a native lifecycle

Each of these is an equality, not a bound.  Together they say precisely what a
native lifecycle total is in terms of its own size vector; `lifecycle_native_bound`
is then arithmetic on positive coefficients. -/

/-- Authority checking is charged once, at prefix `0`, on the initial
declaration base — and `authorityBytesChecked` is exactly that byte count.  This
is the one identity that needs the prefix cover to be *duplicate free*: a family
that repeated prefix `0` would charge the base twice. -/
theorem native_authorityCheckSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.authorityCheckSteps = evaluation.size.authorityBytesChecked := by
  have ht : evaluation.total.authorityCheckSteps
      = ((List.range (body.horizon + 1)).map
          (fun n => if n = 0 then
            ResolvedLifecycleTrace.declarationBytes
              trace.initialState.body.declarationBase.declarations else 0)).sum :=
    evaluation.total_add_coord_eq (fun v => v.authorityCheckSteps) rfl (fun _ _ => rfl)
  have hs : evaluation.size.authorityBytesChecked
      = ResolvedLifecycleTrace.declarationBytes
          trace.initialState.body.declarationBase.declarations := by
    rw [evaluation.size_eq]; rfl
  rw [ht, hs, Cost.sum_range_guarded_zero,
    if_neg (by omega : ¬ (body.horizon + 1 = 0))]

/-- The native operator canonicalizes exactly the novel declarations of each
selected delta, and `deltaBytes` is their total size. -/
theorem native_canonicalizationSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.canonicalizationSteps = evaluation.size.deltaBytes := by
  have ht : evaluation.total.canonicalizationSteps
      = ((List.range (body.horizon + 1)).map
          (fun n => ResolvedLifecycleTrace.declarationBytes
            (trace.novelDeclarationsAt n))).sum :=
    evaluation.total_add_coord_eq (fun v => v.canonicalizationSteps) rfl (fun _ _ => rfl)
  have hs : evaluation.size.deltaBytes
      = ((List.range (body.horizon + 1)).map
          (fun n => ResolvedLifecycleTrace.declarationBytes
            (trace.novelDeclarationsAt n))).sum :=
    evaluation.size_ordinal_coord_eq _ (fun s => s.deltaBytes) (fun _ => rfl)
  rw [ht, hs]

theorem native_canonicalNovelObjects_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.canonicalNovelObjects = evaluation.size.canonicalNovelObjects :=
  (evaluation.total_add_coord_eq (fun v => v.canonicalNovelObjects) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.canonicalNovelObjects)
      (fun s => s.canonicalNovelObjects) (fun _ => rfl)).symm

theorem native_canonicalNovelEdges_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.canonicalNovelEdges = evaluation.size.canonicalNovelEdges :=
  (evaluation.total_add_coord_eq (fun v => v.canonicalNovelEdges) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.canonicalNovelEdges)
      (fun s => s.canonicalNovelEdges) (fun _ => rfl)).symm

theorem native_closureSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.closureSteps = evaluation.size.closureDerivations :=
  (evaluation.total_add_coord_eq (fun v => v.closureSteps) rfl (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.closureSteps)
      (fun s => s.closureDerivations) (fun _ => rfl)).symm

/-- Indexing is charged once per novel declaration, which is also what
`canonicalNovelObjects` counts. -/
theorem native_indexSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.indexSteps = evaluation.size.canonicalNovelObjects := by
  have ht : evaluation.total.indexSteps
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.total_add_coord_eq (fun v => v.indexSteps) rfl (fun _ _ => rfl)
  have hs : evaluation.size.canonicalNovelObjects
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.size_cost_coord_eq (fun v => v.canonicalNovelObjects)
      (fun s => s.canonicalNovelObjects) (fun _ => rfl)
  rw [ht, hs]

theorem native_attentionBucketsTouched_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.attentionBucketsTouched = evaluation.size.attentionBucketsTouched :=
  (evaluation.total_add_coord_eq (fun v => v.attentionBucketsTouched) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.attentionBucketsTouched)
      (fun s => s.attentionBucketsTouched) (fun _ => rfl)).symm

theorem native_dependencyObjectsVisited_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.dependencyObjectsVisited = evaluation.size.dependencyImpactObjects :=
  (evaluation.total_add_coord_eq (fun v => v.dependencyObjectsVisited) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.dependencyObjectsVisited)
      (fun s => s.dependencyImpactObjects) (fun _ => rfl)).symm

/-- **The lifecycle replay performs no partition work.**  Recorded as an
equality rather than hidden inside the bound: the `cPartition` coordinate of
`nativeLifecycleBound` is currently bounding zero. -/
theorem native_partitionSteps_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.partitionSteps = 0 := by
  have ht : evaluation.total.partitionSteps
      = ((List.range (body.horizon + 1)).map (fun _ => (0 : Nat))).sum :=
    evaluation.total_add_coord_eq (fun v => v.partitionSteps) rfl (fun _ _ => rfl)
  rw [ht, Cost.sum_map_zero]

theorem native_size_partitionCellsChanged_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.size.partitionCellsChanged = 0 := by
  have hs : evaluation.size.partitionCellsChanged
      = ((List.range (body.horizon + 1)).map (fun _ => (0 : Nat))).sum :=
    evaluation.size_cost_coord_eq (fun v => v.partitionCellsChanged)
      (fun s => s.partitionCellsChanged) (fun _ => rfl)
  rw [hs, Cost.sum_map_zero]

theorem native_partitionCellsChanged_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.partitionCellsChanged = evaluation.size.partitionCellsChanged :=
  (evaluation.total_add_coord_eq (fun v => v.partitionCellsChanged) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.partitionCellsChanged)
      (fun s => s.partitionCellsChanged) (fun _ => rfl)).symm

theorem native_verifierSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.verifierSteps = evaluation.size.certificateBytesChecked :=
  (evaluation.total_add_coord_eq (fun v => v.verifierSteps) rfl (fun _ _ => rfl)).trans
    (evaluation.size_cost_coord_eq (fun v => v.verifierSteps)
      (fun s => s.certificateBytesChecked) (fun _ => rfl)).symm

/-- A sealing prefix charges one seal plus a scan of the retained base, and the
two size coordinates are exactly the seal count and the cumulative scan. -/
theorem native_sealSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.sealSteps
      = evaluation.size.sealCount + evaluation.size.sealInputBytesScanned := by
  have ht : evaluation.total.sealSteps
      = ((List.range (body.horizon + 1)).map
          (fun n => if trace.isSealPoint n then
            1 + ResolvedLifecycleTrace.declarationBytes
                  (trace.accumulatedDeclarations n).declarations
            else 0)).sum :=
    evaluation.total_add_coord_eq (fun v => v.sealSteps) rfl (fun _ _ => rfl)
  have hscan : evaluation.size.sealInputBytesScanned
      = ((List.range (body.horizon + 1)).map
          (fun n => if trace.isSealPoint n then
            ResolvedLifecycleTrace.declarationBytes
                  (trace.accumulatedDeclarations n).declarations
            else 0)).sum :=
    evaluation.size_ordinal_coord_eq _ (fun s => s.sealInputBytesScanned) (fun _ => rfl)
  rw [ht, Cost.sum_map_guarded_succ (fun n => trace.isSealPoint n)
      (fun n => ResolvedLifecycleTrace.declarationBytes
        (trace.accumulatedDeclarations n).declarations),
    ← hscan, ← evaluation.size_sealCount_eq]

/-- Query work is one step per scheduled request plus one per routed target.
`requestBytesChecked` is charged by the polynomial and by nothing in the
replay — that is the query bracket's slack, and it is visible here. -/
theorem native_querySelectionSteps_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.querySelectionSteps
      = evaluation.size.queryCount + evaluation.size.attentionCandidatesVisited := by
  have ht : evaluation.total.querySelectionSteps
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.scheduledRequests n).length
            + ((trace.scheduledRequests n).map
                (fun r =>
                  (attendTargets (trace.bodyAt .nativeIncremental n) r).length)).sum)).sum :=
    evaluation.total_add_coord_eq (fun v => v.querySelectionSteps) rfl (fun _ _ => rfl)
  have hq : evaluation.size.queryCount
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.scheduledRequests n).length)).sum :=
    evaluation.size_ordinal_coord_eq _ (fun s => s.queryCount) (fun _ => rfl)
  have ha : evaluation.size.attentionCandidatesVisited
      = ((List.range (body.horizon + 1)).map
          (fun n => ((trace.scheduledRequests n).map
            (fun r =>
              (attendTargets (trace.bodyAt .nativeIncremental n) r).length)).sum)).sum :=
    evaluation.size_ordinal_coord_eq _ (fun s => s.attentionCandidatesVisited)
      (fun _ => rfl)
  rw [ht, Cost.sum_map_add (fun n => (trace.scheduledRequests n).length)
      (fun n => ((trace.scheduledRequests n).map
        (fun r => (attendTargets (trace.bodyAt .nativeIncremental n) r).length)).sum),
    ← hq, ← ha]

/-- **The lifecycle replay performs no migration.**  Recorded, not hidden. -/
theorem native_migrationSteps_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.migrationSteps = 0 := by
  have ht : evaluation.total.migrationSteps
      = ((List.range (body.horizon + 1)).map (fun _ => (0 : Nat))).sum :=
    evaluation.total_add_coord_eq (fun v => v.migrationSteps) rfl (fun _ _ => rfl)
  rw [ht, Cost.sum_map_zero]

theorem native_size_migrationObjects_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.size.migrationObjects = 0 := by
  rw [evaluation.size_eq]; rfl

theorem native_retainedStateBytes_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.retainedStateBytes = evaluation.size.retainedStateBytes :=
  (evaluation.total_max_coord_eq (fun v => v.retainedStateBytes) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_max_coord_eq (fun v => v.retainedStateBytes)
      (fun s => s.retainedStateBytes) (fun _ => rfl)).symm

theorem native_peakWorkingBytes_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.peakWorkingBytes = evaluation.size.peakWorkingBytes :=
  (evaluation.total_max_coord_eq (fun v => v.peakWorkingBytes) rfl
      (fun _ _ => rfl)).trans
    (evaluation.size_cost_max_coord_eq (fun v => v.peakWorkingBytes)
      (fun s => s.peakWorkingBytes) (fun _ => rfl)).symm

/-- **A lifecycle charges no artifact cost.**  SPEC 9.2 keeps the two cost
models apart, and the lifecycle replay respects that: every prefix charges
`Cost.ArtifactVector.zero`, so the folded artifact vector is zero on all
thirty-six coordinates, sums and peaks alike. -/
theorem native_artifact_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.artifact = Cost.ArtifactVector.zero := by
  refine Cost.ArtifactVector.coords_injective (fun co => ?_)
  rw [Cost.ArtifactCoordinate.value_zero]
  have hz : ((List.range (body.horizon + 1)).map
        (fun n => co.value (trace.prefixCost .nativeIncremental n).artifact))
      = (List.range (body.horizon + 1)).map (fun _ => (0 : Nat)) :=
    List.map_congr_left (fun _ _ => Cost.ArtifactCoordinate.value_zero co)
  cases hmax : co.IsDynamicMax with
  | false =>
      have ht : co.value evaluation.total.artifact
          = ((List.range (body.horizon + 1)).map
              (fun n => co.value (trace.prefixCost .nativeIncremental n).artifact)).sum :=
        evaluation.total_add_coord_eq (fun v => co.value v.artifact)
          (Cost.ArtifactCoordinate.value_zero co)
          (fun _ _ => by cases co <;> first | rfl | exact absurd hmax (by decide))
      rw [ht, hz]
      exact Cost.sum_map_zero _
  | true =>
      have ht : co.value evaluation.total.artifact
          = Cost.maxOf ((List.range (body.horizon + 1)).map
              (fun n => co.value (trace.prefixCost .nativeIncremental n).artifact)) :=
        evaluation.total_max_coord_eq (fun v => co.value v.artifact)
          (Cost.ArtifactCoordinate.value_zero co)
          (fun _ _ => by cases co <;> first | rfl | exact absurd hmax (by decide))
      rw [ht, hz]
      exact Cost.maxOf_map_zero _

theorem native_size_artifactWork_eq_zero
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.size.artifactWork = Cost.ArtifactVector.zero := by
  rw [evaluation.size_eq]; rfl

/-- The three novelty coordinates of the size vector coincide: each counts the
novel declarations of the trace.  This is why the polynomial's index bracket
over-counts threefold. -/
theorem native_size_canonicalNovelEdges_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.size.canonicalNovelEdges = evaluation.size.canonicalNovelObjects := by
  have h1 : evaluation.size.canonicalNovelEdges
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.size_cost_coord_eq (fun v => v.canonicalNovelEdges)
      (fun s => s.canonicalNovelEdges) (fun _ => rfl)
  have h2 : evaluation.size.canonicalNovelObjects
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.size_cost_coord_eq (fun v => v.canonicalNovelObjects)
      (fun s => s.canonicalNovelObjects) (fun _ => rfl)
  rw [h1, h2]

theorem native_size_attentionBucketsTouched_eq
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.size.attentionBucketsTouched = evaluation.size.canonicalNovelObjects := by
  have h1 : evaluation.size.attentionBucketsTouched
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.size_cost_coord_eq (fun v => v.attentionBucketsTouched)
      (fun s => s.attentionBucketsTouched) (fun _ => rfl)
  have h2 : evaluation.size.canonicalNovelObjects
      = ((List.range (body.horizon + 1)).map
          (fun n => (trace.prefixCost .nativeIncremental n).canonicalNovelObjects)).sum :=
    evaluation.size_cost_coord_eq (fun v => v.canonicalNovelObjects)
      (fun s => s.canonicalNovelObjects) (fun _ => rfl)
  rw [h1, h2]

end LifecycleEvaluation

/--
  **The native lifecycle bound over an arbitrary positive primitive-cost
  table.**

  This is the whole mathematical content of `lifecycle_native_bound`: given only
  that every coefficient of the table is at least one, the frozen fold of a
  native lifecycle's prefix charges is componentwise under the polynomial of its
  own size vector.  No property of any particular table is used, so the release
  table cannot have been chosen to make the statement true.

  The proof is the block of exact accounting identities above, followed by
  `Nat.le_mul_of_pos_left` on each coordinate.  Two coordinates
  (`partitionSteps`, `migrationSteps`) are bounded because the replay charges
  nothing there; that is recorded explicitly rather than absorbed.
-/
theorem lifecycle_native_bound_of_positive {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} (table : Cost.PrimitiveCostTable)
    (hpos : table.AllCoefficientsPositive)
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total ≤ nativeLifecycleBound table evaluation.size := by
  obtain ⟨hAuth, hCanon, hClos, hIdx, hDep, _hPart, hVer, hSeal, hScan, hQuery,
    _hMig⟩ := hpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show evaluation.total.authorityCheckSteps
        ≤ table.cAuthority * evaluation.size.authorityBytesChecked
    rw [evaluation.native_authorityCheckSteps_eq]
    exact Nat.le_mul_of_pos_left _ hAuth
  · show evaluation.total.canonicalizationSteps
        ≤ table.cCanonicalize * evaluation.size.deltaBytes
            * (Nat.log2 (evaluation.size.retainedStateBytes + 2) + 1)
    rw [evaluation.native_canonicalizationSteps_eq]
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ hCanon)
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  · exact Nat.le_of_eq evaluation.native_canonicalNovelObjects_eq
  · exact Nat.le_of_eq evaluation.native_canonicalNovelEdges_eq
  · show evaluation.total.closureSteps
        ≤ table.cClosure * evaluation.size.closureDerivations
    rw [evaluation.native_closureSteps_eq]
    exact Nat.le_mul_of_pos_left _ hClos
  · show evaluation.total.indexSteps
        ≤ table.cIndex * (evaluation.size.canonicalNovelObjects
            + evaluation.size.canonicalNovelEdges + evaluation.size.attentionBucketsTouched)
    rw [evaluation.native_indexSteps_eq]
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ hIdx)
    omega
  · exact Nat.le_of_eq evaluation.native_attentionBucketsTouched_eq
  · show evaluation.total.dependencyObjectsVisited
        ≤ table.cDependency * evaluation.size.dependencyImpactObjects
    rw [evaluation.native_dependencyObjectsVisited_eq]
    exact Nat.le_mul_of_pos_left _ hDep
  · rw [evaluation.native_partitionSteps_eq_zero]
    exact Nat.zero_le _
  · exact Nat.le_of_eq evaluation.native_partitionCellsChanged_eq
  · show evaluation.total.verifierSteps
        ≤ table.cVerify * evaluation.size.certificateBytesChecked
    rw [evaluation.native_verifierSteps_eq]
    exact Nat.le_mul_of_pos_left _ hVer
  · show evaluation.total.sealSteps
        ≤ table.cSeal * evaluation.size.sealCount
          + table.cSealScan * evaluation.size.sealInputBytesScanned
    rw [evaluation.native_sealSteps_eq]
    exact Nat.add_le_add (Nat.le_mul_of_pos_left _ hSeal)
      (Nat.le_mul_of_pos_left _ hScan)
  · show evaluation.total.querySelectionSteps
        ≤ table.cQuery * (evaluation.size.queryCount + evaluation.size.requestBytesChecked
            + evaluation.size.attentionCandidatesVisited)
    rw [evaluation.native_querySelectionSteps_eq]
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ hQuery)
    omega
  · rw [evaluation.native_migrationSteps_eq_zero]
    exact Nat.zero_le _
  · exact Nat.le_of_eq evaluation.native_retainedStateBytes_eq
  · exact Nat.le_of_eq evaluation.native_peakWorkingBytes_eq
  · show Cost.ComponentwiseLE evaluation.total.artifact evaluation.size.artifactWork
    rw [evaluation.native_artifact_eq_zero, evaluation.native_size_artifactWork_eq_zero]
    exact Cost.componentwiseLE_refl _

/--
  **SPEC 16**, `Atlas.lifecycle_native_bound`, quoted verbatim:

  ```lean
  theorem lifecycle_native_bound
      {body : Atlas.LifecycleTraceBody}
      {trace : Atlas.ResolvedLifecycleTrace body}
      (evaluation : Atlas.LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total ≤
      Atlas.nativeLifecycleBound Release.primitiveCostTable evaluation.size
  ```

  ### What this bound actually constrains

  `≤` is `Cost.LifecycleVector.ComponentwiseLE`: all seventeen coordinates at
  once, with no trade between them.  `Release.primitiveCostTable` has every
  coefficient equal to `1`, the componentwise-minimal positive table SPEC 16
  admits, and `lifecycle_native_bound_of_positive` proves the same inequality for
  every positive table — so no coefficient was inflated to make this true.

  Neither side of the inequality is free.  `evaluation.total` is pinned by
  `totalExact` to the frozen fold of the prefix charges, and `evaluation.size` is
  pinned by `VerifiesLifecycleSize` to `lifecycleSize` of that same family — a
  recomputation over the trace, not a number an implementor may choose.  The
  bound therefore cannot be satisfied by reporting a large size vector, and the
  proof does not use the structure fields as assumptions: it recomputes both
  sides from `trace.prefixCost` and compares them.

  **Fourteen of the seventeen coordinates are attained with equality**
  (`lifecycle_native_bound_attained`): authority checking, both novelty counts,
  closure, attention buckets, dependency invalidation, both partition
  coordinates, verification, sealing, migration, retained-state bytes,
  peak-working bytes and artifact work.  On those the bound is not a bound at
  all; it is the exact accounting identity.

  **Three coordinates are loose, and `lifecycle_native_bound_slack` says by
  exactly how much:**

  * `canonicalizationSteps` — the polynomial multiplies the charged delta bytes
    by `log2 (retainedStateBytes + 2) + 1`, a factor of at least `2`, which the
    incremental replay never spends.  The factor is SPEC 16's, not this
    repository's: it is in the fixed shape of `Cost.nativeLifecycleBound`, and it
    cannot be removed without amending SPEC.
  * `indexSteps` — the polynomial's bracket is `canonicalNovelObjects +
    canonicalNovelEdges + attentionBucketsTouched`, and on a lifecycle all three
    count the same novel declarations, so the bracket is exactly three times the
    charge.
  * `querySelectionSteps` — the polynomial's bracket adds `requestBytesChecked`,
    which the replay's query charge does not contain at all.

  Each of those three is slack in SPEC's *polynomial shape*, not slack bought by
  a coefficient.  With coefficients pinned at `1` there is no smaller positive
  table, so this is the tightest form of SPEC 16's statement that exists.

  **How much of this inequality has content, counted honestly.**  Adversarial
  review made the sharpest available criticism of this theorem, and it is right,
  so it is recorded here rather than left for a reader to find.

  `ResolvedLifecycleTrace.lifecycleSize` *defines* nine of its coordinates as the
  sum — or, for the two peak coordinates, the maximum — of the very prefix-cost
  coordinate the polynomial then bounds:

      canonicalNovelObjects   canonicalNovelEdges
      closureDerivations := Σ closureSteps
      attentionBucketsTouched
      dependencyImpactObjects := Σ dependencyObjectsVisited
      partitionCellsChanged
      certificateBytesChecked := Σ verifierSteps
      retainedStateBytes      peakWorkingBytes

  On those nine, with the coefficient pinned at `1`, the inequality is literally
  `x ≤ x`.  It would hold for **any** cost model whatsoever — one charging zero,
  or one charging absurdly — so on those coordinates the theorem measures the
  size vector against itself and says nothing about the algorithm.  Three more
  (`partitionSteps`, `migrationSteps`, `artifact`) are `0 ≤ 0` because the replay
  charges nothing there.

  Only **four of seventeen** coordinates relate the charged total to an
  independent, trace-derived measure: `authorityCheckSteps` against the initial
  base's `declarationBytes`, `canonicalizationSteps` against `deltaBytes`,
  `sealSteps` against `sealCount + sealInputBytesScanned`, and
  `querySelectionSteps` against `queryCount + attentionCandidatesVisited`.

  So "fourteen of seventeen coordinates hold with equality" is true and is the
  wrong thing to be impressed by: nine of those fourteen are equalities of the
  size vector's own definition.  This is a property of SPEC 16's carrier, not of
  the proof — `lifecycleSize` is the size notion SPEC fixes — but a reader
  entitled to know what the bound constrains is entitled to know this.

  What is *not* claimed: that these coefficients are calibrated machine costs.
  Nothing in this repository measures the wall-clock price of a closure
  derivation, and `Release.primitiveCostTable`'s docstring says so.
-/
theorem lifecycle_native_bound {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body}
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total ≤ nativeLifecycleBound Release.primitiveCostTable evaluation.size :=
  lifecycle_native_bound_of_positive Release.primitiveCostTable
    Release.primitiveCostTable_positive evaluation

/-- **Where the native bound is tight.**  Fourteen of the seventeen coordinates
of `lifecycle_native_bound` hold with equality at the release table, so the
theorem is not made true by slack on them.  Stated as equalities against the
bound itself, not against the size vector, so that a later change to a
coefficient would break this. -/
theorem lifecycle_native_bound_attained {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body}
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    evaluation.total.authorityCheckSteps
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).authorityCheckSteps ∧
    evaluation.total.canonicalNovelObjects
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).canonicalNovelObjects ∧
    evaluation.total.canonicalNovelEdges
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).canonicalNovelEdges ∧
    evaluation.total.closureSteps
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).closureSteps ∧
    evaluation.total.attentionBucketsTouched
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).attentionBucketsTouched ∧
    evaluation.total.dependencyObjectsVisited
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).dependencyObjectsVisited ∧
    evaluation.total.partitionSteps
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).partitionSteps ∧
    evaluation.total.partitionCellsChanged
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).partitionCellsChanged ∧
    evaluation.total.verifierSteps
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).verifierSteps ∧
    evaluation.total.sealSteps
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).sealSteps ∧
    evaluation.total.migrationSteps
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).migrationSteps ∧
    evaluation.total.retainedStateBytes
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).retainedStateBytes ∧
    evaluation.total.peakWorkingBytes
        = (nativeLifecycleBound Release.primitiveCostTable
            evaluation.size).peakWorkingBytes ∧
    evaluation.total.artifact
        = (nativeLifecycleBound Release.primitiveCostTable evaluation.size).artifact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show evaluation.total.authorityCheckSteps = 1 * evaluation.size.authorityBytesChecked
    rw [Nat.one_mul]; exact evaluation.native_authorityCheckSteps_eq
  · exact evaluation.native_canonicalNovelObjects_eq
  · exact evaluation.native_canonicalNovelEdges_eq
  · show evaluation.total.closureSteps = 1 * evaluation.size.closureDerivations
    rw [Nat.one_mul]; exact evaluation.native_closureSteps_eq
  · exact evaluation.native_attentionBucketsTouched_eq
  · show evaluation.total.dependencyObjectsVisited
        = 1 * evaluation.size.dependencyImpactObjects
    rw [Nat.one_mul]; exact evaluation.native_dependencyObjectsVisited_eq
  · show evaluation.total.partitionSteps = 1 * evaluation.size.partitionCellsChanged
    rw [Nat.one_mul, evaluation.native_size_partitionCellsChanged_eq_zero]
    exact evaluation.native_partitionSteps_eq_zero
  · exact evaluation.native_partitionCellsChanged_eq
  · show evaluation.total.verifierSteps = 1 * evaluation.size.certificateBytesChecked
    rw [Nat.one_mul]; exact evaluation.native_verifierSteps_eq
  · show evaluation.total.sealSteps
        = 1 * evaluation.size.sealCount + 1 * evaluation.size.sealInputBytesScanned
    rw [Nat.one_mul, Nat.one_mul]; exact evaluation.native_sealSteps_eq
  · show evaluation.total.migrationSteps = 1 * evaluation.size.migrationObjects
    rw [Nat.one_mul, evaluation.native_size_migrationObjects_eq_zero]
    exact evaluation.native_migrationSteps_eq_zero
  · exact evaluation.native_retainedStateBytes_eq
  · exact evaluation.native_peakWorkingBytes_eq
  · show evaluation.total.artifact = evaluation.size.artifactWork
    rw [evaluation.native_artifact_eq_zero, evaluation.native_size_artifactWork_eq_zero]

/-- **Exactly how loose the other three coordinates are.**  Each is slack in the
*shape* of SPEC 16's polynomial, not slack bought by a coefficient: the
logarithmic canonicalization factor, the threefold index bracket, and the
request bytes the query bracket adds and the replay never charges. -/
theorem lifecycle_native_bound_slack {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body}
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    (nativeLifecycleBound Release.primitiveCostTable
        evaluation.size).canonicalizationSteps
      = evaluation.total.canonicalizationSteps
          * (Nat.log2 (evaluation.size.retainedStateBytes + 2) + 1) ∧
    (nativeLifecycleBound Release.primitiveCostTable evaluation.size).indexSteps
      = 3 * evaluation.total.indexSteps ∧
    (nativeLifecycleBound Release.primitiveCostTable
        evaluation.size).querySelectionSteps
      = evaluation.total.querySelectionSteps + evaluation.size.requestBytesChecked := by
  refine ⟨?_, ?_, ?_⟩
  · show 1 * evaluation.size.deltaBytes
          * (Nat.log2 (evaluation.size.retainedStateBytes + 2) + 1)
        = evaluation.total.canonicalizationSteps
          * (Nat.log2 (evaluation.size.retainedStateBytes + 2) + 1)
    rw [Nat.one_mul, evaluation.native_canonicalizationSteps_eq]
  · show 1 * (evaluation.size.canonicalNovelObjects + evaluation.size.canonicalNovelEdges
          + evaluation.size.attentionBucketsTouched)
        = 3 * evaluation.total.indexSteps
    rw [evaluation.native_size_canonicalNovelEdges_eq,
      evaluation.native_size_attentionBucketsTouched_eq,
      evaluation.native_indexSteps_eq]
    omega
  · show 1 * (evaluation.size.queryCount + evaluation.size.requestBytesChecked
          + evaluation.size.attentionCandidatesVisited)
        = evaluation.total.querySelectionSteps + evaluation.size.requestBytesChecked
    rw [evaluation.native_querySelectionSteps_eq]
    omega

/-! ## The comparator strategy, replayed (SPEC 16)

`Atlas.canonicalFullRebuildEvaluation` is a *total* constructor: it produces a
full-rebuild evaluation of every resolved trace, with no hypothesis and no
stored conclusion.  Every field of every prefix result is the replay's own
value, so each `Verifies…` obligation is discharged by `rfl` — a recomputation
that happens to be syntactically trivial, not an assumption.

An earlier note in this file recorded this construction as blocked, on the
grounds that the evaluation's `size` field "would then have to be verified
against `lifecycleSize`, which is a computation over the whole trace".  That
note was over-cautious and is withdrawn.  `VerifiesLifecycleSize trace prefixes
size` is *defined* as `size = trace.lifecycleSize algorithm prefixes`, so taking
the size to be that computation discharges the obligation definitionally; the
computation is performed, not asserted.  The same is true of `totalExact`.  The
only real work is the prefix family, and that is `restOrdinals` below. -/

/-- `1, …, k` as elements of `Fin (m + 1)`, in ascending order. -/
def restOrdinals (m : Nat) : (k : Nat) → k ≤ m → List (Fin (m + 1))
  | 0, _ => []
  | k + 1, h =>
      restOrdinals m k (Nat.le_of_succ_le h) ++ [⟨k + 1, Nat.lt_succ_of_le h⟩]

/-- Prefixed by `0`, `restOrdinals m k` is exactly `List.range (k + 1)` — which
is what `CoversExactlyEveryPrefix` demands. -/
theorem restOrdinals_map_val (m : Nat) :
    ∀ (k : Nat) (h : k ≤ m),
      (0 :: (restOrdinals m k h).map Fin.val) = List.range (k + 1) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      show (0 :: ((restOrdinals m j (Nat.le_of_succ_le h) ++
        [(⟨j + 1, Nat.lt_succ_of_le h⟩ : Fin (m + 1))]).map Fin.val)) = _
      rw [List.map_append, ← List.cons_append, ih (Nat.le_of_succ_le h)]
      show List.range (j + 1) ++ [j + 1] = List.range (j + 1 + 1)
      exact (@List.range_succ (j + 1)).symm

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The prefix result the replay itself determines at one ordinal.  Nothing is
chosen: the before/after state identities, the selected delta, the seal, the
query-result identities and the charge are all read off the replay, and both
verifier obligations are therefore definitional. -/
def canonicalPrefixResult (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) (ordinal : Fin (body.horizon + 1)) :
    LifecyclePrefixResult trace algorithm where
  prefixOrdinal := ordinal
  beforeStateId := StateId (trace.bodyAt algorithm (ordinal.val - 1))
  deltaId := (trace.selectedDelta? ordinal.val).map DeltaId
  afterStateId := StateId (trace.bodyAt algorithm ordinal.val)
  sealId := trace.sealIdAt algorithm ordinal.val
  queryResultIds := trace.queryResultIdsAt algorithm ordinal.val
  cost := trace.prefixCost algorithm ordinal.val
  exactTransition := ⟨rfl, rfl, rfl, rfl, rfl⟩
  exactCost := rfl

@[simp] theorem canonicalPrefixResult_prefixOrdinal
    (trace : ResolvedLifecycleTrace body) (algorithm : LifecycleAlgorithmTag)
    (ordinal : Fin (body.horizon + 1)) :
    (trace.canonicalPrefixResult algorithm ordinal).prefixOrdinal = ordinal := rfl

/-- The replayed family, in prefix order: prefix `0`, then `1, …, horizon`. -/
def canonicalPrefixes (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) :
    PrefixOrderedList (LifecyclePrefixResult trace algorithm) where
  head := trace.canonicalPrefixResult algorithm ⟨0, Nat.succ_pos _⟩
  rest := (restOrdinals body.horizon body.horizon (Nat.le_refl _)).map
    (trace.canonicalPrefixResult algorithm)

/-- The replayed family covers exactly every prefix, in order, once each. -/
theorem canonicalPrefixes_covers (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) :
    CoversExactlyEveryPrefix (trace.canonicalPrefixes algorithm) := by
  show (0 :: ((restOrdinals body.horizon body.horizon (Nat.le_refl _)).map
      (trace.canonicalPrefixResult algorithm)).map
        (fun r => r.prefixOrdinal.val)) = List.range (body.horizon + 1)
  rw [List.map_map]
  exact restOrdinals_map_val body.horizon body.horizon (Nat.le_refl _)

/-- The evaluation a trace and a strategy determine.  Total, and every field is
the replay's own: the size vector is `lifecycleSize` of this very family and the
total is `Cost.sumLifecycle` of its costs, so `sizeExact` and `totalExact` are
discharged by computing, never by assuming. -/
def canonicalEvaluation (trace : ResolvedLifecycleTrace body)
    (algorithm : LifecycleAlgorithmTag) : LifecycleEvaluation trace algorithm where
  prefixes := trace.canonicalPrefixes algorithm
  exactPrefixCover := trace.canonicalPrefixes_covers algorithm
  size := trace.lifecycleSize algorithm (trace.canonicalPrefixes algorithm)
  sizeExact := rfl
  total :=
    Cost.sumLifecycle
      ((trace.canonicalPrefixes algorithm).elements.map (fun r => r.cost))
  totalExact := rfl

end ResolvedLifecycleTrace

/--
  **SPEC 16**, `Atlas.canonicalFullRebuildEvaluation`: the comparator evaluation
  of a resolved trace — a canonical full rebuild at every seal point.

  It is the replayed evaluation at the `canonicalFullRebuildAtEverySeal` tag, so
  its prefix results, size vector and total are computations over the trace, and
  its charge model is the one `prefixCost` fixes for that tag (the whole
  accumulated base is recanonicalized at every seal, the novel declarations
  elsewhere).
-/
def canonicalFullRebuildEvaluation {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) :
    LifecycleEvaluation trace .canonicalFullRebuildAtEverySeal :=
  trace.canonicalEvaluation .canonicalFullRebuildAtEverySeal

/-! ## Regret against the canonical full rebuild (SPEC 16) -/

/-- **SPEC 16**, `Atlas.LifecycleComparatorTag`.  SPEC 16: "A competitive or
regret claim against any comparator other than the canonical full rebuild
requires a new first-order comparator body, a complete causal-information
contract, and a separately proved theorem."  The tag therefore has exactly one
constructor. -/
inductive LifecycleComparatorTag
  /-- The canonical full rebuild at every seal point. -/
  | canonicalFullRebuildAtEverySeal
  deriving DecidableEq, Repr, Inhabited

/--
  **SPEC 16**, `Atlas.regretAgainst`: the regret of an evaluation against a
  named comparator, in the frozen carrier `Cost.truncatedDifference`.

  The definition is by cases on the comparator tag, and the one tag SPEC admits
  is wired to `canonicalFullRebuildEvaluation` — the evaluation of *this* trace
  under the full-rebuild strategy, not a number stored beside it.
-/
def regretAgainst {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
    {algorithm : LifecycleAlgorithmTag} (comparator : LifecycleComparatorTag)
    (evaluation : LifecycleEvaluation trace algorithm) : Cost.LifecycleVector :=
  match comparator with
  | .canonicalFullRebuildAtEverySeal =>
      Cost.truncatedDifference evaluation.total
        (canonicalFullRebuildEvaluation trace).total

/--
  **SPEC 16**, `Atlas.lifecycle_full_rebuild_comparator_exact`.

  **This holds by `rfl`, and the docstring says so rather than letting the
  reader assume otherwise.**  Its content is not an arithmetic fact: it is that
  the comparator tag is wired to the canonical full rebuild *of the same trace*
  and to nothing else, and that the regret carrier is the componentwise
  truncated difference of the two exact totals — no slack term, no comparator
  chosen after the fact, no second table.  The theorem is what pins that wiring
  so a later edit to `regretAgainst` cannot silently redirect the comparator:
  the binding in `Conformance/RequiredSignatures.lean` restates SPEC's
  proposition and closes it by `:= @Atlas.lifecycle_full_rebuild_comparator_exact`,
  so a redirected definition stops elaborating.

  What is *not* claimed here: nothing says the regret is zero, small, or bounded.
  `Cost.truncatedDifference_self` gives zero only against an identical total.
-/
theorem lifecycle_full_rebuild_comparator_exact {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body}
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    regretAgainst .canonicalFullRebuildAtEverySeal evaluation =
      Cost.truncatedDifference evaluation.total
        (canonicalFullRebuildEvaluation trace).total := rfl

/-! ## Incremental and full-rebuild observations (SPEC 16)

SPEC 16 names `SameSealedQueryAndExecutionObservations` in the statement of
`lifecycle_incremental_semantics_eq_full_rebuild` but nowhere defines it.  The
reading used here is the strong one: at every prefix the two strategies agree on
the state identity they reach, on the seal they produce, and on the exact
query-result identities they answer with.  `sameObservations_bodyAt` proves that
this really does force the two replayed state bodies to be equal at every
prefix, so the predicate cannot be read as a weak one.

`sealIdAt_congr` records the opposite fact about the seal component: a seal is
determined by the trace's scope and its accumulated declaration base, both of
which are strategy-independent, so the seal identities agree unconditionally and
the content of the predicate is carried by its state and query components. -/

namespace ResolvedLifecycleTrace

variable {body : LifecycleTraceBody}

/-- The recursion `nativeBodyAt` is defined by, as an equation. -/
theorem nativeBodyAt_succ (trace : ResolvedLifecycleTrace body) (k : Nat) :
    trace.nativeBodyAt (k + 1) =
      match trace.deltas[k]? with
      | some delta => semanticApplyBody (trace.nativeBodyAt k) delta
      | none => trace.nativeBodyAt k := rfl

/-- The incremental replay never leaves the trace's scope. -/
theorem nativeBodyAt_scope (trace : ResolvedLifecycleTrace body) (n : Nat) :
    (trace.nativeBodyAt n).scope = trace.scope := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [nativeBodyAt_succ]
      cases trace.deltas[k]? with
      | none => exact ih
      | some d => rw [semanticApplyBody_scope]; exact ih

/-- **Coherence is preserved along the whole trace.**  This is the step the
earlier omission note believed to be a property of the resolved deltas: it is
not.  `Atlas.semanticApplyBody_coherent` preserves coherence for *every* delta,
so the induction needs nothing beyond coherence of the initial state — which
`ResolvedLifecycleTrace` does not carry, and which is where the real obstacle
lives. -/
theorem nativeBodyAt_coherent (trace : ResolvedLifecycleTrace body)
    (hcoherent : Coherent trace.initialState.body) (n : Nat) :
    Coherent (trace.nativeBodyAt n) := by
  induction n with
  | zero => exact hcoherent
  | succ k ih =>
      rw [nativeBodyAt_succ]
      cases trace.deltas[k]? with
      | none => exact ih
      | some d => exact semanticApplyBody_coherent ih d

/-- The incremental replay and the full rebuild reach the same body at every
prefix, given a coherent start. -/
theorem nativeBodyAt_eq_rebuildBodyAt (trace : ResolvedLifecycleTrace body)
    (hcoherent : Coherent trace.initialState.body) (n : Nat) :
    trace.nativeBodyAt n = trace.rebuildBodyAt n := by
  have hco := trace.nativeBodyAt_coherent hcoherent n
  have hs := trace.nativeBodyAt_scope n
  calc trace.nativeBodyAt n
      = derivedBody (trace.nativeBodyAt n).scope
          (trace.nativeBodyAt n).declarationBase := hco
    _ = derivedBody trace.scope (trace.accumulatedDeclarations n) := by
          rw [hs]; rfl
    _ = trace.rebuildBodyAt n := rfl

/-- The two strategies agree at every prefix, given a coherent start.  This is
`bodyAt_zero_agree` for the whole trace rather than for prefix `0`. -/
theorem bodyAt_agree (trace : ResolvedLifecycleTrace body)
    (hcoherent : Coherent trace.initialState.body) (n : Nat) :
    trace.bodyAt .nativeIncremental n
      = trace.bodyAt .canonicalFullRebuildAtEverySeal n :=
  trace.nativeBodyAt_eq_rebuildBodyAt hcoherent n

/-- Equal state bodies answer every scheduled request with the same exact
query-result identities. -/
theorem queryResultIdsAt_congr (trace : ResolvedLifecycleTrace body)
    {a b : LifecycleAlgorithmTag} (n : Nat)
    (h : trace.bodyAt a n = trace.bodyAt b n) :
    trace.queryResultIdsAt a n = trace.queryResultIdsAt b n := by
  simp only [queryResultIdsAt, queryOutcomeAt, h]

/-- **The seal component is strategy-independent by construction.**  A seal is
the seal of the derived state of the trace's scope and accumulated declaration
base; neither depends on the strategy, so this holds unconditionally — and it is
recorded so that no reader mistakes seal agreement for evidence that the two
strategies computed the same thing. -/
theorem sealIdAt_congr (trace : ResolvedLifecycleTrace body)
    (a b : LifecycleAlgorithmTag) (n : Nat) :
    trace.sealIdAt a n = trace.sealIdAt b n := rfl

end ResolvedLifecycleTrace

/--
  **SPEC 16**, `SameSealedQueryAndExecutionObservations`, which SPEC names but
  does not define.

  Two evaluations of the same trace — possibly under different strategies —
  make the same observations when, at every prefix they both cover, they agree
  on the state identity reached, on the seal produced, and on the exact
  query-result identities answered.  Both families cover exactly every prefix
  (`CoversExactlyEveryPrefix`), so this quantifies over `0, …, horizon` with
  nothing skipped, and `sameObservations_bodyAt` shows it forces the two
  replayed state bodies to be equal at every prefix.
-/
def SameSealedQueryAndExecutionObservations {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {a b : LifecycleAlgorithmTag}
    (x : LifecycleEvaluation trace a) (y : LifecycleEvaluation trace b) : Prop :=
  ∀ (rx : LifecyclePrefixResult trace a) (ry : LifecyclePrefixResult trace b),
    rx ∈ x.prefixes.elements → ry ∈ y.prefixes.elements →
      rx.prefixOrdinal.val = ry.prefixOrdinal.val →
        rx.afterStateId = ry.afterStateId ∧
        rx.sealId = ry.sealId ∧
        rx.queryResultIds = ry.queryResultIds

/-- **The observation predicate is not a weak one.**  It forces the two
strategies' replayed state bodies — not merely their identities — to be equal at
every prefix, and their query answers with them. -/
theorem sameObservations_bodyAt {body : LifecycleTraceBody}
    {trace : ResolvedLifecycleTrace body} {a b : LifecycleAlgorithmTag}
    {x : LifecycleEvaluation trace a} {y : LifecycleEvaluation trace b}
    (h : SameSealedQueryAndExecutionObservations x y) {n : Nat}
    (hn : n ≤ body.horizon) :
    trace.bodyAt a n = trace.bodyAt b n ∧
    trace.queryResultIdsAt a n = trace.queryResultIdsAt b n := by
  obtain ⟨rx, hrx, hox⟩ := coversExactlyEveryPrefix_complete x.exactPrefixCover n hn
  obtain ⟨ry, hry, hoy⟩ := coversExactlyEveryPrefix_complete y.exactPrefixCover n hn
  have hh := h rx ry hrx hry (by rw [hox, hoy])
  refine ⟨?_, ?_⟩
  · have hst := hh.1
    rw [rx.afterStateId_eq, ry.afterStateId_eq, hox, hoy] at hst
    exact StateId_eq_iff.mp hst
  · have hq := hh.2.2
    rw [rx.queryResultIds_eq, ry.queryResultIds_eq, hox, hoy] at hq
    exact hq

/--
  **The conditional form of SPEC 16's observational-equality theorem.**

  It is *not* `Atlas.lifecycle_incremental_semantics_eq_full_rebuild`, and it
  does not carry that name, because it has a hypothesis SPEC's statement does
  not: `Coherent trace.initialState.body`.  That hypothesis cannot be dropped —
  `not_lifecycle_incremental_semantics_eq_full_rebuild` below refutes the
  unconditional statement — and `ResolvedLifecycleTrace` does not supply it:
  none of its ten fields constrains the initial state's semantic half, and
  `semanticApplyBody` leaves an incoherent body untouched when the delta
  declares nothing, so no amount of replaying repairs it.

  Given the hypothesis the theorem is unconditional in everything else: every
  delta, every schedule, every seal set, the whole horizon.
-/
theorem lifecycle_incremental_semantics_eq_full_rebuild_of_coherent
    {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
    (hcoherent : Coherent trace.initialState.body)
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    SameSealedQueryAndExecutionObservations evaluation
      (canonicalFullRebuildEvaluation trace) := by
  intro rx ry _ _ hord
  have hbody := trace.bodyAt_agree hcoherent rx.prefixOrdinal.val
  refine ⟨?_, ?_, ?_⟩
  · rw [rx.afterStateId_eq, ry.afterStateId_eq, ← hord, hbody]
  · rw [rx.exactTransition.2.2.2.1, ry.exactTransition.2.2.2.1, ← hord]
    exact trace.sealIdAt_congr _ _ _
  · rw [rx.queryResultIds_eq, ry.queryResultIds_eq, ← hord]
    exact trace.queryResultIdsAt_congr _ hbody

/-- **The hypothesis is discharged, not assumed, for every lifecycle that starts
from a rebuild.**  SPEC 12.5's `Atlas.rebuild` produces exactly such a state, so
the conditional theorem above is not vacuous on the traces the pipeline
actually produces. -/
theorem lifecycle_incremental_semantics_eq_full_rebuild_of_rebuilt_start
    {body : LifecycleTraceBody} {trace : ResolvedLifecycleTrace body}
    {scope : Scope} {declarations : CanonicalDeclarationSet}
    (hstart : trace.initialState.body = semanticRebuildBodyWith scope declarations)
    (evaluation : LifecycleEvaluation trace .nativeIncremental) :
    SameSealedQueryAndExecutionObservations evaluation
      (canonicalFullRebuildEvaluation trace) :=
  lifecycle_incremental_semantics_eq_full_rebuild_of_coherent
    (by rw [hstart]; exact semanticRebuildBodyWith_coherent scope declarations)
    evaluation

/-! ### SPEC 16's literal observational-equality statement is false

The refutation is built here rather than cited from `Atlas/Rebuild.lean` so that
it stands on this file's own definitions.  It is the lifecycle analogue of
`Atlas.not_incremental_eq_full_rebuild` (deviation `DEV-004`): the same missing
coherence obligation, one layer up. -/

namespace LifecycleCounterexample

/-- A semantic object no declaration derives. -/
def strayObject : ObjectEntry := ⟨nullId, ByteArray.empty⟩

/-- An unscoped body whose recorded semantic half is not the one its declaration
base derives: the base is empty and it records an object anyway. -/
def incoherentBody : StateBody :=
  { derivedBody Scope.unscoped ⟨[]⟩ with semanticObjects := ⟨[strayObject]⟩ }

theorem incoherentBody_not_coherent : ¬ Coherent incoherentBody := by
  intro h
  exact absurd (congrArg StateBody.semanticObjects h) (by decide)

/-- It is a perfectly legal `Atlas.UnsealedState`: that type carries no
coherence obligation. -/
def incoherentState : UnsealedState := unsealedFromBody incoherentBody

/-- A trace over it: horizon `0`, no deltas, no requests, no seal points.  Every
field of `ResolvedLifecycleTrace` is discharged, so this really is a resolved
trace and not a near miss. -/
def traceBody : LifecycleTraceBody where
  version := 1
  profileId := nullId
  problemId := nullId
  objectiveId := nullId
  initialStateId := StateId incoherentBody
  deltaIds := []
  requestIds := []
  requestAfterPrefixes := []
  sealAfterPrefixes := CanonicalNatFinset.empty
  horizon := 0

/-- The resolved trace. -/
def trace : ResolvedLifecycleTrace traceBody where
  initialState := incoherentState
  deltas := []
  requests := []
  resolvesInitial := rfl
  resolvesDeltas := rfl
  resolvesRequests := rfl
  horizonEq := rfl
  requestScheduleLength := rfl
  requestOrdinalsValid := fun _ h => nomatch h
  sealOrdinalsValid := fun _ h => nomatch h
  completePreimages := canonicalLifecycleObjectGraph traceBody

/-- **The two strategies observe different states at prefix `0`.**  The native
replay is the recorded body; the full rebuild is the body its declaration base
derives; they differ exactly because the start is incoherent. -/
theorem observations_differ :
    ¬ SameSealedQueryAndExecutionObservations
        (trace.canonicalEvaluation .nativeIncremental)
        (canonicalFullRebuildEvaluation trace) := by
  intro h
  have hx : trace.canonicalPrefixResult .nativeIncremental ⟨0, Nat.succ_pos _⟩ ∈
      (trace.canonicalEvaluation .nativeIncremental).prefixes.elements :=
    List.mem_cons_self
  have hy : trace.canonicalPrefixResult .canonicalFullRebuildAtEverySeal
      ⟨0, Nat.succ_pos _⟩ ∈
      (canonicalFullRebuildEvaluation trace).prefixes.elements :=
    List.mem_cons_self
  exact incoherentBody_not_coherent (StateId_eq_iff.mp (h _ _ hx hy rfl).1)

end LifecycleCounterexample

/--
  **SPEC 16's `lifecycle_incremental_semantics_eq_full_rebuild` is false as
  stated**, under the strong reading of
  `SameSealedQueryAndExecutionObservations` used here.

  The statement quantifies over every `Atlas.ResolvedLifecycleTrace`, and that
  structure constrains only identities, schedules and retention — never the
  initial state's semantic half.  A trace starting from a state that records one
  semantic object its empty declaration base does not derive therefore falsifies
  it at prefix `0`, before any delta is applied.

  This is why no theorem in this file carries SPEC's name: the missing
  hypothesis is `Coherent trace.initialState.body`, it is supplied by neither
  `ResolvedLifecycleTrace` nor the resolved deltas, and
  `lifecycle_incremental_semantics_eq_full_rebuild_of_coherent` states the
  theorem under exactly that hypothesis instead of hiding it.
-/
theorem not_lifecycle_incremental_semantics_eq_full_rebuild :
    ¬ ∀ (body : LifecycleTraceBody) (trace : ResolvedLifecycleTrace body)
        (evaluation : LifecycleEvaluation trace .nativeIncremental),
        SameSealedQueryAndExecutionObservations evaluation
          (canonicalFullRebuildEvaluation trace) := by
  intro h
  exact LifecycleCounterexample.observations_differ
    (h _ _ (LifecycleCounterexample.trace.canonicalEvaluation .nativeIncremental))

/-- **The native bound is not vacuous.**  `lifecycle_native_bound` quantifies
over a class that is inhabited for *every* resolved trace: the replayed native
evaluation is a total construction, so the theorem applies to it with no
hypothesis.  Recorded because an inequality over an empty class would be
worthless and nothing else in this file says the class is nonempty. -/
theorem lifecycle_native_bound_of_canonicalEvaluation {body : LifecycleTraceBody}
    (trace : ResolvedLifecycleTrace body) :
    (trace.canonicalEvaluation .nativeIncremental).total
      ≤ nativeLifecycleBound Release.primitiveCostTable
          (trace.canonicalEvaluation .nativeIncremental).size :=
  lifecycle_native_bound _

/-! ## Omissions

Recorded here so that a reader of SPEC 16 can see what is *not* closed rather
than having to notice its absence.

* `Atlas.lifecycle_incremental_semantics_eq_full_rebuild` — **absent because it
  is false**, not because it is hard.  `not_lifecycle_incremental_semantics_eq_full_rebuild`
  above refutes it: `ResolvedLifecycleTrace` constrains identities, schedules and
  retention, never the initial state's semantic half, and an incoherent start is
  already observed differently by the two strategies at prefix `0`.  The earlier
  note here said the inductive step "needs coherence to be preserved along the
  whole trace, which is a property of the resolved deltas"; that was wrong in
  both halves.  Coherence *is* preserved by every delta
  (`Atlas.semanticApplyBody_coherent`, lifted here as `nativeBodyAt_coherent`),
  and what is missing is the base case, which is a property of the initial state
  and of nothing else.  `lifecycle_incremental_semantics_eq_full_rebuild_of_coherent`
  states the theorem under exactly the missing hypothesis, and
  `lifecycle_incremental_semantics_eq_full_rebuild_of_rebuilt_start` discharges
  that hypothesis for every lifecycle that begins from a rebuild.  No
  declaration in this file carries SPEC's name, and
  `Conformance/RequiredSignatures.lean` binds nothing to it: the SPEC 15 name
  stays OUTSTANDING.

Closed since this section was first written, and no longer omitted:
`Atlas.canonicalFullRebuildEvaluation`, `Atlas.LifecycleComparatorTag`,
`Atlas.regretAgainst` and `Atlas.lifecycle_full_rebuild_comparator_exact`.  The
recorded obstacle to the first — that its `size` field "would have to be
verified against `lifecycleSize`, which is a computation over the whole trace" —
was over-cautious: `VerifiesLifecycleSize` is *defined* as equality with that
computation, so performing it discharges the obligation rather than storing an
unverified conclusion.  A correct note that turns out to be over-cautious is
worth recording as such.

Also closed since this section was first written:
`Atlas.lifecycle_native_bound`.  The note here used to say the release table it
would be stated over "is not pinned in this repository", which was true and was
the whole of the obstacle.  `Release.primitiveCostTable` is now pinned in
`Cost/Lifecycle.lean` with every coefficient `1`, and the inequality is proved
over it — and, by `lifecycle_native_bound_of_positive`, over every positive
table, so the pinning cannot be what makes it true.  What the bound does and does
not constrain is stated in the theorem's own docstring and machine-checked by
`lifecycle_native_bound_attained` (fourteen coordinates hold with equality) and
`lifecycle_native_bound_slack` (the exact slack on the other three, all of it in
the shape of SPEC 16's polynomial rather than in a coefficient). -/

end WasmGemmGnaf.Atlas
