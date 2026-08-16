/-
  `GlobalOptimal` and the score-sublevel facts that are actually available.
  Normative sources: SPEC.md section 1 (the decisive predicate), section 9.3
  (properness) and section 10.3 (the sublevel construction).

  SCOPE — read this before citing anything here.

  `GlobalOptimal` uses the public amended-Core evaluation carrier. Its *outer
  byte quantifier* is unrestricted, and this file proves structural
  facts about that quantifier: monotonicity in the byte scope, projection to a
  single competitor, and non-vacuity of the competitor premises. The file also
  proves two carrier-level sublevel facts that follow
  from properness alone: a score sublevel bounds every charged coordinate, and
  bounded-length byte strings are finitely covered.

  It proves `possible_winner_within_sublevel` (SPEC §10.3): an evaluated
  competitor that does not score worse than the baseline is confined to the
  sublevel the baseline's score determines.  That is a consequence of
  properness alone and needs no coverage hypothesis — the objective's own
  `boundOfScore` supplies the bound and `ProperObjective.sublevelBound` is the
  field that makes it hold.

  It does NOT prove `universal_sublevel_coverage`.  Confining every *evaluated*
  competitor to a finite carrier is not the same as having searched that
  carrier, nor as knowing that every competitor is evaluated; the gap between
  the two is an attained universal lower bound (UOR-GNAF §19.3), which is
  undischarged.  `universal_sublevel_coverage` and
  `Artifact.released_wasm_gemm_gnaf_global_optimal` are OMITTED, not stubbed and
  not assumed.

  Every declaration in this file is either a definition or a proved theorem.
-/
import WasmGemmGnaf.Universal.Evaluate
import WasmGemmGnaf.Cost.Proper

set_option autoImplicit false

namespace WasmGemmGnaf.Universal

/-! ## The decisive predicate (SPEC §1) -/

section GlobalOptimal

variable {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]

/--
  **SPEC §1**, `GlobalOptimal`, with the competitor quantifier restricted to a
  named scope.

  This generalization exists only so that the outer byte-scope strength of the current predicate
  is checkable: `GlobalOptimal` below is exactly this with the scope `fun _ =>
  True`, and `globalOptimalOver_mono` proves that shrinking the scope can only
  weaken the statement.  A scope-restricted instance is therefore never a
  substitute for the public release theorem.
-/
def GlobalOptimalOver (scope : ByteArray → Prop) (S : Setting P) (D : Decider S)
    (O : Cost.ProperObjective P S.problem) (releasedBytes : ByteArray) : Prop :=
  ProfileValid P releasedBytes ∧
  SemanticCorrect S releasedBytes ∧
  SemanticWithinResources S releasedBytes ∧
  ∃ releasedEval : SystemEvaluation S releasedBytes,
    SystemEvaluationRel S D releasedBytes releasedEval ∧
    Correct releasedEval ∧
    Feasible releasedEval ∧
    (∀ competitorBytes : ByteArray,
       scope competitorBytes →
       ProfileValid P competitorBytes →
       SemanticCorrect S competitorBytes →
       SemanticWithinResources S competitorBytes →
       ∀ competitorEval : SystemEvaluation S competitorBytes,
         SystemEvaluationRel S D competitorBytes competitorEval ∧
         O.score releasedEval.cost ≤ O.score competitorEval.cost) ∧
    (∀ competitorBytes : ByteArray,
       scope competitorBytes →
       ProfileValid P competitorBytes →
       SemanticCorrect S competitorBytes →
       SemanticWithinResources S competitorBytes →
       ∀ competitorEval : SystemEvaluation S competitorBytes,
         SystemEvaluationRel S D competitorBytes competitorEval →
         O.score releasedEval.cost = O.score competitorEval.cost →
         Foundation.CanonicalBytesLE releasedBytes competitorBytes)

/--
  The public amended-Core shape corresponding to **SPEC §1** `GlobalOptimal`.

  All three leading conjuncts, the existential over `releasedEval`, and *both*
  universally quantified clauses.  The competitor quantifier ranges over **all**
  of `ByteArray` — every finite byte sequence, not only GNAF plans, registered
  kernels, familiar algorithms, proof-carrying submissions, or candidates found
  by an attention index. Its `ProfileValid` and `SystemEvaluation` predicates
  range over the public `Wasm.Module` carrier.
-/
def GlobalOptimal (S : Setting P) (D : Decider S)
    (O : Cost.ProperObjective P S.problem) (releasedBytes : ByteArray) : Prop :=
  ProfileValid P releasedBytes ∧
  SemanticCorrect S releasedBytes ∧
  SemanticWithinResources S releasedBytes ∧
  ∃ releasedEval : SystemEvaluation S releasedBytes,
    SystemEvaluationRel S D releasedBytes releasedEval ∧
    Correct releasedEval ∧
    Feasible releasedEval ∧
    (∀ competitorBytes : ByteArray,
       ProfileValid P competitorBytes →
       SemanticCorrect S competitorBytes →
       SemanticWithinResources S competitorBytes →
       ∀ competitorEval : SystemEvaluation S competitorBytes,
         SystemEvaluationRel S D competitorBytes competitorEval ∧
         O.score releasedEval.cost ≤ O.score competitorEval.cost) ∧
    (∀ competitorBytes : ByteArray,
       ProfileValid P competitorBytes →
       SemanticCorrect S competitorBytes →
       SemanticWithinResources S competitorBytes →
       ∀ competitorEval : SystemEvaluation S competitorBytes,
         SystemEvaluationRel S D competitorBytes competitorEval →
         O.score releasedEval.cost = O.score competitorEval.cost →
         Foundation.CanonicalBytesLE releasedBytes competitorBytes)

variable {S : Setting P} {D : Decider S} {O : Cost.ProperObjective P S.problem}
  {releasedBytes : ByteArray}

/-! ### Monotonicity in the competitor scope -/

/-- The unrestricted predicate is the maximal scope. -/
theorem globalOptimal_iff_over_all :
    GlobalOptimal S D O releasedBytes ↔
      GlobalOptimalOver (fun _ => True) S D O releasedBytes := by
  constructor
  · rintro ⟨hp, hc, hw, eval, hrel, hcor, hfea, hlow, htie⟩
    exact ⟨hp, hc, hw, eval, hrel, hcor, hfea,
      fun b _ => hlow b, fun b _ => htie b⟩
  · rintro ⟨hp, hc, hw, eval, hrel, hcor, hfea, hlow, htie⟩
    exact ⟨hp, hc, hw, eval, hrel, hcor, hfea,
      fun b => hlow b trivial, fun b => htie b trivial⟩

/--
  **Monotone in the competitor set, in the right direction.**  A proof over a
  *larger* competitor scope yields a proof over every *smaller* one.  The
  converse direction is not available, which is exactly why `GlobalOptimal`
  fixes the scope at all of `ByteArray`.
-/
theorem globalOptimalOver_mono {scopeSmall scopeLarge : ByteArray → Prop}
    (hsub : ∀ b, scopeSmall b → scopeLarge b)
    (h : GlobalOptimalOver scopeLarge S D O releasedBytes) :
    GlobalOptimalOver scopeSmall S D O releasedBytes := by
  obtain ⟨hp, hc, hw, eval, hrel, hcor, hfea, hlow, htie⟩ := h
  exact ⟨hp, hc, hw, eval, hrel, hcor, hfea,
    fun b hb => hlow b (hsub b hb), fun b hb => htie b (hsub b hb)⟩

/-- `GlobalOptimal` implies every scoped instance.  Narrowing the universe is
therefore never a strengthening. -/
theorem globalOptimal_implies_over (scope : ByteArray → Prop)
    (h : GlobalOptimal S D O releasedBytes) :
    GlobalOptimalOver scope S D O releasedBytes :=
  globalOptimalOver_mono (fun _ _ => trivial) (globalOptimal_iff_over_all.mp h)

/-! ### Projection to a single competitor -/

/-- **Projection.**  Any proof of `GlobalOptimal` yields the lower-bound clause
for *every specific* competitor byte sequence.  This makes the definition's
strength checkable: if the quantifier had been narrowed, this would not
typecheck for an arbitrary `competitorBytes : ByteArray`. -/
theorem globalOptimal_lower_bound_at (h : GlobalOptimal S D O releasedBytes)
    (competitorBytes : ByteArray)
    (hprofile : ProfileValid P competitorBytes)
    (hcorrect : SemanticCorrect S competitorBytes)
    (hresources : SemanticWithinResources S competitorBytes) :
    ∃ releasedEval : SystemEvaluation S releasedBytes,
      SystemEvaluationRel S D releasedBytes releasedEval ∧
      Correct releasedEval ∧ Feasible releasedEval ∧
      ∀ competitorEval : SystemEvaluation S competitorBytes,
        SystemEvaluationRel S D competitorBytes competitorEval ∧
        O.score releasedEval.cost ≤ O.score competitorEval.cost := by
  obtain ⟨_, _, _, eval, hrel, hcor, hfea, hlow, _⟩ := h
  exact ⟨eval, hrel, hcor, hfea, hlow competitorBytes hprofile hcorrect hresources⟩

/-- **Projection**, tie-break half: any proof of `GlobalOptimal` yields the
canonical-least clause for every specific equal-scoring competitor. -/
theorem globalOptimal_canonical_least_at (h : GlobalOptimal S D O releasedBytes)
    (competitorBytes : ByteArray)
    (hprofile : ProfileValid P competitorBytes)
    (hcorrect : SemanticCorrect S competitorBytes)
    (hresources : SemanticWithinResources S competitorBytes) :
    ∃ releasedEval : SystemEvaluation S releasedBytes,
      SystemEvaluationRel S D releasedBytes releasedEval ∧
      ∀ competitorEval : SystemEvaluation S competitorBytes,
        SystemEvaluationRel S D competitorBytes competitorEval →
        O.score releasedEval.cost = O.score competitorEval.cost →
        Foundation.CanonicalBytesLE releasedBytes competitorBytes := by
  obtain ⟨_, _, _, eval, hrel, _, _, _, htie⟩ := h
  exact ⟨eval, hrel, htie competitorBytes hprofile hcorrect hresources⟩

/-- The three leading conjuncts project out. -/
theorem globalOptimal_profileValid (h : GlobalOptimal S D O releasedBytes) :
    ProfileValid P releasedBytes := h.1

/-- The three leading conjuncts project out. -/
theorem globalOptimal_semanticCorrect (h : GlobalOptimal S D O releasedBytes) :
    SemanticCorrect S releasedBytes := h.2.1

/-- The three leading conjuncts project out. -/
theorem globalOptimal_semanticWithinResources
    (h : GlobalOptimal S D O releasedBytes) :
    SemanticWithinResources S releasedBytes := h.2.2.1

/-- The released evaluation exists, is the decider's own answer, and is correct
and feasible. -/
theorem globalOptimal_releasedEval (h : GlobalOptimal S D O releasedBytes) :
    ∃ releasedEval : SystemEvaluation S releasedBytes,
      SystemEvaluationRel S D releasedBytes releasedEval ∧
      Correct releasedEval ∧ Feasible releasedEval := by
  obtain ⟨_, _, _, eval, hrel, hcor, hfea, _, _⟩ := h
  exact ⟨eval, hrel, hcor, hfea⟩

/-! ### Non-vacuity of the competitor clause

The competitor premises are `ProfileValid ∧ SemanticCorrect ∧
SemanticWithinResources`.  Those are *exactly* the first three conjuncts of
`GlobalOptimal`, so the released bytes themselves satisfy them.  The quantified
clause therefore ranges over at least one module and cannot be satisfied by an
empty competitor universe. -/

omit [Foundation.Fintype (Gemm.RawInvocation P)] in
/-- **Non-vacuity.**  Whenever the first three conjuncts hold, the released
bytes themselves satisfy the competitor premises. -/
theorem released_satisfies_competitor_premises (setting : Setting P)
    (bytes : ByteArray)
    (hprofile : ProfileValid P bytes)
    (hcorrect : SemanticCorrect setting bytes)
    (hresources : SemanticWithinResources setting bytes) :
    ∃ competitorBytes : ByteArray,
      ProfileValid P competitorBytes ∧
      SemanticCorrect setting competitorBytes ∧
      SemanticWithinResources setting competitorBytes :=
  ⟨bytes, hprofile, hcorrect, hresources⟩

/-- **Non-vacuity**, applied to a proof of `GlobalOptimal`: the competitor
universe the theorem quantifies over is inhabited. -/
theorem globalOptimal_competitor_universe_inhabited
    (h : GlobalOptimal S D O releasedBytes) :
    ∃ competitorBytes : ByteArray,
      ProfileValid P competitorBytes ∧
      SemanticCorrect S competitorBytes ∧
      SemanticWithinResources S competitorBytes :=
  released_satisfies_competitor_premises S releasedBytes h.1 h.2.1 h.2.2.1

/-- **Non-vacuity**, sharpest form: the lower-bound clause of a proof of
`GlobalOptimal` really fires on a known member of the competitor universe — the
released bytes — so the clause is not satisfied merely because its premises are
unsatisfiable. -/
theorem globalOptimal_lower_bound_fires (h : GlobalOptimal S D O releasedBytes) :
    ∃ releasedEval : SystemEvaluation S releasedBytes,
      SystemEvaluationRel S D releasedBytes releasedEval ∧
      ∀ competitorEval : SystemEvaluation S releasedBytes,
        SystemEvaluationRel S D releasedBytes competitorEval ∧
        O.score releasedEval.cost ≤ O.score competitorEval.cost := by
  obtain ⟨hp, hc, hw, eval, hrel, _, _, hlow, _⟩ := h
  exact ⟨eval, hrel, hlow releasedBytes hp hc hw⟩

/-- **Non-vacuity**, tie-break half: the canonical-least clause also fires on
the released bytes, where it degenerates to reflexivity of the canonical
order. -/
theorem globalOptimal_canonical_least_fires
    (_h : GlobalOptimal S D O releasedBytes) :
    Foundation.CanonicalBytesLE releasedBytes releasedBytes :=
  Foundation.CanonicalBytesLE.refl releasedBytes

end GlobalOptimal

/-! ## Score sublevels bound every coordinate (SPEC §9.3, §10.3) -/

section Sublevel

variable {Profile Problem : Type} {P : Profile} {G : Problem}

/-- **SPEC §10.3.**  A score sublevel bounds *every* charged coordinate.  This
is the properness step: no charged resource is left free. -/
theorem score_sublevel_bounds_every_coordinate
    (O : Cost.ProperObjective P G) {c : Cost.CompleteSystemCost} {u : Nat}
    (h : O.score c ≤ u) (co : Cost.ArtifactCoordinate) : co.value c ≤ u :=
  Cost.ProperObjective.coordinate_le_of_score_le O h co

/-- A score sublevel lies inside the objective's own declared resource bound. -/
theorem score_sublevel_within_bounds
    (O : Cost.ProperObjective P G) {c : Cost.CompleteSystemCost} {u : Nat}
    (h : O.score c ≤ u) : Cost.Within (O.boundOfScore u) c :=
  Cost.ProperObjective.within_boundOfScore O h

/-- A score sublevel bounds the module byte count. -/
theorem score_sublevel_bounds_moduleBytes
    (O : Cost.ProperObjective P G) {c : Cost.CompleteSystemCost} {u : Nat}
    (h : O.score c ≤ u) : c.static.moduleBytes ≤ u :=
  score_sublevel_bounds_every_coordinate O h .staticModuleBytes

end Sublevel

/-- **SPEC §10.3 (1).**  Every competitor inside the score sublevel has a
bounded module byte count.  The bound comes from properness plus the exact
aggregate cost equation `cost.static.moduleBytes = bytes.size`; no coverage
hypothesis is used. -/
theorem sublevel_bytes_size_le {P : Wasm.Profile}
    [Foundation.Fintype (Gemm.RawInvocation P)] {S : Setting P}
    (O : Cost.ProperObjective P S.problem) {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) {u : Nat}
    (h : O.score evaluation.cost ≤ u) : bytes.size ≤ u := by
  have hexact := Cost.module_bytes_exact evaluation.costExact
  have hbound := score_sublevel_bounds_moduleBytes O h
  rw [hexact] at hbound
  exact hbound

/-! ## Bounded-length byte strings are a finite carrier (SPEC §10.3 (1)) -/

namespace Enumerate

/-- Every byte. -/
def allBytes : List UInt8 := (List.range 256).map UInt8.ofNat

theorem mem_allBytes (b : UInt8) : b ∈ allBytes :=
  List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr (UInt8.toNat_lt_size b),
    UInt8.ofNat_toNat⟩

/-- Every byte list of exactly length `n`. -/
def byteListsOfLength : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => allBytes.flatMap (fun b => (byteListsOfLength n).map (fun l => b :: l))

theorem byteListsOfLength_zero : byteListsOfLength 0 = [[]] := rfl

theorem byteListsOfLength_succ (n : Nat) :
    byteListsOfLength (n + 1) =
      allBytes.flatMap (fun b => (byteListsOfLength n).map (fun l => b :: l)) :=
  rfl

/-- Every byte list of length `n` is enumerated. -/
theorem mem_byteListsOfLength : ∀ l : List UInt8, l ∈ byteListsOfLength l.length
  | [] => by simp [byteListsOfLength]
  | b :: rest => by
      rw [List.length_cons, byteListsOfLength_succ]
      refine List.mem_flatMap.mpr ⟨b, mem_allBytes b, ?_⟩
      exact List.mem_map.mpr ⟨rest, mem_byteListsOfLength rest, rfl⟩

/-- Every entry of `byteListsOfLength n` really has length `n`: the enumeration
is exact, not merely complete. -/
theorem length_of_mem_byteListsOfLength :
    ∀ (n : Nat) (l : List UInt8), l ∈ byteListsOfLength n → l.length = n
  | 0, l, h => by
      rw [byteListsOfLength_zero, List.mem_singleton] at h
      simp [h]
  | n + 1, l, h => by
      rw [byteListsOfLength_succ] at h
      obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp h
      obtain ⟨rest, hrest, hl⟩ := List.mem_map.mp hb
      subst hl
      simp [length_of_mem_byteListsOfLength n rest hrest]

/-- Every byte array of size at most `n`. -/
def boundedByteArrays (n : Nat) : List ByteArray :=
  (List.range (n + 1)).flatMap
    (fun k => (byteListsOfLength k).map Foundation.Bytes.pack)

/-- **SPEC §10.3 (1).**  Byte strings within a module-size bound are finitely
covered: `boundedByteArrays n` contains every byte array of size at most
`n`. -/
theorem mem_boundedByteArrays {n : Nat} {b : ByteArray} (h : b.size ≤ n) :
    b ∈ boundedByteArrays n := by
  have hlen : b.toList.length = b.size := by
    rw [← Foundation.Bytes.size_pack b.toList, Foundation.Bytes.pack_toList]
  refine List.mem_flatMap.mpr ⟨b.toList.length, ?_, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_map.mpr
      ⟨b.toList, mem_byteListsOfLength b.toList, Foundation.Bytes.pack_toList b⟩

/-- Every entry of `boundedByteArrays n` really is within the bound: the
enumeration is exact in both directions. -/
theorem size_le_of_mem_boundedByteArrays {n : Nat} {b : ByteArray}
    (h : b ∈ boundedByteArrays n) : b.size ≤ n := by
  obtain ⟨k, hk, hb⟩ := List.mem_flatMap.mp h
  obtain ⟨l, hl, hpack⟩ := List.mem_map.mp hb
  subst hpack
  rw [Foundation.Bytes.size_pack, length_of_mem_byteListsOfLength k l hl]
  exact Nat.lt_succ_iff.mp (List.mem_range.mp hk)

/-- The enumeration is exactly the set of byte arrays within the bound. -/
theorem mem_boundedByteArrays_iff {n : Nat} (b : ByteArray) :
    b ∈ boundedByteArrays n ↔ b.size ≤ n :=
  ⟨size_le_of_mem_boundedByteArrays, mem_boundedByteArrays⟩

end Enumerate

/-- Carrier finiteness for the public `SystemEvaluation`: every
evaluated byte string whose score lies in the sublevel `u` occurs in the finite
list `boundedByteArrays u`.

This is a finiteness fact about the *carrier*.  It is NOT
`universal_sublevel_coverage`: nothing here claims that every winner is
evaluated, that the enumeration is checked, or that modules outside the
sublevel cannot beat the baseline. -/
theorem sublevel_bytes_enumerated {P : Wasm.Profile}
    [Foundation.Fintype (Gemm.RawInvocation P)] {S : Setting P}
    (O : Cost.ProperObjective P S.problem) {bytes : ByteArray}
    (evaluation : SystemEvaluation S bytes) {u : Nat}
    (h : O.score evaluation.cost ≤ u) :
    bytes ∈ Enumerate.boundedByteArrays u :=
  Enumerate.mem_boundedByteArrays (sublevel_bytes_size_le O evaluation h)

/-! ## Membership of a score sublevel (SPEC §10.3)

SPEC §10.3 fixes the shape of the sublevel construction:

> Given a proved correct baseline evaluation `bEval`, let `u = O.score bEval.cost`.
> Properness yields bounds on module bytes, execution steps, memory, instantiated
> state, and every other charged coordinate for any evaluated competitor with
> `O.score cEval.cost ≤ u`.

`WithinSublevel` names that conclusion and `possible_winner_within_sublevel`
proves it.  Both are stated over the objective's **own declared**
`boundOfScore`, so no bound is invented here: the objective supplies it and
`ProperObjective.sublevelBound` is the field that makes it hold.

What this is NOT: it is not `universal_sublevel_coverage`.  Nothing below claims
that every winner is evaluated, that the sublevel is enumerated and checked, or
that a module *outside* the sublevel cannot beat the baseline.
-/

section PossibleWinner

variable {P : Wasm.Profile} [Foundation.Fintype (Gemm.RawInvocation P)]
  {S : Setting P}

/--
  **SPEC §10.3.**  An evaluated competitor lies within a score sublevel when its
  exact aggregate cost is inside the declared resource bound *and* its module
  byte count is inside that bound's own module-size coordinate.

  The second conjunct is not redundant bookkeeping: it is the hypothesis SPEC
  §10.3 (1) needs — "byte strings within the module-size bound are finite and
  exactly enumerable" — stated on the `ByteArray` rather than on the cost
  vector, which is where `Enumerate.boundedByteArrays` can consume it.  It is
  *derived* from the first conjunct through the exact aggregate cost equation
  `cost.static.moduleBytes = bytes.size`, never assumed.
-/
def WithinSublevel (bounds : Cost.ResourceBounds) (bytes : ByteArray)
    (evaluation : SystemEvaluation S bytes) : Prop :=
  Cost.Within bounds evaluation.cost ∧
    bytes.size ≤ bounds.coordinateBound Cost.ArtifactCoordinate.staticModuleBytes

/--
  The core of `possible_winner_within_sublevel`, with **no hypothesis at all
  beyond the score inequality**.

  It is stated separately so the strength of the §15 theorem below is visible:
  that theorem carries SPEC's five extra premises verbatim, and this lemma
  proves none of them is load-bearing.  Properness alone confines a sublevel
  member; being profile valid, correct or feasible adds nothing to the
  confinement, which is exactly the property §10.3 needs — a competitor cannot
  escape the sublevel by being *worse* behaved.
-/
theorem withinSublevel_of_score_le (O : Cost.ProperObjective P S.problem)
    {bytes : ByteArray} (evaluation : SystemEvaluation S bytes) {u : Nat}
    (h : O.score evaluation.cost ≤ u) :
    WithinSublevel (O.boundOfScore u) bytes evaluation := by
  refine ⟨Cost.ProperObjective.within_boundOfScore O h, ?_⟩
  have hcoord :=
    Cost.ProperObjective.within_boundOfScore O h Cost.ArtifactCoordinate.staticModuleBytes
  have hexact := Cost.module_bytes_exact evaluation.costExact
  show bytes.size ≤ _
  rw [← hexact]
  exact hcoord

/--
  **SPEC §10.3 / §15**, `Universal.possible_winner_within_sublevel`.

  Any evaluated competitor that does not score worse than the baseline lies
  inside the sublevel the baseline's score determines.  Contrapositively: a
  module outside that sublevel cannot beat the baseline — which is what makes
  the *search* for a winner a search over a bounded carrier rather than over all
  of `ByteArray`.

  The premises are SPEC's, verbatim and in SPEC's order.  Only `hbetter` is
  used; `withinSublevel_of_score_le` above is the same conclusion without the
  other five, so this statement is faithful to §10.3 without being weaker than
  what is actually proved.

  **Scope.**  This bounds a competitor *given* an evaluation of it.  It does not
  produce that evaluation, does not claim every competitor has one, and does not
  claim the sublevel has been searched.  Those are
  `system_evaluation_rel_complete` and `universal_sublevel_coverage`, both
  outstanding.
-/
theorem possible_winner_within_sublevel {D : Decider S}
    (O : Cost.ProperObjective P S.problem)
    {baselineBytes competitorBytes : ByteArray}
    (bEval : SystemEvaluation S baselineBytes)
    (hc : ProfileValid P competitorBytes)
    (cEval : SystemEvaluation S competitorBytes)
    (heval : SystemEvaluationRel S D competitorBytes cEval)
    (hcorrect : Correct cEval)
    (hfeasible : Feasible cEval)
    (hbetter : O.score cEval.cost ≤ O.score bEval.cost) :
    WithinSublevel (O.boundOfScore (O.score bEval.cost)) competitorBytes cEval := by
  clear hc heval hcorrect hfeasible
  exact withinSublevel_of_score_le O cEval hbetter

/-- A sublevel member's bytes are enumerated by the finite carrier of §10.3 (1).
This is the point of carrying the byte bound in `WithinSublevel`. -/
theorem withinSublevel_bytes_enumerated (O : Cost.ProperObjective P S.problem)
    {bytes : ByteArray} {evaluation : SystemEvaluation S bytes} {u : Nat}
    (h : WithinSublevel (O.boundOfScore u) bytes evaluation) :
    bytes ∈
      Enumerate.boundedByteArrays
        ((O.boundOfScore u).coordinateBound Cost.ArtifactCoordinate.staticModuleBytes) :=
  Enumerate.mem_boundedByteArrays h.2

/-- Every charged coordinate of a sublevel member is bounded, not merely the
module size: `WithinSublevel` carries the whole of `Cost.Within`. -/
theorem withinSublevel_coordinate_le {bounds : Cost.ResourceBounds}
    {bytes : ByteArray} {evaluation : SystemEvaluation S bytes}
    (h : WithinSublevel bounds bytes evaluation) (co : Cost.ArtifactCoordinate) :
    co.value evaluation.cost ≤ bounds.coordinateBound co :=
  h.1 co

end PossibleWinner

end WasmGemmGnaf.Universal
