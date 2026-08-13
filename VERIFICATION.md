# Verification

What each gate discharges, and the defect planted to prove it can fail.

Run everything with `just vv`. It is **expected to fail** at step 9 while `WGG-GO-1`
is outstanding; see [CERTIFICATION.md](CERTIFICATION.md). A green gate in this state
would mean the gate had been weakened.

## Gate map

| Gate | Discharges | Falsifier |
| --- | --- | --- |
| `just build` | the Lean library compiles under the pinned toolchain | — |
| `just axioms` | every `formalProof` claim's transitive axiom closure is inside the SPEC §4 trust base | `M5` |
| `just claims` | registry is nonempty, ids unique, no orphan dependencies | `M2`, `M3` |
| `just schema` | every `scopeCriticalDefinitions` entry of the frozen `WGG-GO-1` authority is bound to its fully spelled-out body by `Iff.rfl` / `rfl` | `M11` |
| `just mutation` | each decisive checker rejects a planted fault | self-testing |
| `just docs` | `CONFORMANCE.md` is generated, deterministic, byte-clean | `reproducible.yml` |
| `just vv` | all 13 conditions of SPEC §20.2 | `M6` |

## Why the source scan is not the decisive audit

SPEC §19 is explicit: source scanning is defence in depth. The decisive audit inspects
the **compiled environment** and the transitive dependencies of every public theorem,
via `#print axioms` in `just axioms`. A `sorry` reaches the environment as
`sorryAx`, so it is caught there even if the text scan is evaded.

Current closure over every `formalProof` claim: `propext`, `Quot.sound`. Both are Lean
core logical axioms and are named individually as SPEC §4 requires. No `sorryAx`, no
project-declared axiom, no `Classical.choice`.

## Planted falsifiers

`just mutation`, registered in `model/falsifiers.json`. Each applies its mutation
to a **copy**, never to the repository.

| ID | Family | Plants | Rejected by |
| --- | --- | --- | --- |
| M1 | CM | mutated authority bytes | content digest recomputation |
| M2 | CM | duplicate claim id | registry uniqueness |
| M3 | CM | orphan claim dependency | registry dependency check |
| M4 | GO | `formalProof` level with no Lean declaration | claim-level rule (SPEC §17.1) |
| M5 | LF | `sorry` on the proof path | forbidden-construct scan |
| M6 | GO | green gate while `GO-001` is outstanding | release gate step 9 |
| M7 | AT | citing the seal's cover check as universal coverage | `AT-001` blindness lemma + `AT-002` absence |
| M8 | CM | a stale `.olean` masking a non-elaborating root | direct `lean WasmGemmGnaf.lean` |
| M9 | UV | a forbidden `Artifact` import into `Universal/Competitor.lean` | dependency firewall (SPEC §10.1) |
| M10 | CM | a manifest stage containing its own identity | acyclicity check (SPEC §4) |
| M11 | GO | `GlobalOptimal` weakened by a competitor scope predicate; a deleted binding; a tactic-proved binding | `Iff.rfl` schema binding in `Conformance/Schema.lean`, and the authority-driven audit in `just schema` |
| M12 | GO | a required declaration present but choice-tainted | SPEC §15 inventory reports `TAINTED`, not discharged |

M11 and M12 answer the audit's two remaining questions about what a *present* name
proves. M11 plants the weakening SPEC §1 forbids — the competitor quantifier
restricted to a named scope — and confirms the definitional binding stops
elaborating, which is the only thing separating "matches the frozen schema" from
"has the right name". It then attacks the wiring that decides whether the
elaborator is ever asked, by deleting a binding and by replacing `Iff.rfl` with
`by simp` on a copy of the binding source, and requires `just schema` to name both.
M12 plants a correctly named executable witness built by `Classical.choice` and
confirms it is reported `TAINTED` and **not** counted as discharged; a name-only
check credited exactly that shape before the audit caught it. Both carry a control:
the unweakened binding must still elaborate and the choice-free witness must still
be credited, so neither can pass by failing for an unrelated reason.

## How the frozen schema is actually compared

The audit's objection was that no tool compared compiled unfolded bodies against
`authority/global-optimality-WGG-GO-1.json`. Two things now do, and neither is a
hand-maintained checklist:

* **The authority JSON supplies the list.** `just schema` reads
  `scopeCriticalDefinitions` — currently fourteen names, not the thirteen quoted in
  review — and fails naming any entry with no binding. Nothing transcribes that
  array, so adding a definition to the frozen authority fails the gate at once.
* **The Lean elaborator is the comparator.** `WasmGemmGnaf/Conformance/Schema.lean`
  states each definition against its fully spelled-out body and closes it with
  `Iff.rfl` (propositions) or `rfl` (data). Narrowing a quantifier, dropping a
  conjunct, adding a hypothesis, substituting a scoped predicate or editing a field
  out of a record all stop elaborating. A tactic proof would establish only a
  *propositional* equivalence — which cannot tell the frozen schema from a weaker
  paraphrase — so `just schema` rejects any binding not closed definitionally.

M7 and M8 were added after real defects, not hypothetically. M7 answers the audit
finding that `universalCoverCompleteCheck` verifies bookkeeping only and is
satisfiable by an empty cover. M8 answers a worse one: `lakefile.lean` used
`globs := #[.submodules ...]`, which never builds the root module, so `lake build`
reported green for an entire cycle while two modules declared clashing `Fault`
types and the root did not elaborate at all. **`lake build` success is not evidence
that the code elaborates**; the gate now checks the root directly.

M4 and M6 are the ones that matter. SPEC §18 warns that a mutation suite which merely
expects runtime output differences does not test claim integrity; M4 and M6 attack the
claim machinery itself — they check that the repository cannot be made to *say* it
proved global optimality without a Lean declaration behind it.

## What is not yet falsifiable

Universal-coverage integrity (partition gaps, overlaps, forged lower bounds, stale
seals) cannot be falsification-tested until the checkers exist. Those falsifiers are
registered as outstanding rather than passing vacuously — a suite that passes because
its target does not exist is worse than no suite.
