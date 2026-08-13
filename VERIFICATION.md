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
| `just claims` | registry is nonempty, ids unique, no orphan dependencies, no `formalProof` row without a Lean declaration | `M2`, `M3`, `M4` |
| `just schema` | every `scopeCriticalDefinitions` entry of the frozen `WGG-GO-1` authority is bound to its fully spelled-out body by `Iff.rfl` / `rfl` | `M11` |
| `just vendor` | the vendored Core 3.0 tree, recomputed from CONTENT, matches the literals `Wasm.profile_matches_pinned_revision` stands on — the digest of `SHA256SUMS`, the per-file digests, the file count, the pinned commit — and every vendored rule anchor the conformance map cites is a label the vendored sources define | `M13` |
| `just core` | how much of the pinned Core 3.0 front end the Lean tree covers, against a checklist extracted from the vendored SpecTec sources; a marker naming an item those sources do not define fails | `M14` |
| `just mutation` | each decisive checker rejects a planted fault | self-testing |
| `just docs` | `CONFORMANCE.md` is generated, deterministic, byte-clean | `reproducible.yml` |
| `just vv` | all 13 conditions of SPEC §20.2 | `M6` |

## Why the source scan is not the decisive audit

SPEC §19 is explicit: source scanning is defence in depth. The decisive audit inspects
the **compiled environment** and the transitive dependencies of every public theorem,
via `#print axioms` in `just axioms`. A `sorry` reaches the environment as
`sorryAx`, so it is caught there even if the text scan is evaded.

Current closure over every `formalProof` claim: `propext`, `Quot.sound`, and
`Classical.choice` on some rows. All three are Lean core logical axioms and are named
individually as SPEC §4 requires — never as a category. No `sorryAx`, no
project-declared axiom, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

`Classical.choice` is permitted by SPEC §4; its one restriction is that it SHALL NOT
produce an executable witness. Every row whose closure contains it is a `Prop`-level
theorem and carries an `axiomNote` in `model/claims.json` saying which core lemma
introduced it. The rule is mechanized, not promised: `xtask claims required` reports a
choice-tainted executable witness as `TAINTED` and refuses to count it as discharged,
and `M12` plants exactly that shape to prove the refusal fires.

## Planted falsifiers

`just mutation`, registered in `model/falsifiers.json`. Each applies its mutation
to a **copy**, never to the repository.

| ID | Family | Plants | Rejected by |
| --- | --- | --- | --- |
| M1 | CM | mutated authority bytes | content digest recomputation |
| M2 | CM | duplicate claim id, spliced into a copy of the registry | `required::registry_violations` |
| M3 | CM | orphan claim dependency, on a copy of the registry | `required::registry_violations` |
| M4 | GO | `open` promoted to `formalProof` with no Lean declaration, on a copy | `required::registry_violations` |
| M5 | LF | `sorry` on the proof path | forbidden-construct scan |
| M6 | GO | green gate while `GO-001` is outstanding | release gate step 9 |
| M7 | AT | citing the seal's cover check as universal coverage | `AT-001` blindness lemma + `AT-002` absence |
| M8 | CM | a stale `.olean` masking a non-elaborating root | direct `lean WasmGemmGnaf.lean` |
| M9 | UV | a forbidden `Artifact` import into `Universal/Competitor.lean` | dependency firewall (SPEC §10.1) |
| M10 | CM | a manifest stage containing its own identity | acyclicity check (SPEC §4) |
| M11 | GO | `GlobalOptimal` weakened by a competitor scope predicate; a deleted binding; a tactic-proved binding | `Iff.rfl` schema binding in `Conformance/Schema.lean`, and the authority-driven audit in `just schema` |
| M12 | GO | a required declaration present but choice-tainted | SPEC §15 inventory reports `TAINTED`, not discharged |
| M13 | WS | a flipped digest, an appended line and a deleted entry in `vendor/wasm-spec/SHA256SUMS`, each on a copy of the vendored tree | `vendor::binding`, the checker `just vendor` and release gate step 1 both call |

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

M13 answers the same question one layer lower, about a *literal* rather than a name.
SPEC §7.1 defines `Wasm.profile_matches_pinned_revision` to mean, in part, that the
model and map are identity-bound to the **vendored** revision — but Lean cannot read
`vendor/wasm-spec/`. The theorem stands on `Wasm.core3VendorManifestSha256`, the
digest of `vendor/wasm-spec/SHA256SUMS`, which is itself the list of digests of all
forty vendored files; a literal that had drifted from the tree would still elaborate.
`just vendor` recomputes it from CONTENT, and M13 plants three faults on a **copy** of
the tree and requires the real checker to reject each. The middle one is the reason
the digest of digests is recorded at all: an appended line leaves every per-file
digest intact, so `sha256sum -c` alone passes it. The unmutated copy is the control.

The same checker closes the other half of the transcription record: every vendored
rule anchor `Wasm.PinnedCoreRuleId.vendorAnchor?` cites must be a label the vendored
reStructuredText actually **defines**, so an invented rule identifier fails the gate.
What that does *not* establish is stated in the header of `Wasm/Adequacy.lean` and
printed by `just vendor` on every run: the enumeration cites 73 distinct anchors of
the 835 rule-shaped labels the vendored tree defines, and 320 unexpanded SpecTec
`${rule: ...}` references remain in those sources with their `.watsup` bodies not
vendored — so the check tests rule *identity*, never rule *content*.

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

M2, M3 and M4 were rewritten after a defect found here rather than in review. Each one
used to reimplement its check *inside the falsifier*: M2 appended a duplicate id to an
in-memory `Vec` and asserted that `dedup` shrank it. That tests Rust's standard library.
None of the three ever invoked a gate, and the suite printed `[PASS] M2 duplicate claim
id rejected` at a moment when `model/claims.json` genuinely carried two rows with the id
`UV-004` and `just claims` accepted them — because `just claims` did not check ids at
all, though this table said it did. Both halves are fixed: `xtask claims list` now runs
the registry checker and fails on a violation, and the three falsifiers plant their fault
in a **copy** and call that same checker, each with the unmutated copy as a control.

The fix is itself falsified: deleting the duplicate rule from `registry_violations` turns
M2 red and leaves M3 and M4 green. **A falsifier that does not invoke the gate it names is
worth less than no falsifier, because it reads as evidence.**

## What is not yet falsifiable

Universal-coverage integrity (partition gaps, overlaps, forged lower bounds, stale
seals) cannot be falsification-tested until the checkers exist. Those falsifiers are
registered as outstanding rather than passing vacuously — a suite that passes because
its target does not exist is worse than no suite.
