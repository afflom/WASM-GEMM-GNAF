/-
# SPEC §15 required-declaration ledger

This module carries no mathematics.  It is the single place where every one of
the 58 declarations SPEC §15 requires is listed with **either** the Lean name
that discharges it **or** the obligation that blocks it.  A name appears in the
"discharged by" column only if a kernel-checked, `sorry`-free proof of that
proposition exists in this repository.  Where the repository proves something
*near* a required name but strictly weaker, the required name is recorded as
OUTSTANDING and the nearer result is named as such — never promoted.

Score: **36 of 58 discharged, 22 outstanding**, as `xtask claims required`
reports it against the compiled environment.  This header is prose and can
drift; that command is the ledger, and where the two disagree the command wins.

**The +2 is not yet release-connected, and that is the most important fact about
this tranche.**  `Universal.ProfileValid` — the predicate `GlobalOptimal`
quantifies over, and therefore the definition of the competitor universe — reads

    ∃ module : Wasm.Module, Wasm.Subset.decode bytes = .ok module ∧ …

So the release universe is still defined by the **subset** decoder, while
`Wasm.decode_sound` and `Wasm.decode_complete` are now about the **Core**
decoder.  Nothing regressed: before this tranche `Wasm.decode` *was* the subset
decoder, so `ProfileValid` denoted the same set it denotes now, and re-pointing
it explicitly is what kept the meaning fixed while the name moved.  But the two
names that moved are, for the moment, theorems about an object the release
theorem does not mention.  A strict release-connected count is entitled to score
this tranche at 24 rather than 26 for exactly that reason, and adversarial review
did.

Closing it needs `Universal/Competitor.lean` on `Wasm.Core.Module`, which needs
`validateUnder` and `HasExactGemmExports` on Core, which is the next tranche.
`Wasm/CoreGap.lean` proves there is **no total map** `Wasm.Module → Wasm.Core.Module`,
so this cannot be bridged — the universe has to be restated, not transported.

35 -> 36 is a NET of three movements this tranche, and the netting is the point:
`Wasm.decode_sound` and `Wasm.decode_complete` were re-pointed from the i32
subset codec to the pinned Core 3.0 decoder and grammar, which cleared both
CIRCULAR demotions (+2); `Artifact.decode_emit` was demoted to WEAKER in the
same movement, because SPEC 11.4 states it over `Wasm.decode` and there is no
Core 3.0 encoder in this repository (-1).  Reporting +2 without the -1 would be
the padding the previous tranche was graded for.

## Three counts, and why the repository report is the loosest of them

External review distinguishes three numbers, and the repository should quote all
three rather than the one that flatters it:

| Count | Value | What it measures |
|---|---|---|
| Repository report | **35 of 58** | the name exists AND carries SPEC's proposition AND is not circular |
| Exact-proposition audit | **30 of 58** | the above, re-derived by an external reviewer |
| Release-connected, full-Core | **24 of 58** | the above, AND stated over the pinned Core model rather than the i32 subset |

**The first row's most recent increment was not earned by a proof.**  34 → 35 is
`Wasm.costed_erase_iff_plain_run`, which `AMD-002` made bindable by amending
SPEC §7.5; `Wasm/Erasure.lean` was not modified and no proof line was added.  The
amendment was necessary — the superseded text is refuted — but the third row
correctly does not move for it, and `SPEC.md` §24 now carries the rule that an
amendment of that shape SHALL record the count it moves and the proof lines that
earned it, saying "zero" where that is the number.

The second and third rows are the external reviewer's figures at this commit.
The reviewer credits three of this round's additions and no more:
`Atlas.seal_verifier_reconstructs_every_preimage` (narrowly, for retained
objects — not universal coverage), `Atlas.lifecycle_native_bound` (with the
four-of-seventeen caveat below) and `Atlas.lifecycle_full_rebuild_comparator_exact`
(definitional wiring, not a regret bound).  **No Core theorem is credited**: the
new decoder has no completeness theorem and omits the GC and SIMD opcode spaces,
and the new validator has neither soundness nor declarative equivalence.

Both decoder findings are answered in this commit, and neither answer moves the
third row on its own.  `Wasm.Core.decode_complete` is closed at full Core --
`Bmodule (ByteArray.toBytes bytes) m -> decode bytes = .ok m`, choice free
(`[propext, Quot.sound]`), proved against the transcribed grammar with no
encoder anywhere in its import graph -- and `Wasm/Core/DecodeInstructions.lean`
now implements the `0xFB` (31 productions) and `0xFD` (256 productions) opcode
spaces, which `Wasm.Core.decode_complete` is what makes checkable: an omitted
production would be a `Binstr` derivation the decoder rejected.  The third row
did not move for it at that commit, because SPEC 15's `Wasm.decode_complete` was
still bound to `Wasm/Declarative.lean`'s theorem over the i32 subset and the
repository's own encoder, which `xtask independence` reported CIRCULAR.

**That re-pointing has now happened.**  `Wasm.decode`,
`Wasm.DeclarativeBinaryRelation`, `Wasm.decode_sound` and `Wasm.decode_complete`
denote the Core 3.0 decoder and the pinned grammar (`Wasm/CoreFrontEnd.lean`),
`xtask independence` passes for both names, and the subset codec survives under
`Wasm.Subset.*` where its type says what it is.  What the third row should now
count for the Wasm block is the two front-end names; `Wasm.validate_iff_declarative`,
`Wasm.validation_progress` and `Wasm.mem_successors_iff_step` are still stated
over the subset, for the reasons this file's debt list gives.

Of the three counts, the third is the one that matters, because it is the only
one that measures progress toward the release theorem.  Where this file's prose
and `xtask claims required` disagree, the command wins; where the command and
the external audit disagree, the audit is measuring something stricter and its
number is the honest one to quote.

The gap between the first and third rows is not a dispute about any Lean term.  It is that five
credited declarations are proved about the **obsolete subset machine and the
repository's own codec**, and must be *reproved* once `Wasm/Core/` replaces
them.  They are listed here so the debt is not forgotten:

* `Wasm.mem_successors_iff_step` — over `Wasm/Step.lean`'s subset relation
* `Wasm.bounded_tree_covers_every_branch` — over that same relation
* `Wasm.runFuel_sound` and `Wasm.runFuel_complete_with_bound` — likewise
* `Artifact.decode_emit` — over `Wasm/Binary.lean`'s custom codec

Each is a correct theorem about the object it names.  None of them is yet a
theorem about pinned Core 3.0, and the release theorem needs the latter.

`just core` measures the model gap directly, against a checklist extracted from
the vendored SpecTec sources:

    syntax 166/166   opcodes 543/543   validation 256/256   execution 239/239
    numerics definitions 84/84         TOTAL 1288/1288

and properties of that layer are known-incomplete rather than assumed sound: the
typing judgment does not yet carry every indexed operator/shape side condition
(so it is *wider* than Core's, which is a soundness defect and not a gap), and
nothing in `Binary`, `Declarative`, `Validate`, `Step`, `Profile`, `Cost`,
`GNAF` or `Release` has been migrated onto the Core types.

Execution is no longer parameterized by an arbitrary `Numerics` record.  Every
auxiliary function `3.1-numerics.scalar.spectec` and `3.2-numerics.vector.spectec`
define by equation -- all 84, the seventeen vector operator dispatchers included
-- is a `def` in `Wasm/Core/Numerics.lean`, so the step relation is quantified
only over the 74 primitives those two files declare `hint(builtin)` and give no
equations for, of which it calls 61.  That residue is irreducible from these
sources: a transcription cannot define what the source leaves abstract.

**The score fell from 36 to 34 when the checker started reading PROPOSITIONS
instead of names.**  An external audit objected that "its checker verifies names
rather than exact proposition types; its own M12 test demonstrates that a
matching-name `Nat := 0` is counted as discharged", and that was accurate.
`WasmGemmGnaf/Conformance/RequiredSignatures.lean` now restates every required
declaration in full and closes each one with `:= @Name`, so the comparison is
definitional and a `Nat := 0` under the right name does not elaborate;
`xtask signature` checks the wiring and `M15` is its falsifier.

Two names that were counted lost their credit to that check, and both rows below
already said why:

* `Wasm.costed_erase_iff_plain_run` — the `DEV-001` amended form, whose
  right-hand side carries a conjunct SPEC's biconditional does not.  The
  deviation is filed and argues SPEC's literal statement is false as written.
* `Atlas.incremental_eq_full_rebuild` — two hypotheses SPEC's statement does not
  have, `Coherent state.body` and `scope = Scope.unscoped`.  `Atlas/Rebuild.lean`
  argues the second is required for truth.  **No deviation is filed for it**;
  until one is, the name is outstanding.

Neither is a regression in what this repository proves.  Both are corrections to
what it was reporting.

**An external audit grades this repository lower than 34, and is right to.**  Its
strict count rejects `Wasm.decode_sound`, `Wasm.decode_complete` and
`Wasm.validate_iff_declarative` — they are proved against a hand-written subset
codec and an i32-only validator, while the released profile enables SIMD, GC and
references, tables, bulk memory, tail calls and exception handling.  Those three
rows below say what they cover; read them as the audit did.  `just core` now
measures the gap against a checklist **extracted from the vendored SpecTec
sources** rather than from anything this repository wrote, so the number is no
longer a matter of opinion.

## Obligation legend

The obligation IDs are the ones already fixed by `CERTIFICATION.md` §2, so this
ledger and the certification document cannot drift apart:

| ID | Obligation |
|----|------------|
| `O-1` | Competitor universe defined extensionally over all byte strings — *definable; stated at full strength in `Universal/Competitor.lean`* |
| `O-2` | Sublevel is finite and decidable — *closable; `Cost.objective_sublevel_finite` is the hinge* |
| `O-3` | Complete admission: `SystemEvaluationRel` sound / complete / functional — *the `functional` third is now closed; `sound` and `complete` are not* |
| `O-4` | Attainment: the shipped bytes' exact score computed |
| `O-5` | A universal lower bound `F`, attained — **no known technique** |
| `O-6` | Mechanized Wasm Core 3.0 semantics (GC, EH, SIMD, tail calls) and a compiler that can emit the four SPEC §8.2 arithmetic modes |

Two supporting records are cited where they are the precise reason:

* `DEV-001` (`model/spec-deviations.json`) — the literal SPEC §7.5 erasure
  biconditional is false as written; the amended form and the unconditional
  intent are both proved.
* `BI-002` / `BI-003` (`model/claims.json`) — `GNAF.compile` emits `unreachable`
  for the `checked`, `strictFloat` and `exactDyadicRoundOnce` arithmetic modes,
  so SPEC §13 Phase B (an input-total scalar GNAF GEMM plan) is not achievable
  with the current compiler and target.

`O-6` blocks `O-4` structurally: no baseline means no attained upper bound,
hence no sublevel, hence no argmin.  `O-5` is obstructed independently.

## Wasm — 10 of 11 discharged

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Wasm.decode_sound` | `WasmGemmGnaf.Wasm.decode_sound` (`Wasm/CoreFrontEnd.lean`), re-indexed as `Theorems.decode_sound`.  **RE-POINTED to `Wasm.Core` this tranche.**  `Wasm.decode` is now the executable decoder for the COMPLETE pinned Core 3.0 binary format (`Wasm/Core/Decode.lean`) and `Wasm.DeclarativeBinaryRelation` is now the pinned grammar `Wasm.Core.Binary.Bmodule`, transcribed from `5.*-binary.*.spectec` at the pinned commit; the theorem is `Wasm.Core.decode_sound`.  Axiom closure `[propext, Quot.sound]`.  `xtask independence` PASSES: there is no encoder anywhere in the import graph of `Wasm/Core/`, so the two sides were written from different documents.  What it used to be, and why it was demoted: the subset codec of `Wasm/Binary.lean` against the subset grammar of `Wasm/Declarative.lean`, proved through `declarativeBinaryRelation_iff_encode` — a decoder inverse to its own encoder.  That pair survives, still proved, as `Wasm.Subset.decode_sound`. |
| `Wasm.decode_complete` | `WasmGemmGnaf.Wasm.decode_complete` (`Wasm/CoreFrontEnd.lean`), re-indexed as `Theorems.decode_complete`.  **RE-POINTED to `Wasm.Core` this tranche**, same relation and same independence verdict as the row above; the theorem is `Wasm.Core.decode_complete`, which covers the whole module format including the `0xFB` (GC) and `0xFD` (SIMD) opcode spaces.  Axiom closure `[propext, Quot.sound]` — choice free, as SPEC §4 requires of an executable witness.  This is the direction a rejecting decoder would fail: a production the decoder did not implement would be a `Bmodule` derivation it rejected, and the theorem says there is none.  The subset pair survives as `Wasm.Subset.decode_complete`. |
| `Wasm.validate_iff_declarative` | `WasmGemmGnaf.Wasm.validate_iff_declarative` (`Wasm/Declarative.lean`), re-indexed as `Theorems.validate_iff_declarative`.  The SPEC §15 statement is exactly the proposition `WasmGemmGnaf.Wasm.validate_bool_iff` proves, so it is discharged by `exact` with no weakening.  Before this row could be claimed, `Wasm.DeclarativelyValid` had to be *strengthened*, because it was strictly laxer than Core 3.0 validation in four places and so could not be aliased to the required name.  (1) **Block frames.**  `block`/`loop`/`if` typed their bodies at the *enclosing absolute* stack height, so a body could consume operands pushed before the block was entered; `i32.const 0 ; block (drop ; i32.const 0) ; drop` was accepted and Core rejects it.  Bodies are now typed frame-relative, at height `0` returning to `0`, which is the `val_height` discipline of `appendix/algorithm.rst` (`push_ctrl` / `pop_val` / `pop_ctrl`) with `Nat` itself as the underflow check.  `Wasm.Ctx.labels` accordingly records label *result arities*, per `valid/conventions.rst` "Contexts", and `Wasm.Module.funcCtx` now seeds the label stack with the function's result arity — the "implicit outermost label" of `appendix/algorithm.rst`.  (2) **Alignment.**  `i32.load`/`i32.store` carried no bound on `memarg.align`; `valid/instructions.rst` `_valid-load-val` requires `2 ^ align <= │t│/8`, here `align <= 2` (`Wasm.alignOk_iff_pow_le`).  (3) **Type section.**  `Module_ok` has `Types_ok` as a premise, so a declared type no function names still has to be well formed; `Wasm.Module.checkTypes` now requires every declared sub type to be final, supertype-free and an all-`i32` function type, which entails `Subtype_ok`.  (4) **Export names.**  `syntax/modules.rst` "Exports" requires each export name to be unique; `Wasm.Module.checkExports` now enforces it.  `Wasm.validate` and its correctness proof were repaired to match, and `GNAF.validate_moduleOf`, `GNAF.checkList_*` and the two `Artifact` modules re-proved against the strengthened checker.  What remains scoped, and is stated in the doc comment of the theorem and in the header of `Wasm/Validate.lean` rather than only here: the judgment does **not** model Core's stack polymorphism (`valid/instructions.rst` `_polymorphism`; `unreachable`, `br` and `throw` are typed concretely), and does not cover SIMD, GC, reference types, tables, bulk memory, tail calls, `try_table`/`throw_ref`, `call`/`call_indirect`/`return`/`br_table`/`select`, non-empty block types, `i64`, `f32` or `f64`.  Both gaps make the judgment *narrower* than Core, never wider, so `DeclarativelyValid` is a sound restriction of Core 3.0 validation and this theorem is an equivalence for the modelled subset rather than for all of Core 3.0.   **STILL OVER THE i32 SUBSET, and still CIRCULAR.**  `xtask independence` rejects it: `Wasm.DeclarativelyValid` is a conjunction of the executable checker's own booleans (`Module.checkGlobal` and eight others), so the biconditional is very nearly `Bool = true ↔ Bool = true`.  It was NOT re-pointed at `Wasm.Core` this tranche, and the reason is a theorem, not a shortage of effort: `Wasm.Core.validate_iff_declarative` reads `validate m = true ↔ Validate.Module.frag m = true ∧ ∃ mt, Module_ok' m mt`, i.e. it carries the residual guard `Module.frag`, which still excludes tables and element segments.  Dropping the guard makes the biconditional FALSE (a module with a table can be `Module_ok'` while `Core.validate` says false); keeping it puts a checker-side boolean back into the declarative side, which is the exact defect the independence check exists to catch.  Removing the guard needs `checkSeq` to match operands by `Valtype_sub` rather than by equality, which needs a decision procedure for `Heaptype_sub`; that does not exist in this repository. |
| `Wasm.validation_progress` | `WasmGemmGnaf.Wasm.validation_progress` (`Wasm/Soundness.lean`), re-indexed as `Theorems.validation_progress`, at SPEC §7.3's statement verbatim.  Axiom closure `[propext, Classical.choice, Quot.sound]`.  `Wasm.Halt`/`Trapped`/`Thrown` are the SPEC §7.1 projections of `Config.status`, and `Wasm.isTerminal_iff_halt_trapped_thrown` proves the SPEC §7.1 equivalence for them, so the first three disjuncts really are "the machine has stopped".  `Wasm.ConfigWellTyped` is the syntactic typing invariant stated in the *declarative* judgment of `Wasm/Validate.lean` (`InstrTyping`/`ExprTyping`): a context whose `numLocals` is the frame's local count and whose `globals` has the store's global count, a well-formed control stack (each `CtrlEntry` at or above the height of the entry outside it, its `cont` typed at its suspended relative height, a `loop`'s `body` typed `0 → 0` one label deeper), an operand stack equal to the innermost recorded height plus the current relative height, and code typed at that relative height with exactly one arity-`0` label per control-stack entry.  It mentions neither `Step` nor `successors` nor `Config.status`, so it does not smuggle the conclusion in; it is proved **preserved** by every reduction rule (`Wasm.validation_preservation`, SPEC §7.3's name carrying the invariant hypothesis SPEC's literal signature omits — without it that statement is false) and proved **reachable** from `Wasm.initialConfig` (`Wasm.initialConfig_configWellTyped`; unconditional when the module has no start function).  `Wasm.ConfigInstantiates` ties the configuration to the module: store globals from the module's globals, harness from the module's exported `gemm`, two ABI arguments; it is itself preserved by reduction (`Wasm.ConfigInstantiates.step`).  That the invariant is not simply `True` is proved, not asserted: `Wasm.not_configWellTyped_drop_empty` rejects an operand-stack underflow and `Wasm.not_configWellTyped_call` rejects any configuration whose head instruction is outside the modelled subset — the second is the load-bearing use of validation.  Two scope facts, both stated in the header of `Wasm/Soundness.lean` rather than only here.  (1) This is soundness for the **modelled** subset, not for Core 3.0: GC, SIMD, tables, calls, `br_table`, `select`, `i64` and floating point have no typing rule at all, which is exactly why `hwelltyped` is load-bearing.  (2) `Module.funcCtx` seeds a body's label stack with the function's own result arity — Core's implicit outermost label — so `Wasm.validate` accepts `br` to it, but `Wasm/Step.lean` models no reduction for that branch (`br`/`br_if` reduce only through `Config.ctrl`).  Such a configuration is genuinely stuck, so no invariant can prove progress for it; the invariant therefore gives the frame exactly one label per `CtrlEntry`, which is precisely "every branch targets a label the code opened itself".  `Wasm.GemmFrameLocal` and `Wasm.StartFrameLocal` name that condition at module level.  It is a restriction on modules, not a weakening of the theorem's statement, and the released compiler of `GNAF/Compile.lean` emits only `block`/`loop`-local branches.   **STILL OVER THE i32 SUBSET.**  Not re-pointed at `Wasm.Core` this tranche, and it cannot be stated there yet: SPEC §7.3's hypothesis `Wasm.ConfigWellTyped config` needs a configuration typing judgment, and `Wasm/Core/` has none — no `Config_ok`, no `Store_ok`, no typing for administrative instructions.  Its conclusion needs `Wasm.successors`, which `Wasm/Core/` also has none of (see the row below).  Stating progress over Core therefore requires building both judgments first; nothing weaker would be SPEC's proposition. |
| `Wasm.mem_successors_iff_step` | `WasmGemmGnaf.Wasm.mem_successors_iff_step`, re-indexed as `Theorems.mem_successors_iff_step`.  **STILL OVER THE i32 SUBSET.**  Not re-pointed at `Wasm.Core` this tranche.  `Wasm/Core/Execution.lean` has the step relation — `Step (Nm : Numerics) : State → List AdminInstr → State → List AdminInstr → Prop`, 239 transcribed rules — but there is no `successors` enumerator anywhere under `Wasm/Core/`, and three things have to be built before one can be: (1) an `Event` notion, since Core `Step` carries no observable label and SPEC's statement is `(event, next) ∈ successors config ↔ Step config event next`; (2) a canonical redex decomposition with a uniqueness proof, because `Step/ctxt-instrs` closes the relation under *every* split `val* instr* instr_1*` and the `↔` has to reproduce exactly that set; (3) decidability for the `Prop`-valued premises of the read rules.  The set-valued numeric results are `List`-valued in `Numerics`, so those are enumerable — the obstruction is the context closure and the missing event, not the nondeterminism. |
| `Wasm.bounded_tree_covers_every_branch` | `WasmGemmGnaf.Wasm.bounded_tree_covers_every_branch` (`Wasm/Fuel.lean`), re-indexed as `Theorems.bounded_tree_covers_every_branch`.  From `Wasm.exploreAll bound initial = .complete obs cov` and `Wasm.FiniteExecution initial o` it concludes `o ∈ obs` with **no** hypothesis on `o.trace.length` — the third clause of SPEC §7.4, "and that `complete` contains every maximal branch", which `Wasm.runFuel_complete_with_bound` does not give because its conclusion is conditional on `observation.trace.length ≤ bound`.  What makes the unconditional form true is proved rather than assumed: the `complete` constructor is reachable only when `Wasm.prefixes (bound + 1) [] initial = []`, and the new `Wasm.prefixes_complete` (the converse of the existing `Wasm.prefixes_sound`, with `Wasm.Reduces.split`) turns that into a proof that *every* finite execution of that `initial` has a trace of length at most `bound + 1`.  So the bound is a proved property of `initial`, not a restriction on the runs covered.  Axiom closure `[propext, Quot.sound]` — choice free.  Scope: the statement is about the `complete` constructor only; a `nonterminalPrefix` result genuinely misses branches that terminate past `bound + 1`, and no claim is made about those.  Divergent branches are outside `FiniteExecution` by construction and remain uncovered, as SPEC §7.4's "No general halting oracle is permitted" requires. |
| `Wasm.runFuel_sound` | `WasmGemmGnaf.Wasm.runFuel_sound` (`Wasm/Fuel.lean`). |
| `Wasm.runFuel_complete_with_bound` | `WasmGemmGnaf.Wasm.runFuel_complete_with_bound` (`Wasm/Fuel.lean`). |
| `Wasm.costed_erase_iff_plain_run` | **OUTSTANDING.**  `WasmGemmGnaf.Wasm.costed_erase_iff_plain_run` exists and is re-indexed as `Theorems.costed_erase_iff_plain_run`, but in the `DEV-001` amended form: its right-hand side carries the extra conjunct `Wasm.CostedLabelling module invocation costedTrace`, so the forward direction is strictly stronger than SPEC §7.5's and the backward direction strictly weaker.  It is therefore not SPEC's proposition and no longer counts.  `Conformance/RequiredSignatures.lean` pins the amended form under `-- spec-signature-amended:` so it cannot drift either; `DEV-001` argues SPEC's literal biconditional is false as written and names `Theorems.costed_run_iff_plain_run` as carrying the unconditional intent. |
| `Wasm.costed_initialization_erase` | `WasmGemmGnaf.Wasm.costed_initialization_erase` (`Wasm/CostedExplore.lean`): erasing the charge from a completed costed initialization leaves exactly `Wasm.initialGemmInvocation`, the plain entry point defined alongside it, on the configuration the costed observation carries.  `Wasm.costed_initialization_of_erase` is the converse (the plain result determines the costed one, at the pinned `Wasm.initializationCost`) and `Wasm.costed_initialization_erase_error` is the failure half, so the two entry points are mutually determined.  Axiom closure `[propext, Quot.sound]`.  `Wasm/Erasure.lean` still covers only the reduction phase; this is the instantiation phase. |
| `Wasm.profile_matches_pinned_revision` | `WasmGemmGnaf.Wasm.profile_matches_pinned_revision` (`Wasm/Adequacy.lean`), re-indexed as `Theorems.profile_matches_pinned_revision`.  Stated as the conjunction SPEC §7.1 *defines* the name to mean, and no more: (i) the concrete model and map are identity-bound to the **vendored** revision — the profile, the conformance map and `Wasm.core3VendoredTree` carry one commit, the map carries the digest of `vendor/wasm-spec/SHA256SUMS` (the digest of digests over all forty vendored files), and both canonical identities are injective, so a different revision or a single different vendored byte gives a different identity; (ii) every enabled vendored rule has **exactly one** mapped Lean declaration — one fully qualified name, one map row and one vendored anchor per enabled identifier, no declaration shared by two identifiers, and nothing at all for a rejected one.  Axiom closure `[propext, Classical.choice, Quot.sound]`; the `Classical.choice` enters through Lean core's `String.ofList_toList`, used by `string_append_left_cancel` to cancel the namespace prefix, and this is a Prop-level theorem, not an executable witness, so SPEC §4's restriction is not triggered.  **What holds it up outside the kernel, stated plainly**: Lean cannot read `vendor/wasm-spec/`, so the tree binding rests on the literals `Wasm.core3VendorManifestSha256`, `fileCount` and `core3RevisionCommit`; `xtask vendor` (gate step 1, `just vendor`) recomputes the digest of digests from CONTENT, rechecks `SHA256SUMS` against all forty files, compares the commit with `vendor/wasm-spec/PINNED-COMMIT`, and checks that every anchor `Wasm.PinnedCoreRuleId.vendorAnchor?` cites is a label the vendored `.rst` sources actually DEFINE; falsifier `M13` plants a flipped digest, an appended line and a deleted entry on a COPY and requires each to be rejected, with the unmutated copy as control.  **What is still not established**: the enumeration cites 73 distinct anchors of the 835 rule-shaped labels the vendored tree defines, so it is a declared *subset* of the pinned rule set and is not proved to be all of it; and 320 unexpanded SpecTec `${rule: ...}` references remain in the vendored sources, whose `.watsup` bodies are not vendored, so the anchor check tests rule IDENTITY and never rule CONTENT.  Neither gap is inside this theorem's statement — SPEC §7.1 explicitly places the transcription on the authority side of the boundary — but both are why `WS-001`/`O-6` stay open.   **THE ADEQUACY MAP IS NOT MIGRATED; ONE ROW OF IT IS.**  `binary-module` now maps to `WasmGemmGnaf.Wasm.decode`, which is the pinned Core 3.0 decoder.  Every other row still names a declaration of the i32 subset model (`InstrTyping.*`, `Step.*`, `Store.*`, `TableInst.*`, `V128.*`).  So what this theorem establishes today is that the map is total, injective and identity-bound to the vendored revision on the enabled set — not that the mapped declarations are the mechanized Core 3.0 rules of `Wasm/Core/`.  `Wasm/Adequacy.lean`'s header carries this as an open gap rather than leaving it implied.  Re-pointing the remaining rows needs, for each one, the Core declaration that actually transcribes its vendored rule; guessing one would be worse than the disclosure. |

## Gemm — 10 of 10 discharged

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Gemm.classify_total` | `WasmGemmGnaf.Gemm.classify_total`, re-indexed as `Theorems.classify_total`.  (`WasmGemmGnaf.GNAF.classify_total` is a different, unrelated theorem about `GNAF.Machine`.) |
| `Gemm.reference_total` | `WasmGemmGnaf.Gemm.reference_total` (`Gemm/Reference.lean`), re-indexed as `Theorems.reference_total`: every raw invocation — malformed, truncated, unsupported, resource-invalid or valid — has an accepted observation. |
| `Gemm.valid_input_finite` | `WasmGemmGnaf.Gemm.valid_input_finite` (`Universal/EnumerateInputs.lean`): a global, constructive `Foundation.Fintype` on `{raw : RawInvocation P // refValid raw.body = true}`, the subtype `Gemm.refValid_iff_classify` identifies with the classifier's `valid` verdict.  The enumeration `validRawInvocations`, both of its proofs and the carrier predicate are choice-free: axiom closure `[propext, Quot.sound]`, as SPEC §4 demands of an executable witness.  The `Decidable` instances `Gemm.refValid` decides through are *data*, so `Shape.isEmpty_eq_false_iff`, `ByteRange.overlapCount_pos_iff`, `View.addr_bounds` and `View.checkInterval_iff` introduce their `Iff` and `∧` connectives by hand rather than by `omega`, which discharges them classically.  `Gemm.classify` and `Gemm.refValid` are choice-free for the same reason. |
| `Gemm.raw_input_finite` | `WasmGemmGnaf.Gemm.raw_input_finite` (`Universal/EnumerateInputs.lean`): SPEC §8.4's `instance problem_input_fintype`, as a **global** instance with no instance hypothesis.  `Gemm.rawInvocations` ranges `ptr` and `len` over `Gemm.allUInt32` and `bytes` over `Gemm.byteArraysOfSize len.toNat`, attaching the SPEC §8.3 lawfulness proof; `Gemm.mem_rawInvocations` and `Gemm.rawInvocations_nodup` are proved structurally, never by evaluation.  Axiom closure: `[propext, Quot.sound]` — no `Classical.choice`.  The hypothesis `[Foundation.Fintype (Gemm.RawInvocation P)]` still *appears* on the older `Universal` and `Artifact` results, which were written before the instance existed; it is now discharged by this instance rather than assumed. |
| `Gemm.raw_invocation_roundtrip` | `WasmGemmGnaf.Gemm.raw_invocation_roundtrip`, re-indexed as `Theorems.raw_invocation_roundtrip`. |
| `Gemm.raw_invocation_surjective` | `WasmGemmGnaf.Gemm.raw_invocation_surjective`, re-indexed as `Theorems.raw_invocation_surjective`. |
| `Gemm.abi_roundtrip` | `WasmGemmGnaf.Gemm.abi_roundtrip`, re-indexed as `Theorems.abi_roundtrip`. |
| `Gemm.classifier_exact_domain` | `WasmGemmGnaf.Gemm.classifier_exact_domain`, re-indexed as `Theorems.classifier_exact_domain`. |
| `Gemm.mandatory_family_nonzero_witnesses` | `WasmGemmGnaf.Gemm.mandatory_family_nonzero_witnesses` (`Gemm/Reference.lean`), re-indexed as `Theorems.mandatory_family_nonzero_witnesses`, with `Gemm.mandatoryCases_covers` proving the family covers every mandatory combination.  **Scope**: this is a statement about the *classifier and the reference arithmetic*, which is what the `Gemm` namespace name asks for.  It does not claim the released compiler can emit code for those modes — that is `GNAF.compile_refines`, still blocked by `BI-002`/`BI-003`. |
| `Gemm.observation_covers_status_and_full_c` | `WasmGemmGnaf.Gemm.observation_covers_status_and_full_c` (`Gemm/Reference.lean`), re-indexed as `Theorems.observation_covers_status_and_full_c`. |

## Cost — 3 of 3 discharged

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Cost.module_bytes_exact` | `WasmGemmGnaf.Cost.module_bytes_exact` (`Cost/Aggregate.lean`), re-indexed as `Theorems.module_bytes_exact`.  Scope: `ExactAggregateCost` takes `decodes`/`decodeSteps`/`validationSteps`/`staticDataBytes` as parameters, so this is conditional on a cost vector being exact — it does not itself pin a released artifact's cost (`O-4`). |
| `Cost.transition_accounting_positive` | `WasmGemmGnaf.Cost.transition_accounting_positive` (`Cost/Event.lean`), re-indexed as `Theorems.transition_accounting_positive`. |
| `Cost.objective_sublevel_finite` | `WasmGemmGnaf.Cost.objective_sublevel_finite`, re-indexed as `Theorems.objective_sublevel_finite`. |

The Cost layer is complete against SPEC §15.  What is missing downstream is not
the objective but anything to apply it to.

## GNAF and the emitter — 2 of 5 discharged

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `GNAF.normalize_semantics` | `WasmGemmGnaf.GNAF.normalize_semantics` (`GNAF/Normalize.lean`). |
| `GNAF.normalize_cost_le` | `WasmGemmGnaf.GNAF.normalize_cost_le` (`GNAF/Normalize.lean`). |
| `GNAF.compile_refines` | **OUTSTANDING — `O-6`** (`BI-002`).  `GNAF/CompileCorrect.lean` proves many compilation invariants (`compile_initialConfig`, `compile_runInvariant`, `compile_body_reachable`, `compile_emit_decodes_valid`, …) but no refinement of the GEMM reference semantics by the compiled module. |
| `GNAF.compile_cost_exact` | **OUTSTANDING — `O-6`.**  Absent. |
| `Artifact.decode_emit` | **OUTSTANDING — DEMOTED this tranche, and the demotion is the honest consequence of re-pointing `Wasm.decode`.**  `WasmGemmGnaf.Artifact.decode_emit` (`Artifact/Emit.lean`) still exists and is still proved, but it now reads `Wasm.Subset.decode (Artifact.emit m) = .ok m`: `emit` is *defined* as `Wasm.Subset.encode`, so it is the subset codec's round trip transported along the definition.  SPEC §11.4's `Wasm.decode` is, since this tranche, the Core 3.0 decoder, and there is no Core 3.0 ENCODER in this repository — `Wasm/Core/` contains none, which is exactly what makes `Wasm.decode_sound`/`_complete` non-circular.  `Wasm/CoreGap.lean` proves in addition that no total map `Wasm.Module → Wasm.Core.Module` exists, so the subset emitter cannot be transported along one either.  `Conformance/RequiredSignatures.lean` pins the weaker proposition under `-- spec-signature-weaker:` so it cannot drift.  Writing a Core 3.0 encoder with a `Bmodule` derivation closes this row. |

## Universal — 3 of 12 discharged

`Universal/Competitor.lean`, `Correct.lean`, `Feasible.lean`, `Sublevel.lean`,
`LowerBound.lean`, `BilinearLowerBound.lean`, `Partition.lean` and `Argmin.lean`
exist and are proof-carrying, but none of them proves a §15 name: they establish
the *definitions* at full strength and the algebraic facts around them.
`Universal/EnumerateInputs.lean` now exists and proves two of them (the input
enumerator and the byte enumerator); `Universal/Argmin.lean` proves the third.
`Universal/CheckExecution.lean` and `Coverage.lean` do not exist, and
`EnumerateBytes.lean` is not a separate file — its content lives in
`EnumerateInputs.lean` beside the input enumerator.

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Universal.possible_winner_within_sublevel` | `WasmGemmGnaf.Universal.possible_winner_within_sublevel` (`Universal/Sublevel.lean`), at SPEC §10.3's exact statement with its five premises verbatim and in SPEC's order.  `Universal.WithinSublevel` is the conclusion: the exact aggregate cost lies inside the objective's **own** `boundOfScore`, and the module byte count inside that bound's `staticModuleBytes` coordinate — the second conjunct *derived* from the first through `Cost.module_bytes_exact`, never assumed.  Only `hbetter` is used: `Universal.withinSublevel_of_score_le` proves the same conclusion from the score inequality alone, so carrying SPEC's other premises cannot be mistaken for needing them.  Axiom closure `[propext, Quot.sound]`.  **Scope**: this CONFINES a competitor *given* an evaluation of it.  It does not produce that evaluation (`system_evaluation_rel_complete`, outstanding), does not claim every competitor has one, and does not claim the sublevel has been searched (`universal_sublevel_coverage`, outstanding).  Bounding a carrier is not covering it. |
| `Universal.byte_enumerator_complete` | `WasmGemmGnaf.Universal.byte_enumerator_complete` (`Universal/EnumerateInputs.lean`): every byte sequence of size at most `bound` occurs in `Universal.byteEnumerator bound`, unconditionally.  `Universal.byte_enumerator_exact` is the converse inclusion and `Universal.byte_enumerator_nodup` the duplicate-freedom — proved from `byteListsOfLength_nodup`, `Foundation.Bytes.pack_injective` and a size argument across length blocks, never by decidable equality on `ByteArray`.  Axiom closure `[propext, Quot.sound]`, as SPEC §4 requires of an executable witness.  `Universal.byte_enumerator_covers_sublevel` is the sublevel bridge.  **This is finiteness of the byte carrier and nothing more**: it is not a decoder/validator pipeline over that carrier, and `Universal.execution_checker_sound` remains outstanding. |
| `Universal.input_enumerator_complete` | `WasmGemmGnaf.Universal.input_enumerator_complete` (`Universal/EnumerateInputs.lean`): every `raw : Gemm.RawInvocation P` occurs in `Universal.inputEnumerator P`, unconditionally — no `Fintype` hypothesis, no sublevel bound, no scope predicate.  `Universal.inputEnumerator_nodup` gives the exactness half. |
| `Universal.execution_checker_sound` | **OUTSTANDING — `O-3`, `O-6`.**  `Universal/CheckExecution.lean` does not exist. |
| `Universal.execution_checker_complete_within_sublevel` | **OUTSTANDING — `O-3`, `O-6`.** |
| `Universal.system_evaluation_rel_sound` | **OUTSTANDING — `O-6`.**  SPEC §10.1 states this as the *reflection biconditional* `(Correct ↔ SemanticCorrect) ∧ (Feasible ↔ SemanticWithinResources)` over the implemented `Universal.evaluate`, which does not exist here.  Nearest proved: `WasmGemmGnaf.Universal.correct_of_admissible` and `feasible_of_admissible` (the ⟸ direction of each, from the three extensional predicates).  `Release.systemEvaluationRel_sound` used to be cited here; it is **deleted** along with `Release.decider`. |
| `Universal.system_evaluation_rel_complete` | **OUTSTANDING — `O-6`.**  SPEC's statement **asserts existence**: profile-valid + semantically correct + within resources ⟹ `∃ evaluation, SystemEvaluationRel …`.  That is exactly the open nonemptiness obligation.  `Release.systemEvaluationRel_complete`, which took the evaluation as an *argument* and was therefore strictly weaker, is **deleted** along with `Release.decider`. |
| `Universal.system_evaluation_rel_functional` | `WasmGemmGnaf.Universal.system_evaluation_rel_functional` (`Universal/Argmin.lean`), stated in SPEC §10.1's exact shape and **unconditionally**: no `Foundation.Fintype` hypothesis, since `Gemm.raw_input_finite` discharges it (`O-3` closed for this row), and quantified over every `Setting` and every `Decider`, so it holds verbatim of SPEC §10.1's implemented `Universal.evaluate` once that exists.  Proved from `Universal.systemEvaluation_subsingleton`, i.e. from uniqueness of the *codomain*, which is strictly stronger than functionality of the relation; `Universal.systemEvaluation_unique` states that decider-independent half separately. |
| `Universal.partition_cover_complete` | `WasmGemmGnaf.Universal.partition_cover_complete` (`Universal/Partition.lean`): every byte string the root cell denotes is either **resolved** — `Universal.Resolved`, the three terminal verdicts of SPEC §10.4 with their proof content carried, not summarised — or the strategy is *exhibited* reporting a coverage gap on a cell that denotes it.  The `incomplete` case is a disjunct of the **conclusion**, not a hypothesis excluding it, so a strategy that gives up is caught rather than assumed away; `partition_cover_complete_of_sealable` is the sealed-certificate corollary.  Strictly stronger than the pre-existing `coverLeaves_covers`, which reached a leaf without saying what happened there.  **Scope**: conditional on `root.Denotes bytes`, and `coverLeaves_covers_scope` proves machine-checked that roots denoting almost nothing exist.  No `dominated` instance is constructed: its `memberLowerBound` field is `O-5` itself, so the third verdict is transported, never produced. |
| `Universal.universal_sublevel_coverage` | **OUTSTANDING — `O-5`** (`UV-001`).  SPEC §10.5 requires this to have *no* coverage hypothesis; `Atlas.universalCoverCompleteCheck_scope_blind` proves the recorded seal cover cannot supply it. |
| `Universal.selected_le_every_sublevel_member` | **OUTSTANDING — `O-4`, `O-5`.** |
| `Universal.all_competitors_lower_bound` | **OUTSTANDING — `O-5`.**  No known technique.  Nearest proved: `WasmGemmGnaf.Universal.attained_lower_bound_is_optimal` — which says an *attained* bound would suffice, and `lower_bound_below_released_is_not_optimality`, which says an unattained one would not. |

## Atlas — 6 of 10 discharged

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Atlas.semantic_closure_least` | `WasmGemmGnaf.Atlas.semantic_closure_least`, re-indexed as `Theorems.semantic_closure_least`. |
| `Atlas.attention_no_optimum_relevant_false_negative` | **OUTSTANDING — `O-3`, `O-5`.**  The statement needs a notion of optimum, which does not exist here.  Nearest proved: `WasmGemmGnaf.Atlas.attend_determined_by_index`, `attend_monotone`, `attend_blind_to_optimizer_state`. |
| `Atlas.invalidation_complete` | `WasmGemmGnaf.Atlas.invalidation_complete` (`Atlas/Dependency.lean`). |
| `Atlas.incremental_eq_full_rebuild` | **OUTSTANDING.**  `WasmGemmGnaf.Atlas.incremental_eq_full_rebuild` exists and is re-indexed as `Theorems.incremental_eq_full_rebuild`, but carries two hypotheses SPEC §12.5's statement does not: `Atlas.Coherent state.body` and `state.body.scope = Scope.unscoped`.  `Atlas/Rebuild.lean` argues the second is required for truth — `semanticRebuildBody` takes only the declaration base and so cannot reproduce a scope the declarations do not name — and proves the general form as `Theorems.incremental_eq_full_rebuild_scoped`, strengthened past canonicalisation by `Theorems.incremental_eq_full_rebuild_exact`.  That argument is very likely right, but **no deviation is filed in `model/spec-deviations.json`**, so unlike `DEV-001` there is no reviewed record of it and the required name stays outstanding.  `Conformance/RequiredSignatures.lean` pins the weaker form under `-- spec-signature-weaker:`.  Filing the deviation, or proving SPEC's literal form, closes this row. |
| `Atlas.seal_verifier_reconstructs_every_preimage` | `WasmGemmGnaf.Atlas.seal_verifier_reconstructs_every_preimage` (`Atlas/Reconstruct.lean`).  SPEC states no fenced theorem, so the binding quotes SPEC §12.1 ("storing the complete checker input, result, and retained preimages in canonical form") and SPEC §20.2 item 10.  The verifier's ONLY input is the seal identity — one `ObjectId (SealCore × SealCertificateBody)`; it is handed no state, no object graph, no preimage and no proof, which is what stops the statement collapsing into a consistency check on the caller.  It opens that identity into the proof-free `SealCertificateBody`, reads the *recorded* `retentionCheckResultId`, opens that into the checker record, and returns its preimages; both openings are total executable readers proved left inverse to the canonical encoders (`Atlas.sealCertificateBodyR_inverts`, `Atlas.sealCheckResultBodyR_inverts`), so the content is effectiveness rather than the schemas' injectivity.  Conclusion: the reconstructed list **is** `state.retainedObjects.graph.preimages`, and every id in the seal's own `retentionRoot` is answered with bytes proved to be that id's retained entry; `seal_verifier_reconstructs_referenced_preimage` specialises it to SPEC §12.1's referenced objects and `seal_verifier_reconstructs_state_body_bytes` recovers the state body's canonical preimage.  **Scope**: everything reconstructed comes from a finite list the seal itself records — this is not coverage of anything, a seal retaining three objects satisfies it, and `Atlas.universalCoverCompleteCheck_scope_blind` is untouched.  `Atlas.sealVerifierPreimages_rejects_malformed` proves the reader can fail, so the statement is not about a constant function. |
| `Atlas.seal_implies_universal_coverage` | **OUTSTANDING — `O-5`, and deliberately so.**  `Theorems.universalCoverCompleteCheck_scope_blind` proves the seal's cover check is a function of three recorded components and therefore cannot witness any proposition quantified over `ByteArray`.  Deriving this name from the seal would be unsound. |
| `Atlas.lifecycle_prefix_conservation` | `WasmGemmGnaf.Atlas.lifecycle_prefix_conservation` (`Atlas/Lifecycle.lean`), matching SPEC §16's statement.  Scope: it holds of every `Atlas.LifecycleEvaluation` because that structure's `totalExact` field *demands* the exact mixed fold — the content is that the carrier stores no unchecked total, not that some particular lifecycle was measured. |
| `Atlas.lifecycle_native_bound` | `WasmGemmGnaf.Atlas.lifecycle_native_bound` (`Atlas/Lifecycle.lean`), at SPEC §16's statement.  The row previously read OUTSTANDING because "the coefficients that would make it true are a property of a release table this repository has not pinned" — true, and the fix rather than the obstacle: `Release.primitiveCostTable` is now pinned in `Cost/Lifecycle.lean` with every coefficient `1`, the componentwise-minimal positive table SPEC §16 admits, and `Atlas.lifecycle_native_bound_of_positive` proves the inequality for *every* positive table so nothing rests on the choice.  Scope: `≤` is componentwise over all seventeen coordinates; `Atlas.lifecycle_native_bound_attained` proves fourteen of them hold with equality, and `Atlas.lifecycle_native_bound_slack` gives the exact slack on the other three (the logarithmic canonicalization factor, the threefold index bracket, the request bytes the query bracket adds) — all of it in the shape of SPEC §16's polynomial, none of it bought by a coefficient.  **How much of it has content, counted honestly** (adversarial review's sharpest criticism, and it is right): `lifecycleSize` *defines* nine of its coordinates as the sum or maximum of the very prefix-cost coordinate the polynomial bounds — `canonicalNovelObjects`, `canonicalNovelEdges`, `closureDerivations`, `attentionBucketsTouched`, `dependencyImpactObjects`, `partitionCellsChanged`, `certificateBytesChecked`, `retainedStateBytes`, `peakWorkingBytes` — so on those, at coefficient `1`, the inequality is literally `x ≤ x` and would hold for *any* cost model, including one charging zero.  Three more are `0 ≤ 0` because the replay charges nothing there.  Only **four of seventeen** coordinates relate the charged total to an independent trace-derived measure: `authorityCheckSteps`, `canonicalizationSteps`, `sealSteps`, `querySelectionSteps`.  "Fourteen hold with equality" is true and is the wrong thing to be impressed by.  This is a property of SPEC §16's size carrier, not of the proof.  Not claimed: that the coefficients are calibrated machine costs; nothing here measures one. |
| `Atlas.lifecycle_incremental_semantics_eq_full_rebuild` | **OUTSTANDING — `O-6`, and provably so.**  `WasmGemmGnaf.Atlas.not_lifecycle_incremental_semantics_eq_full_rebuild` refutes SPEC §16's literal statement: `ResolvedLifecycleTrace` constrains no coherence of its initial state, and an incoherent start is observed differently by the two strategies at prefix `0`.  Proved under exactly the missing hypothesis as `Atlas.lifecycle_incremental_semantics_eq_full_rebuild_of_coherent`, whose hypothesis `Atlas.lifecycle_incremental_semantics_eq_full_rebuild_of_rebuilt_start` discharges for any lifecycle beginning from a rebuild.  No declaration wears SPEC's name and nothing binds it. |
| `Atlas.lifecycle_full_rebuild_comparator_exact` | `WasmGemmGnaf.Atlas.lifecycle_full_rebuild_comparator_exact` (`Atlas/Lifecycle.lean`), at SPEC §16's statement, alongside the total `Atlas.canonicalFullRebuildEvaluation` it compares against.  Scope, stated in the theorem's own docstring: it holds by `rfl`, and its content is that the comparator tag is wired to the canonical full rebuild *of the same trace* with the componentwise truncated difference as carrier — nothing about the regret being zero or bounded. |

## Artifact — 0 of 7 discharged

The layer is `Artifact/Emit.lean`, `Artifact/Release.lean` and
`Artifact/Baseline.lean`; `Select.lean`, `Bytes.lean`, `Manifest.lean` and
`Execute.lean` do not exist.  `Artifact/Baseline.lean` does supply a closed
literal `Artifact.baselineBytes` (the encoding of `GNAF.compile
GNAF.gemmWitnessChecked`) and proves `Universal.ProfileValid Release.wasmProfile
baselineBytes` for it outright, hypothesis-free — but a profile-valid literal is
not a *selection*: no baseline **score** is computed, no `SemanticCorrect` and no
`SemanticWithinResources` proof exists, and no evaluation inhabits
`Universal.SystemEvaluation` at it.  `Artifact/Release.lean` §5 supplies a
*second* closed literal, `Release.witnessBytes`, which is profile valid **and**
carries a `Universal.SystemEvaluation` at the constructed seam — but its module
returns the constant `0`, so it is not semantically correct and is not a
candidate release either.  So none of the seven release theorems exists, and —
per SPEC §1 and UOR-GNAF §13.3 — none is asserted.

| SPEC §15 name | discharged by / blocked by |
|---|---|
| `Artifact.released_bytes_equal_selection` | **OUTSTANDING — `O-4`, `O-6`.**  No selection exists.  `Release.exists_globalOptimal_of_nonempty` produces an existential by classical reasoning; it names no byte literal, so there is nothing to equate a commitment to. |
| `Artifact.committed_literal_equal_selection` | **OUTSTANDING — `O-4`, `O-6`.** |
| `Artifact.released_bytes_decode` | **OUTSTANDING — `O-4`, `O-6`.** |
| `Artifact.released_bytes_validate` | **OUTSTANDING — `O-4`, `O-6`.** |
| `Artifact.released_input_total` | **OUTSTANDING — `O-6`** (`BI-002`/`BI-003`).  Input totality fails for three of the four mandatory arithmetic modes. |
| `Artifact.released_attains_lower_bound` | **OUTSTANDING — `O-5`.**  No universal lower bound exists to attain. |
| `Artifact.released_wasm_gemm_gnaf_global_optimal` | **OUTSTANDING — `O-4`, `O-5`, `O-6`, and NOT DECLARED ANYWHERE IN THIS REPOSITORY.**  SPEC §15 forbids it from accepting `Coverage`, `LowerBound`, `Correct`, `FaithfulWasm`, `CompilerCorrect` or `GlobalOptimal` as parameters, so it cannot be stated as a conditional and must not be stated at all until its antecedents close.  The nearest proved result is `Theorems.release_globalOptimal_of_nonempty`, which is **conditional** and is named after its hypothesis for exactly that reason.  The repository's terminal answer for claim `WGG-GO-1` remains `WorkloadIncomplete` (`CERTIFICATION.md`). |

## The release layer: what is proved, and the four things that are not

`Artifact/Release.lean` instantiates SPEC §7.2 / §8.3 / §9.3 / §10.1 at the
release scope and `Theorems/Release.lean` re-indexes the result at top level
with every hypothesis written out.  Nothing there discharges a §15 name.  What
it does is reduce the release theorem to a single open antecedent, and make the
reduction checkable:

* `Theorems.release_scope_identities` — the profile, problem, setting and
  objective identity equations in one conjunction, including the machine-checked
  cost profile — `Release.wasmProfile.costTableBody.ruleRows` is an exact,
  duplicate-free cover of every pinned `Wasm.RuleId` and
  `initializationRows` of every `Wasm.InitEventId`, with every rule resolving
  through `rowFor?` (this was CO-006; the rows used to be empty) — and the
  **disclosed deviation** that remains: `Release.wasmProfile` is
  `Wasm.unitWitnessProfile`, so its cost table is
  `Wasm.canonicalCostTableUnits`, whose rows are checked against this
  repository's own contribution law rather than built by
  `Wasm.buildCanonicalCostTable` from the Core 3.0 conformance map, which does
  not exist and for which `vendor/wasm-spec` carries no data.  No theorem about
  `Release.wasmProfile` may be cited as being about SPEC §7.2's release
  literal.
* `Theorems.release_seam_nondegenerate` and
  `release_systemEvaluation_inhabited` — claim `GO-008`: the `Release.Seam` is a
  constructed closed term, it is proved not to be the degenerate one, and
  `Universal.SystemEvaluation` at the constructed setting is inhabited on a
  `ProfileValid` closed literal.  Neither discharges a §15 name, and neither
  makes any byte sequence `Universal.Admissible`.

**The release theorem is gone.**  `Theorems.release_decider_answers_admissible`,
`release_globalOptimal_of_nonempty`, `release_globalOptimal_of_admissible`,
`release_obligation_reduction`, `release_lower_bound_clause`,
`release_tie_break_clause`, `release_competitor_universe_inhabited`,
`release_decider_answers_admissible_at_seam`,
`release_globalOptimal_of_nonempty_at_seam` and
`release_globalOptimal_of_witness_semantics` were all indexed by
`Release.decider`, a `noncomputable` `Classical.choice` evaluator that an
external audit ruled a non-conforming discharge of `UV-003`.  That evaluator,
`Release.evaluateClassically`, every result stated against them, and
`Artifact.exists_globalOptimal_of_baseline_semantics` are **deleted**.  `UV-003`
is open — the `open` records in `model/claims.json` and `CONFORMANCE.md` are now
correct, not drift — and this repository states **no** `Universal.GlobalOptimal`
result at the release scope.  `Universal.exists_globalOptimal_of_nonempty` is
decider-agnostic and still stands; nothing instantiates it.

Four hypotheses were recorded here; the first is now closed.  All four are
explicit arguments of those theorems:

1. `[Foundation.Fintype (Gemm.RawInvocation Release.wasmProfile)]` — SPEC §8.4's
   `problem_input_fintype`.  **CLOSED.**  `Gemm.raw_input_finite`
   (`Universal/EnumerateInputs.lean`) is a global constructive instance, so this
   hypothesis is now satisfied rather than assumed.  It is still written as an
   explicit instance binder on the theorems listed above, which predate the
   instance; that is a residual signature, not a residual assumption.
2. `Release.Seam.semantics` — **CLOSED (GO-008).**  `Release.semantics` is
   `Release.costEvent` together with `Wasm.validationCost` and
   `Wasm.instantiatedStaticBytes`.  Disclosure, and it is not small:
   `Release.costEvent` is a configuration-free map out of the *plain*
   `Wasm.Event`, which does not carry the transferred byte count, the
   `memory.grow` delta or the installed byte count, so it is a **lower bound**
   on SPEC §7.5's contribution law and not the law.
   `Release.costEvent_le_eventContribution` proves the inequality,
   `Release.costEvent_charge_wasmRuleSteps` proves no event is free, and
   `Release.costEvent_branch_charge` / `Release.costEvent_trap_charge` prove it
   is exact on the branch and trap rules.  Exactness on arithmetic, memory
   access, grow, `enterGemm`, `throw` and `return` remains `O-6`.
3. `Release.Seam.machine` — **CLOSED (GO-008).**  `Release.machine` is
   `Wasm.releaseCostedMachine` (`Wasm/CostedExplore.lean`): the real costed
   initialization and bounded all-branch costed explorer, with the canonical
   schema, canonical sort and frontier construction
   `Universal.CostedTreeResult.complete` demands.
   `Theorems.release_seam_nondegenerate` proves it initializes and returns a
   **completed, nonempty** frontier at every raw invocation of
   `Release.witnessModule` — the smallest module `GNAF.moduleOf` emits, whose
   `gemm` is `i32.const 0` and every branch of which terminates in at most three
   reduction steps.  It is **not** `Artifact.baselineModule`: discharging the
   explorer on the compiled GEMM witness needs a termination proof for
   `GNAF.bodyCode`'s loops inside a `2 ^ 320` step budget, which is `O-6`.
   (`Release.Seam.limit` is the same seam's third field, also closed:
   `Release.limit` pins five of `Cost.DynamicVector`'s sixteen coordinates
   verbatim from `Gemm.releaseResourceContract` and supplies the other eleven at
   the profile maximum the pinned costed-step budget implies —
   `Release.limit_pinned` and `Release.limit_unpinned` say which are which, and
   `Release.limit_pos` proves no coordinate is budgeted at zero.)
4. **Nonemptiness** — one byte sequence proved `ProfileValid ∧ SemanticCorrect ∧
   SemanticWithinResources` with a system evaluation.  **No such witness exists
   in this repository and none is asserted.**  It is the antecedent `hne`, and
   `Theorems.release_obligation_reduction` proves that nothing else is left in
   it.  Blocked by `O-6` (no compiler output proved correct) and `O-4`.

   Two of its four requirements are now met on a closed literal, and they are
   met on *different* literals from each other's strength:
   `Artifact.baseline_profileValid` proves
   `Universal.ProfileValid Release.wasmProfile Artifact.baselineBytes`
   hypothesis-free for the compiled GEMM witness, and
   `Theorems.release_systemEvaluation_inhabited` proves
   `Universal.ProfileValid` **and** `Nonempty (Universal.SystemEvaluation
   (Release.setting Release.seam) ·)` for `Release.witnessBytes`.  Before
   GO-008 the evaluation conjunct was not known to be satisfiable at any seam
   at all; it now is, at the constructed one.  What is still missing, and what
   keeps `hne` open, is that the literal carrying the evaluation is **not**
   semantically correct: `Release.witnessModule`'s `gemm` returns the constant
   `0`, so `Universal.SemanticCorrect` is false for it, and
   `SemanticWithinResources` is unproved for it.  For the compiled GEMM witness
   the same conjunct is `GNAF.compile_refines`, omitted under `BI-002`/`O-6`,
   and no `Universal.SystemEvaluation` inhabits it.
   `Artifact.baseline_admissible_iff` states the residue at the baseline
   exactly.  The two reduction theorems that used to be cited here,
   `Artifact.exists_globalOptimal_of_baseline_semantics` and
   `Theorems.release_globalOptimal_of_witness_semantics`, are deleted: their
   conclusions were indexed by `Release.decider`.

There is **no decider** at the release scope.  `Release.decider` and
`Release.evaluateClassically` are deleted.  SPEC §10.1 asks for an implemented
finite decoder, validator, input enumerator and all-branch explorer; a
`Classical.choice` inhabitant of the answer type is none of those, it decodes
nothing, enumerates nothing and explores nothing, and `just releasepath`
now rejects that shape under SPEC §19 / §6.3.  Two of the four ingredients do
exist and are proved: `Universal.enumerateInputs` with
`Universal.input_enumerator_complete`, and `Wasm.exploreAllCosted` with
`Release.seam_machine_completes`.  Assembling them into a `Universal.Decider`
and proving `Universal.DeciderAnswersAdmissible` of it is `UV-003`, open.

## Files in `WasmGemmGnaf/Theorems/`

Only the modules whose contents are fully proved exist:

* `WasmModel.lean` — Wasm decode/encode, validation, reduction, faults, cost erasure, cost-table totality.
* `GemmTotal.lean` — ABI round trip, raw-invocation carrier, total classifier and its exact domain, reference totality, the mandatory witness family, observation coverage.
* `CostModel.lean` — SPEC §9.1 composition algebra and exact aggregate (all three §15 Cost names), §9.2 coordinate bound, §9.3 monotonicity and sublevel finiteness.
* `AtlasLaws.lean` — semantic closure leastness and derivability, the merge law, update/rebuild equality, seal-body uniqueness, cover-check scope blindness.
* `Release.lean` — the conditional release theorem, the release scope identities, and the universal competitor clauses.  It declares no §15 name.
* `Status.lean` — this ledger.

`BaselineCorrect.lean`, `CompilerCorrect.lean`, `SublevelComplete.lean`,
`AttentionComplete.lean`, `UpdateEqualsRebuild.lean`, `UniversalLowerBound.lean`,
`Attainment.lean`, `ArtifactCorrect.lean`, `ArtifactGlobal.lean` and
`LifecycleBound.lean` from the SPEC §5 tree are **absent by design**.  An empty
or partially-proved file under one of those names asserts a result it does not
have, which is worse than its absence.  `Release.lean` is present because its
contents are proved *and* its name states a conditional, which is what it is.
-/
import WasmGemmGnaf.Theorems.WasmModel
import WasmGemmGnaf.Theorems.GemmTotal
import WasmGemmGnaf.Theorems.CostModel
import WasmGemmGnaf.Theorems.AtlasLaws
import WasmGemmGnaf.Theorems.Release

set_option autoImplicit false

namespace WasmGemmGnaf.Theorems

/-- Marker declaration.  `Status.lean` is a ledger, not a source of results:
its content is the module doc comment above, and this is the only declaration
it contributes. -/
theorem spec15_ledger_is_documentation : True := trivial

end WasmGemmGnaf.Theorems
