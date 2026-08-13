/-
  Wasm/Adequacy.lean --- the conformance map from pinned rule identifiers to
  Lean declarations.

  Normative source: SPEC.md section 7.1: "`Adequacy` proves correspondence
  between these declarations and the vendored rule identifiers in the
  conformance map", and

    "`profile_matches_pinned_revision` means that the concrete model and map are
     identity-bound to the vendored revision and that every enabled vendored
     rule has exactly one mapped Lean declaration.  It does not claim that Lean
     can derive English prose from bytes.  The reviewed transcription from
     normative rules to initial Lean definitions is an explicitly disclosed
     authority boundary; all subsequent GEMM, cost, coverage, and optimality
     reasoning is kernel checked."

  ## What this file establishes

  * `PinnedCoreRuleId` is a finite inductive with a complete enumeration
    (`mem_all`) that is proved duplicate free (`all_nodup`), so it carries a
    `Fintype` instance.
  * every identifier carries a feature family and a status, and the status is
    proved to agree with the release feature matrix of `Wasm/Feature.lean`
    (`status_eq_rejected_iff`): an identifier has no Lean declaration exactly
    when its family is rejected by the profile.
  * the map `leanDeclaration?` is **total** over the enabled identifiers
    (`adequacy_map_total_on_enabled`) and **injective** there
    (`adequacy_map_injective_on_enabled`); the same holds for the fully
    qualified names (`fullDeclaration?_injective_on_enabled`) and for the
    identifier spellings themselves (`ruleId_injective`).
  * every enabled identifier records the **vendored anchor** it was transcribed
    from (`vendorAnchor?`), total on the enabled set and `none` exactly on the
    rejected one (`vendorAnchor?_isSome_iff_enabled`).
  * the map object `core3AdequacyMap` carries the pinned commit *and* the
    vendored tree record of `Wasm/Revision.lean`, whose `manifestSha256` is the
    digest of `vendor/wasm-spec/SHA256SUMS` --- a digest of digests over the
    whole vendored tree.  The commit is proved equal to the commit every lawful
    `Wasm.Profile` carries (`adequacy_profile_revision_agree`) and to the commit
    the vendored tree carries (`core3AdequacyMap_vendorTree_commit`).
  * `mapped_declarations_referenced` mentions every mapped Lean declaration, so
    renaming or deleting one breaks this file rather than silently invalidating
    the map.
  * `profile_matches_pinned_revision` is the conjunction SPEC section 7.1 names:
    the identity binding above, together with the one-to-one property of the
    map on the enabled rules.

  ## The authority boundary --- what this file does NOT establish

  This file does **not** claim that Lean derives English prose from bytes.  The
  transcription from normative rules to Lean definitions is the disclosed
  authority boundary of SPEC section 7.1.  Three gaps were disclosed here; the
  first is now closed, and the state of each is:

  1. **CLOSED --- the pinned tree is vendored, and Lean is bound to its
     content.**  `vendor/wasm-spec/` holds the forty
     `document/core/{binary,valid,exec,syntax,appendix}` files of the official
     `wg-3.0` tree at the pinned commit, with a per-file digest manifest at
     `vendor/wasm-spec/SHA256SUMS` and the commit at
     `vendor/wasm-spec/PINNED-COMMIT`; `authority/manifest.json` records
     `wasmCore.vendored = true`.  `Wasm/Revision.lean` records the digest of
     that manifest as `core3VendorManifestSha256`, and `xtask vendor`
     recomputes it --- and rechecks `SHA256SUMS` against all forty files ---
     from the bytes on disk, failing the gate when the Lean literal has
     drifted.  Lean stands on the literal; the tool is what stops the literal
     from being a wish.  Falsifier `M13` plants a mutated `SHA256SUMS` on a
     copy and requires the check to reject it.
  2. **OPEN --- strings are not reflected.**  `mapped_declarations_referenced`
     proves that a declaration with each mapped *role* exists in the
     environment, but Lean cannot check --- without metaprogramming, which this
     development does not use --- that the *string* `"Step.nop"` names the
     declaration `Step.nop`.  That correspondence is by review.
  3. **NARROWED, NOT CLOSED --- coverage is relative to this enumeration.**
     Every "total" and "complete" theorem below quantifies over
     `PinnedCoreRuleId`, which is the list written in this file.  Each enabled
     identifier now also records the reStructuredText anchor of the vendored
     rule it was transcribed from (`vendorAnchor?`), and `xtask vendor` checks
     that every one of those anchors is a label actually *defined* in the
     vendored tree, so an invented rule identifier fails the gate.  What that
     does **not** establish, and what keeps this gap open:
     * the converse direction.  The vendored tree defines far more rule labels
       than this enumeration cites; `xtask vendor --list` prints both counts.
       The enumeration is a declared *subset* of the pinned rule set and is not
       proved to be all of it.
     * that the anchor's *body* says what the Lean declaration does.  The
       vendored `.rst` sources state most rule bodies as unexpanded SpecTec
       macro references (`${rule: ...}` / `$${rule: ...}`), whose `.watsup`
       definitions are **not** in the vendored file set.  A label check is
       therefore a check on rule *identity*, not on rule *content*, and no
       tooling in this repository can close that difference from the vendored
       bytes alone.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Run
import WasmGemmGnaf.Wasm.Table
import WasmGemmGnaf.Wasm.Vector

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Two general lemmas -/

/-- A list whose image under `f` is duplicate free is one on which `f` is
injective. -/
theorem nodup_map_injOn {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha _ _; exact absurd ha (by simp)
  | cons x xs ih =>
    intro h a b ha hb hf
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (show f a ∈ xs.map f by rw [hf]; exact List.mem_map_of_mem hb') h.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (show f b ∈ xs.map f by rw [← hf]; exact List.mem_map_of_mem ha') h.1
      · exact ih h.2 a b ha' hb' hf

/-- Appending a fixed prefix to a string is injective. -/
theorem string_append_left_cancel {p a b : String} (h : p ++ a = p ++ b) : a = b := by
  have hd : p.toList ++ a.toList = p.toList ++ b.toList := by
    rw [← String.toList_append, ← String.toList_append, h]
  have h2 := List.append_cancel_left hd
  have h3 := congrArg String.ofList h2
  rwa [String.ofList_toList, String.ofList_toList] at h3

/-! ## The status of a pinned rule -/

/-- What the released development does with a pinned rule. -/
inductive RuleStatus
  /-- The rule has a Lean declaration and is reachable in the released
  machine. -/
  | modelled
  /-- The rule has a Lean declaration, but the released validator rejects the
  instruction, so no released execution reaches it.  See the scope theorems in
  `Wasm/Table.lean` and `Wasm/Vector.lean`. -/
  | modelledUnreachable
  /-- The rule belongs to a family the profile rejects; it has no Lean
  declaration at all. -/
  | rejectedByProfile
  deriving DecidableEq, Repr, Inhabited

namespace RuleStatus

def all : List RuleStatus := [modelled, modelledUnreachable, rejectedByProfile]

theorem mem_all (s : RuleStatus) : s ∈ all := by cases s <;> decide

theorem all_nodup : all.Nodup := by decide

instance instFintype : Fintype RuleStatus where
  elemsList := all
  complete := mem_all
  nodupList := all_nodup

end RuleStatus

/-! ## The pinned rule identifiers -/

/-- The identifiers of the pinned Core 3.0 rules covered by this development.
See the header for the exact scope of this enumeration. -/
inductive PinnedCoreRuleId
  | decodeModule
  | decodeUleb128
  | validUnreachable
  | validNop
  | validI32Const
  | validDrop
  | validIBinOp
  | validITestOp
  | validIRelOp
  | validLocalGet
  | validLocalSet
  | validLocalTee
  | validGlobalGet
  | validGlobalSet
  | validLoad
  | validStore
  | validMemorySize
  | validMemoryGrow
  | validBlock
  | validLoop
  | validIfThenElse
  | validBr
  | validBrIf
  | validThrowTag
  | validExprNil
  | validExprCons
  | validModule
  | validFunc
  | validMems
  | validGemmExport
  | validClosed
  | storeAlloc
  | storeLoadBytes
  | storeStoreBytes
  | storeMemoryGrow
  | execUnreachable
  | execNop
  | execI32Const
  | execDrop
  | execIBinOp
  | execIBinOpTrap
  | execITestOp
  | execIRelOp
  | execLocalGet
  | execLocalSet
  | execLocalTee
  | execGlobalGet
  | execGlobalSet
  | execLoad
  | execLoadTrap
  | execStore
  | execStoreTrap
  | execMemorySize
  | execMemoryGrowSucceed
  | execMemoryGrowRefuse
  | execBlock
  | execLoop
  | execIfFalse
  | execIfTrue
  | execBrLoop
  | execBrBlock
  | execBrIfFalse
  | execBrIfLoop
  | execBrIfBlock
  | execThrowTag
  | execExitLabel
  | execReturnGemm
  | execEnterGemm
  | execInstallTrap
  | trapUnreachable
  | trapOutOfBounds
  | trapDivideByZero
  | nondetMemoryGrow
  | nondetNanResult
  | tableGet
  | tableSet
  | tableSize
  | tableGrow
  | tableFill
  | tableCopy
  | tableInit
  | tableElemDrop
  | vectorExtractLane
  | vectorReplaceLane
  | vectorSplat
  | vectorLanewise
  | vectorShapeWidth
  | refNull
  | refFunc
  | rejectMemory64Load
  | rejectAtomicRmw
  | rejectRelaxedFma
  | rejectComponentModel
  deriving DecidableEq, Repr, Inhabited

namespace PinnedCoreRuleId

/-- The complete enumeration of pinned rule identifiers. -/
def all : List PinnedCoreRuleId :=
  [ .decodeModule
  , .decodeUleb128
  , .validUnreachable
  , .validNop
  , .validI32Const
  , .validDrop
  , .validIBinOp
  , .validITestOp
  , .validIRelOp
  , .validLocalGet
  , .validLocalSet
  , .validLocalTee
  , .validGlobalGet
  , .validGlobalSet
  , .validLoad
  , .validStore
  , .validMemorySize
  , .validMemoryGrow
  , .validBlock
  , .validLoop
  , .validIfThenElse
  , .validBr
  , .validBrIf
  , .validThrowTag
  , .validExprNil
  , .validExprCons
  , .validModule
  , .validFunc
  , .validMems
  , .validGemmExport
  , .validClosed
  , .storeAlloc
  , .storeLoadBytes
  , .storeStoreBytes
  , .storeMemoryGrow
  , .execUnreachable
  , .execNop
  , .execI32Const
  , .execDrop
  , .execIBinOp
  , .execIBinOpTrap
  , .execITestOp
  , .execIRelOp
  , .execLocalGet
  , .execLocalSet
  , .execLocalTee
  , .execGlobalGet
  , .execGlobalSet
  , .execLoad
  , .execLoadTrap
  , .execStore
  , .execStoreTrap
  , .execMemorySize
  , .execMemoryGrowSucceed
  , .execMemoryGrowRefuse
  , .execBlock
  , .execLoop
  , .execIfFalse
  , .execIfTrue
  , .execBrLoop
  , .execBrBlock
  , .execBrIfFalse
  , .execBrIfLoop
  , .execBrIfBlock
  , .execThrowTag
  , .execExitLabel
  , .execReturnGemm
  , .execEnterGemm
  , .execInstallTrap
  , .trapUnreachable
  , .trapOutOfBounds
  , .trapDivideByZero
  , .nondetMemoryGrow
  , .nondetNanResult
  , .tableGet
  , .tableSet
  , .tableSize
  , .tableGrow
  , .tableFill
  , .tableCopy
  , .tableInit
  , .tableElemDrop
  , .vectorExtractLane
  , .vectorReplaceLane
  , .vectorSplat
  , .vectorLanewise
  , .vectorShapeWidth
  , .refNull
  , .refFunc
  , .rejectMemory64Load
  , .rejectAtomicRmw
  , .rejectRelaxedFma
  , .rejectComponentModel ]

theorem mem_all (id : PinnedCoreRuleId) : id ∈ all := by cases id <;> decide

/-- **Duplicate-free coverage.** -/
theorem all_nodup : all.Nodup := by decide

theorem all_length : all.length = 93 := rfl

instance instFintype : Fintype PinnedCoreRuleId where
  elemsList := all
  complete := mem_all
  nodupList := all_nodup

/-- The vendored spelling of a rule identifier (see the header: this is a
hand transcription, not a list read from a vendored tree). -/
def ruleId : PinnedCoreRuleId → String
  | .decodeModule => "decode.module"
  | .decodeUleb128 => "decode.uleb128"
  | .validUnreachable => "valid.unreachable"
  | .validNop => "valid.nop"
  | .validI32Const => "valid.i32-const"
  | .validDrop => "valid.drop"
  | .validIBinOp => "valid.i-binop"
  | .validITestOp => "valid.i-testop"
  | .validIRelOp => "valid.i-relop"
  | .validLocalGet => "valid.local-get"
  | .validLocalSet => "valid.local-set"
  | .validLocalTee => "valid.local-tee"
  | .validGlobalGet => "valid.global-get"
  | .validGlobalSet => "valid.global-set"
  | .validLoad => "valid.load"
  | .validStore => "valid.store"
  | .validMemorySize => "valid.memory-size"
  | .validMemoryGrow => "valid.memory-grow"
  | .validBlock => "valid.block"
  | .validLoop => "valid.loop"
  | .validIfThenElse => "valid.if"
  | .validBr => "valid.br"
  | .validBrIf => "valid.br-if"
  | .validThrowTag => "valid.throw"
  | .validExprNil => "valid.expr-nil"
  | .validExprCons => "valid.expr-cons"
  | .validModule => "valid.module"
  | .validFunc => "valid.func"
  | .validMems => "valid.mems"
  | .validGemmExport => "valid.gemm-export"
  | .validClosed => "valid.closed"
  | .storeAlloc => "store.alloc"
  | .storeLoadBytes => "store.load-bytes"
  | .storeStoreBytes => "store.store-bytes"
  | .storeMemoryGrow => "store.memory-grow"
  | .execUnreachable => "exec.unreachable"
  | .execNop => "exec.nop"
  | .execI32Const => "exec.i32-const"
  | .execDrop => "exec.drop"
  | .execIBinOp => "exec.i-binop"
  | .execIBinOpTrap => "exec.i-binop-trap"
  | .execITestOp => "exec.i-testop"
  | .execIRelOp => "exec.i-relop"
  | .execLocalGet => "exec.local-get"
  | .execLocalSet => "exec.local-set"
  | .execLocalTee => "exec.local-tee"
  | .execGlobalGet => "exec.global-get"
  | .execGlobalSet => "exec.global-set"
  | .execLoad => "exec.load"
  | .execLoadTrap => "exec.load-trap"
  | .execStore => "exec.store"
  | .execStoreTrap => "exec.store-trap"
  | .execMemorySize => "exec.memory-size"
  | .execMemoryGrowSucceed => "exec.memory-grow-succeed"
  | .execMemoryGrowRefuse => "exec.memory-grow-refuse"
  | .execBlock => "exec.block"
  | .execLoop => "exec.loop"
  | .execIfFalse => "exec.if-false"
  | .execIfTrue => "exec.if-true"
  | .execBrLoop => "exec.br-loop"
  | .execBrBlock => "exec.br-block"
  | .execBrIfFalse => "exec.br-if-false"
  | .execBrIfLoop => "exec.br-if-loop"
  | .execBrIfBlock => "exec.br-if-block"
  | .execThrowTag => "exec.throw"
  | .execExitLabel => "exec.exit-label"
  | .execReturnGemm => "exec.return-gemm"
  | .execEnterGemm => "exec.enter-gemm"
  | .execInstallTrap => "exec.install-trap"
  | .trapUnreachable => "trap.unreachable"
  | .trapOutOfBounds => "trap.out-of-bounds"
  | .trapDivideByZero => "trap.divide-by-zero"
  | .nondetMemoryGrow => "nondet.memory-grow"
  | .nondetNanResult => "nondet.nan-result"
  | .tableGet => "table.get"
  | .tableSet => "table.set"
  | .tableSize => "table.size"
  | .tableGrow => "table.grow"
  | .tableFill => "table.fill"
  | .tableCopy => "table.copy"
  | .tableInit => "table.init"
  | .tableElemDrop => "table.elem-drop"
  | .vectorExtractLane => "vector.extract-lane"
  | .vectorReplaceLane => "vector.replace-lane"
  | .vectorSplat => "vector.splat"
  | .vectorLanewise => "vector.lanewise"
  | .vectorShapeWidth => "vector.shape-width"
  | .refNull => "ref.null"
  | .refFunc => "ref.func"
  | .rejectMemory64Load => "reject.memory64-load"
  | .rejectAtomicRmw => "reject.atomic-rmw"
  | .rejectRelaxedFma => "reject.relaxed-fma"
  | .rejectComponentModel => "reject.component-model"

/-- The Core 3.0 feature family a rule belongs to. -/
def family : PinnedCoreRuleId → FeatureFamily
  | .decodeModule => .scalarCore
  | .decodeUleb128 => .scalarCore
  | .validUnreachable => .scalarCore
  | .validNop => .scalarCore
  | .validI32Const => .scalarCore
  | .validDrop => .scalarCore
  | .validIBinOp => .scalarCore
  | .validITestOp => .scalarCore
  | .validIRelOp => .scalarCore
  | .validLocalGet => .scalarCore
  | .validLocalSet => .scalarCore
  | .validLocalTee => .scalarCore
  | .validGlobalGet => .scalarCore
  | .validGlobalSet => .scalarCore
  | .validLoad => .bulkMemoryMultipleMemoriesTables
  | .validStore => .bulkMemoryMultipleMemoriesTables
  | .validMemorySize => .bulkMemoryMultipleMemoriesTables
  | .validMemoryGrow => .bulkMemoryMultipleMemoriesTables
  | .validBlock => .multiValueAndExtendedConst
  | .validLoop => .multiValueAndExtendedConst
  | .validIfThenElse => .multiValueAndExtendedConst
  | .validBr => .scalarCore
  | .validBrIf => .scalarCore
  | .validThrowTag => .exceptionHandling
  | .validExprNil => .scalarCore
  | .validExprCons => .scalarCore
  | .validModule => .scalarCore
  | .validFunc => .scalarCore
  | .validMems => .bulkMemoryMultipleMemoriesTables
  | .validGemmExport => .scalarCore
  | .validClosed => .scalarCore
  | .storeAlloc => .scalarCore
  | .storeLoadBytes => .bulkMemoryMultipleMemoriesTables
  | .storeStoreBytes => .bulkMemoryMultipleMemoriesTables
  | .storeMemoryGrow => .bulkMemoryMultipleMemoriesTables
  | .execUnreachable => .scalarCore
  | .execNop => .scalarCore
  | .execI32Const => .scalarCore
  | .execDrop => .scalarCore
  | .execIBinOp => .scalarCore
  | .execIBinOpTrap => .scalarCore
  | .execITestOp => .scalarCore
  | .execIRelOp => .scalarCore
  | .execLocalGet => .scalarCore
  | .execLocalSet => .scalarCore
  | .execLocalTee => .scalarCore
  | .execGlobalGet => .scalarCore
  | .execGlobalSet => .scalarCore
  | .execLoad => .bulkMemoryMultipleMemoriesTables
  | .execLoadTrap => .bulkMemoryMultipleMemoriesTables
  | .execStore => .bulkMemoryMultipleMemoriesTables
  | .execStoreTrap => .bulkMemoryMultipleMemoriesTables
  | .execMemorySize => .bulkMemoryMultipleMemoriesTables
  | .execMemoryGrowSucceed => .bulkMemoryMultipleMemoriesTables
  | .execMemoryGrowRefuse => .bulkMemoryMultipleMemoriesTables
  | .execBlock => .multiValueAndExtendedConst
  | .execLoop => .multiValueAndExtendedConst
  | .execIfFalse => .multiValueAndExtendedConst
  | .execIfTrue => .multiValueAndExtendedConst
  | .execBrLoop => .scalarCore
  | .execBrBlock => .scalarCore
  | .execBrIfFalse => .scalarCore
  | .execBrIfLoop => .scalarCore
  | .execBrIfBlock => .scalarCore
  | .execThrowTag => .exceptionHandling
  | .execExitLabel => .multiValueAndExtendedConst
  | .execReturnGemm => .scalarCore
  | .execEnterGemm => .scalarCore
  | .execInstallTrap => .bulkMemoryMultipleMemoriesTables
  | .trapUnreachable => .scalarCore
  | .trapOutOfBounds => .bulkMemoryMultipleMemoriesTables
  | .trapDivideByZero => .scalarCore
  | .nondetMemoryGrow => .bulkMemoryMultipleMemoriesTables
  | .nondetNanResult => .scalarCore
  | .tableGet => .bulkMemoryMultipleMemoriesTables
  | .tableSet => .bulkMemoryMultipleMemoriesTables
  | .tableSize => .bulkMemoryMultipleMemoriesTables
  | .tableGrow => .bulkMemoryMultipleMemoriesTables
  | .tableFill => .bulkMemoryMultipleMemoriesTables
  | .tableCopy => .bulkMemoryMultipleMemoriesTables
  | .tableInit => .bulkMemoryMultipleMemoriesTables
  | .tableElemDrop => .bulkMemoryMultipleMemoriesTables
  | .vectorExtractLane => .fixedWidthSimd128
  | .vectorReplaceLane => .fixedWidthSimd128
  | .vectorSplat => .fixedWidthSimd128
  | .vectorLanewise => .fixedWidthSimd128
  | .vectorShapeWidth => .fixedWidthSimd128
  | .refNull => .referenceTypesTypedFunctionReferencesGc
  | .refFunc => .referenceTypesTypedFunctionReferencesGc
  | .rejectMemory64Load => .memory64
  | .rejectAtomicRmw => .sharedMemoriesAtomicsThreads
  | .rejectRelaxedFma => .relaxedSimd
  | .rejectComponentModel => .componentModelAndPostCore3

/-- What the released development does with the rule. -/
def status : PinnedCoreRuleId → RuleStatus
  | .decodeModule => .modelled
  | .decodeUleb128 => .modelled
  | .validUnreachable => .modelled
  | .validNop => .modelled
  | .validI32Const => .modelled
  | .validDrop => .modelled
  | .validIBinOp => .modelled
  | .validITestOp => .modelled
  | .validIRelOp => .modelled
  | .validLocalGet => .modelled
  | .validLocalSet => .modelled
  | .validLocalTee => .modelled
  | .validGlobalGet => .modelled
  | .validGlobalSet => .modelled
  | .validLoad => .modelled
  | .validStore => .modelled
  | .validMemorySize => .modelled
  | .validMemoryGrow => .modelled
  | .validBlock => .modelled
  | .validLoop => .modelled
  | .validIfThenElse => .modelled
  | .validBr => .modelled
  | .validBrIf => .modelled
  | .validThrowTag => .modelled
  | .validExprNil => .modelled
  | .validExprCons => .modelled
  | .validModule => .modelled
  | .validFunc => .modelled
  | .validMems => .modelled
  | .validGemmExport => .modelled
  | .validClosed => .modelled
  | .storeAlloc => .modelled
  | .storeLoadBytes => .modelled
  | .storeStoreBytes => .modelled
  | .storeMemoryGrow => .modelled
  | .execUnreachable => .modelled
  | .execNop => .modelled
  | .execI32Const => .modelled
  | .execDrop => .modelled
  | .execIBinOp => .modelled
  | .execIBinOpTrap => .modelled
  | .execITestOp => .modelled
  | .execIRelOp => .modelled
  | .execLocalGet => .modelled
  | .execLocalSet => .modelled
  | .execLocalTee => .modelled
  | .execGlobalGet => .modelled
  | .execGlobalSet => .modelled
  | .execLoad => .modelled
  | .execLoadTrap => .modelled
  | .execStore => .modelled
  | .execStoreTrap => .modelled
  | .execMemorySize => .modelled
  | .execMemoryGrowSucceed => .modelled
  | .execMemoryGrowRefuse => .modelled
  | .execBlock => .modelled
  | .execLoop => .modelled
  | .execIfFalse => .modelled
  | .execIfTrue => .modelled
  | .execBrLoop => .modelled
  | .execBrBlock => .modelled
  | .execBrIfFalse => .modelled
  | .execBrIfLoop => .modelled
  | .execBrIfBlock => .modelled
  | .execThrowTag => .modelled
  | .execExitLabel => .modelled
  | .execReturnGemm => .modelled
  | .execEnterGemm => .modelled
  | .execInstallTrap => .modelled
  | .trapUnreachable => .modelled
  | .trapOutOfBounds => .modelled
  | .trapDivideByZero => .modelled
  | .nondetMemoryGrow => .modelled
  | .nondetNanResult => .modelled
  | .tableGet => .modelledUnreachable
  | .tableSet => .modelledUnreachable
  | .tableSize => .modelledUnreachable
  | .tableGrow => .modelledUnreachable
  | .tableFill => .modelledUnreachable
  | .tableCopy => .modelledUnreachable
  | .tableInit => .modelledUnreachable
  | .tableElemDrop => .modelledUnreachable
  | .vectorExtractLane => .modelledUnreachable
  | .vectorReplaceLane => .modelledUnreachable
  | .vectorSplat => .modelledUnreachable
  | .vectorLanewise => .modelledUnreachable
  | .vectorShapeWidth => .modelledUnreachable
  | .refNull => .modelledUnreachable
  | .refFunc => .modelledUnreachable
  | .rejectMemory64Load => .rejectedByProfile
  | .rejectAtomicRmw => .rejectedByProfile
  | .rejectRelaxedFma => .rejectedByProfile
  | .rejectComponentModel => .rejectedByProfile

/-- The Lean declaration implementing the rule, relative to the
`WasmGemmGnaf.Wasm` namespace.  `none` is exactly a rejected family. -/
def leanDeclaration? : PinnedCoreRuleId → Option String
  | .decodeModule => some "decode"
  | .decodeUleb128 => some "decodeULEB"
  | .validUnreachable => some "InstrTyping.unreachable"
  | .validNop => some "InstrTyping.nop"
  | .validI32Const => some "InstrTyping.i32Const"
  | .validDrop => some "InstrTyping.drop"
  | .validIBinOp => some "InstrTyping.iBinOp"
  | .validITestOp => some "InstrTyping.iTestOp"
  | .validIRelOp => some "InstrTyping.iRelOp"
  | .validLocalGet => some "InstrTyping.localGet"
  | .validLocalSet => some "InstrTyping.localSet"
  | .validLocalTee => some "InstrTyping.localTee"
  | .validGlobalGet => some "InstrTyping.globalGet"
  | .validGlobalSet => some "InstrTyping.globalSet"
  | .validLoad => some "InstrTyping.load"
  | .validStore => some "InstrTyping.store"
  | .validMemorySize => some "InstrTyping.memorySize"
  | .validMemoryGrow => some "InstrTyping.memoryGrow"
  | .validBlock => some "InstrTyping.block"
  | .validLoop => some "InstrTyping.loop"
  | .validIfThenElse => some "InstrTyping.ifThenElse"
  | .validBr => some "InstrTyping.br"
  | .validBrIf => some "InstrTyping.brIf"
  | .validThrowTag => some "InstrTyping.throwTag"
  | .validExprNil => some "ExprTyping.nil"
  | .validExprCons => some "ExprTyping.cons"
  | .validModule => some "validate"
  | .validFunc => some "Module.checkFunc"
  | .validMems => some "Module.checkMems"
  | .validGemmExport => some "Module.checkGemmExport"
  | .validClosed => some "Module.checkClosed"
  | .storeAlloc => some "Store.alloc"
  | .storeLoadBytes => some "Store.loadBytes"
  | .storeStoreBytes => some "Store.storeBytes"
  | .storeMemoryGrow => some "Memory.grow"
  | .execUnreachable => some "Step.unreachable"
  | .execNop => some "Step.nop"
  | .execI32Const => some "Step.i32Const"
  | .execDrop => some "Step.drop"
  | .execIBinOp => some "Step.iBinOp"
  | .execIBinOpTrap => some "Step.iBinOpTrap"
  | .execITestOp => some "Step.iTestOp"
  | .execIRelOp => some "Step.iRelOp"
  | .execLocalGet => some "Step.localGet"
  | .execLocalSet => some "Step.localSet"
  | .execLocalTee => some "Step.localTee"
  | .execGlobalGet => some "Step.globalGet"
  | .execGlobalSet => some "Step.globalSet"
  | .execLoad => some "Step.load"
  | .execLoadTrap => some "Step.loadTrap"
  | .execStore => some "Step.store"
  | .execStoreTrap => some "Step.storeTrap"
  | .execMemorySize => some "Step.memorySize"
  | .execMemoryGrowSucceed => some "Step.memoryGrowSucceed"
  | .execMemoryGrowRefuse => some "Step.memoryGrowRefuse"
  | .execBlock => some "Step.block"
  | .execLoop => some "Step.loop"
  | .execIfFalse => some "Step.ifFalse"
  | .execIfTrue => some "Step.ifTrue"
  | .execBrLoop => some "Step.brLoop"
  | .execBrBlock => some "Step.brBlock"
  | .execBrIfFalse => some "Step.brIfFalse"
  | .execBrIfLoop => some "Step.brIfLoop"
  | .execBrIfBlock => some "Step.brIfBlock"
  | .execThrowTag => some "Step.throwTag"
  | .execExitLabel => some "Step.exitLabel"
  | .execReturnGemm => some "Step.returnGemm"
  | .execEnterGemm => some "Step.enterGemm"
  | .execInstallTrap => some "Step.installTrap"
  | .trapUnreachable => some "Trap.unreachable"
  | .trapOutOfBounds => some "Trap.outOfBounds"
  | .trapDivideByZero => some "Trap.divideByZero"
  | .nondetMemoryGrow => some "Num.growResults"
  | .nondetNanResult => some "Num.nanResults32"
  | .tableGet => some "TableInst.get"
  | .tableSet => some "TableInst.set"
  | .tableSize => some "TableInst.size"
  | .tableGrow => some "TableInst.grow"
  | .tableFill => some "TableInst.fill"
  | .tableCopy => some "TableInst.copy"
  | .tableInit => some "TableInst.init"
  | .tableElemDrop => some "ElemInst.dropSeg"
  | .vectorExtractLane => some "V128.extractLane"
  | .vectorReplaceLane => some "V128.replaceLane"
  | .vectorSplat => some "V128.splat"
  | .vectorLanewise => some "V128.zipLanes"
  | .vectorShapeWidth => some "VecShape.lanes_mul_laneWidth"
  | .refNull => some "Ref.null"
  | .refFunc => some "Ref.func"
  | .rejectMemory64Load => none
  | .rejectAtomicRmw => none
  | .rejectRelaxedFma => none
  | .rejectComponentModel => none

/-- The reStructuredText label of the vendored rule this identifier was
transcribed from, without its leading underscore: `"valid-nop"` is the anchor
`.. _valid-nop:` of `vendor/wasm-spec/document/core/valid/instructions.rst`.
`none` is exactly a rejected family, which by definition has no vendored rule
in the released profile.

`xtask vendor` checks that every anchor here is a label DEFINED in the vendored
tree, so an invented identifier fails the gate.  Two things this map is not:

* it is not injective, and is not claimed to be.  A vendored rule and its trap
  case are one label and two Lean declarations (`exec-load-val` covers both
  `Step.load` and `Step.loadTrap`), and the harness rules specialize the
  vendored invocation and store rules.
* it is not a claim about the rule's *body*.  The vendored `.rst` sources carry
  most rule bodies as unexpanded SpecTec macros whose `.watsup` definitions are
  not vendored, so the label is checkable and the body is not. -/
def vendorAnchor? : PinnedCoreRuleId → Option String
  | .decodeModule => some "binary-module"
  | .decodeUleb128 => some "binary-uint"
  | .validUnreachable => some "valid-unreachable"
  | .validNop => some "valid-nop"
  | .validI32Const => some "valid-const"
  | .validDrop => some "valid-drop"
  | .validIBinOp => some "valid-binop"
  | .validITestOp => some "valid-testop"
  | .validIRelOp => some "valid-relop"
  | .validLocalGet => some "valid-local.get"
  | .validLocalSet => some "valid-local.set"
  | .validLocalTee => some "valid-local.tee"
  | .validGlobalGet => some "valid-global.get"
  | .validGlobalSet => some "valid-global.set"
  | .validLoad => some "valid-load-val"
  | .validStore => some "valid-store-val"
  | .validMemorySize => some "valid-memory.size"
  | .validMemoryGrow => some "valid-memory.grow"
  | .validBlock => some "valid-block"
  | .validLoop => some "valid-loop"
  | .validIfThenElse => some "valid-if"
  | .validBr => some "valid-br"
  | .validBrIf => some "valid-br_if"
  | .validThrowTag => some "valid-throw"
  | .validExprNil => some "valid-instrs"
  | .validExprCons => some "valid-instrs"
  | .validModule => some "valid-module"
  | .validFunc => some "valid-func"
  | .validMems => some "valid-mem"
  | .validGemmExport => some "valid-export"
  | .validClosed => some "valid-import"
  | .storeAlloc => some "alloc-module"
  | .storeLoadBytes => some "exec-load-val"
  | .storeStoreBytes => some "exec-store-val"
  | .storeMemoryGrow => some "exec-memory.grow"
  | .execUnreachable => some "exec-unreachable"
  | .execNop => some "exec-nop"
  | .execI32Const => some "exec-const"
  | .execDrop => some "exec-drop"
  | .execIBinOp => some "exec-binop"
  | .execIBinOpTrap => some "exec-binop"
  | .execITestOp => some "exec-testop"
  | .execIRelOp => some "exec-relop"
  | .execLocalGet => some "exec-local.get"
  | .execLocalSet => some "exec-local.set"
  | .execLocalTee => some "exec-local.tee"
  | .execGlobalGet => some "exec-global.get"
  | .execGlobalSet => some "exec-global.set"
  | .execLoad => some "exec-load-val"
  | .execLoadTrap => some "exec-load-val"
  | .execStore => some "exec-store-val"
  | .execStoreTrap => some "exec-store-val"
  | .execMemorySize => some "exec-memory.size"
  | .execMemoryGrowSucceed => some "exec-memory.grow"
  | .execMemoryGrowRefuse => some "exec-memory.grow"
  | .execBlock => some "exec-block"
  | .execLoop => some "exec-loop"
  | .execIfFalse => some "exec-if"
  | .execIfTrue => some "exec-if"
  | .execBrLoop => some "exec-br"
  | .execBrBlock => some "exec-br"
  | .execBrIfFalse => some "exec-br_if"
  | .execBrIfLoop => some "exec-br_if"
  | .execBrIfBlock => some "exec-br_if"
  | .execThrowTag => some "exec-throw"
  | .execExitLabel => some "exec-instrs-exit"
  | .execReturnGemm => some "exec-invoke-exit"
  | .execEnterGemm => some "exec-invoke"
  | .execInstallTrap => some "exec-store-val"
  | .trapUnreachable => some "syntax-trap"
  | .trapOutOfBounds => some "syntax-trap"
  | .trapDivideByZero => some "syntax-trap"
  | .nondetMemoryGrow => some "exec-memory.grow"
  | .nondetNanResult => some "syntax-nan"
  | .tableGet => some "exec-table.get"
  | .tableSet => some "exec-table.set"
  | .tableSize => some "exec-table.size"
  | .tableGrow => some "exec-table.grow"
  | .tableFill => some "exec-table.fill"
  | .tableCopy => some "exec-table.copy"
  | .tableInit => some "exec-table.init"
  | .tableElemDrop => some "exec-elem.drop"
  | .vectorExtractLane => some "exec-vextract_lane"
  | .vectorReplaceLane => some "exec-vreplace_lane"
  | .vectorSplat => some "exec-vsplat"
  | .vectorLanewise => some "exec-vbinop"
  | .vectorShapeWidth => some "syntax-shape"
  | .refNull => some "exec-ref.null"
  | .refFunc => some "exec-ref.func"
  | .rejectMemory64Load => none
  | .rejectAtomicRmw => none
  | .rejectRelaxedFma => none
  | .rejectComponentModel => none

/-- The vendored anchor of an identifier, with the rejected ones collapsed to
the empty string.  Used to build the map rows as a decidable computation. -/
def anchorOf (id : PinnedCoreRuleId) : String := (vendorAnchor? id).getD ""

/-- A rule is enabled when the profile does not reject its family. -/
def RuleEnabled (id : PinnedCoreRuleId) : Prop := status id ≠ .rejectedByProfile

instance instDecidableRuleEnabled (id : PinnedCoreRuleId) :
    Decidable (RuleEnabled id) := by
  unfold RuleEnabled
  infer_instance

/-- The status agrees with the release feature matrix: a rule has no Lean
declaration exactly when its family is rejected by the profile. -/
theorem status_eq_rejected_iff (id : PinnedCoreRuleId) :
    status id = .rejectedByProfile ↔ Rejected (family id) := by
  cases id <;> decide

theorem ruleEnabled_iff_family_enabled (id : PinnedCoreRuleId) :
    RuleEnabled id ↔ Enabled (family id) := by
  cases id <;> decide

/-- **Totality over the enabled rule set.**  Every enabled identifier has a
mapped Lean declaration, and every rejected one has none. -/
theorem adequacy_map_total_on_enabled (id : PinnedCoreRuleId) :
    (leanDeclaration? id).isSome = true ↔ RuleEnabled id := by
  cases id <;> decide

theorem leanDeclaration?_eq_none_iff (id : PinnedCoreRuleId) :
    leanDeclaration? id = none ↔ Rejected (family id) := by
  cases id <;> decide

/-- **Every enabled identifier names a vendored anchor**, and every rejected one
names none.  The anchors themselves are checked against the vendored tree by
`xtask vendor`, which is outside the kernel; what is proved here is that the
transcription record has no hole and no entry for a rejected family. -/
theorem vendorAnchor?_isSome_iff_enabled (id : PinnedCoreRuleId) :
    (vendorAnchor? id).isSome = true ↔ RuleEnabled id := by
  cases id <;> decide

theorem vendorAnchor?_eq_none_iff (id : PinnedCoreRuleId) :
    vendorAnchor? id = none ↔ Rejected (family id) := by
  cases id <;> decide

theorem exists_vendorAnchor_of_enabled {id : PinnedCoreRuleId}
    (h : RuleEnabled id) : ∃ anchor, vendorAnchor? id = some anchor := by
  have hs := (vendorAnchor?_isSome_iff_enabled id).mpr h
  cases ha : vendorAnchor? id with
  | none => rw [ha] at hs; exact absurd hs (by simp)
  | some anchor => exact ⟨anchor, rfl⟩

theorem exists_leanDeclaration_of_enabled {id : PinnedCoreRuleId}
    (h : RuleEnabled id) : ∃ name, leanDeclaration? id = some name := by
  have hs := (adequacy_map_total_on_enabled id).mpr h
  cases hd : leanDeclaration? id with
  | none => rw [hd] at hs; exact absurd hs (by simp)
  | some name => exact ⟨name, rfl⟩

/-- The enabled identifiers, in enumeration order. -/
def enabledRuleIds : List PinnedCoreRuleId :=
  [ .decodeModule
  , .decodeUleb128
  , .validUnreachable
  , .validNop
  , .validI32Const
  , .validDrop
  , .validIBinOp
  , .validITestOp
  , .validIRelOp
  , .validLocalGet
  , .validLocalSet
  , .validLocalTee
  , .validGlobalGet
  , .validGlobalSet
  , .validLoad
  , .validStore
  , .validMemorySize
  , .validMemoryGrow
  , .validBlock
  , .validLoop
  , .validIfThenElse
  , .validBr
  , .validBrIf
  , .validThrowTag
  , .validExprNil
  , .validExprCons
  , .validModule
  , .validFunc
  , .validMems
  , .validGemmExport
  , .validClosed
  , .storeAlloc
  , .storeLoadBytes
  , .storeStoreBytes
  , .storeMemoryGrow
  , .execUnreachable
  , .execNop
  , .execI32Const
  , .execDrop
  , .execIBinOp
  , .execIBinOpTrap
  , .execITestOp
  , .execIRelOp
  , .execLocalGet
  , .execLocalSet
  , .execLocalTee
  , .execGlobalGet
  , .execGlobalSet
  , .execLoad
  , .execLoadTrap
  , .execStore
  , .execStoreTrap
  , .execMemorySize
  , .execMemoryGrowSucceed
  , .execMemoryGrowRefuse
  , .execBlock
  , .execLoop
  , .execIfFalse
  , .execIfTrue
  , .execBrLoop
  , .execBrBlock
  , .execBrIfFalse
  , .execBrIfLoop
  , .execBrIfBlock
  , .execThrowTag
  , .execExitLabel
  , .execReturnGemm
  , .execEnterGemm
  , .execInstallTrap
  , .trapUnreachable
  , .trapOutOfBounds
  , .trapDivideByZero
  , .nondetMemoryGrow
  , .nondetNanResult
  , .tableGet
  , .tableSet
  , .tableSize
  , .tableGrow
  , .tableFill
  , .tableCopy
  , .tableInit
  , .tableElemDrop
  , .vectorExtractLane
  , .vectorReplaceLane
  , .vectorSplat
  , .vectorLanewise
  , .vectorShapeWidth
  , .refNull
  , .refFunc ]

theorem mem_enabledRuleIds_iff (id : PinnedCoreRuleId) :
    id ∈ enabledRuleIds ↔ RuleEnabled id := by cases id <;> decide

theorem enabledRuleIds_nodup : enabledRuleIds.Nodup := by decide

theorem enabledRuleIds_length : enabledRuleIds.length = 89 := rfl

theorem rejectedRuleIds_length :
    all.length - enabledRuleIds.length = 4 := rfl

/-- The mapped declaration name of an identifier, with the rejected ones
collapsed to the empty string.  Used only to state duplicate freedom of the
mapped names as a decidable computation. -/
def declarationOf (id : PinnedCoreRuleId) : String := (leanDeclaration? id).getD ""

/-- **The mapped Lean declarations are pairwise distinct.** -/
theorem enabledDeclarations_nodup :
    (enabledRuleIds.map declarationOf).Nodup := by decide

/-- **The identifier spellings are pairwise distinct.** -/
theorem ruleIds_nodup : (all.map ruleId).Nodup := by decide

/-- **Injectivity over the enabled rule set.**  Two enabled identifiers with the
same mapped Lean declaration are the same identifier: no declaration is claimed
by two rules. -/
theorem adequacy_map_injective_on_enabled {a b : PinnedCoreRuleId}
    (ha : RuleEnabled a) (hb : RuleEnabled b)
    (h : leanDeclaration? a = leanDeclaration? b) : a = b := by
  refine nodup_map_injOn declarationOf enabledRuleIds enabledDeclarations_nodup a b
    ((mem_enabledRuleIds_iff a).mpr ha) ((mem_enabledRuleIds_iff b).mpr hb) ?_
  unfold declarationOf
  rw [h]

/-- The identifier spelling is injective on the whole enumeration. -/
theorem ruleId_injective {a b : PinnedCoreRuleId} (h : ruleId a = ruleId b) :
    a = b :=
  nodup_map_injOn ruleId all ruleIds_nodup a b (mem_all a) (mem_all b) h

/-! ### Fully qualified names -/

/-- The namespace every mapped declaration lives in. -/
def declarationNamespace : String := "WasmGemmGnaf.Wasm."

/-- The fully qualified Lean declaration name of a rule. -/
def fullDeclaration? (id : PinnedCoreRuleId) : Option String :=
  (leanDeclaration? id).map (fun name => declarationNamespace ++ name)

theorem fullDeclaration?_isSome_iff (id : PinnedCoreRuleId) :
    (fullDeclaration? id).isSome = true ↔ RuleEnabled id := by
  unfold fullDeclaration?
  rw [← adequacy_map_total_on_enabled id]
  cases leanDeclaration? id <;> simp

/-- Injectivity survives qualification. -/
theorem fullDeclaration?_injective_on_enabled {a b : PinnedCoreRuleId}
    (ha : RuleEnabled a) (hb : RuleEnabled b)
    (h : fullDeclaration? a = fullDeclaration? b) : a = b := by
  obtain ⟨na, hna⟩ := exists_leanDeclaration_of_enabled ha
  obtain ⟨nb, hnb⟩ := exists_leanDeclaration_of_enabled hb
  unfold fullDeclaration? at h
  rw [hna, hnb] at h
  simp only [Option.map_some, Option.some.injEq] at h
  have : na = nb := string_append_left_cancel h
  exact adequacy_map_injective_on_enabled ha hb (by rw [hna, hnb, this])

end PinnedCoreRuleId

/-! ## The conformance map object -/

/-- One row of the conformance map: the pinned rule identifier, the Lean
declaration implementing it, its feature family, and its status. -/
structure AdequacyRow where
  /-- The vendored rule identifier spelling. -/
  ruleId : String
  /-- The reStructuredText label of the vendored rule this row was transcribed
  from, without its leading underscore. -/
  vendorAnchor : String
  /-- The Lean declaration, relative to the `WasmGemmGnaf.Wasm` namespace. -/
  leanDeclaration : String
  /-- The Core 3.0 feature family. -/
  family : FeatureFamily
  /-- What the released development does with the rule. -/
  status : RuleStatus
  deriving DecidableEq, Repr, Inhabited

/-- The conformance map: the revision and the vendored tree it is bound to, and
its rows. -/
structure AdequacyMap where
  /-- The commit of the pinned WebAssembly Core revision. -/
  revisionCommit : String
  /-- The vendored copy of that revision, carrying the digest of digests over
  every vendored file (`Wasm/Revision.lean`). -/
  vendorTree : VendoredTreeBody
  /-- One row per enabled pinned rule identifier. -/
  rows : List AdequacyRow
  deriving DecidableEq, Repr, Inhabited

/-- The row of an enabled rule identifier. -/
def PinnedCoreRuleId.row (id : PinnedCoreRuleId) : AdequacyRow :=
  { ruleId := id.ruleId
    vendorAnchor := id.anchorOf
    leanDeclaration := id.declarationOf
    family := id.family
    status := id.status }

/-- The released conformance map: the pinned commit and the vendored tree,
together with one row per enabled identifier. -/
def core3AdequacyMap : AdequacyMap :=
  { revisionCommit := core3RevisionCommit
    vendorTree := core3VendoredTree
    rows := PinnedCoreRuleId.enabledRuleIds.map PinnedCoreRuleId.row }

/-- **Identity binding to the pinned revision.**  The map carries the pinned
`wg-3.0` commit. -/
theorem core3AdequacyMap_revisionCommit :
    core3AdequacyMap.revisionCommit = core3Revision.commit := rfl

/-- **Identity binding to the vendored content.**  The map carries the vendored
tree record, whose `manifestSha256` is the digest of
`vendor/wasm-spec/SHA256SUMS`, itself the list of digests of all forty vendored
files.  Changing any vendored byte changes that literal, and `xtask vendor`
recomputes it from the bytes on disk. -/
theorem core3AdequacyMap_vendorTree :
    core3AdequacyMap.vendorTree = core3VendoredTree := rfl

theorem core3AdequacyMap_vendorDigest :
    core3AdequacyMap.vendorTree.manifestSha256 = core3VendorManifestSha256 := rfl

/-- **The commit and the vendored tree are the same revision.**  The map cannot
name one revision and vendor another. -/
theorem core3AdequacyMap_vendorTree_commit :
    core3AdequacyMap.vendorTree.commit = core3AdequacyMap.revisionCommit := rfl

/-- **The model and the map are bound to the same revision.**  Every lawful
profile carries the commit the map carries; a profile pinned to a different
revision cannot satisfy this. -/
theorem adequacy_profile_revision_agree (profile : Profile) :
    profile.body.revisionCommit = core3AdequacyMap.revisionCommit :=
  profile.revisionCommit_eq

/-- **Every lawful profile is bound to the vendored content.**  The commit a
lawful profile carries is the commit of the tree whose digest of digests the map
records, so a profile cannot be pinned to a revision other than the vendored
one. -/
theorem adequacy_profile_vendorTree_agree (profile : Profile) :
    profile.body.revisionCommit = core3AdequacyMap.vendorTree.commit :=
  profile.revisionCommit_eq

/-- Distinct revisions have distinct canonical identities, so the binding above
is a real one. -/
theorem adequacy_revision_identity_eq_iff (r : RevisionBody) :
    RevisionBody.identity r = RevisionBody.identity core3Revision ↔
      r = core3Revision :=
  RevisionBody.identity_eq_iff

/-- Distinct vendored trees have distinct canonical identities: the content
binding is a real one too, and is not satisfied by a tree that merely claims the
same commit. -/
theorem adequacy_vendorTree_identity_eq_iff (t : VendoredTreeBody) :
    VendoredTreeBody.identity t =
        VendoredTreeBody.identity core3AdequacyMap.vendorTree ↔
      t = core3AdequacyMap.vendorTree :=
  VendoredTreeBody.identity_eq_iff

theorem core3AdequacyMap_rows_length :
    core3AdequacyMap.rows.length = PinnedCoreRuleId.enabledRuleIds.length := by
  simp [core3AdequacyMap]

/-- Every enabled identifier has a row. -/
theorem core3AdequacyMap_covers {id : PinnedCoreRuleId}
    (h : PinnedCoreRuleId.RuleEnabled id) : id.row ∈ core3AdequacyMap.rows :=
  List.mem_map_of_mem ((PinnedCoreRuleId.mem_enabledRuleIds_iff id).mpr h)

/-- No rejected identifier has a row: a rejected family contributes no Lean
declaration to the map. -/
theorem core3AdequacyMap_excludes_rejected {id : PinnedCoreRuleId}
    (h : ¬ PinnedCoreRuleId.RuleEnabled id) :
    id.ruleId ∉ core3AdequacyMap.rows.map AdequacyRow.ruleId := by
  intro hmem
  simp only [core3AdequacyMap, List.map_map, List.mem_map] at hmem
  obtain ⟨other, hother, heq⟩ := hmem
  have : other = id := PinnedCoreRuleId.ruleId_injective heq
  subst this
  exact h ((PinnedCoreRuleId.mem_enabledRuleIds_iff other).mp hother)

/-- **The map is duplicate free in its identifiers.** -/
theorem core3AdequacyMap_ruleIds_nodup :
    (core3AdequacyMap.rows.map AdequacyRow.ruleId).Nodup := by decide

/-- **The map is duplicate free in its Lean declarations**: no Lean declaration
is claimed by two pinned rules. -/
theorem core3AdequacyMap_declarations_nodup :
    (core3AdequacyMap.rows.map AdequacyRow.leanDeclaration).Nodup := by decide

/-- Every row of the map records a status that the release feature matrix
admits: no row of the map belongs to a rejected family. -/
theorem core3AdequacyMap_rows_enabled {row : AdequacyRow}
    (h : row ∈ core3AdequacyMap.rows) : Enabled row.family := by
  simp only [core3AdequacyMap, List.mem_map] at h
  obtain ⟨id, hid, rfl⟩ := h
  exact (PinnedCoreRuleId.ruleEnabled_iff_family_enabled id).mp
    ((PinnedCoreRuleId.mem_enabledRuleIds_iff id).mp hid)

/-- A witnessed `Option` has exactly one witness.  `∃!` is Mathlib notation and
this development is Std-only, so uniqueness is written out. -/
theorem exists_unique_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    ∃ b : α, o = some b ∧ ∀ c : α, o = some c → c = b := by
  refine ⟨a, h, ?_⟩
  intro c hc
  rw [h] at hc
  simpa using hc.symm

/-- **Exactly one row per enabled rule.**  The map has a row for every enabled
identifier and no identifier has two, so a rule cannot be mapped twice. -/
theorem core3AdequacyMap_row_unique {id : PinnedCoreRuleId}
    (h : PinnedCoreRuleId.RuleEnabled id) :
    ∃ row : AdequacyRow,
      (row ∈ core3AdequacyMap.rows ∧ row.ruleId = id.ruleId) ∧
      ∀ other : AdequacyRow,
        other ∈ core3AdequacyMap.rows → other.ruleId = id.ruleId → other = row := by
  refine ⟨id.row, ⟨core3AdequacyMap_covers h, rfl⟩, ?_⟩
  intro other hmem hrule
  simp only [core3AdequacyMap, List.mem_map] at hmem
  obtain ⟨other', _, rfl⟩ := hmem
  have : other' = id := PinnedCoreRuleId.ruleId_injective hrule
  rw [this]

/-! ## SPEC section 15: `profile_matches_pinned_revision`

SPEC section 7.1 is the definition of this name, verbatim:

> "`profile_matches_pinned_revision` means that the concrete model and map are
>  identity-bound to the vendored revision and that every enabled vendored rule
>  has exactly one mapped Lean declaration.  It does not claim that Lean can
>  derive English prose from bytes.  The reviewed transcription from normative
>  rules to initial Lean definitions is an explicitly disclosed authority
>  boundary; all subsequent GEMM, cost, coverage, and optimality reasoning is
>  kernel checked."

The theorem below is exactly that conjunction, and no more:

* **identity binding to the vendored revision.**  The profile, the map and the
  vendored tree carry one commit; the map carries the vendored tree record whose
  `manifestSha256` is the digest of `vendor/wasm-spec/SHA256SUMS`, itself the
  list of digests of every vendored file; and both identities are injective, so
  a different revision or a single different vendored byte gives a different
  identity.  `xtask vendor` recomputes the digest from the bytes on disk and
  fails the gate if the literal has drifted.
* **exactly one mapped Lean declaration per enabled vendored rule.**  Each
  enabled identifier has exactly one fully qualified Lean declaration name,
  exactly one row in the map, and exactly one vendored anchor; distinct enabled
  identifiers never share a declaration; and a rejected identifier has no
  declaration, no anchor and no row.

It does **not** claim the transcription is faithful to the vendored rule bodies.
That is the disclosed authority boundary of SPEC section 7.1, restated in the
header of this file together with the two gaps that remain open. -/

/-- **SPEC section 15, `Wasm.profile_matches_pinned_revision`.**

Both conjuncts of SPEC section 7.1: the concrete model and map are
identity-bound to the vendored revision, and every enabled vendored rule has
exactly one mapped Lean declaration. -/
theorem profile_matches_pinned_revision (profile : Profile) :
    (profile.body.revisionCommit = core3AdequacyMap.revisionCommit ∧
      core3AdequacyMap.revisionCommit = core3Revision.commit ∧
      core3AdequacyMap.vendorTree = core3VendoredTree ∧
      core3AdequacyMap.vendorTree.commit = core3AdequacyMap.revisionCommit ∧
      core3AdequacyMap.vendorTree.manifestSha256 = core3VendorManifestSha256 ∧
      (∀ r : RevisionBody,
        RevisionBody.identity r = RevisionBody.identity core3Revision ↔
          r = core3Revision) ∧
      (∀ t : VendoredTreeBody,
        VendoredTreeBody.identity t =
            VendoredTreeBody.identity core3AdequacyMap.vendorTree ↔
          t = core3AdequacyMap.vendorTree)) ∧
    (∀ id : PinnedCoreRuleId, PinnedCoreRuleId.RuleEnabled id →
      (∃ name : String,
        PinnedCoreRuleId.fullDeclaration? id = some name ∧
        ∀ other : String,
          PinnedCoreRuleId.fullDeclaration? id = some other → other = name) ∧
      (∃ row : AdequacyRow,
        (row ∈ core3AdequacyMap.rows ∧ row.ruleId = id.ruleId) ∧
        ∀ other : AdequacyRow,
          other ∈ core3AdequacyMap.rows → other.ruleId = id.ruleId → other = row) ∧
      (∃ anchor : String,
        PinnedCoreRuleId.vendorAnchor? id = some anchor ∧
        ∀ other : String,
          PinnedCoreRuleId.vendorAnchor? id = some other → other = anchor)) ∧
    (∀ a b : PinnedCoreRuleId,
      PinnedCoreRuleId.RuleEnabled a → PinnedCoreRuleId.RuleEnabled b →
        PinnedCoreRuleId.fullDeclaration? a = PinnedCoreRuleId.fullDeclaration? b →
          a = b) ∧
    (∀ id : PinnedCoreRuleId, ¬ PinnedCoreRuleId.RuleEnabled id →
      PinnedCoreRuleId.leanDeclaration? id = none ∧
      PinnedCoreRuleId.vendorAnchor? id = none ∧
      id.ruleId ∉ core3AdequacyMap.rows.map AdequacyRow.ruleId) := by
  refine ⟨⟨adequacy_profile_revision_agree profile, core3AdequacyMap_revisionCommit,
      core3AdequacyMap_vendorTree, core3AdequacyMap_vendorTree_commit,
      core3AdequacyMap_vendorDigest, adequacy_revision_identity_eq_iff,
      adequacy_vendorTree_identity_eq_iff⟩, ?_, ?_, ?_⟩
  · intro id h
    obtain ⟨name, hname⟩ := PinnedCoreRuleId.exists_leanDeclaration_of_enabled h
    obtain ⟨anchor, hanchor⟩ := PinnedCoreRuleId.exists_vendorAnchor_of_enabled h
    refine ⟨exists_unique_eq_some (a := PinnedCoreRuleId.declarationNamespace ++ name) ?_,
      core3AdequacyMap_row_unique h, exists_unique_eq_some hanchor⟩
    unfold PinnedCoreRuleId.fullDeclaration?
    rw [hname]
    rfl
  · intro a b ha hb h
    exact PinnedCoreRuleId.fullDeclaration?_injective_on_enabled ha hb h
  · intro id h
    -- `RuleEnabled` is decidable, so its double negation is eliminated without
    -- `Classical.choice`.
    have hnn : ¬ ¬ (PinnedCoreRuleId.status id = RuleStatus.rejectedByProfile) := h
    have hrej : Rejected (PinnedCoreRuleId.family id) :=
      (PinnedCoreRuleId.status_eq_rejected_iff id).mp (Decidable.of_not_not hnn)
    exact ⟨(PinnedCoreRuleId.leanDeclaration?_eq_none_iff id).mpr hrej,
      (PinnedCoreRuleId.vendorAnchor?_eq_none_iff id).mpr hrej,
      core3AdequacyMap_excludes_rejected h⟩

/-! ## Non-vacuity: the mapped declarations exist

Each mapped Lean declaration is mentioned below, so deleting or renaming one
breaks this file.  As disclosed in the header, this establishes that a
declaration with each mapped *role* exists; it does not establish that the
recorded string is that declaration's name, which Lean cannot check without
metaprogramming. -/

theorem mapped_declarations_referenced : True := by
  have _ := @decode
  have _ := @decodeULEB
  have _ := @InstrTyping.unreachable
  have _ := @InstrTyping.nop
  have _ := @InstrTyping.i32Const
  have _ := @InstrTyping.drop
  have _ := @InstrTyping.iBinOp
  have _ := @InstrTyping.iTestOp
  have _ := @InstrTyping.iRelOp
  have _ := @InstrTyping.localGet
  have _ := @InstrTyping.localSet
  have _ := @InstrTyping.localTee
  have _ := @InstrTyping.globalGet
  have _ := @InstrTyping.globalSet
  have _ := @InstrTyping.load
  have _ := @InstrTyping.store
  have _ := @InstrTyping.memorySize
  have _ := @InstrTyping.memoryGrow
  have _ := @InstrTyping.block
  have _ := @InstrTyping.loop
  have _ := @InstrTyping.ifThenElse
  have _ := @InstrTyping.br
  have _ := @InstrTyping.brIf
  have _ := @InstrTyping.throwTag
  have _ := @ExprTyping.nil
  have _ := @ExprTyping.cons
  have _ := @validate
  have _ := @WasmGemmGnaf.Wasm.Module.checkFunc
  have _ := @WasmGemmGnaf.Wasm.Module.checkMems
  have _ := @WasmGemmGnaf.Wasm.Module.checkGemmExport
  have _ := @WasmGemmGnaf.Wasm.Module.checkClosed
  have _ := @Store.alloc
  have _ := @Store.loadBytes
  have _ := @Store.storeBytes
  have _ := @Memory.grow
  have _ := @Step.unreachable
  have _ := @Step.nop
  have _ := @Step.i32Const
  have _ := @Step.drop
  have _ := @Step.iBinOp
  have _ := @Step.iBinOpTrap
  have _ := @Step.iTestOp
  have _ := @Step.iRelOp
  have _ := @Step.localGet
  have _ := @Step.localSet
  have _ := @Step.localTee
  have _ := @Step.globalGet
  have _ := @Step.globalSet
  have _ := @Step.load
  have _ := @Step.loadTrap
  have _ := @Step.store
  have _ := @Step.storeTrap
  have _ := @Step.memorySize
  have _ := @Step.memoryGrowSucceed
  have _ := @Step.memoryGrowRefuse
  have _ := @Step.block
  have _ := @Step.loop
  have _ := @Step.ifFalse
  have _ := @Step.ifTrue
  have _ := @Step.brLoop
  have _ := @Step.brBlock
  have _ := @Step.brIfFalse
  have _ := @Step.brIfLoop
  have _ := @Step.brIfBlock
  have _ := @Step.throwTag
  have _ := @Step.exitLabel
  have _ := @Step.returnGemm
  have _ := @Step.enterGemm
  have _ := @Step.installTrap
  have _ := @Trap.unreachable
  have _ := @Trap.outOfBounds
  have _ := @Trap.divideByZero
  have _ := @Num.growResults
  have _ := @Num.nanResults32
  have _ := @TableInst.get
  have _ := @TableInst.set
  have _ := @TableInst.size
  have _ := @TableInst.grow
  have _ := @TableInst.fill
  have _ := @TableInst.copy
  have _ := @TableInst.init
  have _ := @ElemInst.dropSeg
  have _ := @V128.extractLane
  have _ := @V128.replaceLane
  have _ := @V128.splat
  have _ := @V128.zipLanes
  have _ := @VecShape.lanes_mul_laneWidth
  have _ := @Ref.null
  have _ := @Ref.func
  trivial

/-! ## Scope of the `modelledUnreachable` status

`Wasm/Table.lean` proves that the released validator rejects every table
instruction, that a validating module declares no table or element segment at
all, and that `Wasm/Step.lean` enumerates no successor for a table instruction.
The same holds of the vector instructions, and is proved here because this is
the first module importing both `Wasm/Vector.lean` and `Wasm/Step.lean`.

Together these are the machine-checked meaning of `RuleStatus.modelledUnreachable`:
the mapped declaration exists and its laws are proved, but no released execution
reaches it. -/

/-- The released validator types no vector instruction. -/
theorem checkInstr_vector_rejected (C : Ctx) (h : Nat) (s : VecShape)
    (lane : Nat) (lo hi : UInt64) (arg : MemArg) (lanes : List Nat)
    (u : VecUnOp) (b : VecBinOp) (r : VecRelOp) (ext : Option SignExt) :
    checkInstr C h (.vecConst lo hi) = none ∧
    checkInstr C h (.vecUnOp s u) = none ∧
    checkInstr C h (.vecBinOp s b) = none ∧
    checkInstr C h (.vecRelOp s r) = none ∧
    checkInstr C h .vecBitselect = none ∧
    checkInstr C h (.vecSplat s) = none ∧
    checkInstr C h (.vecExtractLane s lane ext) = none ∧
    checkInstr C h (.vecReplaceLane s lane) = none ∧
    checkInstr C h (.vecShuffle lanes) = none ∧
    checkInstr C h (.vecLoad arg) = none ∧
    checkInstr C h (.vecStore arg) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The released reduction relation enumerates no successor for a vector
instruction. -/
theorem successorsOfInstr_vector_empty (c : Config) (rest : List Instr)
    (s : VecShape) (lane : Nat) (lo hi : UInt64) (arg : MemArg)
    (lanes : List Nat) (u : VecUnOp) (b : VecBinOp) (r : VecRelOp)
    (ext : Option SignExt) :
    successorsOfInstr c (.vecConst lo hi) rest = [] ∧
    successorsOfInstr c (.vecUnOp s u) rest = [] ∧
    successorsOfInstr c (.vecBinOp s b) rest = [] ∧
    successorsOfInstr c (.vecRelOp s r) rest = [] ∧
    successorsOfInstr c .vecBitselect rest = [] ∧
    successorsOfInstr c (.vecSplat s) rest = [] ∧
    successorsOfInstr c (.vecExtractLane s lane ext) rest = [] ∧
    successorsOfInstr c (.vecReplaceLane s lane) rest = [] ∧
    successorsOfInstr c (.vecShuffle lanes) rest = [] ∧
    successorsOfInstr c (.vecLoad arg) rest = [] ∧
    successorsOfInstr c (.vecStore arg) rest = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end WasmGemmGnaf.Wasm
