/-
  Wasm/Core/Profile.lean --- PROFILE ADMISSION over the pinned Core 3.0 module
  syntax.

  WHAT THIS IS.  SPEC section 7.2 says that "disabled forms decode when
  grammatically valid and then fail profile validation".  This file is the
  second half of that sentence, stated over `Wasm.Core.Module` --- the syntax
  the pinned decoder of `Wasm/Core/Decode.lean` actually produces --- rather
  than over the older `Wasm.Module` of `Wasm/Syntax.lean`.  `Module.admittedBy`
  is the decidable predicate "the released profile admits this module".

  WHY IT IS NOT THE VALIDATOR.  Core validity (`Module_ok'` of
  `Core/Validation/ModulesAmended.lean`, and the algorithm of
  `Core/ValidateModule.lean`) asks whether a module is a well-typed Core 3.0
  module.  Profile admission asks the separate question SPEC section 7.2 poses:
  whether the module stays inside the RELEASED profile --- its feature matrix,
  its limits, its closed import policy and its exported ABI.  A module can be
  core-valid and profile-rejected; `memory64Module` below is exactly that.  The
  two halves are conjoined by `Module.ValidUnder` in
  `Wasm/Core/ProfileAmendment.lean`.

  HOW THE FEATURE MATRIX IS APPLIED.  `Instr.requiredFeature` is a TOTAL,
  EXHAUSTIVE match with one arm per instruction constructor and NO default arm,
  in the same discipline `Wasm/Feature.lean`'s `releaseDecision` uses: SPEC
  section 7.2 forbids feature defaults, and a `| _ =>` arm here would be one.
  `Module.requiredFeatures` collects the families of every construct of a
  module, and `Module.featuresAdmittedBy` requires each of them to be `enabled`
  in the profile's OWN stored feature table --- not in a fresh literal written
  here.  So an admission verdict is driven by the profile record the release
  gate identity-checks.

  WHICH REJECTED FAMILIES ARE SYNTACTICALLY REACHABLE, STATED PLAINLY.  Two of
  the four rejected families of SPEC section 7.2 have witnesses in the pinned
  Core 3.0 abstract syntax and are rejected here, by theorems with concrete
  modules:

  * `memory64` --- `memtype = addrtype limits PAGE` and `tabletype = addrtype
    limits reftype` both carry an `addrtype`, and `AddrType.i64` is the
    memory64 proposal (`memory64Module_not_admitted`,
    `memory64TableModule_not_admitted`).
  * `relaxedSimd` --- the pinned `1.3-syntax.instructions.spectec` really does
    contain `RELAXED_SWIZZLE`, `RELAXED_MIN`/`MAX`, `RELAXED_Q15MULR`,
    `RELAXED_LANESELECT`, `RELAXED_MADD`/`NMADD`, `RELAXED_DOT`,
    `RELAXED_DOT_ADD` and `RELAXED_TRUNC`, so a relaxed instruction is an
    ordinary term of `Instr` (`relaxedSimdModule_not_admitted`).

  The other two --- `sharedMemoriesAtomicsThreads` and
  `componentModelAndPostCore3` --- have no form in the pinned Core 3.0 syntax
  at all: `limits` has no shared flag and `instr` has no atomic instruction, and
  a component binary is not a core module.  `requiredFeature_ne_shared` and
  `requiredFeature_ne_componentModel` below prove that no construct of the
  pinned syntax is ever attributed to them.  Their rejection therefore happens
  at the BINARY layer, and it is proved there --- see
  `Wasm/Core/ProfileBinary.lean`.  Nothing here pretends to discharge it.

  The general rejection theorem `not_admittedBy_of_rejected` is uniform over all
  four: whatever family a construct is attributed to, if the profile rejects
  that family the module is not admitted.

  ANTI-VACUITY.  A predicate nothing satisfies would satisfy every rejection
  theorem, so `releaseBaselineModule_admitted` exhibits a module the release
  profile DOES admit, and `releaseRichModule_admitted` together with
  `releaseRichModule_uses_every_enabled_family` exhibits an admitted module that
  uses all seven enabled families at once.

  Every declaration in this file is proved.  Nothing is assumed, and no
  declaration here carries a Core 3.0 coverage marker: this file transcribes no
  pinned rule.
-/
import WasmGemmGnaf.Wasm.Core.Modules
import WasmGemmGnaf.Wasm.Profile

set_option autoImplicit false
set_option maxRecDepth 100000

namespace WasmGemmGnaf.Wasm

/-! ## The bridge from the profile's ABI record to Core 3.0 types

`Wasm.ProfileBody.requiredExports` states the exported ABI with the value types
of `Wasm/Types.lean`.  Admission is decided over `Wasm.Core` types, so the two
readings are connected by an explicit, total translation rather than by a
coincidence of constructor names.  `Wasm.RefType` has no `Core.ValType` image in
general (the Core reference types carry a `heaptype` with a different shape), so
the translation is partial and says so; the release ABI is numeric. -/

/-- The Core 3.0 value type a profile-level value type denotes. -/
def ValType.toCore? : ValType → Option Core.ValType
  | .num .i32 => some (.num .i32)
  | .num .i64 => some (.num .i64)
  | .num .f32 => some (.num .f32)
  | .num .f64 => some (.num .f64)
  | .vec .v128 => some (.vec .v128)
  | .ref _ => none

/-- The Core 3.0 function type a profile-level ABI type denotes. -/
def FuncType.toCore? (t : FuncType) :
    Option (List Core.ValType × List Core.ValType) :=
  match t.params.mapM ValType.toCore?, t.results.mapM ValType.toCore? with
  | some dom, some cod => some (dom, cod)
  | _, _ => none

/-- The released ABI of SPEC section 7.2, read in Core 3.0 types: the exported
`gemm` really is `(i32, i32) -> i32` on both sides of the translation. -/
theorem gemmFuncType_toCore :
    FuncType.toCore? gemmFuncType =
      some ([Core.ValType.num .i32, Core.ValType.num .i32],
            [Core.ValType.num .i32]) := rfl

end WasmGemmGnaf.Wasm

namespace WasmGemmGnaf.Wasm.Core

/-! ## Feature attribution of the Core 3.0 syntax

One family per construct, mirroring `Wasm.ValType.requiredFeature` and
`Wasm.AddressType.requiredFeature` of the older model. -/

/-- The feature family that permits this address type.  `i64` addresses are
exactly the memory64 proposal, which SPEC section 7.2 rejects. -/
def AddrType.requiredFeature : AddrType → FeatureFamily
  | .i32 => .scalarCore
  | .i64 => .memory64

/-- The feature family a value type belongs to.

`BOT` is a `/sem` form: `Module.isSyn` rejects it and `Module.admittedBy`
requires `Module.wf`, so this arm is unreachable for any admitted module. -/
def ValType.requiredFeature : ValType → FeatureFamily
  | .num _ => .scalarCore
  | .vec _ => .fixedWidthSimd128
  | .ref _ => .referenceTypesTypedFunctionReferencesGc
  | .bot => .scalarCore

/-- The feature family a composite type belongs to: structures and arrays are
the GC proposal, function types are core. -/
def CompType.requiredFeature : CompType → FeatureFamily
  | .struct _ => .referenceTypesTypedFunctionReferencesGc
  | .array _ => .referenceTypesTypedFunctionReferencesGc
  | .func _ _ => .scalarCore

/-- The feature family a block type belongs to: a `_RESULT` block is core, a
`_IDX` block takes its type from the type section and is the multi-value
extension. -/
def BlockType.requiredFeature : BlockType → FeatureFamily
  | .result _ => .scalarCore
  | .idx _ => .multiValueAndExtendedConst

/-! ### The relaxed SIMD operators

The eight places `1.3-syntax.instructions.spectec` introduces a relaxed
operator.  Each match below is exhaustive over its operator sort, with no
default arm, so a new relaxed constructor could not be silently classified as
standard SIMD. -/

/-- `vbinop_(Jnn X M)` and `vbinop_(Fnn X M)`: `RELAXED_Q15MULR`, `RELAXED_MIN`
and `RELAXED_MAX` are relaxed. -/
def VBinop.isRelaxed : VBinop → Bool
  | .int .add => false
  | .int .sub => false
  | .int (.addSat _) => false
  | .int (.subSat _) => false
  | .int .mul => false
  | .int (.avgr _) => false
  | .int (.q15mulrSat _) => false
  | .int (.relaxedQ15mulr _) => true
  | .int (.min _) => false
  | .int (.max _) => false
  | .float .add => false
  | .float .sub => false
  | .float .mul => false
  | .float .div => false
  | .float .min => false
  | .float .max => false
  | .float .pmin => false
  | .float .pmax => false
  | .float .relaxedMin => true
  | .float .relaxedMax => true

/-- `vternop_`: every case is relaxed --- the pinned source gives `vternop_(Jnn
X M) = RELAXED_LANESELECT` and `vternop_(Fnn X M) = RELAXED_MADD |
RELAXED_NMADD` and nothing else. -/
def VTernop.isRelaxed : VTernop → Bool
  | .int .relaxedLaneselect => true
  | .float .relaxedMadd => true
  | .float .relaxedNmadd => true

/-- `vswizzlop_(I8 X M) = SWIZZLE | RELAXED_SWIZZLE`. -/
def VSwizzlop.isRelaxed : VSwizzlop → Bool
  | .swizzle => false
  | .relaxedSwizzle => true

/-- `vextbinop__` : `RELAXED_DOT` is relaxed, `EXTMUL` and `DOT` are not. -/
def VExtBinop.isRelaxed : VExtBinop → Bool
  | .extmul _ _ => false
  | .dot _ => false
  | .relaxedDot _ => true

/-- `vextternop__ = RELAXED_DOT_ADD S`: the only case, and it is relaxed. -/
def VExtTernop.isRelaxed : VExtTernop → Bool
  | .relaxedDotAdd _ => true

/-- `vcvtop__`: `RELAXED_TRUNC` is relaxed, the other five conversions are
not. -/
def VCvtop.isRelaxed : VCvtop → Bool
  | .jj (.extend _ _) => false
  | .jf (.convert _ _) => false
  | .fj (.truncSat _ _) => false
  | .fj (.relaxedTrunc _ _) => true
  | .ff (.demote _) => false
  | .ff (.promote _) => false

/-- The family a vector instruction's operator selects: the relaxed family when
the operator is one of the eight relaxed forms, the standard fixed-width
128-bit family otherwise. -/
def vectorFamily (relaxed : Bool) : FeatureFamily :=
  if relaxed then .relaxedSimd else .fixedWidthSimd128

/-- The family `SELECT (valtype*)?` belongs to: the untyped form is core, the
typed form is the reference-types extension. -/
def selectFamily : Option (List ValType) → FeatureFamily
  | none => .scalarCore
  | some _ => .referenceTypesTypedFunctionReferencesGc

/-! ### The instruction classification

A total, exhaustive match: one arm per constructor of `Instr`, in the source's
own fragment order, and NO default arm.  SPEC section 7.2: "no feature defaults
are permitted". -/

/-- The feature family THIS instruction belongs to, ignoring the instructions
nested inside it (`Instr.requiredFeatures` collects those). -/
def Instr.requiredFeature : Instr → FeatureFamily
  -- instr/parametric
  | .nop => .scalarCore
  | .unreachable => .scalarCore
  | .drop => .scalarCore
  | .select ts => selectFamily ts
  -- instr/block
  | .block bt _ => BlockType.requiredFeature bt
  | .loop bt _ => BlockType.requiredFeature bt
  | .ifElse bt _ _ => BlockType.requiredFeature bt
  -- instr/br
  | .br _ => .scalarCore
  | .brIf _ => .scalarCore
  | .brTable _ _ => .scalarCore
  | .brOnNull _ => .referenceTypesTypedFunctionReferencesGc
  | .brOnNonNull _ => .referenceTypesTypedFunctionReferencesGc
  | .brOnCast _ _ _ => .referenceTypesTypedFunctionReferencesGc
  | .brOnCastFail _ _ _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/call
  | .call _ => .scalarCore
  | .callRef _ => .referenceTypesTypedFunctionReferencesGc
  | .callIndirect _ _ => .bulkMemoryMultipleMemoriesTables
  | .ret => .scalarCore
  | .returnCall _ => .tailCalls
  | .returnCallRef _ => .tailCalls
  | .returnCallIndirect _ _ => .tailCalls
  -- instr/exn
  | .throw _ => .exceptionHandling
  | .throwRef => .exceptionHandling
  | .tryTable _ _ _ => .exceptionHandling
  -- instr/local
  | .localGet _ => .scalarCore
  | .localSet _ => .scalarCore
  | .localTee _ => .scalarCore
  -- instr/global
  | .globalGet _ => .scalarCore
  | .globalSet _ => .scalarCore
  -- instr/table
  | .tableGet _ => .bulkMemoryMultipleMemoriesTables
  | .tableSet _ => .bulkMemoryMultipleMemoriesTables
  | .tableSize _ => .bulkMemoryMultipleMemoriesTables
  | .tableGrow _ => .bulkMemoryMultipleMemoriesTables
  | .tableFill _ => .bulkMemoryMultipleMemoriesTables
  | .tableCopy _ _ => .bulkMemoryMultipleMemoriesTables
  | .tableInit _ _ => .bulkMemoryMultipleMemoriesTables
  -- instr/elem
  | .elemDrop _ => .bulkMemoryMultipleMemoriesTables
  -- instr/memory
  | .load _ _ _ _ => .scalarCore
  | .store _ _ _ _ => .scalarCore
  | .vload _ _ _ _ => .fixedWidthSimd128
  | .vloadLane _ _ _ _ _ => .fixedWidthSimd128
  | .vstore _ _ _ => .fixedWidthSimd128
  | .vstoreLane _ _ _ _ _ => .fixedWidthSimd128
  | .memorySize _ => .scalarCore
  | .memoryGrow _ => .scalarCore
  | .memoryFill _ => .bulkMemoryMultipleMemoriesTables
  | .memoryCopy _ _ => .bulkMemoryMultipleMemoriesTables
  | .memoryInit _ _ => .bulkMemoryMultipleMemoriesTables
  -- instr/data
  | .dataDrop _ => .bulkMemoryMultipleMemoriesTables
  -- instr/ref
  | .refNull _ => .referenceTypesTypedFunctionReferencesGc
  | .refIsNull => .referenceTypesTypedFunctionReferencesGc
  | .refAsNonNull => .referenceTypesTypedFunctionReferencesGc
  | .refEq => .referenceTypesTypedFunctionReferencesGc
  | .refTest _ => .referenceTypesTypedFunctionReferencesGc
  | .refCast _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/func
  | .refFunc _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/i31
  | .refI31 => .referenceTypesTypedFunctionReferencesGc
  | .i31Get _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/struct
  | .structNew _ => .referenceTypesTypedFunctionReferencesGc
  | .structNewDefault _ => .referenceTypesTypedFunctionReferencesGc
  | .structGet _ _ _ => .referenceTypesTypedFunctionReferencesGc
  | .structSet _ _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/array
  | .arrayNew _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayNewDefault _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayNewFixed _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayNewData _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayNewElem _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayGet _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arraySet _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayLen => .referenceTypesTypedFunctionReferencesGc
  | .arrayFill _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayCopy _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayInitData _ _ => .referenceTypesTypedFunctionReferencesGc
  | .arrayInitElem _ _ => .referenceTypesTypedFunctionReferencesGc
  -- instr/extern
  | .externConvertAny => .referenceTypesTypedFunctionReferencesGc
  | .anyConvertExtern => .referenceTypesTypedFunctionReferencesGc
  -- instr/num
  | .const _ _ => .scalarCore
  | .unop _ _ => .scalarCore
  | .binop _ _ => .scalarCore
  | .testop _ _ => .scalarCore
  | .relop _ _ => .scalarCore
  | .cvtop _ _ _ => .scalarCore
  -- instr/vec
  | .vconst _ _ => .fixedWidthSimd128
  | .vvunop _ _ => .fixedWidthSimd128
  | .vvbinop _ _ => .fixedWidthSimd128
  | .vvternop _ _ => .fixedWidthSimd128
  | .vvtestop _ _ => .fixedWidthSimd128
  | .vunop _ _ => .fixedWidthSimd128
  | .vbinop _ op => vectorFamily (VBinop.isRelaxed op)
  | .vternop _ op => vectorFamily (VTernop.isRelaxed op)
  | .vtestop _ _ => .fixedWidthSimd128
  | .vrelop _ _ => .fixedWidthSimd128
  | .vshiftop _ _ => .fixedWidthSimd128
  | .vbitmask _ => .fixedWidthSimd128
  | .vswizzlop _ op => vectorFamily (VSwizzlop.isRelaxed op)
  | .vshuffle _ _ => .fixedWidthSimd128
  | .vextunop _ _ _ => .fixedWidthSimd128
  | .vextbinop _ _ op => vectorFamily (VExtBinop.isRelaxed op)
  | .vextternop _ _ op => vectorFamily (VExtTernop.isRelaxed op)
  | .vnarrow _ _ _ => .fixedWidthSimd128
  | .vcvtop _ _ op => vectorFamily (VCvtop.isRelaxed op)
  | .vsplat _ => .fixedWidthSimd128
  | .vextractLane _ _ _ => .fixedWidthSimd128
  | .vreplaceLane _ _ => .fixedWidthSimd128

mutual

/-- Every family this instruction and the instructions nested inside it
require. -/
def Instr.requiredFeatures : Instr → List FeatureFamily
  | .block bt body =>
      BlockType.requiredFeature bt :: InstrSeq.requiredFeatures body
  | .loop bt body =>
      BlockType.requiredFeature bt :: InstrSeq.requiredFeatures body
  | .ifElse bt thn els =>
      BlockType.requiredFeature bt ::
        (InstrSeq.requiredFeatures thn ++ InstrSeq.requiredFeatures els)
  | .tryTable bt _ body =>
      FeatureFamily.exceptionHandling ::
        BlockType.requiredFeature bt :: InstrSeq.requiredFeatures body
  | i => [Instr.requiredFeature i]

/-- Every family the instructions of this sequence require. -/
def InstrSeq.requiredFeatures : InstrSeq → List FeatureFamily
  | .nil => []
  | .cons i rest => Instr.requiredFeatures i ++ InstrSeq.requiredFeatures rest

end

/-- The collector never disagrees with the classification: the head of
`Instr.requiredFeatures i` is `Instr.requiredFeature i`, in every case. -/
theorem Instr.requiredFeatures_head (i : Instr) :
    (Instr.requiredFeatures i).head? = some (Instr.requiredFeature i) := by
  cases i <;> rfl

theorem Instr.requiredFeature_mem (i : Instr) :
    Instr.requiredFeature i ∈ Instr.requiredFeatures i := by
  cases i <;> simp [Instr.requiredFeatures, Instr.requiredFeature]

/-! ### Attribution of the module's declarations -/

/-- The families a composite type of the type section requires. -/
def CompType.requiredFeatures : CompType → List FeatureFamily
  | .struct fts => [CompType.requiredFeature (.struct fts)]
  | .array ft => [CompType.requiredFeature (.array ft)]
  | .func dom cod =>
      CompType.requiredFeature (.func dom cod) ::
        ((dom.toList ++ cod.toList).map ValType.requiredFeature)

/-- The families a `subtype` requires. -/
def SubType.requiredFeatures : SubType → List FeatureFamily
  | .sub _ _ ct => CompType.requiredFeatures ct

/-- The `subtype`s of a `rectype`, in order: the type index space a module's
type section defines. -/
def RecType.subTypes : RecType → List SubType
  | .recr sts => SubTypes.toList sts

/-- The families a type-section entry requires. -/
def TypeDef.requiredFeatures (td : TypeDef) : List FeatureFamily :=
  (RecType.subTypes td.rectype).flatMap SubType.requiredFeatures

/-- The families an external type requires: the address type of a memory or
table is the memory64 witness, a tag is exception handling. -/
def ExternType.requiredFeatures : ExternType → List FeatureFamily
  | .tag _ => [.exceptionHandling]
  | .global gt => [ValType.requiredFeature gt.valtype]
  | .mem mt => [AddrType.requiredFeature mt.addr]
  | .table tt =>
      [AddrType.requiredFeature tt.addr, .bulkMemoryMultipleMemoriesTables]
  | .func _ => [.scalarCore]

/-- The families a data segment requires. -/
def DataMode.requiredFeatures : DataMode → List FeatureFamily
  | .active _ e => .bulkMemoryMultipleMemoriesTables :: InstrSeq.requiredFeatures e
  | .passive => [.bulkMemoryMultipleMemoriesTables]

/-- The families an element mode requires. -/
def ElemMode.requiredFeatures : ElemMode → List FeatureFamily
  | .active _ e =>
      .bulkMemoryMultipleMemoriesTables :: InstrSeq.requiredFeatures e
  | .passive => [.bulkMemoryMultipleMemoriesTables]
  | .declare => [.referenceTypesTypedFunctionReferencesGc]

/-- Every feature family the module's declarations require.

The list is the concatenation of the per-declaration attributions, in the field
order of `Core/Modules.lean`'s `module` production.  Duplicates are not removed:
`Module.featuresAdmittedBy` quantifies over membership, for which duplicates are
irrelevant, and removing them would need a decidable-erasure step that buys
nothing. -/
def Module.requiredFeatures (m : Module) : List FeatureFamily :=
  m.types.flatMap TypeDef.requiredFeatures ++
  m.imports.flatMap (fun i => ExternType.requiredFeatures i.externtype) ++
  m.tags.map (fun _ => FeatureFamily.exceptionHandling) ++
  m.globals.flatMap (fun g =>
    ValType.requiredFeature g.globaltype.valtype :: InstrSeq.requiredFeatures g.init) ++
  m.mems.map (fun mm => AddrType.requiredFeature mm.memtype.addr) ++
  (if 1 < m.mems.length then [FeatureFamily.bulkMemoryMultipleMemoriesTables] else []) ++
  m.tables.flatMap (fun t =>
    AddrType.requiredFeature t.tabletype.addr ::
      FeatureFamily.bulkMemoryMultipleMemoriesTables ::
      InstrSeq.requiredFeatures t.init) ++
  m.funcs.flatMap (fun f =>
    f.locals.map (fun l => ValType.requiredFeature l.valtype) ++
      InstrSeq.requiredFeatures f.body) ++
  m.datas.flatMap (fun d => DataMode.requiredFeatures d.mode) ++
  m.elems.flatMap (fun e =>
    ValType.requiredFeature (.ref e.reftype) ::
      (e.init.flatMap InstrSeq.requiredFeatures ++ ElemMode.requiredFeatures e.mode))

/-! ### No pinned Core 3.0 construct is attributed to a family outside the
pinned grammar

`sharedMemoriesAtomicsThreads` and `componentModelAndPostCore3` name proposals
that the pinned Core 3.0 sources do not contain.  The classification never
produces them --- which is the honest statement of "not expressible here", and
is why their rejection is proved at the binary layer instead. -/

theorem AddrType.requiredFeature_ne_shared (a : AddrType) :
    AddrType.requiredFeature a ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases a <;> simp only [AddrType.requiredFeature] <;> decide

theorem ValType.requiredFeature_ne_shared (t : ValType) :
    ValType.requiredFeature t ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases t <;> simp only [ValType.requiredFeature] <;> decide

theorem CompType.requiredFeature_ne_shared (ct : CompType) :
    CompType.requiredFeature ct ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases ct <;> simp only [CompType.requiredFeature] <;> decide

theorem BlockType.requiredFeature_ne_shared (bt : BlockType) :
    BlockType.requiredFeature bt ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases bt <;> simp only [BlockType.requiredFeature] <;> decide

theorem BlockType.requiredFeature_ne_componentModel (bt : BlockType) :
    BlockType.requiredFeature bt ≠ FeatureFamily.componentModelAndPostCore3 := by
  cases bt <;> simp only [BlockType.requiredFeature] <;> decide

theorem selectFamily_ne_shared (ts : Option (List ValType)) :
    selectFamily ts ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases ts <;> simp only [selectFamily] <;> decide

theorem selectFamily_ne_componentModel (ts : Option (List ValType)) :
    selectFamily ts ≠ FeatureFamily.componentModelAndPostCore3 := by
  cases ts <;> simp only [selectFamily] <;> decide

theorem vectorFamily_ne_shared (b : Bool) :
    vectorFamily b ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases b <;> simp only [vectorFamily] <;> decide

theorem vectorFamily_ne_componentModel (b : Bool) :
    vectorFamily b ≠ FeatureFamily.componentModelAndPostCore3 := by
  cases b <;> simp only [vectorFamily] <;> decide

theorem Instr.requiredFeature_ne_shared (i : Instr) :
    Instr.requiredFeature i ≠ FeatureFamily.sharedMemoriesAtomicsThreads := by
  cases i <;>
    simp only [Instr.requiredFeature] <;>
    first
      | decide
      | exact selectFamily_ne_shared _
      | exact BlockType.requiredFeature_ne_shared _
      | exact vectorFamily_ne_shared _

theorem Instr.requiredFeature_ne_componentModel (i : Instr) :
    Instr.requiredFeature i ≠ FeatureFamily.componentModelAndPostCore3 := by
  cases i <;>
    simp only [Instr.requiredFeature] <;>
    first
      | decide
      | exact selectFamily_ne_componentModel _
      | exact BlockType.requiredFeature_ne_componentModel _
      | exact vectorFamily_ne_componentModel _

/-! ## The limits of SPEC section 7.2

Every limit the profile body carries that is a property of the module SYNTAX is
checked here.  Three of the fifteen are not:

* `maxModuleBytes` is a property of the ENCODING, and is checked by
  `Wasm/Core/ProfileBinary.lean`'s `admitsBytes`;
* `maxStackValues` and `maxManagedHeapBytes` are properties of an EXECUTION, not
  of a module, and belong to the configuration layer.

Saying so is the point: a limit silently omitted from a syntactic check would be
a limit not enforced anywhere. -/

/-- The module's declaration counts and its table and memory bounds lie inside
the given limits, with memories additionally bounded by the profile's page
limit (SPEC section 7.2's normative 65,536-page bound). -/
def Module.withinLimits (L : ResourceLimits) (maxPages : Nat) (m : Module) : Bool :=
  decide (m.types.length ≤ L.maxTypes) &&
  decide (m.funcs.length ≤ L.maxFunctions) &&
  decide (m.tables.length ≤ L.maxTables) &&
  decide (m.mems.length ≤ L.maxMemories) &&
  decide (m.globals.length ≤ L.maxGlobals) &&
  decide (m.tags.length ≤ L.maxTags) &&
  decide (m.elems.length ≤ L.maxElementSegments) &&
  decide (m.datas.length ≤ L.maxDataSegments) &&
  decide (m.imports.length ≤ L.maxImports) &&
  decide (m.exports.length ≤ L.maxExports) &&
  m.tables.all (fun t =>
    decide (t.tabletype.lim.min.val ≤ L.maxTableElements) &&
    (match t.tabletype.lim.max with
     | none => true
     | some n => decide (n.val ≤ L.maxTableElements))) &&
  m.funcs.all (fun f => decide (f.locals.length ≤ L.maxLocals)) &&
  m.mems.all (fun mm =>
    decide (mm.memtype.lim.min.val ≤ maxPages) &&
    (match mm.memtype.lim.max with
     | none => true
     | some n => decide (n.val ≤ maxPages)))

/-- The module lies inside the profile's OWN stored limits. -/
def Module.withinLimitsOf (P : Profile) (m : Module) : Bool :=
  Module.withinLimits P.body.limits P.body.maxPages m

/-! ## The exported ABI -/

/-- A profile-level export name (an ASCII `String`) and a Core 3.0 `name` (a
list of Unicode scalar values) denote the same name. -/
def nameMatches (s : String) (n : Name) : Bool :=
  (n.val.map (fun c => c.val)) == s.toList.map Char.toNat

/-- The type index space a module's type section defines: every `subtype` of
every recursive group, in order. -/
def Module.subTypes (m : Module) : List SubType :=
  m.types.flatMap (fun td => RecType.subTypes td.rectype)

/-- The Core 3.0 function type of the module's own function `x`.

The function index space of a module with no imports is exactly `m.funcs`, and
`Module.admittedBy` requires the module to have no imports (SPEC section 7.2's
closed profile), so this is the whole index space wherever it is used. -/
def Module.funcTypeAt? (m : Module) (x : FuncIdx) :
    Option (List ValType × List ValType) :=
  match m.funcs[x.val]? with
  | none => none
  | some f =>
      match (Module.subTypes m)[f.typeidx.val]? with
      | some (.sub _ _ (.func dom cod)) => some (dom.toList, cod.toList)
      | _ => none

/-- The module satisfies one of the profile's required exports. -/
def Module.satisfiesExport (m : Module) (r : ExportRequirement) : Bool :=
  m.exports.any (fun e =>
    nameMatches r.name e.name &&
    (match r.kind, e.externidx with
     | .memory, .mem _ => true
     | .function ft, .func x =>
         match Module.funcTypeAt? m x, FuncType.toCore? ft with
         | some (dom, cod), some (dom', cod') => (dom == dom') && (cod == cod')
         | _, _ => false
     | _, _ => false))

/-- Every export the profile requires is present, with the right kind and, for a
function, the right ABI type. -/
def Module.exportsAdmittedBy (P : Profile) (m : Module) : Bool :=
  P.body.requiredExports.all (Module.satisfiesExport m)

/-! ## Admission -/

/-- Every family the module requires is `enabled` in the given feature table. -/
def Module.featuresAdmitted (table : List FeatureRow) (m : Module) : Bool :=
  (Module.requiredFeatures m).all
    (fun f => lookupDecision table f == some FeatureDecision.enabled)

/-- Every family the module requires is `enabled` in the profile's OWN stored
feature table. -/
def Module.featuresAdmittedBy (P : Profile) (m : Module) : Bool :=
  Module.featuresAdmitted P.body.featureTable m

/-- **The released profile admits this module.**

Six conjuncts, each a clause of SPEC section 7.2:

1. the module is a Core 3.0 module at all (`Module.wf`: every `-- if` side
   condition and the `/syn` phase invariant);
2. the profile is CLOSED --- it permits no import;
3. and the module imports nothing;
4. every feature family the module requires is enabled by the profile's stored
   matrix;
5. the module's counts and its table and memory bounds lie inside the profile's
   stored limits;
6. the profile's required exports are all present with the right ABI.

Conjunct 2 makes the predicate `false` on any profile that permits an import,
rather than silently guessing an import-matching rule: SPEC section 7.2 requires
the release profile to be closed, and a profile that is not closed needs a new
theorem, not this one. -/
def Module.admittedBy (P : Profile) (m : Module) : Bool :=
  m.wf &&
  P.body.importPolicy.permitted.isEmpty &&
  m.imports.isEmpty &&
  Module.featuresAdmittedBy P m &&
  Module.withinLimitsOf P m &&
  Module.exportsAdmittedBy P m

/-- Admission as a proposition. -/
def Module.AdmittedBy (P : Profile) (m : Module) : Prop :=
  Module.admittedBy P m = true

instance Module.instDecidableAdmittedBy (P : Profile) (m : Module) :
    Decidable (Module.AdmittedBy P m) := by
  unfold Module.AdmittedBy; exact inferInstance

/-! ## The two directions that matter -/

/-- An admitted module requires only enabled families. -/
theorem Module.enabled_of_admittedBy {P : Profile} {m : Module}
    (h : Module.AdmittedBy P m) :
    ∀ f ∈ Module.requiredFeatures m, Enabled f := by
  have hf : Module.featuresAdmitted P.body.featureTable m = true := by
    unfold Module.AdmittedBy Module.admittedBy Module.featuresAdmittedBy at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.2
  intro f hmem
  have hall := (List.all_eq_true.mp hf) f hmem
  have hdec : P.decisionFor f = some FeatureDecision.enabled := by
    unfold Profile.decisionFor Profile.featureTable
    simpa using hall
  have heq := P.decisionFor_eq f
  rw [hdec] at heq
  exact (Option.some.inj heq).symm

/-- **A module using a rejected family is not admitted.**  Uniform over all four
rejected families of SPEC section 7.2: whichever construct carries the family,
and whichever profile is asked, admission fails. -/
theorem Module.not_admittedBy_of_rejected (P : Profile) (m : Module)
    {f : FeatureFamily} (hmem : f ∈ Module.requiredFeatures m) (hf : Rejected f) :
    ¬ Module.AdmittedBy P m := by
  intro h
  exact not_enabled_and_rejected f ⟨Module.enabled_of_admittedBy h f hmem, hf⟩

/-- The contrapositive, as a `Bool` fact. -/
theorem Module.admittedBy_eq_false_of_rejected (P : Profile) (m : Module)
    {f : FeatureFamily} (hmem : f ∈ Module.requiredFeatures m) (hf : Rejected f) :
    Module.admittedBy P m = false := by
  have := Module.not_admittedBy_of_rejected P m hmem hf
  unfold Module.AdmittedBy at this
  simpa using this

/-- The converse direction: admission is exactly the six conjuncts, so a module
meeting them all IS admitted.  Nothing is hidden behind the predicate. -/
theorem Module.admittedBy_of_conjuncts {P : Profile} {m : Module}
    (hwf : m.wf = true)
    (hclosed : P.body.importPolicy.permitted.isEmpty = true)
    (himp : m.imports.isEmpty = true)
    (hfeat : Module.featuresAdmittedBy P m = true)
    (hlim : Module.withinLimitsOf P m = true)
    (hexp : Module.exportsAdmittedBy P m = true) :
    Module.AdmittedBy P m := by
  unfold Module.AdmittedBy Module.admittedBy
  simp [hwf, hclosed, himp, hfeat, hlim, hexp]

/-- Admission implies the module has no imports: the release profile is closed
(SPEC section 7.2), which is what makes `Module.funcTypeAt?` above the whole
function index space. -/
theorem Module.imports_eq_nil_of_admittedBy {P : Profile} {m : Module}
    (h : Module.AdmittedBy P m) : m.imports = [] := by
  unfold Module.AdmittedBy Module.admittedBy at h
  simp only [Bool.and_eq_true] at h
  exact List.isEmpty_iff.mp h.1.1.1.2

/-- Admission implies the module is a Core 3.0 module: every `-- if` side
condition holds and no `/sem` form occurs in it. -/
theorem Module.wf_of_admittedBy {P : Profile} {m : Module}
    (h : Module.AdmittedBy P m) : m.wf = true := by
  unfold Module.AdmittedBy Module.admittedBy at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-! ## Admission does not depend on which lawful profile is asked

Every field of the profile body that admission reads --- the feature table, the
import policy, the limits, the page bound and the required exports --- is pinned
by `ProfileLawful`.  So the verdict is the same for every `Profile`, and the
witnesses below are closed computations rather than statements about an
unknown record. -/

/-- Admission with SPEC section 7.2's literals substituted for the profile's
stored fields. -/
def Module.admittedByRelease (m : Module) : Bool :=
  m.wf &&
  closedImportPolicy.permitted.isEmpty &&
  m.imports.isEmpty &&
  Module.featuresAdmitted releaseFeatureTable m &&
  Module.withinLimits canonicalResourceLimits 65536 m &&
  requiredReleaseExports.all (Module.satisfiesExport m)

/-- **Any lawful profile gives the same verdict.**  `ProfileLawful` pins every
field admission reads, so `Module.admittedBy` is a function of the module
alone. -/
theorem Module.admittedBy_eq_release (P : Profile) (m : Module) :
    Module.admittedBy P m = Module.admittedByRelease m := by
  unfold Module.admittedBy Module.admittedByRelease Module.featuresAdmittedBy
    Module.withinLimitsOf Module.exportsAdmittedBy
  rw [P.lawful.importPolicy, P.lawful.featureTable, P.lawful.limits,
    P.lawful.maxPages, P.lawful.requiredExports]

theorem Module.admittedBy_iff_release (P : Profile) (m : Module) :
    Module.AdmittedBy P m ↔ Module.admittedByRelease m = true := by
  unfold Module.AdmittedBy
  rw [Module.admittedBy_eq_release]

/-! ## Witnesses

A rejection theorem is satisfied by a predicate nothing satisfies, so the
positive witnesses come first. -/

/-- An ASCII code point as a Core 3.0 `char`. -/
def asciiChar (n : Nat) : UChar := ⟨n % 0x80, Or.inl (by omega)⟩

/-- An ASCII string as a Core 3.0 `name`.  The `|$utf8(char*)| < 2^32` side
condition of the `name` production is discharged by computation, not assumed. -/
def asciiName (ns : List Nat)
    (h : (utf8 (ns.map asciiChar)).length < 2 ^ 32 := by decide) : Name :=
  ⟨ns.map asciiChar, h⟩

/-- SPEC section 7.2's required memory export name. -/
def memoryExportName : Name := asciiName [0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79]

/-- SPEC section 7.2's required function export name. -/
def gemmExportName : Name := asciiName [0x67, 0x65, 0x6D, 0x6D]

theorem memoryExportName_matches : nameMatches "memory" memoryExportName = true := by
  decide

theorem gemmExportName_matches : nameMatches "gemm" gemmExportName = true := by
  decide

/-- The pinned GEMM ABI as a Core 3.0 type-section entry: one recursive group
holding one final `SUB` whose composite type is `FUNC (i32 i32) -> (i32)`. -/
def gemmTypeDef : TypeDef :=
  { rectype := .recr (SubTypes.ofList
      [ .sub (some .final) TypeUses.nil
          (.func (ValTypes.ofList [.num .i32, .num .i32])
                 (ValTypes.ofList [.num .i32])) ]) }

/-- A `u32` index. -/
def idx0 : Idx := ⟨0, by decide⟩

/-- A one-page wasm32 memory. -/
def onePageMem : Mem :=
  { memtype := { addr := .i32, lim := { min := ⟨1, by decide⟩, max := none } } }

/-- **THE ANTI-VACUITY WITNESS.**  The released baseline shape of SPEC section
7.2: no imports, a wasm32 memory zero carrying the ABI, one function of the
pinned ABI type, and the two required exports `memory` and `gemm`. -/
def releaseBaselineModule : Module :=
  { types := [gemmTypeDef]
    imports := []
    tags := []
    globals := []
    mems := [onePageMem]
    tables := []
    funcs := [{ typeidx := idx0, locals := [],
                body := .cons (.localGet idx0) .nil }]
    datas := []
    elems := []
    start := none
    exports := [ { name := memoryExportName, externidx := .mem idx0 }
               , { name := gemmExportName, externidx := .func idx0 } ] }

/-- The baseline shape really is a Core 3.0 module. -/
theorem releaseBaselineModule_wf : releaseBaselineModule.wf = true := by decide

/-- **The released profile admits the released baseline shape.**  Without this
every rejection theorem above would be vacuously true. -/
theorem releaseBaselineModule_admitted (P : Profile) :
    Module.AdmittedBy P releaseBaselineModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-! ### Every enabled family is actually accepted

One module that exercises all seven enabled families of SPEC section 7.2 at
once, and is admitted.  A profile predicate that quietly rejected an enabled
family would fail here. -/

/-- A module using every enabled family: a tag (exception handling), two
memories and a table (bulk memory, multiple memories, tables), a `_IDX` block
(multi-value), a vector splat (fixed-width SIMD), a reference test (reference
types and GC), a tail call, and ordinary scalar instructions. -/
def releaseRichModule : Module :=
  { types := [gemmTypeDef]
    imports := []
    tags := [{ tagtype := .idx idx0 }]
    globals := [{ globaltype := { mutability := none, valtype := .num .i32 }
                  init := .cons (.const .i32 ⟨0, by decide⟩) .nil }]
    mems := [onePageMem, onePageMem]
    tables := [{ tabletype := { addr := .i32
                                lim := { min := ⟨0, by decide⟩, max := none }
                                elem := RefType.funcref }
                 init := .nil }]
    funcs := [{ typeidx := idx0, locals := [],
                body := InstrSeq.ofList
                  [ .localGet idx0
                  , .block (.idx idx0) .nil
                  , .vsplat { lane := .num .i32, dim := .d4 }
                  , .refIsNull
                  , .throwRef
                  , .tableSize idx0
                  , .returnCall idx0 ] }]
    datas := []
    elems := []
    start := none
    exports := [ { name := memoryExportName, externidx := .mem idx0 }
               , { name := gemmExportName, externidx := .func idx0 } ] }

theorem releaseRichModule_wf : releaseRichModule.wf = true := by decide

/-- The rich module uses every one of the seven enabled families. -/
theorem releaseRichModule_uses_every_enabled_family :
    ∀ f ∈ enabledFamilies, f ∈ Module.requiredFeatures releaseRichModule := by
  decide

/-- ... and the released profile admits it. -/
theorem releaseRichModule_admitted (P : Profile) :
    Module.AdmittedBy P releaseRichModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-! ### The rejected families that the pinned syntax can express -/

/-- The baseline shape with a memory64 memory: `memtype = I64 limits PAGE`. -/
def memory64Module : Module :=
  { releaseBaselineModule with
    mems := [{ memtype := { addr := .i64,
                            lim := { min := ⟨1, by decide⟩, max := none } } }] }

theorem memory64Module_wf : memory64Module.wf = true := by decide

theorem memory64Module_uses_memory64 :
    FeatureFamily.memory64 ∈ Module.requiredFeatures memory64Module := by decide

/-- **A module using memory64 is not admitted** --- and not because it failed
some other conjunct: `memory64Module_wf` says it is a Core 3.0 module, and the
verdict follows from the feature matrix alone. -/
theorem memory64Module_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P memory64Module :=
  Module.not_admittedBy_of_rejected P memory64Module
    memory64Module_uses_memory64 (by decide)

/-- A memory64 TABLE: `tabletype = I64 limits reftype`. -/
def memory64TableModule : Module :=
  { releaseBaselineModule with
    tables := [{ tabletype := { addr := .i64
                                lim := { min := ⟨0, by decide⟩, max := none }
                                elem := RefType.funcref }
                 init := .nil }] }

theorem memory64TableModule_wf : memory64TableModule.wf = true := by decide

theorem memory64TableModule_uses_memory64 :
    FeatureFamily.memory64 ∈ Module.requiredFeatures memory64TableModule := by
  decide

theorem memory64TableModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P memory64TableModule :=
  Module.not_admittedBy_of_rejected P memory64TableModule
    memory64TableModule_uses_memory64 (by decide)

/-- The baseline shape whose function body contains `F32X4.RELAXED_MADD`, a
term of the pinned `vternop_(Fnn X M)`. -/
def relaxedSimdModule : Module :=
  { releaseBaselineModule with
    funcs := [{ typeidx := idx0, locals := [],
                body := .cons
                  (.vternop { lane := .num .f32, dim := .d4 }
                    (.float .relaxedMadd)) .nil }] }

/-- It really is a Core 3.0 module: every `-- if` side condition of the pinned
instruction fragments holds of it. -/
theorem relaxedSimdModule_wf : relaxedSimdModule.wf = true := by decide

theorem relaxedSimdModule_uses_relaxedSimd :
    FeatureFamily.relaxedSimd ∈ Module.requiredFeatures relaxedSimdModule := by
  decide

/-- **A module using relaxed SIMD is not admitted.** -/
theorem relaxedSimdModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P relaxedSimdModule :=
  Module.not_admittedBy_of_rejected P relaxedSimdModule
    relaxedSimdModule_uses_relaxedSimd (by decide)

/-- The same, with `F32X4.RELAXED_MIN` of `vbinop_(Fnn X M)`: the rejection is
not an accident of one constructor. -/
def relaxedMinModule : Module :=
  { releaseBaselineModule with
    funcs := [{ typeidx := idx0, locals := [],
                body := .cons
                  (.vbinop { lane := .num .f32, dim := .d4 }
                    (.float .relaxedMin)) .nil }] }

theorem relaxedMinModule_wf : relaxedMinModule.wf = true := by decide

theorem relaxedMinModule_uses_relaxedSimd :
    FeatureFamily.relaxedSimd ∈ Module.requiredFeatures relaxedMinModule := by
  decide

theorem relaxedMinModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P relaxedMinModule :=
  Module.not_admittedBy_of_rejected P relaxedMinModule
    relaxedMinModule_uses_relaxedSimd (by decide)

/-- ... while the STANDARD SIMD instruction at the same shape IS admitted: the
rejection is of the relaxed family, not of vector instructions. -/
def standardSimdModule : Module :=
  { releaseBaselineModule with
    funcs := [{ typeidx := idx0, locals := [],
                body := .cons
                  (.vbinop { lane := .num .f32, dim := .d4 }
                    (.float .min)) .nil }] }

theorem standardSimdModule_admitted (P : Profile) :
    Module.AdmittedBy P standardSimdModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-! ### The other admission conjuncts bite too

A feature-only admission predicate would be a partial one. -/

/-- A module with no `gemm` export is not admitted, however core-valid. -/
def noGemmExportModule : Module :=
  { releaseBaselineModule with
    exports := [{ name := memoryExportName, externidx := .mem idx0 }] }

theorem noGemmExportModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P noGemmExportModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-- A module exporting `gemm` at the wrong ABI type is not admitted. -/
def wrongAbiModule : Module :=
  { releaseBaselineModule with
    types := [{ rectype := .recr (SubTypes.ofList
        [ .sub (some .final) TypeUses.nil
            (.func (ValTypes.ofList [.num .i64, .num .i32])
                   (ValTypes.ofList [.num .i32])) ]) }] }

theorem wrongAbiModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P wrongAbiModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-- A module whose memory exceeds the normative 65,536-page limit is not
admitted. -/
def oversizedMemoryModule : Module :=
  { releaseBaselineModule with
    mems := [{ memtype := { addr := .i32,
                            lim := { min := ⟨65537, by decide⟩, max := none } } }] }

theorem oversizedMemoryModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P oversizedMemoryModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-- A module with an import is not admitted: the release profile is closed. -/
def importingModule : Module :=
  { releaseBaselineModule with
    imports := [{ moduleName := gemmExportName, itemName := gemmExportName,
                  externtype := .mem { addr := .i32,
                                       lim := { min := ⟨1, by decide⟩,
                                                max := none } } }] }

theorem importingModule_not_admitted (P : Profile) :
    ¬ Module.AdmittedBy P importingModule := by
  rw [Module.admittedBy_iff_release]
  decide

end WasmGemmGnaf.Wasm.Core
