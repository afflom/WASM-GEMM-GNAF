/-
  Wasm/Core/Instructions.lean --- the instruction sort of the pinned WebAssembly
  Core 3.0 front end.

  NORMATIVE SOURCE.  Every constructor below transcribes an alternative of

      vendor/wasm-spec/specification/wasm-3.0/1.3-syntax.instructions.spectec

  from `syntax instr` onwards, in source order and grouped by the source's own
  `instr/<fragment>` headings: parametric, block, br, call, exn, local, global,
  table, elem, memory, data, ref, func, i31, struct, array, extern, num, vec.
  SpecTec writes those fragments as successive extensions of ONE sort `instr`
  (`= ... | NEW_CASES | ...`), which is why they are one Lean inductive and why
  `xtask core` lists `instr` once.

  The instruction sort covers the whole Core 3.0 release surface: SIMD, GC and
  references, tables, bulk memory, tail calls and exception handling all appear
  here, because they all appear in the pinned source.

  `expr = instr*` and every `instr*` inside `instr` are the same sort, and are
  represented by the companion cons-list `InstrSeq` for the reason given in
  `Core/Types.lean`: Lean's nested-inductive restriction forbids `List Instr` in
  a position where `DecidableEq` must be derived, and the decoder and validator
  both need that instance.  `InstrSeq.toList` / `ofList` are proved mutually
  inverse below, so nothing is lost.

  `Instr.wf` collects every `-- if` side condition of the instruction fragments
  together with the family-membership conditions of `Core/Operators.lean`: a
  `Instr` value is a Core 3.0 instruction exactly when `Instr.wf` holds of it.
-/
import WasmGemmGnaf.Wasm.Core.Operators

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- `syntax catch = CATCH tagidx labelidx | CATCH_REF tagidx labelidx
    | CATCH_ALL labelidx | CATCH_ALL_REF labelidx`. -/
-- core-syntax: catch
inductive Catch where
  /-- `CATCH tagidx labelidx`. -/
  | tag (x : TagIdx) (l : LabelIdx)
  /-- `CATCH_REF tagidx labelidx`. -/
  | tagRef (x : TagIdx) (l : LabelIdx)
  /-- `CATCH_ALL labelidx`. -/
  | all (l : LabelIdx)
  /-- `CATCH_ALL_REF labelidx`. -/
  | allRef (l : LabelIdx)
  deriving DecidableEq, Repr, Inhabited

mutual

/-- `syntax instr`, all fragments. -/
-- core-syntax: instr
inductive Instr where
  -- instr/parametric
  /-- `NOP`. -/
  | nop
  /-- `UNREACHABLE`. -/
  | unreachable
  /-- `DROP`. -/
  | drop
  /-- `SELECT (valtype*)?`. -/
  | select (ts : Option (List ValType))
  -- instr/block
  /-- `BLOCK blocktype instr*`. -/
  | block (bt : BlockType) (body : InstrSeq)
  /-- `LOOP blocktype instr*`. -/
  | loop (bt : BlockType) (body : InstrSeq)
  /-- `IF blocktype instr* ELSE instr*`. -/
  | ifElse (bt : BlockType) (thn : InstrSeq) (els : InstrSeq)
  -- instr/br
  /-- `BR labelidx`. -/
  | br (l : LabelIdx)
  /-- `BR_IF labelidx`. -/
  | brIf (l : LabelIdx)
  /-- `BR_TABLE labelidx* labelidx`. -/
  | brTable (ls : List LabelIdx) (l : LabelIdx)
  /-- `BR_ON_NULL labelidx`. -/
  | brOnNull (l : LabelIdx)
  /-- `BR_ON_NON_NULL labelidx`. -/
  | brOnNonNull (l : LabelIdx)
  /-- `BR_ON_CAST labelidx reftype reftype`. -/
  | brOnCast (l : LabelIdx) (rt₁ : RefType) (rt₂ : RefType)
  /-- `BR_ON_CAST_FAIL labelidx reftype reftype`. -/
  | brOnCastFail (l : LabelIdx) (rt₁ : RefType) (rt₂ : RefType)
  -- instr/call
  /-- `CALL funcidx`. -/
  | call (x : FuncIdx)
  /-- `CALL_REF typeuse`. -/
  | callRef (tu : TypeUse)
  /-- `CALL_INDIRECT tableidx typeuse`. -/
  | callIndirect (x : TableIdx) (tu : TypeUse)
  /-- `RETURN`. -/
  | ret
  /-- `RETURN_CALL funcidx`. -/
  | returnCall (x : FuncIdx)
  /-- `RETURN_CALL_REF typeuse`. -/
  | returnCallRef (tu : TypeUse)
  /-- `RETURN_CALL_INDIRECT tableidx typeuse`. -/
  | returnCallIndirect (x : TableIdx) (tu : TypeUse)
  -- instr/exn
  /-- `THROW tagidx`. -/
  | throw (x : TagIdx)
  /-- `THROW_REF`. -/
  | throwRef
  /-- `TRY_TABLE blocktype list(catch) instr*`. -/
  | tryTable (bt : BlockType) (cs : List_ Catch) (body : InstrSeq)
  -- instr/local
  /-- `LOCAL.GET localidx`. -/
  | localGet (x : LocalIdx)
  /-- `LOCAL.SET localidx`. -/
  | localSet (x : LocalIdx)
  /-- `LOCAL.TEE localidx`. -/
  | localTee (x : LocalIdx)
  -- instr/global
  /-- `GLOBAL.GET globalidx`. -/
  | globalGet (x : GlobalIdx)
  /-- `GLOBAL.SET globalidx`. -/
  | globalSet (x : GlobalIdx)
  -- instr/table
  /-- `TABLE.GET tableidx`. -/
  | tableGet (x : TableIdx)
  /-- `TABLE.SET tableidx`. -/
  | tableSet (x : TableIdx)
  /-- `TABLE.SIZE tableidx`. -/
  | tableSize (x : TableIdx)
  /-- `TABLE.GROW tableidx`. -/
  | tableGrow (x : TableIdx)
  /-- `TABLE.FILL tableidx`. -/
  | tableFill (x : TableIdx)
  /-- `TABLE.COPY tableidx tableidx`. -/
  | tableCopy (x : TableIdx) (y : TableIdx)
  /-- `TABLE.INIT tableidx elemidx`. -/
  | tableInit (x : TableIdx) (y : ElemIdx)
  -- instr/elem
  /-- `ELEM.DROP elemidx`. -/
  | elemDrop (x : ElemIdx)
  -- instr/memory
  /-- `LOAD numtype loadop_(numtype)? memidx memarg`. -/
  | load (nt : NumType) (op : Option LoadOp) (x : MemIdx) (ao : MemArg)
  /-- `STORE numtype storeop_(numtype)? memidx memarg`. -/
  | store (nt : NumType) (op : Option StoreOp) (x : MemIdx) (ao : MemArg)
  /-- `VLOAD vectype vloadop_(vectype)? memidx memarg`. -/
  | vload (vt : VecType) (op : Option VLoadOp) (x : MemIdx) (ao : MemArg)
  /-- `VLOAD_LANE vectype sz memidx memarg laneidx`. -/
  | vloadLane (vt : VecType) (sz : Sz) (x : MemIdx) (ao : MemArg) (i : LaneIdx)
  /-- `VSTORE vectype memidx memarg`. -/
  | vstore (vt : VecType) (x : MemIdx) (ao : MemArg)
  /-- `VSTORE_LANE vectype sz memidx memarg laneidx`. -/
  | vstoreLane (vt : VecType) (sz : Sz) (x : MemIdx) (ao : MemArg) (i : LaneIdx)
  /-- `MEMORY.SIZE memidx`. -/
  | memorySize (x : MemIdx)
  /-- `MEMORY.GROW memidx`. -/
  | memoryGrow (x : MemIdx)
  /-- `MEMORY.FILL memidx`. -/
  | memoryFill (x : MemIdx)
  /-- `MEMORY.COPY memidx memidx`. -/
  | memoryCopy (x : MemIdx) (y : MemIdx)
  /-- `MEMORY.INIT memidx dataidx`. -/
  | memoryInit (x : MemIdx) (y : DataIdx)
  -- instr/data
  /-- `DATA.DROP dataidx`. -/
  | dataDrop (x : DataIdx)
  -- instr/ref
  /-- `REF.NULL heaptype`. -/
  | refNull (ht : HeapType)
  /-- `REF.IS_NULL`. -/
  | refIsNull
  /-- `REF.AS_NON_NULL`. -/
  | refAsNonNull
  /-- `REF.EQ`. -/
  | refEq
  /-- `REF.TEST reftype`. -/
  | refTest (rt : RefType)
  /-- `REF.CAST reftype`. -/
  | refCast (rt : RefType)
  -- instr/func
  /-- `REF.FUNC funcidx`. -/
  | refFunc (x : FuncIdx)
  -- instr/i31
  /-- `REF.I31`. -/
  | refI31
  /-- `I31.GET sx`. -/
  | i31Get (sx : Sx)
  -- instr/struct
  /-- `STRUCT.NEW typeidx`. -/
  | structNew (x : TypeIdx)
  /-- `STRUCT.NEW_DEFAULT typeidx`. -/
  | structNewDefault (x : TypeIdx)
  /-- `STRUCT.GET sx? typeidx u32`. -/
  | structGet (sx : Option Sx) (x : TypeIdx) (i : U32)
  /-- `STRUCT.SET typeidx u32`. -/
  | structSet (x : TypeIdx) (i : U32)
  -- instr/array
  /-- `ARRAY.NEW typeidx`. -/
  | arrayNew (x : TypeIdx)
  /-- `ARRAY.NEW_DEFAULT typeidx`. -/
  | arrayNewDefault (x : TypeIdx)
  /-- `ARRAY.NEW_FIXED typeidx u32`. -/
  | arrayNewFixed (x : TypeIdx) (n : U32)
  /-- `ARRAY.NEW_DATA typeidx dataidx`. -/
  | arrayNewData (x : TypeIdx) (y : DataIdx)
  /-- `ARRAY.NEW_ELEM typeidx elemidx`. -/
  | arrayNewElem (x : TypeIdx) (y : ElemIdx)
  /-- `ARRAY.GET sx? typeidx`. -/
  | arrayGet (sx : Option Sx) (x : TypeIdx)
  /-- `ARRAY.SET typeidx`. -/
  | arraySet (x : TypeIdx)
  /-- `ARRAY.LEN`. -/
  | arrayLen
  /-- `ARRAY.FILL typeidx`. -/
  | arrayFill (x : TypeIdx)
  /-- `ARRAY.COPY typeidx typeidx`. -/
  | arrayCopy (x : TypeIdx) (y : TypeIdx)
  /-- `ARRAY.INIT_DATA typeidx dataidx`. -/
  | arrayInitData (x : TypeIdx) (y : DataIdx)
  /-- `ARRAY.INIT_ELEM typeidx elemidx`. -/
  | arrayInitElem (x : TypeIdx) (y : ElemIdx)
  -- instr/extern
  /-- `EXTERN.CONVERT_ANY`. -/
  | externConvertAny
  /-- `ANY.CONVERT_EXTERN`. -/
  | anyConvertExtern
  -- instr/num
  /-- `CONST numtype num_(numtype)`. -/
  | const (nt : NumType) (c : Num_ nt)
  /-- `UNOP numtype unop_(numtype)`. -/
  | unop (nt : NumType) (op : Unop)
  /-- `BINOP numtype binop_(numtype)`. -/
  | binop (nt : NumType) (op : Binop)
  /-- `TESTOP numtype testop_(numtype)`. -/
  | testop (nt : NumType) (op : Testop)
  /-- `RELOP numtype relop_(numtype)`. -/
  | relop (nt : NumType) (op : Relop)
  /-- `CVTOP numtype_1 numtype_2 cvtop__(numtype_2, numtype_1)`: `nt₁` is the
  result type and `nt₂` the operand type, and `op` is indexed by
  `(nt₂, nt₁)`. -/
  | cvtop (nt₁ : NumType) (nt₂ : NumType) (op : Cvtop)
  -- instr/vec
  /-- `VCONST vectype vec_(vectype)`. -/
  | vconst (vt : VecType) (c : VecLit vt.toVnn)
  /-- `VVUNOP vectype vvunop`. -/
  | vvunop (vt : VecType) (op : VVUnop)
  /-- `VVBINOP vectype vvbinop`. -/
  | vvbinop (vt : VecType) (op : VVBinop)
  /-- `VVTERNOP vectype vvternop`. -/
  | vvternop (vt : VecType) (op : VVTernop)
  /-- `VVTESTOP vectype vvtestop`. -/
  | vvtestop (vt : VecType) (op : VVTestop)
  /-- `VUNOP shape vunop_(shape)`. -/
  | vunop (sh : Shape) (op : VUnop)
  /-- `VBINOP shape vbinop_(shape)`. -/
  | vbinop (sh : Shape) (op : VBinop)
  /-- `VTERNOP shape vternop_(shape)`. -/
  | vternop (sh : Shape) (op : VTernop)
  /-- `VTESTOP shape vtestop_(shape)`. -/
  | vtestop (sh : Shape) (op : VTestop)
  /-- `VRELOP shape vrelop_(shape)`. -/
  | vrelop (sh : Shape) (op : VRelop)
  /-- `VSHIFTOP ishape vshiftop_(ishape)`. -/
  | vshiftop (sh : IShape) (op : VShiftop)
  /-- `VBITMASK ishape`. -/
  | vbitmask (sh : IShape)
  /-- `VSWIZZLOP bshape vswizzlop_(bshape)`. -/
  | vswizzlop (sh : BShape) (op : VSwizzlop)
  /-- `VSHUFFLE bshape laneidx*  -- if |laneidx*| = $dim(bshape)`. -/
  | vshuffle (sh : BShape) (is : List LaneIdx)
  /-- `VEXTUNOP ishape_1 ishape_2 vextunop__(ishape_2, ishape_1)`. -/
  | vextunop (sh₁ : IShape) (sh₂ : IShape) (op : VExtUnop)
  /-- `VEXTBINOP ishape_1 ishape_2 vextbinop__(ishape_2, ishape_1)`. -/
  | vextbinop (sh₁ : IShape) (sh₂ : IShape) (op : VExtBinop)
  /-- `VEXTTERNOP ishape_1 ishape_2 vextternop__(ishape_2, ishape_1)`. -/
  | vextternop (sh₁ : IShape) (sh₂ : IShape) (op : VExtTernop)
  /-- `VNARROW ishape_1 ishape_2 sx`. -/
  | vnarrow (sh₁ : IShape) (sh₂ : IShape) (sx : Sx)
  /-- `VCVTOP shape_1 shape_2 vcvtop__(shape_2, shape_1)`: `sh₁` is the result
  shape and `sh₂` the operand shape. -/
  | vcvtop (sh₁ : Shape) (sh₂ : Shape) (op : VCvtop)
  /-- `VSPLAT shape`. -/
  | vsplat (sh : Shape)
  /-- `VEXTRACT_LANE shape sx? laneidx`. -/
  | vextractLane (sh : Shape) (sx : Option Sx) (i : LaneIdx)
  /-- `VREPLACE_LANE shape laneidx`. -/
  | vreplaceLane (sh : Shape) (i : LaneIdx)

/-- `instr*`, as a companion cons-list; see the header. -/
inductive InstrSeq where
  | nil
  | cons (i : Instr) (rest : InstrSeq)

end

deriving instance DecidableEq for Instr, InstrSeq
deriving instance Repr for Instr, InstrSeq

instance : Inhabited Instr := ⟨.nop⟩
instance : Inhabited InstrSeq := ⟨.nil⟩

/-- `syntax expr = instr*`. -/
-- core-syntax: expr
abbrev Expr : Type := InstrSeq

namespace InstrSeq

/-- The instruction sequence as an ordinary list. -/
def toList : InstrSeq → List Instr
  | .nil => []
  | .cons i rest => i :: toList rest

/-- The instruction sequence of an ordinary list. -/
def ofList : List Instr → InstrSeq
  | [] => .nil
  | i :: is => .cons i (ofList is)

/-- The number of top-level instructions. -/
def length : InstrSeq → Nat
  | .nil => 0
  | .cons _ rest => length rest + 1

@[simp] theorem toList_ofList (l : List Instr) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons i is ih => simp [toList, ofList, ih]

@[simp] theorem ofList_toList : ∀ s : InstrSeq, ofList (toList s) = s
  | .nil => rfl
  | .cons i rest => by
      show InstrSeq.cons i (ofList (toList rest)) = InstrSeq.cons i rest
      rw [ofList_toList rest]

@[simp] theorem length_toList : ∀ s : InstrSeq, (toList s).length = length s
  | .nil => rfl
  | .cons _ rest => by
      show (toList rest).length + 1 = length rest + 1
      rw [length_toList rest]

theorem ofList_injective : Function.Injective ofList := by
  intro a b h
  have := congrArg toList h
  simpa using this

theorem toList_injective : Function.Injective toList := by
  intro a b h
  have := congrArg ofList h
  simpa using this

end InstrSeq

/-! ## Well-formedness

Every `-- if` side condition the instruction fragments carry, together with the
family-membership conditions of `Core/Operators.lean` and the `shape` condition
`$lsize(lanetype) * dim = 128`.  An `Instr` is a Core 3.0 instruction exactly
when `Instr.wf` holds of it. -/

mutual

/-- Every side condition of this instruction and of the instructions inside
it. -/
def Instr.wf : Instr → Bool
  | .nop => true
  | .unreachable => true
  | .drop => true
  | .select _ => true
  | .block _ body => InstrSeq.wf body
  | .loop _ body => InstrSeq.wf body
  | .ifElse _ thn els => InstrSeq.wf thn && InstrSeq.wf els
  | .br _ => true
  | .brIf _ => true
  | .brTable _ _ => true
  | .brOnNull _ => true
  | .brOnNonNull _ => true
  | .brOnCast _ _ _ => true
  | .brOnCastFail _ _ _ => true
  | .call _ => true
  | .callRef _ => true
  | .callIndirect _ _ => true
  | .ret => true
  | .returnCall _ => true
  | .returnCallRef _ => true
  | .returnCallIndirect _ _ => true
  | .throw _ => true
  | .throwRef => true
  | .tryTable _ _ body => InstrSeq.wf body
  | .localGet _ => true
  | .localSet _ => true
  | .localTee _ => true
  | .globalGet _ => true
  | .globalSet _ => true
  | .tableGet _ => true
  | .tableSet _ => true
  | .tableSize _ => true
  | .tableGrow _ => true
  | .tableFill _ => true
  | .tableCopy _ _ => true
  | .tableInit _ _ => true
  | .elemDrop _ => true
  | .load nt op _ _ =>
      match op with
      | none => true
      | some o => LoadOp.wf nt o
  | .store nt op _ _ =>
      match op with
      | none => true
      | some o => StoreOp.wf nt o
  | .vload vt op _ _ =>
      match op with
      | none => true
      | some o => VLoadOp.wf vt o
  | .vloadLane _ _ _ _ _ => true
  | .vstore _ _ _ => true
  | .vstoreLane _ _ _ _ _ => true
  | .memorySize _ => true
  | .memoryGrow _ => true
  | .memoryFill _ => true
  | .memoryCopy _ _ => true
  | .memoryInit _ _ => true
  | .dataDrop _ => true
  | .refNull _ => true
  | .refIsNull => true
  | .refAsNonNull => true
  | .refEq => true
  | .refTest _ => true
  | .refCast _ => true
  | .refFunc _ => true
  | .refI31 => true
  | .i31Get _ => true
  | .structNew _ => true
  | .structNewDefault _ => true
  | .structGet _ _ _ => true
  | .structSet _ _ => true
  | .arrayNew _ => true
  | .arrayNewDefault _ => true
  | .arrayNewFixed _ _ => true
  | .arrayNewData _ _ => true
  | .arrayNewElem _ _ => true
  | .arrayGet _ _ => true
  | .arraySet _ => true
  | .arrayLen => true
  | .arrayFill _ => true
  | .arrayCopy _ _ => true
  | .arrayInitData _ _ => true
  | .arrayInitElem _ _ => true
  | .externConvertAny => true
  | .anyConvertExtern => true
  | .const nt c => Num_.wf nt c
  | .unop nt op => Unop.wf nt op
  | .binop nt op => Binop.wf nt op
  | .testop nt op => Testop.wf nt op
  | .relop nt op => Relop.wf nt op
  | .cvtop nt₁ nt₂ op => Cvtop.wf nt₂ nt₁ op
  | .vconst _ _ => true
  | .vvunop _ _ => true
  | .vvbinop _ _ => true
  | .vvternop _ _ => true
  | .vvtestop _ _ => true
  | .vunop sh op => sh.wf && VUnop.wf sh op
  | .vbinop sh op => sh.wf && VBinop.wf sh op
  | .vternop sh op => sh.wf && VTernop.wf sh op
  | .vtestop sh op => sh.wf && VTestop.wf sh op
  | .vrelop sh op => sh.wf && VRelop.wf sh op
  | .vshiftop sh _ => sh.val.wf
  | .vbitmask sh => sh.val.wf
  | .vswizzlop sh _ => sh.val.wf
  | .vshuffle sh is => sh.val.wf && decide (is.length = sh.val.dim.toNat)
  | .vextunop sh₁ sh₂ op =>
      sh₁.val.wf && sh₂.val.wf && VExtUnop.wf sh₂ sh₁ op
  | .vextbinop sh₁ sh₂ op =>
      sh₁.val.wf && sh₂.val.wf && VExtBinop.wf sh₂ sh₁ op
  | .vextternop sh₁ sh₂ op =>
      sh₁.val.wf && sh₂.val.wf && VExtTernop.wf sh₂ sh₁ op
  | .vnarrow sh₁ sh₂ _ =>
      sh₁.val.wf && sh₂.val.wf &&
      decide (sh₂.laneSize = 2 * sh₁.laneSize) &&
      decide (2 * sh₁.laneSize ≤ 32)
  | .vcvtop sh₁ sh₂ op => sh₁.wf && sh₂.wf && VCvtop.wf sh₂ sh₁ op
  | .vsplat sh => sh.wf
  | .vextractLane sh sx _ =>
      sh.wf &&
      (sx.isNone == (match sh.lane with | .num _ => true | .pack _ => false))
  | .vreplaceLane sh _ => sh.wf

/-- Every side condition of every instruction in the sequence. -/
def InstrSeq.wf : InstrSeq → Bool
  | .nil => true
  | .cons i rest => Instr.wf i && InstrSeq.wf rest

end

/-! ## Sanity checks

`wf` is only worth transcribing if it actually discriminates.  These are
kernel-checked evaluations, not tests: each one names a side condition of the
pinned source and pins down which way it falls. -/

/-- `unop_(Inn)`'s `EXTEND sz -- if sz < $sizenn(Inn)` admits `I32.EXTEND8_S`. -/
example : Instr.wf (.unop .i32 (.int (.extend .s8))) = true := by decide

/-- ... and rejects an `EXTEND` at or above the operand width. -/
example : Instr.wf (.unop .i32 (.int (.extend .s32))) = false := by decide

/-- `unop_(Inn)` has no instance at a float type. -/
example : Instr.wf (.unop .f32 (.int .clz)) = false := by decide

/-- `shape`'s `$lsize(lanetype) * dim = 128` admits `I8 X 16`. -/
example : Shape.wf { lane := .pack .i8, dim := .d16 } = true := by decide

/-- ... and rejects `I8 X 8`. -/
example : Shape.wf { lane := .pack .i8, dim := .d8 } = false := by decide

/-- `vunop_(Jnn X M)`'s `POPCNT -- if $lsizenn(Jnn) = 8` admits `I8X16.POPCNT`. -/
example : Instr.wf (.vunop { lane := .pack .i8, dim := .d16 } (.int .popcnt))
    = true := by decide

/-- ... and rejects `I32X4.POPCNT`. -/
example : Instr.wf (.vunop { lane := .num .i32, dim := .d4 } (.int .popcnt))
    = false := by decide

/-- `cvtop__(Inn_1, Inn_2)`'s `WRAP -- if size_1 > size_2` admits
`I32.WRAP_I64` (result `I32`, operand `I64`). -/
example : Instr.wf (.cvtop .i32 .i64 (.ii .wrap)) = true := by decide

/-- ... and rejects a `WRAP` in the widening direction. -/
example : Instr.wf (.cvtop .i64 .i32 (.ii .wrap)) = false := by decide

/-- `loadop_(Inn)`'s `-- if sz < $sizenn(Inn)` admits `I32.LOAD8_S`. -/
example :
    Instr.wf (.load .i32 (some { sz := .s8, sx := .s }) default default)
      = true := by decide

/-- ... and rejects a load of 32 bits into `I32` as a `loadop_`; that form is
written with no `loadop_` at all. -/
example :
    Instr.wf (.load .i32 (some { sz := .s32, sx := .s }) default default)
      = false := by decide

/-- The `/syn` fragment of `valtype` excludes `BOT`. -/
example : ValType.isSyn .bot = false := by decide

/-- The `/syn` fragment of `typeuse` is `_IDX` only, so a semantic `REC n` is
not syntactic. -/
example : TypeUse.isSyn (.recu 0) = false := by decide

/-- ... while a type index is. -/
example : TypeUse.isSyn (.idx default) = true := by decide

/-- `def $const(consttype, lit_(consttype)) : instr`, the numeric case. -/
def constNum (nt : NumType) (c : Num_ nt) : Instr := .const nt c

/-- `def $const(consttype, lit_(consttype)) : instr`, the vector case. -/
def constVec (vt : VecType) (c : VecLit vt.toVnn) : Instr := .vconst vt c

end WasmGemmGnaf.Wasm.Core
