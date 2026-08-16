/-
  Wasm/Core/BinaryGrammar/Instructions.lean --- the DECLARATIVE binary grammar
  of the non-vector instruction fragments, for the pinned WebAssembly Core 3.0
  front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/5.3-binary.instructions.spectec

  at the pinned commit, in source order, with one Lean relation per
  `grammar Binstr/<fragment>` heading and one constructor per alternative.
  The vector fragments are `BinaryGrammar/Vector.lean`; the four alternatives
  that recur into `Binstr` itself (`BLOCK`, `LOOP`, `IF`, `TRY_TABLE`) are
  `BinaryGrammar/Expressions.lean`, which also assembles the fragments into the
  single grammar `Binstr` that the source's `Binstr/<fragment> = ...` notation
  means.

  Nothing here imports or mentions a decoder.

  THE OPCODE BYTES ARE THE SOURCE'S.  A prefixed opcode `0xFB k` / `0xFC k` is
  `Bprefixed`: the prefix byte followed by a *`Bu32`* encoding of `k`, not by the
  single byte `k`.  That matters, because `Bu32` admits non-minimal encodings, so
  `0xFC 0x8C 0x80 0x80 0x80 0x00` is as much a `TABLE.INIT` prefix as
  `0xFC 0x0C` is.  An opcode table keyed on single bytes would miss that, and
  missing it is one of the ways a decoder can be incomplete.

  IMMEDIATE ORDER.  Several instructions take their immediates in a different
  order from their abstract-syntax arguments -- `0xFC 12:Bu32 y:Belemidx
  x:Btableidx => TABLE.INIT x y` reads the ELEMENT index first and the TABLE
  index second.  The byte-side concatenations below follow the source, not the
  argument order of `Instr`.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Types

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

/-! ## Operand grammars

`blocktype`, `catch`, `memidxop`, `castop` and `laneidx`, which the instruction
fragments share. -/

/-- `grammar Bblocktype : blocktype`.

The `_IDX` alternative repeats the selected `Bs33For` caveat recorded on `BsN`: the value has
to land in `typeidx`, which is what demanding a `TypeIdx` witness says. -/
inductive Bblocktype : Bytes → BlockType → Prop where
  -- core-opcode: 0x40 _RESULT
  | empty : Bblocktype [tb 0x40] (.result none)
  | val (bs : Bytes) (t : ValType) : Bvaltype bs t → Bblocktype bs (.result (some t))
  | idx (bs : Bytes) (i : Int) (x : TypeIdx) :
      Bs33For bs i → 0 ≤ i → (x.val : Int) = i → Bblocktype bs (.idx x)

/-- `grammar Bcatch : catch`. -/
inductive Bcatch : Bytes → Catch → Prop where
  -- core-opcode: 0x00 CATCH
  | tag (bx bl : Bytes) (x : TagIdx) (l : LabelIdx) :
      Btagidx bx x → Blabelidx bl l → Bcatch (tb 0x00 :: (bx ++ bl)) (.tag x l)
  -- core-opcode: 0x01 CATCH_REF
  | tagRef (bx bl : Bytes) (x : TagIdx) (l : LabelIdx) :
      Btagidx bx x → Blabelidx bl l → Bcatch (tb 0x01 :: (bx ++ bl)) (.tagRef x l)
  -- core-opcode: 0x02 CATCH_ALL
  | all (bl : Bytes) (l : LabelIdx) :
      Blabelidx bl l → Bcatch (tb 0x02 :: bl) (.all l)
  -- core-opcode: 0x03 CATCH_ALL_REF
  | allRef (bl : Bytes) (l : LabelIdx) :
      Blabelidx bl l → Bcatch (tb 0x03 :: bl) (.allRef l)

/-- `syntax memidxop = (memidx, memarg)`. -/
abbrev MemIdxOp : Type := MemIdx × MemArg

/-- `grammar Bmemarg : memidxop`.

The alignment field doubles as the discriminator: `n < 2^6` is the one-memory
form and the memory index is `0`; `2^6 <= n < 2^7` carries an explicit memory
index and the alignment is `n - 2^6`. -/
inductive Bmemarg : Bytes → MemIdxOp → Prop where
  /-- `| n:Bu32 m:Bu32 => (0, {ALIGN n, OFFSET m})  -- if $(n < 2^6)`. -/
  | mem0 (bn bm : Bytes) (n m : U32) (x : MemIdx) :
      Bu32 bn n → Bu32 bm m → n.val < 2 ^ 6 → x.val = 0 →
      Bmemarg (bn ++ bm) (x, { align := n, offset := m })
  /-- `| n:Bu32 x:Bmemidx m:Bu32 => (x, {ALIGN $((n - 2^6)), OFFSET m})
      -- if $(2^6 <= n < 2^7)`. -/
  | memx (bn bx bm : Bytes) (n a m : U32) (x : MemIdx) :
      Bu32 bn n → Bmemidx bx x → Bu32 bm m →
      2 ^ 6 ≤ n.val → n.val < 2 ^ 7 → a.val = n.val - 2 ^ 6 →
      Bmemarg (bn ++ bx ++ bm) (x, { align := a, offset := m })

/-- `syntax castop = (null?, null?)`. -/
abbrev CastOp : Type := Option Null × Option Null

/-- `grammar Bcastop : castop`. -/
inductive Bcastop : Bytes → CastOp → Prop where
  -- core-opcode: 0x00 (eps,
  | nn : Bcastop [tb 0x00] (none, none)
  -- core-opcode: 0x01 (NULL,
  | yn : Bcastop [tb 0x01] (some .null, none)
  -- core-opcode: 0x02 (eps,
  | ny : Bcastop [tb 0x02] (none, some .null)
  -- core-opcode: 0x03 (NULL,
  | yy : Bcastop [tb 0x03] (some .null, some .null)

/-- `grammar Blaneidx : laneidx = | l:Bbyte => l`. -/
inductive Blaneidx : Bytes → LaneIdx → Prop where
  | mk (b : Byte) (l : LaneIdx) : l.val = b.val → Blaneidx [b] l

/-! ## `grammar Binstr/parametric` -/

/-- `grammar Binstr/parametric : instr`. -/
inductive BinstrParametric : Bytes → Instr → Prop where
  -- core-opcode: 0x00 UNREACHABLE
  | unreachable : BinstrParametric [tb 0x00] .unreachable
  -- core-opcode: 0x01 NOP
  | nop : BinstrParametric [tb 0x01] .nop
  -- core-opcode: 0x1A DROP
  | drop : BinstrParametric [tb 0x1A] .drop
  -- core-opcode: 0x1B SELECT
  | select : BinstrParametric [tb 0x1B] (.select none)
  -- core-opcode: 0x1C SELECT
  | selectT (bs : Bytes) (ts : List ValType) :
      Blist Bvaltype bs ts → BinstrParametric (tb 0x1C :: bs) (.select (some ts))

/-! ## `grammar Binstr/control`

The `0x1F TRY_TABLE` alternative recurs into `Binstr` and is therefore in
`BinaryGrammar/Expressions.lean`; every other alternative of the fragment is
here. -/

/-- `grammar Binstr/control : instr`, the non-recursive alternatives. -/
inductive BinstrControl : Bytes → Instr → Prop where
  -- core-opcode: 0x08 THROW
  | throw (bs : Bytes) (x : TagIdx) :
      Btagidx bs x → BinstrControl (tb 0x08 :: bs) (.throw x)
  -- core-opcode: 0x0A THROW_REF
  | throwRef : BinstrControl [tb 0x0A] .throwRef
  -- core-opcode: 0x0C BR
  | br (bs : Bytes) (l : LabelIdx) :
      Blabelidx bs l → BinstrControl (tb 0x0C :: bs) (.br l)
  -- core-opcode: 0x0D BR_IF
  | brIf (bs : Bytes) (l : LabelIdx) :
      Blabelidx bs l → BinstrControl (tb 0x0D :: bs) (.brIf l)
  -- core-opcode: 0x0E BR_TABLE
  | brTable (bl bn : Bytes) (ls : List LabelIdx) (l : LabelIdx) :
      Blist Blabelidx bl ls → Blabelidx bn l →
      BinstrControl (tb 0x0E :: (bl ++ bn)) (.brTable ls l)
  -- core-opcode: 0x0F RETURN
  | ret : BinstrControl [tb 0x0F] .ret
  -- core-opcode: 0x10 CALL
  | call (bs : Bytes) (x : FuncIdx) :
      Bfuncidx bs x → BinstrControl (tb 0x10 :: bs) (.call x)
  -- core-opcode: 0x11 CALL_INDIRECT
  | callIndirect (by' bx : Bytes) (y : TypeIdx) (x : TableIdx) :
      Btypeidx by' y → Btableidx bx x →
      BinstrControl (tb 0x11 :: (by' ++ bx)) (.callIndirect x (.idx y))
  -- core-opcode: 0x12 RETURN_CALL
  | returnCall (bs : Bytes) (x : FuncIdx) :
      Bfuncidx bs x → BinstrControl (tb 0x12 :: bs) (.returnCall x)
  -- core-opcode: 0x13 RETURN_CALL_INDIRECT
  | returnCallIndirect (by' bx : Bytes) (y : TypeIdx) (x : TableIdx) :
      Btypeidx by' y → Btableidx bx x →
      BinstrControl (tb 0x13 :: (by' ++ bx)) (.returnCallIndirect x (.idx y))

/-! ## `grammar Binstr/local` and `grammar Binstr/global` -/

/-- `grammar Binstr/local : instr`. -/
inductive BinstrLocal : Bytes → Instr → Prop where
  -- core-opcode: 0x20 LOCAL.GET
  | get (bs : Bytes) (x : LocalIdx) :
      Blocalidx bs x → BinstrLocal (tb 0x20 :: bs) (.localGet x)
  -- core-opcode: 0x21 LOCAL.SET
  | set (bs : Bytes) (x : LocalIdx) :
      Blocalidx bs x → BinstrLocal (tb 0x21 :: bs) (.localSet x)
  -- core-opcode: 0x22 LOCAL.TEE
  | tee (bs : Bytes) (x : LocalIdx) :
      Blocalidx bs x → BinstrLocal (tb 0x22 :: bs) (.localTee x)

/-- `grammar Binstr/global : instr`. -/
inductive BinstrGlobal : Bytes → Instr → Prop where
  -- core-opcode: 0x23 GLOBAL.GET
  | get (bs : Bytes) (x : GlobalIdx) :
      Bglobalidx bs x → BinstrGlobal (tb 0x23 :: bs) (.globalGet x)
  -- core-opcode: 0x24 GLOBAL.SET
  | set (bs : Bytes) (x : GlobalIdx) :
      Bglobalidx bs x → BinstrGlobal (tb 0x24 :: bs) (.globalSet x)

/-! ## `grammar Binstr/table` -/

/-- `grammar Binstr/table : instr`. -/
inductive BinstrTable : Bytes → Instr → Prop where
  -- core-opcode: 0x25 TABLE.GET
  | get (bs : Bytes) (x : TableIdx) :
      Btableidx bs x → BinstrTable (tb 0x25 :: bs) (.tableGet x)
  -- core-opcode: 0x26 TABLE.SET
  | set (bs : Bytes) (x : TableIdx) :
      Btableidx bs x → BinstrTable (tb 0x26 :: bs) (.tableSet x)
  -- core-opcode: 0xFC 12 TABLE.INIT
  | init (bo by' bx : Bytes) (y : ElemIdx) (x : TableIdx) :
      Bprefixed 0xFC 12 bo → Belemidx by' y → Btableidx bx x →
      BinstrTable (bo ++ by' ++ bx) (.tableInit x y)
  -- core-opcode: 0xFC 13 ELEM.DROP
  | elemDrop (bo bx : Bytes) (x : ElemIdx) :
      Bprefixed 0xFC 13 bo → Belemidx bx x → BinstrTable (bo ++ bx) (.elemDrop x)
  -- core-opcode: 0xFC 14 TABLE.COPY
  | copy (bo b₁ b₂ : Bytes) (x₁ x₂ : TableIdx) :
      Bprefixed 0xFC 14 bo → Btableidx b₁ x₁ → Btableidx b₂ x₂ →
      BinstrTable (bo ++ b₁ ++ b₂) (.tableCopy x₁ x₂)
  -- core-opcode: 0xFC 15 TABLE.GROW
  | grow (bo bx : Bytes) (x : TableIdx) :
      Bprefixed 0xFC 15 bo → Btableidx bx x → BinstrTable (bo ++ bx) (.tableGrow x)
  -- core-opcode: 0xFC 16 TABLE.SIZE
  | size (bo bx : Bytes) (x : TableIdx) :
      Bprefixed 0xFC 16 bo → Btableidx bx x → BinstrTable (bo ++ bx) (.tableSize x)
  -- core-opcode: 0xFC 17 TABLE.FILL
  | fill (bo bx : Bytes) (x : TableIdx) :
      Bprefixed 0xFC 17 bo → Btableidx bx x → BinstrTable (bo ++ bx) (.tableFill x)

/-! ## `grammar Binstr/memory` -/

/-- `grammar Binstr/memory : instr`. -/
inductive BinstrMemory : Bytes → Instr → Prop where
  -- core-opcode: 0x28 LOAD
  | i32Load (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x28 :: bm) (.load .i32 none x ao)
  -- core-opcode: 0x29 LOAD
  | i64Load (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x29 :: bm) (.load .i64 none x ao)
  -- core-opcode: 0x2A LOAD
  | f32Load (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x2A :: bm) (.load .f32 none x ao)
  -- core-opcode: 0x2B LOAD
  | f64Load (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x2B :: bm) (.load .f64 none x ao)
  -- core-opcode: 0x2C LOAD
  | i32Load8S (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x2C :: bm) (.load .i32 (some { sz := .s8, sx := .s }) x ao)
  -- core-opcode: 0x2D LOAD
  | i32Load8U (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x2D :: bm) (.load .i32 (some { sz := .s8, sx := .u }) x ao)
  -- core-opcode: 0x2E LOAD
  | i32Load16S (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x2E :: bm) (.load .i32 (some { sz := .s16, sx := .s }) x ao)
  -- core-opcode: 0x2F LOAD
  | i32Load16U (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x2F :: bm) (.load .i32 (some { sz := .s16, sx := .u }) x ao)
  -- core-opcode: 0x30 LOAD
  | i64Load8S (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x30 :: bm) (.load .i64 (some { sz := .s8, sx := .s }) x ao)
  -- core-opcode: 0x31 LOAD
  | i64Load8U (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x31 :: bm) (.load .i64 (some { sz := .s8, sx := .u }) x ao)
  -- core-opcode: 0x32 LOAD
  | i64Load16S (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x32 :: bm) (.load .i64 (some { sz := .s16, sx := .s }) x ao)
  -- core-opcode: 0x33 LOAD
  | i64Load16U (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x33 :: bm) (.load .i64 (some { sz := .s16, sx := .u }) x ao)
  -- core-opcode: 0x34 LOAD
  | i64Load32S (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x34 :: bm) (.load .i64 (some { sz := .s32, sx := .s }) x ao)
  -- core-opcode: 0x35 LOAD
  | i64Load32U (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x35 :: bm) (.load .i64 (some { sz := .s32, sx := .u }) x ao)
  -- core-opcode: 0x36 STORE
  | i32Store (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x36 :: bm) (.store .i32 none x ao)
  -- core-opcode: 0x37 STORE
  | i64Store (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x37 :: bm) (.store .i64 none x ao)
  -- core-opcode: 0x38 STORE
  | f32Store (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x38 :: bm) (.store .f32 none x ao)
  -- core-opcode: 0x39 STORE
  | f64Store (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) → BinstrMemory (tb 0x39 :: bm) (.store .f64 none x ao)
  -- core-opcode: 0x3A STORE
  | i32Store8 (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x3A :: bm) (.store .i32 (some { sz := .s8 }) x ao)
  -- core-opcode: 0x3B STORE
  | i32Store16 (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x3B :: bm) (.store .i32 (some { sz := .s16 }) x ao)
  -- core-opcode: 0x3C STORE
  | i64Store8 (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x3C :: bm) (.store .i64 (some { sz := .s8 }) x ao)
  -- core-opcode: 0x3D STORE
  | i64Store16 (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x3D :: bm) (.store .i64 (some { sz := .s16 }) x ao)
  -- core-opcode: 0x3E STORE
  | i64Store32 (bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bmemarg bm (x, ao) →
      BinstrMemory (tb 0x3E :: bm) (.store .i64 (some { sz := .s32 }) x ao)
  -- core-opcode: 0x3F MEMORY.SIZE
  | size (bs : Bytes) (x : MemIdx) :
      Bmemidx bs x → BinstrMemory (tb 0x3F :: bs) (.memorySize x)
  -- core-opcode: 0x40 MEMORY.GROW
  | grow (bs : Bytes) (x : MemIdx) :
      Bmemidx bs x → BinstrMemory (tb 0x40 :: bs) (.memoryGrow x)
  -- core-opcode: 0xFC 8 MEMORY.INIT
  | init (bo by' bx : Bytes) (y : DataIdx) (x : MemIdx) :
      Bprefixed 0xFC 8 bo → Bdataidx by' y → Bmemidx bx x →
      BinstrMemory (bo ++ by' ++ bx) (.memoryInit x y)
  -- core-opcode: 0xFC 9 DATA.DROP
  | dataDrop (bo bx : Bytes) (x : DataIdx) :
      Bprefixed 0xFC 9 bo → Bdataidx bx x → BinstrMemory (bo ++ bx) (.dataDrop x)
  -- core-opcode: 0xFC 10 MEMORY.COPY
  | copy (bo b₁ b₂ : Bytes) (x₁ x₂ : MemIdx) :
      Bprefixed 0xFC 10 bo → Bmemidx b₁ x₁ → Bmemidx b₂ x₂ →
      BinstrMemory (bo ++ b₁ ++ b₂) (.memoryCopy x₁ x₂)
  -- core-opcode: 0xFC 11 MEMORY.FILL
  | fill (bo bx : Bytes) (x : MemIdx) :
      Bprefixed 0xFC 11 bo → Bmemidx bx x → BinstrMemory (bo ++ bx) (.memoryFill x)

/-! ## `grammar Binstr/ref` -/

/-- `grammar Binstr/ref : instr`. -/
inductive BinstrRef : Bytes → Instr → Prop where
  -- core-opcode: 0xD0 REF.NULL
  | null (bs : Bytes) (ht : HeapType) :
      Bheaptype bs ht → BinstrRef (tb 0xD0 :: bs) (.refNull ht)
  -- core-opcode: 0xD1 REF.IS_NULL
  | isNull : BinstrRef [tb 0xD1] .refIsNull
  -- core-opcode: 0xD2 REF.FUNC
  | func (bs : Bytes) (x : FuncIdx) :
      Bfuncidx bs x → BinstrRef (tb 0xD2 :: bs) (.refFunc x)
  -- core-opcode: 0xD3 REF.EQ
  | eq : BinstrRef [tb 0xD3] .refEq
  -- core-opcode: 0xD4 REF.AS_NON_NULL
  | asNonNull : BinstrRef [tb 0xD4] .refAsNonNull
  -- core-opcode: 0xD5 BR_ON_NULL
  | brOnNull (bs : Bytes) (l : LabelIdx) :
      Blabelidx bs l → BinstrRef (tb 0xD5 :: bs) (.brOnNull l)
  -- core-opcode: 0xD6 BR_ON_NON_NULL
  | brOnNonNull (bs : Bytes) (l : LabelIdx) :
      Blabelidx bs l → BinstrRef (tb 0xD6 :: bs) (.brOnNonNull l)

/-! ## `grammar Binstr/struct` -/

/-- `grammar Binstr/struct : instr`. -/
inductive BinstrStruct : Bytes → Instr → Prop where
  -- core-opcode: 0xFB 0 STRUCT.NEW
  | new (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 0 bo → Btypeidx bx x → BinstrStruct (bo ++ bx) (.structNew x)
  -- core-opcode: 0xFB 1 STRUCT.NEW_DEFAULT
  | newDefault (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 1 bo → Btypeidx bx x →
      BinstrStruct (bo ++ bx) (.structNewDefault x)
  -- core-opcode: 0xFB 2 STRUCT.GET
  | get (bo bx bi : Bytes) (x : TypeIdx) (i : U32) :
      Bprefixed 0xFB 2 bo → Btypeidx bx x → Bu32 bi i →
      BinstrStruct (bo ++ bx ++ bi) (.structGet none x i)
  -- core-opcode: 0xFB 3 STRUCT.GET
  | getS (bo bx bi : Bytes) (x : TypeIdx) (i : U32) :
      Bprefixed 0xFB 3 bo → Btypeidx bx x → Bu32 bi i →
      BinstrStruct (bo ++ bx ++ bi) (.structGet (some .s) x i)
  -- core-opcode: 0xFB 4 STRUCT.GET
  | getU (bo bx bi : Bytes) (x : TypeIdx) (i : U32) :
      Bprefixed 0xFB 4 bo → Btypeidx bx x → Bu32 bi i →
      BinstrStruct (bo ++ bx ++ bi) (.structGet (some .u) x i)
  -- core-opcode: 0xFB 5 STRUCT.SET
  | set (bo bx bi : Bytes) (x : TypeIdx) (i : U32) :
      Bprefixed 0xFB 5 bo → Btypeidx bx x → Bu32 bi i →
      BinstrStruct (bo ++ bx ++ bi) (.structSet x i)

/-! ## `grammar Binstr/array` -/

/-- `grammar Binstr/array : instr`. -/
inductive BinstrArray : Bytes → Instr → Prop where
  -- core-opcode: 0xFB 6 ARRAY.NEW
  | new (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 6 bo → Btypeidx bx x → BinstrArray (bo ++ bx) (.arrayNew x)
  -- core-opcode: 0xFB 7 ARRAY.NEW_DEFAULT
  | newDefault (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 7 bo → Btypeidx bx x →
      BinstrArray (bo ++ bx) (.arrayNewDefault x)
  -- core-opcode: 0xFB 8 ARRAY.NEW_FIXED
  | newFixed (bo bx bn : Bytes) (x : TypeIdx) (n : U32) :
      Bprefixed 0xFB 8 bo → Btypeidx bx x → Bu32 bn n →
      BinstrArray (bo ++ bx ++ bn) (.arrayNewFixed x n)
  -- core-opcode: 0xFB 9 ARRAY.NEW_DATA
  | newData (bo bx by' : Bytes) (x : TypeIdx) (y : DataIdx) :
      Bprefixed 0xFB 9 bo → Btypeidx bx x → Bdataidx by' y →
      BinstrArray (bo ++ bx ++ by') (.arrayNewData x y)
  -- core-opcode: 0xFB 10 ARRAY.NEW_ELEM
  | newElem (bo bx by' : Bytes) (x : TypeIdx) (y : ElemIdx) :
      Bprefixed 0xFB 10 bo → Btypeidx bx x → Belemidx by' y →
      BinstrArray (bo ++ bx ++ by') (.arrayNewElem x y)
  -- core-opcode: 0xFB 11 ARRAY.GET
  | get (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 11 bo → Btypeidx bx x → BinstrArray (bo ++ bx) (.arrayGet none x)
  -- core-opcode: 0xFB 12 ARRAY.GET
  | getS (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 12 bo → Btypeidx bx x →
      BinstrArray (bo ++ bx) (.arrayGet (some .s) x)
  -- core-opcode: 0xFB 13 ARRAY.GET
  | getU (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 13 bo → Btypeidx bx x →
      BinstrArray (bo ++ bx) (.arrayGet (some .u) x)
  -- core-opcode: 0xFB 14 ARRAY.SET
  | set (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 14 bo → Btypeidx bx x → BinstrArray (bo ++ bx) (.arraySet x)
  -- core-opcode: 0xFB 15 ARRAY.LEN
  | len (bo : Bytes) : Bprefixed 0xFB 15 bo → BinstrArray bo .arrayLen
  -- core-opcode: 0xFB 16 ARRAY.FILL
  | fill (bo bx : Bytes) (x : TypeIdx) :
      Bprefixed 0xFB 16 bo → Btypeidx bx x → BinstrArray (bo ++ bx) (.arrayFill x)
  -- core-opcode: 0xFB 17 ARRAY.COPY
  | copy (bo b₁ b₂ : Bytes) (x₁ x₂ : TypeIdx) :
      Bprefixed 0xFB 17 bo → Btypeidx b₁ x₁ → Btypeidx b₂ x₂ →
      BinstrArray (bo ++ b₁ ++ b₂) (.arrayCopy x₁ x₂)
  -- core-opcode: 0xFB 18 ARRAY.INIT_DATA
  | initData (bo bx by' : Bytes) (x : TypeIdx) (y : DataIdx) :
      Bprefixed 0xFB 18 bo → Btypeidx bx x → Bdataidx by' y →
      BinstrArray (bo ++ bx ++ by') (.arrayInitData x y)
  -- core-opcode: 0xFB 19 ARRAY.INIT_ELEM
  | initElem (bo bx by' : Bytes) (x : TypeIdx) (y : ElemIdx) :
      Bprefixed 0xFB 19 bo → Btypeidx bx x → Belemidx by' y →
      BinstrArray (bo ++ bx ++ by') (.arrayInitElem x y)

/-! ## `grammar Binstr/cast` -/

/-- `grammar Binstr/cast : instr`. -/
inductive BinstrCast : Bytes → Instr → Prop where
  -- core-opcode: 0xFB 20 REF.TEST
  | test (bo bh : Bytes) (ht : HeapType) :
      Bprefixed 0xFB 20 bo → Bheaptype bh ht →
      BinstrCast (bo ++ bh) (.refTest (.ref none ht))
  -- core-opcode: 0xFB 21 REF.TEST
  | testNull (bo bh : Bytes) (ht : HeapType) :
      Bprefixed 0xFB 21 bo → Bheaptype bh ht →
      BinstrCast (bo ++ bh) (.refTest (.ref (some .null) ht))
  -- core-opcode: 0xFB 22 REF.CAST
  | cast (bo bh : Bytes) (ht : HeapType) :
      Bprefixed 0xFB 22 bo → Bheaptype bh ht →
      BinstrCast (bo ++ bh) (.refCast (.ref none ht))
  -- core-opcode: 0xFB 23 REF.CAST
  | castNull (bo bh : Bytes) (ht : HeapType) :
      Bprefixed 0xFB 23 bo → Bheaptype bh ht →
      BinstrCast (bo ++ bh) (.refCast (.ref (some .null) ht))
  /-- `| 0xFB 24:Bu32 (null_1?, null_2?):Bcastop
        l:Blabelidx ht_1:Bheaptype ht_2:Bheaptype
        => BR_ON_CAST l (REF null_1? ht_1) (REF null_2? ht_2)`.

  The coverage extractor joins the two source lines before identifying this
  production, so it remains a distinct pinned obligation. -/
  -- core-opcode: 0xFB 24 BR_ON_CAST
  | brOnCast (bo bc bl b₁ b₂ : Bytes) (n₁ n₂ : Option Null) (l : LabelIdx)
      (ht₁ ht₂ : HeapType) :
      Bprefixed 0xFB 24 bo → Bcastop bc (n₁, n₂) → Blabelidx bl l →
      Bheaptype b₁ ht₁ → Bheaptype b₂ ht₂ →
      BinstrCast (bo ++ bc ++ bl ++ b₁ ++ b₂)
        (.brOnCast l (.ref n₁ ht₁) (.ref n₂ ht₂))
  /-- `| 0xFB 25:Bu32 (null_1?, null_2?):Bcastop
        l:Blabelidx ht_1:Bheaptype ht_2:Bheaptype
        => BR_ON_CAST_FAIL l (REF null_1? ht_1) (REF null_2? ht_2)`.

  Two lines in the pinned source, as `0xFB 24` is; the same joined-production
  extraction applies. -/
  -- core-opcode: 0xFB 25 BR_ON_CAST_FAIL
  | brOnCastFail (bo bc bl b₁ b₂ : Bytes) (n₁ n₂ : Option Null) (l : LabelIdx)
      (ht₁ ht₂ : HeapType) :
      Bprefixed 0xFB 25 bo → Bcastop bc (n₁, n₂) → Blabelidx bl l →
      Bheaptype b₁ ht₁ → Bheaptype b₂ ht₂ →
      BinstrCast (bo ++ bc ++ bl ++ b₁ ++ b₂)
        (.brOnCastFail l (.ref n₁ ht₁) (.ref n₂ ht₂))

/-! ## `grammar Binstr/extern` and `grammar Binstr/i31` -/

/-- `grammar Binstr/extern : instr`. -/
inductive BinstrExtern : Bytes → Instr → Prop where
  -- core-opcode: 0xFB 26 ANY.CONVERT_EXTERN
  | anyConvertExtern (bo : Bytes) :
      Bprefixed 0xFB 26 bo → BinstrExtern bo .anyConvertExtern
  -- core-opcode: 0xFB 27 EXTERN.CONVERT_ANY
  | externConvertAny (bo : Bytes) :
      Bprefixed 0xFB 27 bo → BinstrExtern bo .externConvertAny

/-- `grammar Binstr/i31 : instr`. -/
inductive BinstrI31 : Bytes → Instr → Prop where
  -- core-opcode: 0xFB 28 REF.I31
  | refI31 (bo : Bytes) : Bprefixed 0xFB 28 bo → BinstrI31 bo .refI31
  -- core-opcode: 0xFB 29 I31.GET
  | getS (bo : Bytes) : Bprefixed 0xFB 29 bo → BinstrI31 bo (.i31Get .s)
  -- core-opcode: 0xFB 30 I31.GET
  | getU (bo : Bytes) : Bprefixed 0xFB 30 bo → BinstrI31 bo (.i31Get .u)

/-! ## The numeric fragments

`Binstr/num-const`, `num-test-*`, `num-rel-*`, `num-un-*`, `num-bin-*`,
`num-un-ext-*`, `num-cvt` and `num-cvt-sat`, in source order.

`CVTOP nt_1 nt_2 op` has `nt_1` for the RESULT type and `nt_2` for the operand
type (`rule Instr_ok/cvtop: C |- CVTOP nt_1 nt_2 cvtop : nt_2 -> nt_1`), and
`Core/Operators.lean` indexes the operator family by `(operand, result)`
accordingly. -/

/-- The numeric fragments of `grammar Binstr`. -/
inductive BinstrNum : Bytes → Instr → Prop where
  -- Binstr/num-const
  -- core-opcode: 0x41 CONST
  | i32Const (bs : Bytes) (n : U32) :
      Bu32 bs n → BinstrNum (tb 0x41 :: bs) (.const .i32 n)
  -- core-opcode: 0x42 CONST
  | i64Const (bs : Bytes) (n : U64) :
      Bu64 bs n → BinstrNum (tb 0x42 :: bs) (.const .i64 n)
  -- core-opcode: 0x43 CONST
  | f32Const (bs : Bytes) (p : F32) :
      Bf32 bs p → BinstrNum (tb 0x43 :: bs) (.const .f32 p)
  -- core-opcode: 0x44 CONST
  | f64Const (bs : Bytes) (p : F64) :
      Bf64 bs p → BinstrNum (tb 0x44 :: bs) (.const .f64 p)
  -- Binstr/num-test-i32
  -- core-opcode: 0x45 TESTOP
  | i32Eqz : BinstrNum [tb 0x45] (.testop .i32 (.int .eqz))
  -- Binstr/num-rel-i32
  -- core-opcode: 0x46 RELOP
  | i32Eq : BinstrNum [tb 0x46] (.relop .i32 (.int .eq))
  -- core-opcode: 0x47 RELOP
  | i32Ne : BinstrNum [tb 0x47] (.relop .i32 (.int .ne))
  -- core-opcode: 0x48 RELOP
  | i32LtS : BinstrNum [tb 0x48] (.relop .i32 (.int (.lt .s)))
  -- core-opcode: 0x49 RELOP
  | i32LtU : BinstrNum [tb 0x49] (.relop .i32 (.int (.lt .u)))
  -- core-opcode: 0x4A RELOP
  | i32GtS : BinstrNum [tb 0x4A] (.relop .i32 (.int (.gt .s)))
  -- core-opcode: 0x4B RELOP
  | i32GtU : BinstrNum [tb 0x4B] (.relop .i32 (.int (.gt .u)))
  -- core-opcode: 0x4C RELOP
  | i32LeS : BinstrNum [tb 0x4C] (.relop .i32 (.int (.le .s)))
  -- core-opcode: 0x4D RELOP
  | i32LeU : BinstrNum [tb 0x4D] (.relop .i32 (.int (.le .u)))
  -- core-opcode: 0x4E RELOP
  | i32GeS : BinstrNum [tb 0x4E] (.relop .i32 (.int (.ge .s)))
  -- core-opcode: 0x4F RELOP
  | i32GeU : BinstrNum [tb 0x4F] (.relop .i32 (.int (.ge .u)))
  -- Binstr/num-test-i64
  -- core-opcode: 0x50 TESTOP
  | i64Eqz : BinstrNum [tb 0x50] (.testop .i64 (.int .eqz))
  -- Binstr/num-rel-i64
  -- core-opcode: 0x51 RELOP
  | i64Eq : BinstrNum [tb 0x51] (.relop .i64 (.int .eq))
  -- core-opcode: 0x52 RELOP
  | i64Ne : BinstrNum [tb 0x52] (.relop .i64 (.int .ne))
  -- core-opcode: 0x53 RELOP
  | i64LtS : BinstrNum [tb 0x53] (.relop .i64 (.int (.lt .s)))
  -- core-opcode: 0x54 RELOP
  | i64LtU : BinstrNum [tb 0x54] (.relop .i64 (.int (.lt .u)))
  -- core-opcode: 0x55 RELOP
  | i64GtS : BinstrNum [tb 0x55] (.relop .i64 (.int (.gt .s)))
  -- core-opcode: 0x56 RELOP
  | i64GtU : BinstrNum [tb 0x56] (.relop .i64 (.int (.gt .u)))
  -- core-opcode: 0x57 RELOP
  | i64LeS : BinstrNum [tb 0x57] (.relop .i64 (.int (.le .s)))
  -- core-opcode: 0x58 RELOP
  | i64LeU : BinstrNum [tb 0x58] (.relop .i64 (.int (.le .u)))
  -- core-opcode: 0x59 RELOP
  | i64GeS : BinstrNum [tb 0x59] (.relop .i64 (.int (.ge .s)))
  -- core-opcode: 0x5A RELOP
  | i64GeU : BinstrNum [tb 0x5A] (.relop .i64 (.int (.ge .u)))
  -- Binstr/num-rel-f32
  -- core-opcode: 0x5B RELOP
  | f32Eq : BinstrNum [tb 0x5B] (.relop .f32 (.float .eq))
  -- core-opcode: 0x5C RELOP
  | f32Ne : BinstrNum [tb 0x5C] (.relop .f32 (.float .ne))
  -- core-opcode: 0x5D RELOP
  | f32Lt : BinstrNum [tb 0x5D] (.relop .f32 (.float .lt))
  -- core-opcode: 0x5E RELOP
  | f32Gt : BinstrNum [tb 0x5E] (.relop .f32 (.float .gt))
  -- core-opcode: 0x5F RELOP
  | f32Le : BinstrNum [tb 0x5F] (.relop .f32 (.float .le))
  -- core-opcode: 0x60 RELOP
  | f32Ge : BinstrNum [tb 0x60] (.relop .f32 (.float .ge))
  -- Binstr/num-rel-f64
  -- core-opcode: 0x61 RELOP
  | f64Eq : BinstrNum [tb 0x61] (.relop .f64 (.float .eq))
  -- core-opcode: 0x62 RELOP
  | f64Ne : BinstrNum [tb 0x62] (.relop .f64 (.float .ne))
  -- core-opcode: 0x63 RELOP
  | f64Lt : BinstrNum [tb 0x63] (.relop .f64 (.float .lt))
  -- core-opcode: 0x64 RELOP
  | f64Gt : BinstrNum [tb 0x64] (.relop .f64 (.float .gt))
  -- core-opcode: 0x65 RELOP
  | f64Le : BinstrNum [tb 0x65] (.relop .f64 (.float .le))
  -- core-opcode: 0x66 RELOP
  | f64Ge : BinstrNum [tb 0x66] (.relop .f64 (.float .ge))
  -- Binstr/num-un-i32
  -- core-opcode: 0x67 UNOP
  | i32Clz : BinstrNum [tb 0x67] (.unop .i32 (.int .clz))
  -- core-opcode: 0x68 UNOP
  | i32Ctz : BinstrNum [tb 0x68] (.unop .i32 (.int .ctz))
  -- core-opcode: 0x69 UNOP
  | i32Popcnt : BinstrNum [tb 0x69] (.unop .i32 (.int .popcnt))
  -- Binstr/num-bin-i32
  -- core-opcode: 0x6A BINOP
  | i32Add : BinstrNum [tb 0x6A] (.binop .i32 (.int .add))
  -- core-opcode: 0x6B BINOP
  | i32Sub : BinstrNum [tb 0x6B] (.binop .i32 (.int .sub))
  -- core-opcode: 0x6C BINOP
  | i32Mul : BinstrNum [tb 0x6C] (.binop .i32 (.int .mul))
  -- core-opcode: 0x6D BINOP
  | i32DivS : BinstrNum [tb 0x6D] (.binop .i32 (.int (.div .s)))
  -- core-opcode: 0x6E BINOP
  | i32DivU : BinstrNum [tb 0x6E] (.binop .i32 (.int (.div .u)))
  -- core-opcode: 0x6F BINOP
  | i32RemS : BinstrNum [tb 0x6F] (.binop .i32 (.int (.rem .s)))
  -- core-opcode: 0x70 BINOP
  | i32RemU : BinstrNum [tb 0x70] (.binop .i32 (.int (.rem .u)))
  -- core-opcode: 0x71 BINOP
  | i32And : BinstrNum [tb 0x71] (.binop .i32 (.int .and))
  -- core-opcode: 0x72 BINOP
  | i32Or : BinstrNum [tb 0x72] (.binop .i32 (.int .or))
  -- core-opcode: 0x73 BINOP
  | i32Xor : BinstrNum [tb 0x73] (.binop .i32 (.int .xor))
  -- core-opcode: 0x74 BINOP
  | i32Shl : BinstrNum [tb 0x74] (.binop .i32 (.int .shl))
  -- core-opcode: 0x75 BINOP
  | i32ShrS : BinstrNum [tb 0x75] (.binop .i32 (.int (.shr .s)))
  -- core-opcode: 0x76 BINOP
  | i32ShrU : BinstrNum [tb 0x76] (.binop .i32 (.int (.shr .u)))
  -- core-opcode: 0x77 BINOP
  | i32Rotl : BinstrNum [tb 0x77] (.binop .i32 (.int .rotl))
  -- core-opcode: 0x78 BINOP
  | i32Rotr : BinstrNum [tb 0x78] (.binop .i32 (.int .rotr))
  -- Binstr/num-un-i64
  -- core-opcode: 0x79 UNOP
  | i64Clz : BinstrNum [tb 0x79] (.unop .i64 (.int .clz))
  -- core-opcode: 0x7A UNOP
  | i64Ctz : BinstrNum [tb 0x7A] (.unop .i64 (.int .ctz))
  -- core-opcode: 0x7B UNOP
  | i64Popcnt : BinstrNum [tb 0x7B] (.unop .i64 (.int .popcnt))
  -- Binstr/num-un-ext-i32
  -- core-opcode: 0xC0 UNOP
  | i32Extend8 : BinstrNum [tb 0xC0] (.unop .i32 (.int (.extend .s8)))
  -- core-opcode: 0xC1 UNOP
  | i32Extend16 : BinstrNum [tb 0xC1] (.unop .i32 (.int (.extend .s16)))
  -- Binstr/num-un-ext-i64
  -- core-opcode: 0xC2 UNOP
  | i64Extend8 : BinstrNum [tb 0xC2] (.unop .i64 (.int (.extend .s8)))
  -- core-opcode: 0xC3 UNOP
  | i64Extend16 : BinstrNum [tb 0xC3] (.unop .i64 (.int (.extend .s16)))
  -- core-opcode: 0xC4 UNOP
  | i64Extend32 : BinstrNum [tb 0xC4] (.unop .i64 (.int (.extend .s32)))
  -- Binstr/num-bin-i64
  -- core-opcode: 0x7C BINOP
  | i64Add : BinstrNum [tb 0x7C] (.binop .i64 (.int .add))
  -- core-opcode: 0x7D BINOP
  | i64Sub : BinstrNum [tb 0x7D] (.binop .i64 (.int .sub))
  -- core-opcode: 0x7E BINOP
  | i64Mul : BinstrNum [tb 0x7E] (.binop .i64 (.int .mul))
  -- core-opcode: 0x7F BINOP
  | i64DivS : BinstrNum [tb 0x7F] (.binop .i64 (.int (.div .s)))
  -- core-opcode: 0x80 BINOP
  | i64DivU : BinstrNum [tb 0x80] (.binop .i64 (.int (.div .u)))
  -- core-opcode: 0x81 BINOP
  | i64RemS : BinstrNum [tb 0x81] (.binop .i64 (.int (.rem .s)))
  -- core-opcode: 0x82 BINOP
  | i64RemU : BinstrNum [tb 0x82] (.binop .i64 (.int (.rem .u)))
  -- core-opcode: 0x83 BINOP
  | i64And : BinstrNum [tb 0x83] (.binop .i64 (.int .and))
  -- core-opcode: 0x84 BINOP
  | i64Or : BinstrNum [tb 0x84] (.binop .i64 (.int .or))
  -- core-opcode: 0x85 BINOP
  | i64Xor : BinstrNum [tb 0x85] (.binop .i64 (.int .xor))
  -- core-opcode: 0x86 BINOP
  | i64Shl : BinstrNum [tb 0x86] (.binop .i64 (.int .shl))
  -- core-opcode: 0x87 BINOP
  | i64ShrS : BinstrNum [tb 0x87] (.binop .i64 (.int (.shr .s)))
  -- core-opcode: 0x88 BINOP
  | i64ShrU : BinstrNum [tb 0x88] (.binop .i64 (.int (.shr .u)))
  -- core-opcode: 0x89 BINOP
  | i64Rotl : BinstrNum [tb 0x89] (.binop .i64 (.int .rotl))
  -- core-opcode: 0x8A BINOP
  | i64Rotr : BinstrNum [tb 0x8A] (.binop .i64 (.int .rotr))
  -- Binstr/num-un-f32
  -- core-opcode: 0x8B UNOP
  | f32Abs : BinstrNum [tb 0x8B] (.unop .f32 (.float .abs))
  -- core-opcode: 0x8C UNOP
  | f32Neg : BinstrNum [tb 0x8C] (.unop .f32 (.float .neg))
  -- core-opcode: 0x8D UNOP
  | f32Ceil : BinstrNum [tb 0x8D] (.unop .f32 (.float .ceil))
  -- core-opcode: 0x8E UNOP
  | f32Floor : BinstrNum [tb 0x8E] (.unop .f32 (.float .floor))
  -- core-opcode: 0x8F UNOP
  | f32Trunc : BinstrNum [tb 0x8F] (.unop .f32 (.float .trunc))
  -- core-opcode: 0x90 UNOP
  | f32Nearest : BinstrNum [tb 0x90] (.unop .f32 (.float .nearest))
  -- core-opcode: 0x91 UNOP
  | f32Sqrt : BinstrNum [tb 0x91] (.unop .f32 (.float .sqrt))
  -- Binstr/num-bin-f32
  -- core-opcode: 0x92 BINOP
  | f32Add : BinstrNum [tb 0x92] (.binop .f32 (.float .add))
  -- core-opcode: 0x93 BINOP
  | f32Sub : BinstrNum [tb 0x93] (.binop .f32 (.float .sub))
  -- core-opcode: 0x94 BINOP
  | f32Mul : BinstrNum [tb 0x94] (.binop .f32 (.float .mul))
  -- core-opcode: 0x95 BINOP
  | f32Div : BinstrNum [tb 0x95] (.binop .f32 (.float .div))
  -- core-opcode: 0x96 BINOP
  | f32Min : BinstrNum [tb 0x96] (.binop .f32 (.float .min))
  -- core-opcode: 0x97 BINOP
  | f32Max : BinstrNum [tb 0x97] (.binop .f32 (.float .max))
  -- core-opcode: 0x98 BINOP
  | f32Copysign : BinstrNum [tb 0x98] (.binop .f32 (.float .copysign))
  -- Binstr/num-un-f64
  -- core-opcode: 0x99 UNOP
  | f64Abs : BinstrNum [tb 0x99] (.unop .f64 (.float .abs))
  -- core-opcode: 0x9A UNOP
  | f64Neg : BinstrNum [tb 0x9A] (.unop .f64 (.float .neg))
  -- core-opcode: 0x9B UNOP
  | f64Ceil : BinstrNum [tb 0x9B] (.unop .f64 (.float .ceil))
  -- core-opcode: 0x9C UNOP
  | f64Floor : BinstrNum [tb 0x9C] (.unop .f64 (.float .floor))
  -- core-opcode: 0x9D UNOP
  | f64Trunc : BinstrNum [tb 0x9D] (.unop .f64 (.float .trunc))
  -- core-opcode: 0x9E UNOP
  | f64Nearest : BinstrNum [tb 0x9E] (.unop .f64 (.float .nearest))
  -- core-opcode: 0x9F UNOP
  | f64Sqrt : BinstrNum [tb 0x9F] (.unop .f64 (.float .sqrt))
  -- Binstr/num-bin-f64
  -- core-opcode: 0xA0 BINOP
  | f64Add : BinstrNum [tb 0xA0] (.binop .f64 (.float .add))
  -- core-opcode: 0xA1 BINOP
  | f64Sub : BinstrNum [tb 0xA1] (.binop .f64 (.float .sub))
  -- core-opcode: 0xA2 BINOP
  | f64Mul : BinstrNum [tb 0xA2] (.binop .f64 (.float .mul))
  -- core-opcode: 0xA3 BINOP
  | f64Div : BinstrNum [tb 0xA3] (.binop .f64 (.float .div))
  -- core-opcode: 0xA4 BINOP
  | f64Min : BinstrNum [tb 0xA4] (.binop .f64 (.float .min))
  -- core-opcode: 0xA5 BINOP
  | f64Max : BinstrNum [tb 0xA5] (.binop .f64 (.float .max))
  -- core-opcode: 0xA6 BINOP
  | f64Copysign : BinstrNum [tb 0xA6] (.binop .f64 (.float .copysign))
  -- Binstr/num-cvt
  -- core-opcode: 0xA7 CVTOP
  | i32WrapI64 : BinstrNum [tb 0xA7] (.cvtop .i32 .i64 (.ii .wrap))
  -- core-opcode: 0xA8 CVTOP
  | i32TruncF32S : BinstrNum [tb 0xA8] (.cvtop .i32 .f32 (.fi (.trunc .s)))
  -- core-opcode: 0xA9 CVTOP
  | i32TruncF32U : BinstrNum [tb 0xA9] (.cvtop .i32 .f32 (.fi (.trunc .u)))
  -- core-opcode: 0xAA CVTOP
  | i32TruncF64S : BinstrNum [tb 0xAA] (.cvtop .i32 .f64 (.fi (.trunc .s)))
  -- core-opcode: 0xAB CVTOP
  | i32TruncF64U : BinstrNum [tb 0xAB] (.cvtop .i32 .f64 (.fi (.trunc .u)))
  -- core-opcode: 0xAC CVTOP
  | i64ExtendI32S : BinstrNum [tb 0xAC] (.cvtop .i64 .i32 (.ii (.extend .s)))
  -- core-opcode: 0xAD CVTOP
  | i64ExtendI32U : BinstrNum [tb 0xAD] (.cvtop .i64 .i32 (.ii (.extend .u)))
  -- core-opcode: 0xAE CVTOP
  | i64TruncF32S : BinstrNum [tb 0xAE] (.cvtop .i64 .f32 (.fi (.trunc .s)))
  -- core-opcode: 0xAF CVTOP
  | i64TruncF32U : BinstrNum [tb 0xAF] (.cvtop .i64 .f32 (.fi (.trunc .u)))
  -- core-opcode: 0xB0 CVTOP
  | i64TruncF64S : BinstrNum [tb 0xB0] (.cvtop .i64 .f64 (.fi (.trunc .s)))
  -- core-opcode: 0xB1 CVTOP
  | i64TruncF64U : BinstrNum [tb 0xB1] (.cvtop .i64 .f64 (.fi (.trunc .u)))
  -- core-opcode: 0xB2 CVTOP
  | f32ConvertI32S : BinstrNum [tb 0xB2] (.cvtop .f32 .i32 (.ifl (.convert .s)))
  -- core-opcode: 0xB3 CVTOP
  | f32ConvertI32U : BinstrNum [tb 0xB3] (.cvtop .f32 .i32 (.ifl (.convert .u)))
  -- core-opcode: 0xB4 CVTOP
  | f32ConvertI64S : BinstrNum [tb 0xB4] (.cvtop .f32 .i64 (.ifl (.convert .s)))
  -- core-opcode: 0xB5 CVTOP
  | f32ConvertI64U : BinstrNum [tb 0xB5] (.cvtop .f32 .i64 (.ifl (.convert .u)))
  -- core-opcode: 0xB6 CVTOP
  | f32DemoteF64 : BinstrNum [tb 0xB6] (.cvtop .f32 .f64 (.ff .demote))
  -- core-opcode: 0xB7 CVTOP
  | f64ConvertI32S : BinstrNum [tb 0xB7] (.cvtop .f64 .i32 (.ifl (.convert .s)))
  -- core-opcode: 0xB8 CVTOP
  | f64ConvertI32U : BinstrNum [tb 0xB8] (.cvtop .f64 .i32 (.ifl (.convert .u)))
  -- core-opcode: 0xB9 CVTOP
  | f64ConvertI64S : BinstrNum [tb 0xB9] (.cvtop .f64 .i64 (.ifl (.convert .s)))
  -- core-opcode: 0xBA CVTOP
  | f64ConvertI64U : BinstrNum [tb 0xBA] (.cvtop .f64 .i64 (.ifl (.convert .u)))
  /-- `| 0xBB => CVTOP F32 F64 PROMOTE`, TRANSCRIBED VERBATIM.

  Read with the source's own convention that `CVTOP nt_1 nt_2` has `nt_1` for
  the RESULT (`rule Instr_ok/cvtop`), this says `f32.promote_f64`, whose
  operator instance `cvtop__(F64, F32)` requires the operand to be NARROWER than
  the result -- so the instruction this production derives fails
  `Core/Operators.lean`'s `Cvtop.wf`, and 0xBB, which every other part of the
  pinned specification treats as `f64.promote_f32`, gets no derivation with the
  operand and result the other way round.  Every neighbouring production
  (`0xB6 => CVTOP F32 F64 DEMOTE`, `0xBC => CVTOP I32 F32 REINTERPRET`) follows
  the result-first convention, so this reads as an upstream defect at the pinned
  commit.  It is transcribed rather than corrected, because a transcription that
  silently disagrees with its source cannot be audited against it; the
  disagreement is recorded here instead. -/
  -- core-opcode: 0xBB CVTOP
  | f32PromoteF64 : BinstrNum [tb 0xBB] (.cvtop .f32 .f64 (.ff .promote))
  -- core-opcode: 0xBC CVTOP
  | i32ReinterpretF32 : BinstrNum [tb 0xBC] (.cvtop .i32 .f32 (.fi .reinterpret))
  -- core-opcode: 0xBD CVTOP
  | i64ReinterpretF64 : BinstrNum [tb 0xBD] (.cvtop .i64 .f64 (.fi .reinterpret))
  -- core-opcode: 0xBE CVTOP
  | f32ReinterpretI32 : BinstrNum [tb 0xBE] (.cvtop .f32 .i32 (.ifl .reinterpret))
  -- core-opcode: 0xBF CVTOP
  | f64ReinterpretI64 : BinstrNum [tb 0xBF] (.cvtop .f64 .i64 (.ifl .reinterpret))
  -- Binstr/num-cvt-sat
  -- core-opcode: 0xFC 0 CVTOP
  | i32TruncSatF32S (bo : Bytes) :
      Bprefixed 0xFC 0 bo → BinstrNum bo (.cvtop .i32 .f32 (.fi (.truncSat .s)))
  -- core-opcode: 0xFC 1 CVTOP
  | i32TruncSatF32U (bo : Bytes) :
      Bprefixed 0xFC 1 bo → BinstrNum bo (.cvtop .i32 .f32 (.fi (.truncSat .u)))
  -- core-opcode: 0xFC 2 CVTOP
  | i32TruncSatF64S (bo : Bytes) :
      Bprefixed 0xFC 2 bo → BinstrNum bo (.cvtop .i32 .f64 (.fi (.truncSat .s)))
  -- core-opcode: 0xFC 3 CVTOP
  | i32TruncSatF64U (bo : Bytes) :
      Bprefixed 0xFC 3 bo → BinstrNum bo (.cvtop .i32 .f64 (.fi (.truncSat .u)))
  -- core-opcode: 0xFC 4 CVTOP
  | i64TruncSatF32S (bo : Bytes) :
      Bprefixed 0xFC 4 bo → BinstrNum bo (.cvtop .i64 .f32 (.fi (.truncSat .s)))
  -- core-opcode: 0xFC 5 CVTOP
  | i64TruncSatF32U (bo : Bytes) :
      Bprefixed 0xFC 5 bo → BinstrNum bo (.cvtop .i64 .f32 (.fi (.truncSat .u)))
  -- core-opcode: 0xFC 6 CVTOP
  | i64TruncSatF64S (bo : Bytes) :
      Bprefixed 0xFC 6 bo → BinstrNum bo (.cvtop .i64 .f64 (.fi (.truncSat .s)))
  -- core-opcode: 0xFC 7 CVTOP
  | i64TruncSatF64U (bo : Bytes) :
      Bprefixed 0xFC 7 bo → BinstrNum bo (.cvtop .i64 .f64 (.fi (.truncSat .u)))

end WasmGemmGnaf.Wasm.Core.Binary
