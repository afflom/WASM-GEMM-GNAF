/-
  Wasm/Core/BinaryGrammar/Vector.lean --- the DECLARATIVE binary grammar of the
  vector (SIMD) instruction fragments, for the pinned WebAssembly Core 3.0 front
  end.

  NORMATIVE SOURCE.  Every constructor below transcribes an alternative of a
  `grammar Binstr/vec-*` production of

      vendor/wasm-spec/specification/wasm-3.0/5.3-binary.instructions.spectec

  at the pinned commit, in source order, grouped by the source's own fragment
  headings.  256 of the 543 opcode productions of the pinned binary format are
  in this file: the release profile enables SIMD and relaxed SIMD, so leaving
  them out is exactly the narrowing the external audit rejected.

  None of these alternatives recurs into `Binstr`, so they are ordinary
  non-recursive relations; `BinaryGrammar/Expressions.lean` folds them into the
  single grammar `Binstr`.

  SHAPES.  `(I8 X `16)` and friends are `Core/Operators.lean`'s `shape`, i.e. a
  lane type and a dimension.  The `ishape` and `bshape` refinements carry their
  side condition in the type (`$lanetype(shape) = Jnn`, `= I8`), so the six
  shapes are named once, below, and used by name.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

/-! ## The six shapes the binary format names -/

/-- `I8 X `16`. -/
def shI8x16 : Shape := { lane := .pack .i8, dim := .d16 }
/-- `I16 X `8`. -/
def shI16x8 : Shape := { lane := .pack .i16, dim := .d8 }
/-- `I32 X `4`. -/
def shI32x4 : Shape := { lane := .num .i32, dim := .d4 }
/-- `I64 X `2`. -/
def shI64x2 : Shape := { lane := .num .i64, dim := .d2 }
/-- `F32 X `4`. -/
def shF32x4 : Shape := { lane := .num .f32, dim := .d4 }
/-- `F64 X `2`. -/
def shF64x2 : Shape := { lane := .num .f64, dim := .d2 }

/-- `I8 X `16` as an `ishape`. -/
def ishI8x16 : IShape := ⟨shI8x16, rfl⟩
/-- `I16 X `8` as an `ishape`. -/
def ishI16x8 : IShape := ⟨shI16x8, rfl⟩
/-- `I32 X `4` as an `ishape`. -/
def ishI32x4 : IShape := ⟨shI32x4, rfl⟩
/-- `I64 X `2` as an `ishape`. -/
def ishI64x2 : IShape := ⟨shI64x2, rfl⟩
/-- `I8 X `16` as a `bshape`. -/
def bshI8x16 : BShape := ⟨shI8x16, rfl⟩

/-! ## `grammar Binstr/vec-memory`, `vec-const`, `vec-shuffle`, `vec-splat`,
`vec-lane` -/

/-- The memory, constant, shuffle, splat and lane vector fragments. -/
inductive BinstrVecMem : Bytes → Instr → Prop where
  -- Binstr/vec-memory
  -- core-opcode: 0xFD 0 VLOAD
  | v128Load (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 0 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 none x ao)
  -- core-opcode: 0xFD 1 VLOAD
  | v128Load8x8S (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 1 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s8 8 .s)) x ao)
  -- core-opcode: 0xFD 2 VLOAD
  | v128Load8x8U (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 2 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s8 8 .u)) x ao)
  -- core-opcode: 0xFD 3 VLOAD
  | v128Load16x4S (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 3 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s16 4 .s)) x ao)
  -- core-opcode: 0xFD 4 VLOAD
  | v128Load16x4U (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 4 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s16 4 .u)) x ao)
  -- core-opcode: 0xFD 5 VLOAD
  | v128Load32x2S (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 5 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s32 2 .s)) x ao)
  -- core-opcode: 0xFD 6 VLOAD
  | v128Load32x2U (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 6 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.shape .s32 2 .u)) x ao)
  -- core-opcode: 0xFD 7 VLOAD
  | v128Load8Splat (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 7 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.splat .s8)) x ao)
  -- core-opcode: 0xFD 8 VLOAD
  | v128Load16Splat (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 8 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.splat .s16)) x ao)
  -- core-opcode: 0xFD 9 VLOAD
  | v128Load32Splat (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 9 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.splat .s32)) x ao)
  -- core-opcode: 0xFD 10 VLOAD
  | v128Load64Splat (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 10 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.splat .s64)) x ao)
  -- core-opcode: 0xFD 11 VSTORE
  | v128Store (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 11 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vstore .v128 x ao)
  -- core-opcode: 0xFD 84 VLOAD_LANE
  | v128Load8Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 84 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vloadLane .v128 .s8 x ao i)
  -- core-opcode: 0xFD 85 VLOAD_LANE
  | v128Load16Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 85 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vloadLane .v128 .s16 x ao i)
  -- core-opcode: 0xFD 86 VLOAD_LANE
  | v128Load32Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 86 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vloadLane .v128 .s32 x ao i)
  -- core-opcode: 0xFD 87 VLOAD_LANE
  | v128Load64Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 87 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vloadLane .v128 .s64 x ao i)
  -- core-opcode: 0xFD 88 VSTORE_LANE
  | v128Store8Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 88 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vstoreLane .v128 .s8 x ao i)
  -- core-opcode: 0xFD 89 VSTORE_LANE
  | v128Store16Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 89 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vstoreLane .v128 .s16 x ao i)
  -- core-opcode: 0xFD 90 VSTORE_LANE
  | v128Store32Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 90 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vstoreLane .v128 .s32 x ao i)
  -- core-opcode: 0xFD 91 VSTORE_LANE
  | v128Store64Lane (bo bm bi : Bytes) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
      Bprefixed 0xFD 91 bo → Bmemarg bm (x, ao) → Blaneidx bi i →
      BinstrVecMem (bo ++ bm ++ bi) (.vstoreLane .v128 .s64 x ao i)
  -- core-opcode: 0xFD 92 VLOAD
  | v128Load32Zero (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 92 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.zero .s32)) x ao)
  -- core-opcode: 0xFD 93 VLOAD
  | v128Load64Zero (bo bm : Bytes) (x : MemIdx) (ao : MemArg) :
      Bprefixed 0xFD 93 bo → Bmemarg bm (x, ao) →
      BinstrVecMem (bo ++ bm) (.vload .v128 (some (.zero .s64)) x ao)
  -- Binstr/vec-const
  /-- `| 0xFD 12:Bu32 (b:Bbyte)^16 => VCONST V128 $inv_ibytes_(`128, (b)^16)`.

  `$inv_ibytes_` is declared `hint(builtin)` in `3.1-numerics.scalar.spectec`
  and has no equations there; the little-endian reading is `leNat`, defined in
  `BinaryGrammar/Values.lean` rather than assumed. -/
  -- core-opcode: 0xFD 12 VCONST
  | v128Const (bo bb : Bytes) (bl : List Byte) (c : VecLit Vnn.v128) :
      Bprefixed 0xFD 12 bo → Rep Bbyte 16 bb bl → c.val = leNat bl →
      BinstrVecMem (bo ++ bb) (.vconst .v128 c)
  -- Binstr/vec-shuffle
  -- core-opcode: 0xFD 13 VSHUFFLE
  | i8x16Shuffle (bo bl : Bytes) (ls : List LaneIdx) :
      Bprefixed 0xFD 13 bo → Rep Blaneidx 16 bl ls →
      BinstrVecMem (bo ++ bl) (.vshuffle bshI8x16 ls)
  -- core-opcode: 0xFD 14 VSWIZZLOP
  | i8x16Swizzle (bo : Bytes) :
      Bprefixed 0xFD 14 bo → BinstrVecMem bo (.vswizzlop bshI8x16 .swizzle)
  -- core-opcode: 0xFD 256 VSWIZZLOP
  | i8x16RelaxedSwizzle (bo : Bytes) :
      Bprefixed 0xFD 256 bo → BinstrVecMem bo (.vswizzlop bshI8x16 .relaxedSwizzle)
  -- Binstr/vec-splat
  -- core-opcode: 0xFD 15 VSPLAT
  | i8x16Splat (bo : Bytes) : Bprefixed 0xFD 15 bo → BinstrVecMem bo (.vsplat shI8x16)
  -- core-opcode: 0xFD 16 VSPLAT
  | i16x8Splat (bo : Bytes) : Bprefixed 0xFD 16 bo → BinstrVecMem bo (.vsplat shI16x8)
  -- core-opcode: 0xFD 17 VSPLAT
  | i32x4Splat (bo : Bytes) : Bprefixed 0xFD 17 bo → BinstrVecMem bo (.vsplat shI32x4)
  -- core-opcode: 0xFD 18 VSPLAT
  | i64x2Splat (bo : Bytes) : Bprefixed 0xFD 18 bo → BinstrVecMem bo (.vsplat shI64x2)
  -- core-opcode: 0xFD 19 VSPLAT
  | f32x4Splat (bo : Bytes) : Bprefixed 0xFD 19 bo → BinstrVecMem bo (.vsplat shF32x4)
  -- core-opcode: 0xFD 20 VSPLAT
  | f64x2Splat (bo : Bytes) : Bprefixed 0xFD 20 bo → BinstrVecMem bo (.vsplat shF64x2)
  -- Binstr/vec-lane
  -- core-opcode: 0xFD 21 VEXTRACT_LANE
  | i8x16ExtractLaneS (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 21 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI8x16 (some .s) l)
  -- core-opcode: 0xFD 22 VEXTRACT_LANE
  | i8x16ExtractLaneU (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 22 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI8x16 (some .u) l)
  -- core-opcode: 0xFD 23 VREPLACE_LANE
  | i8x16ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 23 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shI8x16 l)
  -- core-opcode: 0xFD 24 VEXTRACT_LANE
  | i16x8ExtractLaneS (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 24 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI16x8 (some .s) l)
  -- core-opcode: 0xFD 25 VEXTRACT_LANE
  | i16x8ExtractLaneU (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 25 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI16x8 (some .u) l)
  -- core-opcode: 0xFD 26 VREPLACE_LANE
  | i16x8ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 26 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shI16x8 l)
  -- core-opcode: 0xFD 27 VEXTRACT_LANE
  | i32x4ExtractLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 27 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI32x4 none l)
  -- core-opcode: 0xFD 28 VREPLACE_LANE
  | i32x4ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 28 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shI32x4 l)
  -- core-opcode: 0xFD 29 VEXTRACT_LANE
  | i64x2ExtractLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 29 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shI64x2 none l)
  -- core-opcode: 0xFD 30 VREPLACE_LANE
  | i64x2ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 30 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shI64x2 l)
  -- core-opcode: 0xFD 31 VEXTRACT_LANE
  | f32x4ExtractLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 31 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shF32x4 none l)
  -- core-opcode: 0xFD 32 VREPLACE_LANE
  | f32x4ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 32 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shF32x4 l)
  -- core-opcode: 0xFD 33 VEXTRACT_LANE
  | f64x2ExtractLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 33 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vextractLane shF64x2 none l)
  -- core-opcode: 0xFD 34 VREPLACE_LANE
  | f64x2ReplaceLane (bo bi : Bytes) (l : LaneIdx) :
      Bprefixed 0xFD 34 bo → Blaneidx bi l →
      BinstrVecMem (bo ++ bi) (.vreplaceLane shF64x2 l)

/-! ## `grammar Binstr/vec-rel-*` -/

/-- The vector comparison fragments. -/
inductive BinstrVecRel : Bytes → Instr → Prop where
  -- Binstr/vec-rel-i8x16
  -- core-opcode: 0xFD 35 VRELOP
  | i8x16Eq (bo : Bytes) : Bprefixed 0xFD 35 bo → BinstrVecRel bo (.vrelop shI8x16 (.int .eq))
  -- core-opcode: 0xFD 36 VRELOP
  | i8x16Ne (bo : Bytes) : Bprefixed 0xFD 36 bo → BinstrVecRel bo (.vrelop shI8x16 (.int .ne))
  -- core-opcode: 0xFD 37 VRELOP
  | i8x16LtS (bo : Bytes) : Bprefixed 0xFD 37 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.lt .s)))
  -- core-opcode: 0xFD 38 VRELOP
  | i8x16LtU (bo : Bytes) : Bprefixed 0xFD 38 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.lt .u)))
  -- core-opcode: 0xFD 39 VRELOP
  | i8x16GtS (bo : Bytes) : Bprefixed 0xFD 39 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.gt .s)))
  -- core-opcode: 0xFD 40 VRELOP
  | i8x16GtU (bo : Bytes) : Bprefixed 0xFD 40 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.gt .u)))
  -- core-opcode: 0xFD 41 VRELOP
  | i8x16LeS (bo : Bytes) : Bprefixed 0xFD 41 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.le .s)))
  -- core-opcode: 0xFD 42 VRELOP
  | i8x16LeU (bo : Bytes) : Bprefixed 0xFD 42 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.le .u)))
  -- core-opcode: 0xFD 43 VRELOP
  | i8x16GeS (bo : Bytes) : Bprefixed 0xFD 43 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.ge .s)))
  -- core-opcode: 0xFD 44 VRELOP
  | i8x16GeU (bo : Bytes) : Bprefixed 0xFD 44 bo → BinstrVecRel bo (.vrelop shI8x16 (.int (.ge .u)))
  -- Binstr/vec-rel-i16x8
  -- core-opcode: 0xFD 45 VRELOP
  | i16x8Eq (bo : Bytes) : Bprefixed 0xFD 45 bo → BinstrVecRel bo (.vrelop shI16x8 (.int .eq))
  -- core-opcode: 0xFD 46 VRELOP
  | i16x8Ne (bo : Bytes) : Bprefixed 0xFD 46 bo → BinstrVecRel bo (.vrelop shI16x8 (.int .ne))
  -- core-opcode: 0xFD 47 VRELOP
  | i16x8LtS (bo : Bytes) : Bprefixed 0xFD 47 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.lt .s)))
  -- core-opcode: 0xFD 48 VRELOP
  | i16x8LtU (bo : Bytes) : Bprefixed 0xFD 48 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.lt .u)))
  -- core-opcode: 0xFD 49 VRELOP
  | i16x8GtS (bo : Bytes) : Bprefixed 0xFD 49 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.gt .s)))
  -- core-opcode: 0xFD 50 VRELOP
  | i16x8GtU (bo : Bytes) : Bprefixed 0xFD 50 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.gt .u)))
  -- core-opcode: 0xFD 51 VRELOP
  | i16x8LeS (bo : Bytes) : Bprefixed 0xFD 51 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.le .s)))
  -- core-opcode: 0xFD 52 VRELOP
  | i16x8LeU (bo : Bytes) : Bprefixed 0xFD 52 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.le .u)))
  -- core-opcode: 0xFD 53 VRELOP
  | i16x8GeS (bo : Bytes) : Bprefixed 0xFD 53 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.ge .s)))
  -- core-opcode: 0xFD 54 VRELOP
  | i16x8GeU (bo : Bytes) : Bprefixed 0xFD 54 bo → BinstrVecRel bo (.vrelop shI16x8 (.int (.ge .u)))
  -- Binstr/vec-rel-i32x4
  -- core-opcode: 0xFD 55 VRELOP
  | i32x4Eq (bo : Bytes) : Bprefixed 0xFD 55 bo → BinstrVecRel bo (.vrelop shI32x4 (.int .eq))
  -- core-opcode: 0xFD 56 VRELOP
  | i32x4Ne (bo : Bytes) : Bprefixed 0xFD 56 bo → BinstrVecRel bo (.vrelop shI32x4 (.int .ne))
  -- core-opcode: 0xFD 57 VRELOP
  | i32x4LtS (bo : Bytes) : Bprefixed 0xFD 57 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.lt .s)))
  -- core-opcode: 0xFD 58 VRELOP
  | i32x4LtU (bo : Bytes) : Bprefixed 0xFD 58 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.lt .u)))
  -- core-opcode: 0xFD 59 VRELOP
  | i32x4GtS (bo : Bytes) : Bprefixed 0xFD 59 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.gt .s)))
  -- core-opcode: 0xFD 60 VRELOP
  | i32x4GtU (bo : Bytes) : Bprefixed 0xFD 60 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.gt .u)))
  -- core-opcode: 0xFD 61 VRELOP
  | i32x4LeS (bo : Bytes) : Bprefixed 0xFD 61 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.le .s)))
  -- core-opcode: 0xFD 62 VRELOP
  | i32x4LeU (bo : Bytes) : Bprefixed 0xFD 62 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.le .u)))
  -- core-opcode: 0xFD 63 VRELOP
  | i32x4GeS (bo : Bytes) : Bprefixed 0xFD 63 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.ge .s)))
  -- core-opcode: 0xFD 64 VRELOP
  | i32x4GeU (bo : Bytes) : Bprefixed 0xFD 64 bo → BinstrVecRel bo (.vrelop shI32x4 (.int (.ge .u)))
  -- Binstr/vec-rel-f32x4
  -- core-opcode: 0xFD 65 VRELOP
  | f32x4Eq (bo : Bytes) : Bprefixed 0xFD 65 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .eq))
  -- core-opcode: 0xFD 66 VRELOP
  | f32x4Ne (bo : Bytes) : Bprefixed 0xFD 66 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .ne))
  -- core-opcode: 0xFD 67 VRELOP
  | f32x4Lt (bo : Bytes) : Bprefixed 0xFD 67 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .lt))
  -- core-opcode: 0xFD 68 VRELOP
  | f32x4Gt (bo : Bytes) : Bprefixed 0xFD 68 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .gt))
  -- core-opcode: 0xFD 69 VRELOP
  | f32x4Le (bo : Bytes) : Bprefixed 0xFD 69 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .le))
  -- core-opcode: 0xFD 70 VRELOP
  | f32x4Ge (bo : Bytes) : Bprefixed 0xFD 70 bo → BinstrVecRel bo (.vrelop shF32x4 (.float .ge))
  -- Binstr/vec-rel-f64x2
  -- core-opcode: 0xFD 71 VRELOP
  | f64x2Eq (bo : Bytes) : Bprefixed 0xFD 71 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .eq))
  -- core-opcode: 0xFD 72 VRELOP
  | f64x2Ne (bo : Bytes) : Bprefixed 0xFD 72 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .ne))
  -- core-opcode: 0xFD 73 VRELOP
  | f64x2Lt (bo : Bytes) : Bprefixed 0xFD 73 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .lt))
  -- core-opcode: 0xFD 74 VRELOP
  | f64x2Gt (bo : Bytes) : Bprefixed 0xFD 74 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .gt))
  -- core-opcode: 0xFD 75 VRELOP
  | f64x2Le (bo : Bytes) : Bprefixed 0xFD 75 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .le))
  -- core-opcode: 0xFD 76 VRELOP
  | f64x2Ge (bo : Bytes) : Bprefixed 0xFD 76 bo → BinstrVecRel bo (.vrelop shF64x2 (.float .ge))
  -- Binstr/vec-rel-i64x2
  -- core-opcode: 0xFD 214 VRELOP
  | i64x2Eq (bo : Bytes) : Bprefixed 0xFD 214 bo → BinstrVecRel bo (.vrelop shI64x2 (.int .eq))
  -- core-opcode: 0xFD 215 VRELOP
  | i64x2Ne (bo : Bytes) : Bprefixed 0xFD 215 bo → BinstrVecRel bo (.vrelop shI64x2 (.int .ne))
  -- core-opcode: 0xFD 216 VRELOP
  | i64x2LtS (bo : Bytes) : Bprefixed 0xFD 216 bo → BinstrVecRel bo (.vrelop shI64x2 (.int (.lt .s)))
  -- core-opcode: 0xFD 217 VRELOP
  | i64x2GtS (bo : Bytes) : Bprefixed 0xFD 217 bo → BinstrVecRel bo (.vrelop shI64x2 (.int (.gt .s)))
  -- core-opcode: 0xFD 218 VRELOP
  | i64x2LeS (bo : Bytes) : Bprefixed 0xFD 218 bo → BinstrVecRel bo (.vrelop shI64x2 (.int (.le .s)))
  -- core-opcode: 0xFD 219 VRELOP
  | i64x2GeS (bo : Bytes) : Bprefixed 0xFD 219 bo → BinstrVecRel bo (.vrelop shI64x2 (.int (.ge .s)))

/-! ## `grammar Binstr/vec-*-v128` -/

/-- The bitwise `v128` fragments. -/
inductive BinstrVecV128 : Bytes → Instr → Prop where
  -- core-opcode: 0xFD 77 VVUNOP
  | not (bo : Bytes) : Bprefixed 0xFD 77 bo → BinstrVecV128 bo (.vvunop .v128 .not)
  -- core-opcode: 0xFD 78 VVBINOP
  | and (bo : Bytes) : Bprefixed 0xFD 78 bo → BinstrVecV128 bo (.vvbinop .v128 .and)
  -- core-opcode: 0xFD 79 VVBINOP
  | andnot (bo : Bytes) : Bprefixed 0xFD 79 bo → BinstrVecV128 bo (.vvbinop .v128 .andnot)
  -- core-opcode: 0xFD 80 VVBINOP
  | or (bo : Bytes) : Bprefixed 0xFD 80 bo → BinstrVecV128 bo (.vvbinop .v128 .or)
  -- core-opcode: 0xFD 81 VVBINOP
  | xor (bo : Bytes) : Bprefixed 0xFD 81 bo → BinstrVecV128 bo (.vvbinop .v128 .xor)
  -- core-opcode: 0xFD 82 VVTERNOP
  | bitselect (bo : Bytes) :
      Bprefixed 0xFD 82 bo → BinstrVecV128 bo (.vvternop .v128 .bitselect)
  -- core-opcode: 0xFD 83 VVTESTOP
  | anyTrue (bo : Bytes) :
      Bprefixed 0xFD 83 bo → BinstrVecV128 bo (.vvtestop .v128 .anyTrue)

/-! ## The integer-shape fragments

`vec-un-*`, `vec-test-*`, `vec-bitmask-*`, `vec-narrow-*`, `vec-shift-*`,
`vec-bin-*`, `vec-extun-*`, `vec-ext-*`, `vec-extbin-*` and `vec-exttern-*` at
the four `Jnn` shapes, in the source's order. -/

/-- The `I8 X 16` and `I16 X 8` integer fragments. -/
inductive BinstrVecInt8And16 : Bytes → Instr → Prop where
  -- Binstr/vec-un-i8x16
  -- core-opcode: 0xFD 96 VUNOP
  | i8x16Abs (bo : Bytes) :
      Bprefixed 0xFD 96 bo → BinstrVecInt8And16 bo (.vunop shI8x16 (.int .abs))
  -- core-opcode: 0xFD 97 VUNOP
  | i8x16Neg (bo : Bytes) :
      Bprefixed 0xFD 97 bo → BinstrVecInt8And16 bo (.vunop shI8x16 (.int .neg))
  -- core-opcode: 0xFD 98 VUNOP
  | i8x16Popcnt (bo : Bytes) :
      Bprefixed 0xFD 98 bo → BinstrVecInt8And16 bo (.vunop shI8x16 (.int .popcnt))
  -- Binstr/vec-test-i8x16
  -- core-opcode: 0xFD 99 VTESTOP
  | i8x16AllTrue (bo : Bytes) :
      Bprefixed 0xFD 99 bo → BinstrVecInt8And16 bo (.vtestop shI8x16 (.int .allTrue))
  -- Binstr/vec-bitmask-i8x16
  -- core-opcode: 0xFD 100 VBITMASK
  | i8x16Bitmask (bo : Bytes) :
      Bprefixed 0xFD 100 bo → BinstrVecInt8And16 bo (.vbitmask ishI8x16)
  -- Binstr/vec-narrow-i8x16
  -- core-opcode: 0xFD 101 VNARROW
  | i8x16NarrowI16x8S (bo : Bytes) :
      Bprefixed 0xFD 101 bo → BinstrVecInt8And16 bo (.vnarrow ishI8x16 ishI16x8 .s)
  -- core-opcode: 0xFD 102 VNARROW
  | i8x16NarrowI16x8U (bo : Bytes) :
      Bprefixed 0xFD 102 bo → BinstrVecInt8And16 bo (.vnarrow ishI8x16 ishI16x8 .u)
  -- Binstr/vec-shift-i8x16
  -- core-opcode: 0xFD 107 VSHIFTOP
  | i8x16Shl (bo : Bytes) :
      Bprefixed 0xFD 107 bo → BinstrVecInt8And16 bo (.vshiftop ishI8x16 .shl)
  -- core-opcode: 0xFD 108 VSHIFTOP
  | i8x16ShrS (bo : Bytes) :
      Bprefixed 0xFD 108 bo → BinstrVecInt8And16 bo (.vshiftop ishI8x16 (.shr .s))
  -- core-opcode: 0xFD 109 VSHIFTOP
  | i8x16ShrU (bo : Bytes) :
      Bprefixed 0xFD 109 bo → BinstrVecInt8And16 bo (.vshiftop ishI8x16 (.shr .u))
  -- Binstr/vec-bin-i8x16
  -- core-opcode: 0xFD 110 VBINOP
  | i8x16Add (bo : Bytes) :
      Bprefixed 0xFD 110 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int .add))
  -- core-opcode: 0xFD 111 VBINOP
  | i8x16AddSatS (bo : Bytes) :
      Bprefixed 0xFD 111 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.addSat .s)))
  -- core-opcode: 0xFD 112 VBINOP
  | i8x16AddSatU (bo : Bytes) :
      Bprefixed 0xFD 112 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.addSat .u)))
  -- core-opcode: 0xFD 113 VBINOP
  | i8x16Sub (bo : Bytes) :
      Bprefixed 0xFD 113 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int .sub))
  -- core-opcode: 0xFD 114 VBINOP
  | i8x16SubSatS (bo : Bytes) :
      Bprefixed 0xFD 114 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.subSat .s)))
  -- core-opcode: 0xFD 115 VBINOP
  | i8x16SubSatU (bo : Bytes) :
      Bprefixed 0xFD 115 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.subSat .u)))
  -- core-opcode: 0xFD 118 VBINOP
  | i8x16MinS (bo : Bytes) :
      Bprefixed 0xFD 118 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.min .s)))
  -- core-opcode: 0xFD 119 VBINOP
  | i8x16MinU (bo : Bytes) :
      Bprefixed 0xFD 119 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.min .u)))
  -- core-opcode: 0xFD 120 VBINOP
  | i8x16MaxS (bo : Bytes) :
      Bprefixed 0xFD 120 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.max .s)))
  -- core-opcode: 0xFD 121 VBINOP
  | i8x16MaxU (bo : Bytes) :
      Bprefixed 0xFD 121 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.max .u)))
  -- core-opcode: 0xFD 123 VBINOP
  | i8x16AvgrU (bo : Bytes) :
      Bprefixed 0xFD 123 bo → BinstrVecInt8And16 bo (.vbinop shI8x16 (.int (.avgr .u)))
  -- Binstr/vec-extun-i16x8
  -- core-opcode: 0xFD 124 VEXTUNOP
  | i16x8ExtaddPairwiseI8x16S (bo : Bytes) :
      Bprefixed 0xFD 124 bo →
      BinstrVecInt8And16 bo (.vextunop ishI16x8 ishI8x16 (.extaddPairwise .s))
  -- core-opcode: 0xFD 125 VEXTUNOP
  | i16x8ExtaddPairwiseI8x16U (bo : Bytes) :
      Bprefixed 0xFD 125 bo →
      BinstrVecInt8And16 bo (.vextunop ishI16x8 ishI8x16 (.extaddPairwise .u))
  -- Binstr/vec-un-i16x8
  -- core-opcode: 0xFD 128 VUNOP
  | i16x8Abs (bo : Bytes) :
      Bprefixed 0xFD 128 bo → BinstrVecInt8And16 bo (.vunop shI16x8 (.int .abs))
  -- core-opcode: 0xFD 129 VUNOP
  | i16x8Neg (bo : Bytes) :
      Bprefixed 0xFD 129 bo → BinstrVecInt8And16 bo (.vunop shI16x8 (.int .neg))
  -- Binstr/vec-bin-i16x8
  -- core-opcode: 0xFD 130 VBINOP
  | i16x8Q15mulrSatS (bo : Bytes) :
      Bprefixed 0xFD 130 bo →
      BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.q15mulrSat .s)))
  -- core-opcode: 0xFD 142 VBINOP
  | i16x8Add (bo : Bytes) :
      Bprefixed 0xFD 142 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int .add))
  -- core-opcode: 0xFD 143 VBINOP
  | i16x8AddSatS (bo : Bytes) :
      Bprefixed 0xFD 143 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.addSat .s)))
  -- core-opcode: 0xFD 144 VBINOP
  | i16x8AddSatU (bo : Bytes) :
      Bprefixed 0xFD 144 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.addSat .u)))
  -- core-opcode: 0xFD 145 VBINOP
  | i16x8Sub (bo : Bytes) :
      Bprefixed 0xFD 145 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int .sub))
  -- core-opcode: 0xFD 146 VBINOP
  | i16x8SubSatS (bo : Bytes) :
      Bprefixed 0xFD 146 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.subSat .s)))
  -- core-opcode: 0xFD 147 VBINOP
  | i16x8SubSatU (bo : Bytes) :
      Bprefixed 0xFD 147 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.subSat .u)))
  -- core-opcode: 0xFD 149 VBINOP
  | i16x8Mul (bo : Bytes) :
      Bprefixed 0xFD 149 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int .mul))
  -- core-opcode: 0xFD 150 VBINOP
  | i16x8MinS (bo : Bytes) :
      Bprefixed 0xFD 150 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.min .s)))
  -- core-opcode: 0xFD 151 VBINOP
  | i16x8MinU (bo : Bytes) :
      Bprefixed 0xFD 151 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.min .u)))
  -- core-opcode: 0xFD 152 VBINOP
  | i16x8MaxS (bo : Bytes) :
      Bprefixed 0xFD 152 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.max .s)))
  -- core-opcode: 0xFD 153 VBINOP
  | i16x8MaxU (bo : Bytes) :
      Bprefixed 0xFD 153 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.max .u)))
  -- core-opcode: 0xFD 155 VBINOP
  | i16x8AvgrU (bo : Bytes) :
      Bprefixed 0xFD 155 bo → BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.avgr .u)))
  -- core-opcode: 0xFD 273 VBINOP
  | i16x8RelaxedQ15mulrS (bo : Bytes) :
      Bprefixed 0xFD 273 bo →
      BinstrVecInt8And16 bo (.vbinop shI16x8 (.int (.relaxedQ15mulr .s)))
  -- Binstr/vec-test-i16x8
  -- core-opcode: 0xFD 131 VTESTOP
  | i16x8AllTrue (bo : Bytes) :
      Bprefixed 0xFD 131 bo → BinstrVecInt8And16 bo (.vtestop shI16x8 (.int .allTrue))
  -- Binstr/vec-bitmask-i16x8
  -- core-opcode: 0xFD 132 VBITMASK
  | i16x8Bitmask (bo : Bytes) :
      Bprefixed 0xFD 132 bo → BinstrVecInt8And16 bo (.vbitmask ishI16x8)
  -- Binstr/vec-narrow-i16x8
  -- core-opcode: 0xFD 133 VNARROW
  | i16x8NarrowI32x4S (bo : Bytes) :
      Bprefixed 0xFD 133 bo → BinstrVecInt8And16 bo (.vnarrow ishI16x8 ishI32x4 .s)
  -- core-opcode: 0xFD 134 VNARROW
  | i16x8NarrowI32x4U (bo : Bytes) :
      Bprefixed 0xFD 134 bo → BinstrVecInt8And16 bo (.vnarrow ishI16x8 ishI32x4 .u)
  -- Binstr/vec-ext-i16x8
  -- core-opcode: 0xFD 135 VCVTOP
  | i16x8ExtendLowI8x16S (bo : Bytes) :
      Bprefixed 0xFD 135 bo →
      BinstrVecInt8And16 bo (.vcvtop shI16x8 shI8x16 (.jj (.extend .low .s)))
  -- core-opcode: 0xFD 136 VCVTOP
  | i16x8ExtendHighI8x16S (bo : Bytes) :
      Bprefixed 0xFD 136 bo →
      BinstrVecInt8And16 bo (.vcvtop shI16x8 shI8x16 (.jj (.extend .high .s)))
  -- core-opcode: 0xFD 137 VCVTOP
  | i16x8ExtendLowI8x16U (bo : Bytes) :
      Bprefixed 0xFD 137 bo →
      BinstrVecInt8And16 bo (.vcvtop shI16x8 shI8x16 (.jj (.extend .low .u)))
  -- core-opcode: 0xFD 138 VCVTOP
  | i16x8ExtendHighI8x16U (bo : Bytes) :
      Bprefixed 0xFD 138 bo →
      BinstrVecInt8And16 bo (.vcvtop shI16x8 shI8x16 (.jj (.extend .high .u)))
  -- Binstr/vec-shift-i16x8
  -- core-opcode: 0xFD 139 VSHIFTOP
  | i16x8Shl (bo : Bytes) :
      Bprefixed 0xFD 139 bo → BinstrVecInt8And16 bo (.vshiftop ishI16x8 .shl)
  -- core-opcode: 0xFD 140 VSHIFTOP
  | i16x8ShrS (bo : Bytes) :
      Bprefixed 0xFD 140 bo → BinstrVecInt8And16 bo (.vshiftop ishI16x8 (.shr .s))
  -- core-opcode: 0xFD 141 VSHIFTOP
  | i16x8ShrU (bo : Bytes) :
      Bprefixed 0xFD 141 bo → BinstrVecInt8And16 bo (.vshiftop ishI16x8 (.shr .u))
  -- Binstr/vec-extbin-i16x8
  -- core-opcode: 0xFD 156 VEXTBINOP
  | i16x8ExtmulLowI8x16S (bo : Bytes) :
      Bprefixed 0xFD 156 bo →
      BinstrVecInt8And16 bo (.vextbinop ishI16x8 ishI8x16 (.extmul .low .s))
  -- core-opcode: 0xFD 157 VEXTBINOP
  | i16x8ExtmulHighI8x16S (bo : Bytes) :
      Bprefixed 0xFD 157 bo →
      BinstrVecInt8And16 bo (.vextbinop ishI16x8 ishI8x16 (.extmul .high .s))
  -- core-opcode: 0xFD 158 VEXTBINOP
  | i16x8ExtmulLowI8x16U (bo : Bytes) :
      Bprefixed 0xFD 158 bo →
      BinstrVecInt8And16 bo (.vextbinop ishI16x8 ishI8x16 (.extmul .low .u))
  -- core-opcode: 0xFD 159 VEXTBINOP
  | i16x8ExtmulHighI8x16U (bo : Bytes) :
      Bprefixed 0xFD 159 bo →
      BinstrVecInt8And16 bo (.vextbinop ishI16x8 ishI8x16 (.extmul .high .u))
  -- core-opcode: 0xFD 274 VEXTBINOP
  | i16x8RelaxedDotI8x16S (bo : Bytes) :
      Bprefixed 0xFD 274 bo →
      BinstrVecInt8And16 bo (.vextbinop ishI16x8 ishI8x16 (.relaxedDot .s))

/-- The `I32 X 4` and `I64 X 2` integer fragments. -/
inductive BinstrVecInt32And64 : Bytes → Instr → Prop where
  -- Binstr/vec-extun-i32x4
  -- core-opcode: 0xFD 126 VEXTUNOP
  | i32x4ExtaddPairwiseI16x8S (bo : Bytes) :
      Bprefixed 0xFD 126 bo →
      BinstrVecInt32And64 bo (.vextunop ishI32x4 ishI16x8 (.extaddPairwise .s))
  -- core-opcode: 0xFD 127 VEXTUNOP
  | i32x4ExtaddPairwiseI16x8U (bo : Bytes) :
      Bprefixed 0xFD 127 bo →
      BinstrVecInt32And64 bo (.vextunop ishI32x4 ishI16x8 (.extaddPairwise .u))
  -- Binstr/vec-un-i32x4
  -- core-opcode: 0xFD 160 VUNOP
  | i32x4Abs (bo : Bytes) :
      Bprefixed 0xFD 160 bo → BinstrVecInt32And64 bo (.vunop shI32x4 (.int .abs))
  -- core-opcode: 0xFD 161 VUNOP
  | i32x4Neg (bo : Bytes) :
      Bprefixed 0xFD 161 bo → BinstrVecInt32And64 bo (.vunop shI32x4 (.int .neg))
  -- Binstr/vec-test-i32x4
  -- core-opcode: 0xFD 163 VTESTOP
  | i32x4AllTrue (bo : Bytes) :
      Bprefixed 0xFD 163 bo → BinstrVecInt32And64 bo (.vtestop shI32x4 (.int .allTrue))
  -- Binstr/vec-bitmask-i32x4
  -- core-opcode: 0xFD 164 VBITMASK
  | i32x4Bitmask (bo : Bytes) :
      Bprefixed 0xFD 164 bo → BinstrVecInt32And64 bo (.vbitmask ishI32x4)
  -- Binstr/vec-ext-i32x4
  -- core-opcode: 0xFD 167 VCVTOP
  | i32x4ExtendLowI16x8S (bo : Bytes) :
      Bprefixed 0xFD 167 bo →
      BinstrVecInt32And64 bo (.vcvtop shI32x4 shI16x8 (.jj (.extend .low .s)))
  -- core-opcode: 0xFD 168 VCVTOP
  | i32x4ExtendHighI16x8S (bo : Bytes) :
      Bprefixed 0xFD 168 bo →
      BinstrVecInt32And64 bo (.vcvtop shI32x4 shI16x8 (.jj (.extend .high .s)))
  -- core-opcode: 0xFD 169 VCVTOP
  | i32x4ExtendLowI16x8U (bo : Bytes) :
      Bprefixed 0xFD 169 bo →
      BinstrVecInt32And64 bo (.vcvtop shI32x4 shI16x8 (.jj (.extend .low .u)))
  -- core-opcode: 0xFD 170 VCVTOP
  | i32x4ExtendHighI16x8U (bo : Bytes) :
      Bprefixed 0xFD 170 bo →
      BinstrVecInt32And64 bo (.vcvtop shI32x4 shI16x8 (.jj (.extend .high .u)))
  -- Binstr/vec-shift-i32x4
  -- core-opcode: 0xFD 171 VSHIFTOP
  | i32x4Shl (bo : Bytes) :
      Bprefixed 0xFD 171 bo → BinstrVecInt32And64 bo (.vshiftop ishI32x4 .shl)
  -- core-opcode: 0xFD 172 VSHIFTOP
  | i32x4ShrS (bo : Bytes) :
      Bprefixed 0xFD 172 bo → BinstrVecInt32And64 bo (.vshiftop ishI32x4 (.shr .s))
  -- core-opcode: 0xFD 173 VSHIFTOP
  | i32x4ShrU (bo : Bytes) :
      Bprefixed 0xFD 173 bo → BinstrVecInt32And64 bo (.vshiftop ishI32x4 (.shr .u))
  -- Binstr/vec-bin-i32x4
  -- core-opcode: 0xFD 174 VBINOP
  | i32x4Add (bo : Bytes) :
      Bprefixed 0xFD 174 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int .add))
  -- core-opcode: 0xFD 177 VBINOP
  | i32x4Sub (bo : Bytes) :
      Bprefixed 0xFD 177 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int .sub))
  -- core-opcode: 0xFD 181 VBINOP
  | i32x4Mul (bo : Bytes) :
      Bprefixed 0xFD 181 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int .mul))
  -- core-opcode: 0xFD 182 VBINOP
  | i32x4MinS (bo : Bytes) :
      Bprefixed 0xFD 182 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int (.min .s)))
  -- core-opcode: 0xFD 183 VBINOP
  | i32x4MinU (bo : Bytes) :
      Bprefixed 0xFD 183 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int (.min .u)))
  -- core-opcode: 0xFD 184 VBINOP
  | i32x4MaxS (bo : Bytes) :
      Bprefixed 0xFD 184 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int (.max .s)))
  -- core-opcode: 0xFD 185 VBINOP
  | i32x4MaxU (bo : Bytes) :
      Bprefixed 0xFD 185 bo → BinstrVecInt32And64 bo (.vbinop shI32x4 (.int (.max .u)))
  -- Binstr/vec-extbin-i32x4
  -- core-opcode: 0xFD 186 VEXTBINOP
  | i32x4DotI16x8S (bo : Bytes) :
      Bprefixed 0xFD 186 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI32x4 ishI16x8 (.dot .s))
  -- core-opcode: 0xFD 188 VEXTBINOP
  | i32x4ExtmulLowI16x8S (bo : Bytes) :
      Bprefixed 0xFD 188 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI32x4 ishI16x8 (.extmul .low .s))
  -- core-opcode: 0xFD 189 VEXTBINOP
  | i32x4ExtmulHighI16x8S (bo : Bytes) :
      Bprefixed 0xFD 189 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI32x4 ishI16x8 (.extmul .high .s))
  -- core-opcode: 0xFD 190 VEXTBINOP
  | i32x4ExtmulLowI16x8U (bo : Bytes) :
      Bprefixed 0xFD 190 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI32x4 ishI16x8 (.extmul .low .u))
  -- core-opcode: 0xFD 191 VEXTBINOP
  | i32x4ExtmulHighI16x8U (bo : Bytes) :
      Bprefixed 0xFD 191 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI32x4 ishI16x8 (.extmul .high .u))
  -- Binstr/vec-exttern-i32x4
  -- core-opcode: 0xFD 275 VEXTTERNOP
  | i32x4RelaxedDotAddI16x8S (bo : Bytes) :
      Bprefixed 0xFD 275 bo →
      BinstrVecInt32And64 bo (.vextternop ishI32x4 ishI16x8 (.relaxedDotAdd .s))
  -- Binstr/vec-un-i64x2
  -- core-opcode: 0xFD 192 VUNOP
  | i64x2Abs (bo : Bytes) :
      Bprefixed 0xFD 192 bo → BinstrVecInt32And64 bo (.vunop shI64x2 (.int .abs))
  -- core-opcode: 0xFD 193 VUNOP
  | i64x2Neg (bo : Bytes) :
      Bprefixed 0xFD 193 bo → BinstrVecInt32And64 bo (.vunop shI64x2 (.int .neg))
  -- Binstr/vec-test-i64x2
  -- core-opcode: 0xFD 195 VTESTOP
  | i64x2AllTrue (bo : Bytes) :
      Bprefixed 0xFD 195 bo → BinstrVecInt32And64 bo (.vtestop shI64x2 (.int .allTrue))
  -- Binstr/vec-bitmask-i64x2
  -- core-opcode: 0xFD 196 VBITMASK
  | i64x2Bitmask (bo : Bytes) :
      Bprefixed 0xFD 196 bo → BinstrVecInt32And64 bo (.vbitmask ishI64x2)
  -- Binstr/vec-ext-i64x2
  -- core-opcode: 0xFD 199 VCVTOP
  | i64x2ExtendLowI32x4S (bo : Bytes) :
      Bprefixed 0xFD 199 bo →
      BinstrVecInt32And64 bo (.vcvtop shI64x2 shI32x4 (.jj (.extend .low .s)))
  -- core-opcode: 0xFD 200 VCVTOP
  | i64x2ExtendHighI32x4S (bo : Bytes) :
      Bprefixed 0xFD 200 bo →
      BinstrVecInt32And64 bo (.vcvtop shI64x2 shI32x4 (.jj (.extend .high .s)))
  -- core-opcode: 0xFD 201 VCVTOP
  | i64x2ExtendLowI32x4U (bo : Bytes) :
      Bprefixed 0xFD 201 bo →
      BinstrVecInt32And64 bo (.vcvtop shI64x2 shI32x4 (.jj (.extend .low .u)))
  -- core-opcode: 0xFD 202 VCVTOP
  | i64x2ExtendHighI32x4U (bo : Bytes) :
      Bprefixed 0xFD 202 bo →
      BinstrVecInt32And64 bo (.vcvtop shI64x2 shI32x4 (.jj (.extend .high .u)))
  -- Binstr/vec-shift-i64x2
  -- core-opcode: 0xFD 203 VSHIFTOP
  | i64x2Shl (bo : Bytes) :
      Bprefixed 0xFD 203 bo → BinstrVecInt32And64 bo (.vshiftop ishI64x2 .shl)
  -- core-opcode: 0xFD 204 VSHIFTOP
  | i64x2ShrS (bo : Bytes) :
      Bprefixed 0xFD 204 bo → BinstrVecInt32And64 bo (.vshiftop ishI64x2 (.shr .s))
  -- core-opcode: 0xFD 205 VSHIFTOP
  | i64x2ShrU (bo : Bytes) :
      Bprefixed 0xFD 205 bo → BinstrVecInt32And64 bo (.vshiftop ishI64x2 (.shr .u))
  -- Binstr/vec-bin-i64x2
  -- core-opcode: 0xFD 206 VBINOP
  | i64x2Add (bo : Bytes) :
      Bprefixed 0xFD 206 bo → BinstrVecInt32And64 bo (.vbinop shI64x2 (.int .add))
  -- core-opcode: 0xFD 209 VBINOP
  | i64x2Sub (bo : Bytes) :
      Bprefixed 0xFD 209 bo → BinstrVecInt32And64 bo (.vbinop shI64x2 (.int .sub))
  -- core-opcode: 0xFD 213 VBINOP
  | i64x2Mul (bo : Bytes) :
      Bprefixed 0xFD 213 bo → BinstrVecInt32And64 bo (.vbinop shI64x2 (.int .mul))
  -- Binstr/vec-extbin-i64x2
  -- core-opcode: 0xFD 220 VEXTBINOP
  | i64x2ExtmulLowI32x4S (bo : Bytes) :
      Bprefixed 0xFD 220 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI64x2 ishI32x4 (.extmul .low .s))
  -- core-opcode: 0xFD 221 VEXTBINOP
  | i64x2ExtmulHighI32x4S (bo : Bytes) :
      Bprefixed 0xFD 221 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI64x2 ishI32x4 (.extmul .high .s))
  -- core-opcode: 0xFD 222 VEXTBINOP
  | i64x2ExtmulLowI32x4U (bo : Bytes) :
      Bprefixed 0xFD 222 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI64x2 ishI32x4 (.extmul .low .u))
  -- core-opcode: 0xFD 223 VEXTBINOP
  | i64x2ExtmulHighI32x4U (bo : Bytes) :
      Bprefixed 0xFD 223 bo →
      BinstrVecInt32And64 bo (.vextbinop ishI64x2 ishI32x4 (.extmul .high .u))

/-! ## The floating-shape fragments and `vec-cvt` -/

/-- The `F32 X 4` and `F64 X 2` fragments, and the vector conversions. -/
inductive BinstrVecFloat : Bytes → Instr → Prop where
  -- Binstr/vec-un-f32x4
  -- core-opcode: 0xFD 103 VUNOP
  | f32x4Ceil (bo : Bytes) :
      Bprefixed 0xFD 103 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .ceil))
  -- core-opcode: 0xFD 104 VUNOP
  | f32x4Floor (bo : Bytes) :
      Bprefixed 0xFD 104 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .floor))
  -- core-opcode: 0xFD 105 VUNOP
  | f32x4Trunc (bo : Bytes) :
      Bprefixed 0xFD 105 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .trunc))
  -- core-opcode: 0xFD 106 VUNOP
  | f32x4Nearest (bo : Bytes) :
      Bprefixed 0xFD 106 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .nearest))
  -- core-opcode: 0xFD 224 VUNOP
  | f32x4Abs (bo : Bytes) :
      Bprefixed 0xFD 224 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .abs))
  -- core-opcode: 0xFD 225 VUNOP
  | f32x4Neg (bo : Bytes) :
      Bprefixed 0xFD 225 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .neg))
  -- core-opcode: 0xFD 227 VUNOP
  | f32x4Sqrt (bo : Bytes) :
      Bprefixed 0xFD 227 bo → BinstrVecFloat bo (.vunop shF32x4 (.float .sqrt))
  -- Binstr/vec-bin-f32x4
  -- core-opcode: 0xFD 228 VBINOP
  | f32x4Add (bo : Bytes) :
      Bprefixed 0xFD 228 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .add))
  -- core-opcode: 0xFD 229 VBINOP
  | f32x4Sub (bo : Bytes) :
      Bprefixed 0xFD 229 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .sub))
  -- core-opcode: 0xFD 230 VBINOP
  | f32x4Mul (bo : Bytes) :
      Bprefixed 0xFD 230 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .mul))
  -- core-opcode: 0xFD 231 VBINOP
  | f32x4Div (bo : Bytes) :
      Bprefixed 0xFD 231 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .div))
  -- core-opcode: 0xFD 232 VBINOP
  | f32x4Min (bo : Bytes) :
      Bprefixed 0xFD 232 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .min))
  -- core-opcode: 0xFD 233 VBINOP
  | f32x4Max (bo : Bytes) :
      Bprefixed 0xFD 233 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .max))
  -- core-opcode: 0xFD 234 VBINOP
  | f32x4Pmin (bo : Bytes) :
      Bprefixed 0xFD 234 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .pmin))
  -- core-opcode: 0xFD 235 VBINOP
  | f32x4Pmax (bo : Bytes) :
      Bprefixed 0xFD 235 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .pmax))
  -- core-opcode: 0xFD 269 VBINOP
  | f32x4RelaxedMin (bo : Bytes) :
      Bprefixed 0xFD 269 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .relaxedMin))
  -- core-opcode: 0xFD 270 VBINOP
  | f32x4RelaxedMax (bo : Bytes) :
      Bprefixed 0xFD 270 bo → BinstrVecFloat bo (.vbinop shF32x4 (.float .relaxedMax))
  -- Binstr/vec-tern-f32x4
  -- core-opcode: 0xFD 261 VTERNOP
  | f32x4RelaxedMadd (bo : Bytes) :
      Bprefixed 0xFD 261 bo → BinstrVecFloat bo (.vternop shF32x4 (.float .relaxedMadd))
  -- core-opcode: 0xFD 262 VTERNOP
  | f32x4RelaxedNmadd (bo : Bytes) :
      Bprefixed 0xFD 262 bo → BinstrVecFloat bo (.vternop shF32x4 (.float .relaxedNmadd))
  -- Binstr/vec-un-f64x2
  -- core-opcode: 0xFD 116 VUNOP
  | f64x2Ceil (bo : Bytes) :
      Bprefixed 0xFD 116 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .ceil))
  -- core-opcode: 0xFD 117 VUNOP
  | f64x2Floor (bo : Bytes) :
      Bprefixed 0xFD 117 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .floor))
  -- core-opcode: 0xFD 122 VUNOP
  | f64x2Trunc (bo : Bytes) :
      Bprefixed 0xFD 122 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .trunc))
  -- core-opcode: 0xFD 148 VUNOP
  | f64x2Nearest (bo : Bytes) :
      Bprefixed 0xFD 148 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .nearest))
  -- core-opcode: 0xFD 236 VUNOP
  | f64x2Abs (bo : Bytes) :
      Bprefixed 0xFD 236 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .abs))
  -- core-opcode: 0xFD 237 VUNOP
  | f64x2Neg (bo : Bytes) :
      Bprefixed 0xFD 237 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .neg))
  -- core-opcode: 0xFD 239 VUNOP
  | f64x2Sqrt (bo : Bytes) :
      Bprefixed 0xFD 239 bo → BinstrVecFloat bo (.vunop shF64x2 (.float .sqrt))
  -- Binstr/vec-bin-f64x2
  -- core-opcode: 0xFD 240 VBINOP
  | f64x2Add (bo : Bytes) :
      Bprefixed 0xFD 240 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .add))
  -- core-opcode: 0xFD 241 VBINOP
  | f64x2Sub (bo : Bytes) :
      Bprefixed 0xFD 241 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .sub))
  -- core-opcode: 0xFD 242 VBINOP
  | f64x2Mul (bo : Bytes) :
      Bprefixed 0xFD 242 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .mul))
  -- core-opcode: 0xFD 243 VBINOP
  | f64x2Div (bo : Bytes) :
      Bprefixed 0xFD 243 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .div))
  -- core-opcode: 0xFD 244 VBINOP
  | f64x2Min (bo : Bytes) :
      Bprefixed 0xFD 244 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .min))
  -- core-opcode: 0xFD 245 VBINOP
  | f64x2Max (bo : Bytes) :
      Bprefixed 0xFD 245 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .max))
  -- core-opcode: 0xFD 246 VBINOP
  | f64x2Pmin (bo : Bytes) :
      Bprefixed 0xFD 246 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .pmin))
  -- core-opcode: 0xFD 247 VBINOP
  | f64x2Pmax (bo : Bytes) :
      Bprefixed 0xFD 247 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .pmax))
  -- core-opcode: 0xFD 271 VBINOP
  | f64x2RelaxedMin (bo : Bytes) :
      Bprefixed 0xFD 271 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .relaxedMin))
  -- core-opcode: 0xFD 272 VBINOP
  | f64x2RelaxedMax (bo : Bytes) :
      Bprefixed 0xFD 272 bo → BinstrVecFloat bo (.vbinop shF64x2 (.float .relaxedMax))
  -- Binstr/vec-tern-f64x2
  -- core-opcode: 0xFD 263 VTERNOP
  | f64x2RelaxedMadd (bo : Bytes) :
      Bprefixed 0xFD 263 bo → BinstrVecFloat bo (.vternop shF64x2 (.float .relaxedMadd))
  -- core-opcode: 0xFD 264 VTERNOP
  | f64x2RelaxedNmadd (bo : Bytes) :
      Bprefixed 0xFD 264 bo → BinstrVecFloat bo (.vternop shF64x2 (.float .relaxedNmadd))
  -- core-opcode: 0xFD 265 VTERNOP
  | i8x16RelaxedLaneselect (bo : Bytes) :
      Bprefixed 0xFD 265 bo →
      BinstrVecFloat bo (.vternop shI8x16 (.int .relaxedLaneselect))
  -- core-opcode: 0xFD 266 VTERNOP
  | i16x8RelaxedLaneselect (bo : Bytes) :
      Bprefixed 0xFD 266 bo →
      BinstrVecFloat bo (.vternop shI16x8 (.int .relaxedLaneselect))
  -- core-opcode: 0xFD 267 VTERNOP
  | i32x4RelaxedLaneselect (bo : Bytes) :
      Bprefixed 0xFD 267 bo →
      BinstrVecFloat bo (.vternop shI32x4 (.int .relaxedLaneselect))
  -- core-opcode: 0xFD 268 VTERNOP
  | i64x2RelaxedLaneselect (bo : Bytes) :
      Bprefixed 0xFD 268 bo →
      BinstrVecFloat bo (.vternop shI64x2 (.int .relaxedLaneselect))
  -- Binstr/vec-cvt
  -- core-opcode: 0xFD 94 VCVTOP
  | f32x4DemoteF64x2Zero (bo : Bytes) :
      Bprefixed 0xFD 94 bo →
      BinstrVecFloat bo (.vcvtop shF32x4 shF64x2 (.ff (.demote .zero)))
  -- core-opcode: 0xFD 95 VCVTOP
  | f64x2PromoteLowF32x4 (bo : Bytes) :
      Bprefixed 0xFD 95 bo →
      BinstrVecFloat bo (.vcvtop shF64x2 shF32x4 (.ff (.promote .low)))
  -- core-opcode: 0xFD 248 VCVTOP
  | i32x4TruncSatF32x4S (bo : Bytes) :
      Bprefixed 0xFD 248 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF32x4 (.fj (.truncSat .s none)))
  -- core-opcode: 0xFD 249 VCVTOP
  | i32x4TruncSatF32x4U (bo : Bytes) :
      Bprefixed 0xFD 249 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF32x4 (.fj (.truncSat .u none)))
  -- core-opcode: 0xFD 250 VCVTOP
  | f32x4ConvertI32x4S (bo : Bytes) :
      Bprefixed 0xFD 250 bo →
      BinstrVecFloat bo (.vcvtop shF32x4 shI32x4 (.jf (.convert none .s)))
  -- core-opcode: 0xFD 251 VCVTOP
  | f32x4ConvertI32x4U (bo : Bytes) :
      Bprefixed 0xFD 251 bo →
      BinstrVecFloat bo (.vcvtop shF32x4 shI32x4 (.jf (.convert none .u)))
  -- core-opcode: 0xFD 252 VCVTOP
  | i32x4TruncSatF64x2SZero (bo : Bytes) :
      Bprefixed 0xFD 252 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF64x2 (.fj (.truncSat .s (some .zero))))
  -- core-opcode: 0xFD 253 VCVTOP
  | i32x4TruncSatF64x2UZero (bo : Bytes) :
      Bprefixed 0xFD 253 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF64x2 (.fj (.truncSat .u (some .zero))))
  -- core-opcode: 0xFD 254 VCVTOP
  | f64x2ConvertLowI32x4S (bo : Bytes) :
      Bprefixed 0xFD 254 bo →
      BinstrVecFloat bo (.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .s)))
  -- core-opcode: 0xFD 255 VCVTOP
  | f64x2ConvertLowI32x4U (bo : Bytes) :
      Bprefixed 0xFD 255 bo →
      BinstrVecFloat bo (.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .u)))
  -- core-opcode: 0xFD 257 VCVTOP
  | i32x4RelaxedTruncF32x4S (bo : Bytes) :
      Bprefixed 0xFD 257 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .s none)))
  -- core-opcode: 0xFD 258 VCVTOP
  | i32x4RelaxedTruncF32x4U (bo : Bytes) :
      Bprefixed 0xFD 258 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .u none)))
  -- core-opcode: 0xFD 259 VCVTOP
  | i32x4RelaxedTruncF64x2SZero (bo : Bytes) :
      Bprefixed 0xFD 259 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .s (some .zero))))
  -- core-opcode: 0xFD 260 VCVTOP
  | i32x4RelaxedTruncF64x2UZero (bo : Bytes) :
      Bprefixed 0xFD 260 bo →
      BinstrVecFloat bo (.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .u (some .zero))))

end WasmGemmGnaf.Wasm.Core.Binary
