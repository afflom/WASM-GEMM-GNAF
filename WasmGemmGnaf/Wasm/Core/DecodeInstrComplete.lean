/-
  Wasm/Core/DecodeInstrComplete.lean --- COMPLETENESS of the executable Core 3.0
  instruction decoder against the declarative binary grammar.

  WHAT THIS FILE ADDS.  `Wasm/Core/DecodeInstructions.lean` proves
  `decInstr_sound`: whatever the decoder accepts is derivable in the pinned
  grammar.  That direction alone would be satisfied by a decoder that rejects
  everything.  This file proves the other direction for the whole instruction
  format:

      decInstr_complete : Binstr b i -> b.length <= d ->
                          decInstr d (b ++ r) = .ok (i, r)

  -- every derivation of the pinned `Binstr`, INCLUDING the `0xFB` garbage
  collection space and the 256 `0xFD` SIMD productions, is decoded, to the value
  the grammar gives it, consuming exactly the derivation's bytes and handing the
  rest back untouched.

  HOW IT IS ORGANISED.  `Binstr` is the union of five recursive constructors
  (`BLOCK`, `LOOP`, the two `IF`s, `TRY_TABLE`) and nineteen non-recursive
  fragments.  `decInstrFlat` of `DecodeInstructions.lean` decodes exactly the
  nineteen; `flat_BinstrX` below is one theorem per fragment, proved by a case
  analysis with one line per pinned production, and `decInstr_complete` is then
  an induction on the byte length with twenty-four cases.

  THE GRAMMAR IS NOT CONSULTED FOR THE DECODER, AND THE DECODER IS NOT CONSULTED
  FOR THE GRAMMAR.  Nothing under `Wasm/Core/BinaryGrammar/` imports anything
  from this file or from `Decode*.lean`, and no proof below routes through an
  encoder -- there is no encoder in this import graph at all.  That is the
  property `xtask independence` checks, and it is the whole content of a
  completeness theorem.

  TWO FACTS THE PROOF NEEDS AND ESTABLISHES RATHER THAN ASSUMES.

  * `Binstr_ne_nil` -- no production of the pinned grammar derives the empty
    byte sequence.  It is obtained from the fragment lemmas themselves: if a
    fragment derived `eps`, the decoder would have to accept the empty input,
    and `decInstrFlat [] = .error .eof`.
  * `Binstrs_length_le` -- an instruction sequence has no more instructions than
    it has bytes, which is what makes the decoder's length-derived fuel enough.
-/
import WasmGemmGnaf.Wasm.Core.DecodeInstructions

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Entering the flat dispatch

Four lemmas, one per shape a non-recursive production can have: a bare opcode
byte, an opcode byte with immediates, and the two prefixed spaces. -/

/-- A single-byte production with no immediate. -/
theorem flat_op0 {v : Nat} {i : Instr} (hv : v < 0x100) (h : op0 v = some i)
    (r : Bytes) : decInstrFlat (tb v :: r) = .ok (i, r) := by
  rw [decInstrFlat, tb_val v hv, h]

/-- A single-byte production with immediates. -/
theorem flat_op1 {v : Nat} {i : Instr} (hv : v < 0x100) (h0 : op0 v = none)
    (h1 : ¬ (v = 0xFB)) (h2 : ¬ (v = 0xFC)) (h3 : ¬ (v = 0xFD))
    (bb r : Bytes) (h : decOp1 v (bb ++ r) = .ok (i, r)) :
    decInstrFlat (tb v :: (bb ++ r)) = .ok (i, r) := by
  rw [decInstrFlat, tb_val v hv, h0]
  simp only [if_neg h1, if_neg h2, if_neg h3]
  exact h

/-- A `0xFB` production. -/
theorem flat_FB {k : Nat} {bo : Bytes} (hbo : Bprefixed 0xFB k bo) (bb r : Bytes)
    {i : Instr} (h : decFBbody k (bb ++ r) = .ok (i, r)) :
    decInstrFlat (bo ++ (bb ++ r)) = .ok (i, r) := by
  obtain ⟨bn, hbn, x, hx, hxk⟩ := hbo
  subst hbn
  subst hxk
  show decInstrFlat (tb 0xFB :: (bn ++ (bb ++ r))) = _
  rw [decInstrFlat, tb_val 0xFB (by decide),
    show op0 (0xFB : Nat) = none from rfl, if_pos rfl,
    decU32_complete bn x (bb ++ r) hx]
  exact h

/-- A `0xFC` production. -/
theorem flat_FC {k : Nat} {bo : Bytes} (hbo : Bprefixed 0xFC k bo) (bb r : Bytes)
    {i : Instr} (h : decFCbody k (bb ++ r) = .ok (i, r)) :
    decInstrFlat (bo ++ (bb ++ r)) = .ok (i, r) := by
  obtain ⟨bn, hbn, x, hx, hxk⟩ := hbo
  subst hbn
  subst hxk
  show decInstrFlat (tb 0xFC :: (bn ++ (bb ++ r))) = _
  rw [decInstrFlat, tb_val 0xFC (by decide),
    show op0 (0xFC : Nat) = none from rfl, if_neg (by decide : ¬ ((0xFC : Nat) = 0xFB)),
    if_pos rfl, decU32_complete bn x (bb ++ r) hx]
  exact h

/-- A `0xFD` production. -/
theorem flat_FD {k : Nat} {bo : Bytes} (hbo : Bprefixed 0xFD k bo) (bb r : Bytes)
    {i : Instr} (h : decFDbody k (bb ++ r) = .ok (i, r)) :
    decInstrFlat (bo ++ (bb ++ r)) = .ok (i, r) := by
  obtain ⟨bn, hbn, x, hx, hxk⟩ := hbo
  subst hbn
  subst hxk
  show decInstrFlat (tb 0xFD :: (bn ++ (bb ++ r))) = _
  rw [decInstrFlat, tb_val 0xFD (by decide),
    show op0 (0xFD : Nat) = none from rfl, if_neg (by decide : ¬ ((0xFD : Nat) = 0xFB)),
    if_neg (by decide : ¬ ((0xFD : Nat) = 0xFC)), if_pos rfl,
    decU32_complete bn x (bb ++ r) hx]
  exact h

/-! ## The two `0xFD` productions that are not an `argN` shape -/

theorem decV128Const_complete (c : VecLit Vnn.v128) (bl : List Byte) (bb r : Bytes)
    (hrep : Rep Bbyte 16 bb bl) (hc : c.val = leNat bl) :
    decFDbody 12 (bb ++ r) = .ok (Instr.vconst .v128 c, r) := by
  have hlt : leNat bl < 2 ^ 128 := by rw [← hc]; exact c.property
  have hc' : (⟨leNat bl, hlt⟩ : VecLit Vnn.v128) = c := Subtype.ext hc.symm
  show decV128Const (bb ++ r) = _
  simp only [decV128Const, decBytes_complete 16 bb bl r hrep, dif_pos hlt, hc']

theorem decShuffle_complete (ls : List LaneIdx) (bl r : Bytes)
    (hrep : Rep Blaneidx 16 bl ls) :
    decFDbody 13 (bl ++ r) = .ok (Instr.vshuffle bshI8x16 ls, r) := by
  show decShuffle (bl ++ r) = _
  simp only [decShuffle, decRep_complete decLaneIdx_complete 16 bl ls r hrep]

/-! ## Completeness of the flat dispatch, fragment by fragment

One theorem per `grammar Binstr/<fragment>` group of the pinned source, and one
line per alternative of that group. -/

/-- Completeness of the flat dispatch on `BinstrParametric`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrParametric {b : Bytes} {i : Instr} (h : BinstrParametric b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | unreachable  =>
      exact flat_op0 (v := 0x00) (by decide) rfl r
  | nop  =>
      exact flat_op0 (v := 0x01) (by decide) rfl r
  | drop  =>
      exact flat_op0 (v := 0x1A) (by decide) rfl r
  | select  =>
      exact flat_op0 (v := 0x1B) (by decide) rfl r
  | selectT bs ts hh1 =>
      have h' : decOp1 0x1C ((bs) ++ r) = .ok (Instr.select (some ts), r) :=
        arg1_complete (decList_complete decValtype_complete) _ r hh1
      exact flat_op1 (v := 0x1C) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'

/-- Completeness of the flat dispatch on `BinstrControl`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrControl {b : Bytes} {i : Instr} (h : BinstrControl b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | throw bs x hh1 =>
      have h' : decOp1 0x08 ((bs) ++ r) = .ok (Instr.throw x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x08) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | throwRef  =>
      exact flat_op0 (v := 0x0A) (by decide) rfl r
  | br bs l hh1 =>
      have h' : decOp1 0x0C ((bs) ++ r) = .ok (Instr.br l, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x0C) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | brIf bs l hh1 =>
      have h' : decOp1 0x0D ((bs) ++ r) = .ok (Instr.brIf l, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x0D) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | brTable bl bn ls l hh1 hh2 =>
      have h' : decOp1 0x0E ((bl ++ bn) ++ r) = .ok (Instr.brTable ls l, r) :=
        arg2_complete (decList_complete decIdx_complete) decIdx_complete _ r hh1 hh2
      exact flat_op1 (v := 0x0E) (by decide) rfl (by decide) (by decide) (by decide)
        (bl ++ bn) r h'
  | ret  =>
      exact flat_op0 (v := 0x0F) (by decide) rfl r
  | call bs x hh1 =>
      have h' : decOp1 0x10 ((bs) ++ r) = .ok (Instr.call x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x10) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | callIndirect by' bx y x hh1 hh2 =>
      have h' : decOp1 0x11 ((by' ++ bx) ++ r) = .ok (Instr.callIndirect x (.idx y), r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      exact flat_op1 (v := 0x11) (by decide) rfl (by decide) (by decide) (by decide)
        (by' ++ bx) r h'
  | returnCall bs x hh1 =>
      have h' : decOp1 0x12 ((bs) ++ r) = .ok (Instr.returnCall x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x12) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | returnCallIndirect by' bx y x hh1 hh2 =>
      have h' : decOp1 0x13 ((by' ++ bx) ++ r) = .ok (Instr.returnCallIndirect x (.idx y), r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      exact flat_op1 (v := 0x13) (by decide) rfl (by decide) (by decide) (by decide)
        (by' ++ bx) r h'

/-- Completeness of the flat dispatch on `BinstrLocal`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrLocal {b : Bytes} {i : Instr} (h : BinstrLocal b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | get bs x hh1 =>
      have h' : decOp1 0x20 ((bs) ++ r) = .ok (Instr.localGet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x20) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | set bs x hh1 =>
      have h' : decOp1 0x21 ((bs) ++ r) = .ok (Instr.localSet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x21) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | tee bs x hh1 =>
      have h' : decOp1 0x22 ((bs) ++ r) = .ok (Instr.localTee x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x22) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'

/-- Completeness of the flat dispatch on `BinstrGlobal`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrGlobal {b : Bytes} {i : Instr} (h : BinstrGlobal b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | get bs x hh1 =>
      have h' : decOp1 0x23 ((bs) ++ r) = .ok (Instr.globalGet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x23) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | set bs x hh1 =>
      have h' : decOp1 0x24 ((bs) ++ r) = .ok (Instr.globalSet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x24) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'

/-- Completeness of the flat dispatch on `BinstrTable`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrTable {b : Bytes} {i : Instr} (h : BinstrTable b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | get bs x hh1 =>
      have h' : decOp1 0x25 ((bs) ++ r) = .ok (Instr.tableGet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x25) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | set bs x hh1 =>
      have h' : decOp1 0x26 ((bs) ++ r) = .ok (Instr.tableSet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x26) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | init bo by' bx y x hbo hh1 hh2 =>
      have h' : decFCbody 12 ((by' ++ bx) ++ r) = .ok (Instr.tableInit x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ by' ++ bx ++ r = bo ++ ((by' ++ bx) ++ r) from by simp]
      exact flat_FC hbo (by' ++ bx) r h'
  | elemDrop bo bx x hbo hh1 =>
      have h' : decFCbody 13 ((bx) ++ r) = .ok (Instr.elemDrop x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'
  | copy bo b₁ b₂ x₁ x₂ hbo hh1 hh2 =>
      have h' : decFCbody 14 ((b₁ ++ b₂) ++ r) = .ok (Instr.tableCopy x₁ x₂, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ b₁ ++ b₂ ++ r = bo ++ ((b₁ ++ b₂) ++ r) from by simp]
      exact flat_FC hbo (b₁ ++ b₂) r h'
  | grow bo bx x hbo hh1 =>
      have h' : decFCbody 15 ((bx) ++ r) = .ok (Instr.tableGrow x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'
  | size bo bx x hbo hh1 =>
      have h' : decFCbody 16 ((bx) ++ r) = .ok (Instr.tableSize x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'
  | fill bo bx x hbo hh1 =>
      have h' : decFCbody 17 ((bx) ++ r) = .ok (Instr.tableFill x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'

/-- Completeness of the flat dispatch on `BinstrMemory`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrMemory {b : Bytes} {i : Instr} (h : BinstrMemory b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | i32Load bm x ao hh1 =>
      have h' : decOp1 0x28 ((bm) ++ r) = .ok (Instr.load .i32 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x28) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load bm x ao hh1 =>
      have h' : decOp1 0x29 ((bm) ++ r) = .ok (Instr.load .i64 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x29) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | f32Load bm x ao hh1 =>
      have h' : decOp1 0x2A ((bm) ++ r) = .ok (Instr.load .f32 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2A) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | f64Load bm x ao hh1 =>
      have h' : decOp1 0x2B ((bm) ++ r) = .ok (Instr.load .f64 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2B) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Load8S bm x ao hh1 =>
      have h' : decOp1 0x2C ((bm) ++ r) = .ok (Instr.load .i32 (some { sz := .s8, sx := .s }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2C) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Load8U bm x ao hh1 =>
      have h' : decOp1 0x2D ((bm) ++ r) = .ok (Instr.load .i32 (some { sz := .s8, sx := .u }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2D) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Load16S bm x ao hh1 =>
      have h' : decOp1 0x2E ((bm) ++ r) = .ok (Instr.load .i32 (some { sz := .s16, sx := .s }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2E) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Load16U bm x ao hh1 =>
      have h' : decOp1 0x2F ((bm) ++ r) = .ok (Instr.load .i32 (some { sz := .s16, sx := .u }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x2F) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load8S bm x ao hh1 =>
      have h' : decOp1 0x30 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s8, sx := .s }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x30) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load8U bm x ao hh1 =>
      have h' : decOp1 0x31 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s8, sx := .u }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x31) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load16S bm x ao hh1 =>
      have h' : decOp1 0x32 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s16, sx := .s }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x32) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load16U bm x ao hh1 =>
      have h' : decOp1 0x33 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s16, sx := .u }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x33) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load32S bm x ao hh1 =>
      have h' : decOp1 0x34 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s32, sx := .s }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x34) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Load32U bm x ao hh1 =>
      have h' : decOp1 0x35 ((bm) ++ r) = .ok (Instr.load .i64 (some { sz := .s32, sx := .u }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x35) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Store bm x ao hh1 =>
      have h' : decOp1 0x36 ((bm) ++ r) = .ok (Instr.store .i32 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x36) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Store bm x ao hh1 =>
      have h' : decOp1 0x37 ((bm) ++ r) = .ok (Instr.store .i64 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x37) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | f32Store bm x ao hh1 =>
      have h' : decOp1 0x38 ((bm) ++ r) = .ok (Instr.store .f32 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x38) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | f64Store bm x ao hh1 =>
      have h' : decOp1 0x39 ((bm) ++ r) = .ok (Instr.store .f64 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x39) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Store8 bm x ao hh1 =>
      have h' : decOp1 0x3A ((bm) ++ r) = .ok (Instr.store .i32 (some { sz := .s8 }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x3A) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i32Store16 bm x ao hh1 =>
      have h' : decOp1 0x3B ((bm) ++ r) = .ok (Instr.store .i32 (some { sz := .s16 }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x3B) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Store8 bm x ao hh1 =>
      have h' : decOp1 0x3C ((bm) ++ r) = .ok (Instr.store .i64 (some { sz := .s8 }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x3C) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Store16 bm x ao hh1 =>
      have h' : decOp1 0x3D ((bm) ++ r) = .ok (Instr.store .i64 (some { sz := .s16 }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x3D) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | i64Store32 bm x ao hh1 =>
      have h' : decOp1 0x3E ((bm) ++ r) = .ok (Instr.store .i64 (some { sz := .s32 }) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      exact flat_op1 (v := 0x3E) (by decide) rfl (by decide) (by decide) (by decide)
        (bm) r h'
  | size bs x hh1 =>
      have h' : decOp1 0x3F ((bs) ++ r) = .ok (Instr.memorySize x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x3F) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | grow bs x hh1 =>
      have h' : decOp1 0x40 ((bs) ++ r) = .ok (Instr.memoryGrow x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0x40) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | init bo by' bx y x hbo hh1 hh2 =>
      have h' : decFCbody 8 ((by' ++ bx) ++ r) = .ok (Instr.memoryInit x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ by' ++ bx ++ r = bo ++ ((by' ++ bx) ++ r) from by simp]
      exact flat_FC hbo (by' ++ bx) r h'
  | dataDrop bo bx x hbo hh1 =>
      have h' : decFCbody 9 ((bx) ++ r) = .ok (Instr.dataDrop x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'
  | copy bo b₁ b₂ x₁ x₂ hbo hh1 hh2 =>
      have h' : decFCbody 10 ((b₁ ++ b₂) ++ r) = .ok (Instr.memoryCopy x₁ x₂, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ b₁ ++ b₂ ++ r = bo ++ ((b₁ ++ b₂) ++ r) from by simp]
      exact flat_FC hbo (b₁ ++ b₂) r h'
  | fill bo bx x hbo hh1 =>
      have h' : decFCbody 11 ((bx) ++ r) = .ok (Instr.memoryFill x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FC hbo (bx) r h'

/-- Completeness of the flat dispatch on `BinstrRef`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrRef {b : Bytes} {i : Instr} (h : BinstrRef b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | null bs ht hh1 =>
      have h' : decOp1 0xD0 ((bs) ++ r) = .ok (Instr.refNull ht, r) :=
        arg1_complete decHeaptype_complete _ r hh1
      exact flat_op1 (v := 0xD0) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | isNull  =>
      exact flat_op0 (v := 0xD1) (by decide) rfl r
  | func bs x hh1 =>
      have h' : decOp1 0xD2 ((bs) ++ r) = .ok (Instr.refFunc x, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0xD2) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | eq  =>
      exact flat_op0 (v := 0xD3) (by decide) rfl r
  | asNonNull  =>
      exact flat_op0 (v := 0xD4) (by decide) rfl r
  | brOnNull bs l hh1 =>
      have h' : decOp1 0xD5 ((bs) ++ r) = .ok (Instr.brOnNull l, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0xD5) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | brOnNonNull bs l hh1 =>
      have h' : decOp1 0xD6 ((bs) ++ r) = .ok (Instr.brOnNonNull l, r) :=
        arg1_complete decIdx_complete _ r hh1
      exact flat_op1 (v := 0xD6) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'

/-- Completeness of the flat dispatch on `BinstrStruct`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrStruct {b : Bytes} {i : Instr} (h : BinstrStruct b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | new bo bx x hbo hh1 =>
      have h' : decFBbody 0 ((bx) ++ r) = .ok (Instr.structNew x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | newDefault bo bx x hbo hh1 =>
      have h' : decFBbody 1 ((bx) ++ r) = .ok (Instr.structNewDefault x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | get bo bx bi x i hbo hh1 hh2 =>
      have h' : decFBbody 2 ((bx ++ bi) ++ r) = .ok (Instr.structGet none x i, r) :=
        arg2_complete decIdx_complete decU32_complete _ r hh1 hh2
      rw [show bo ++ bx ++ bi ++ r = bo ++ ((bx ++ bi) ++ r) from by simp]
      exact flat_FB hbo (bx ++ bi) r h'
  | getS bo bx bi x i hbo hh1 hh2 =>
      have h' : decFBbody 3 ((bx ++ bi) ++ r) = .ok (Instr.structGet (some .s) x i, r) :=
        arg2_complete decIdx_complete decU32_complete _ r hh1 hh2
      rw [show bo ++ bx ++ bi ++ r = bo ++ ((bx ++ bi) ++ r) from by simp]
      exact flat_FB hbo (bx ++ bi) r h'
  | getU bo bx bi x i hbo hh1 hh2 =>
      have h' : decFBbody 4 ((bx ++ bi) ++ r) = .ok (Instr.structGet (some .u) x i, r) :=
        arg2_complete decIdx_complete decU32_complete _ r hh1 hh2
      rw [show bo ++ bx ++ bi ++ r = bo ++ ((bx ++ bi) ++ r) from by simp]
      exact flat_FB hbo (bx ++ bi) r h'
  | set bo bx bi x i hbo hh1 hh2 =>
      have h' : decFBbody 5 ((bx ++ bi) ++ r) = .ok (Instr.structSet x i, r) :=
        arg2_complete decIdx_complete decU32_complete _ r hh1 hh2
      rw [show bo ++ bx ++ bi ++ r = bo ++ ((bx ++ bi) ++ r) from by simp]
      exact flat_FB hbo (bx ++ bi) r h'

/-- Completeness of the flat dispatch on `BinstrArray`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrArray {b : Bytes} {i : Instr} (h : BinstrArray b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | new bo bx x hbo hh1 =>
      have h' : decFBbody 6 ((bx) ++ r) = .ok (Instr.arrayNew x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | newDefault bo bx x hbo hh1 =>
      have h' : decFBbody 7 ((bx) ++ r) = .ok (Instr.arrayNewDefault x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | newFixed bo bx bn x n hbo hh1 hh2 =>
      have h' : decFBbody 8 ((bx ++ bn) ++ r) = .ok (Instr.arrayNewFixed x n, r) :=
        arg2_complete decIdx_complete decU32_complete _ r hh1 hh2
      rw [show bo ++ bx ++ bn ++ r = bo ++ ((bx ++ bn) ++ r) from by simp]
      exact flat_FB hbo (bx ++ bn) r h'
  | newData bo bx by' x y hbo hh1 hh2 =>
      have h' : decFBbody 9 ((bx ++ by') ++ r) = .ok (Instr.arrayNewData x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ bx ++ by' ++ r = bo ++ ((bx ++ by') ++ r) from by simp]
      exact flat_FB hbo (bx ++ by') r h'
  | newElem bo bx by' x y hbo hh1 hh2 =>
      have h' : decFBbody 10 ((bx ++ by') ++ r) = .ok (Instr.arrayNewElem x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ bx ++ by' ++ r = bo ++ ((bx ++ by') ++ r) from by simp]
      exact flat_FB hbo (bx ++ by') r h'
  | get bo bx x hbo hh1 =>
      have h' : decFBbody 11 ((bx) ++ r) = .ok (Instr.arrayGet none x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | getS bo bx x hbo hh1 =>
      have h' : decFBbody 12 ((bx) ++ r) = .ok (Instr.arrayGet (some .s) x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | getU bo bx x hbo hh1 =>
      have h' : decFBbody 13 ((bx) ++ r) = .ok (Instr.arrayGet (some .u) x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | set bo bx x hbo hh1 =>
      have h' : decFBbody 14 ((bx) ++ r) = .ok (Instr.arraySet x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | len =>
      rename_i hbo
      exact flat_FB hbo [] r rfl
  | fill bo bx x hbo hh1 =>
      have h' : decFBbody 16 ((bx) ++ r) = .ok (Instr.arrayFill x, r) :=
        arg1_complete decIdx_complete _ r hh1
      rw [show bo ++ bx ++ r = bo ++ ((bx) ++ r) from by simp]
      exact flat_FB hbo (bx) r h'
  | copy bo b₁ b₂ x₁ x₂ hbo hh1 hh2 =>
      have h' : decFBbody 17 ((b₁ ++ b₂) ++ r) = .ok (Instr.arrayCopy x₁ x₂, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ b₁ ++ b₂ ++ r = bo ++ ((b₁ ++ b₂) ++ r) from by simp]
      exact flat_FB hbo (b₁ ++ b₂) r h'
  | initData bo bx by' x y hbo hh1 hh2 =>
      have h' : decFBbody 18 ((bx ++ by') ++ r) = .ok (Instr.arrayInitData x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ bx ++ by' ++ r = bo ++ ((bx ++ by') ++ r) from by simp]
      exact flat_FB hbo (bx ++ by') r h'
  | initElem bo bx by' x y hbo hh1 hh2 =>
      have h' : decFBbody 19 ((bx ++ by') ++ r) = .ok (Instr.arrayInitElem x y, r) :=
        arg2_complete decIdx_complete decIdx_complete _ r hh1 hh2
      rw [show bo ++ bx ++ by' ++ r = bo ++ ((bx ++ by') ++ r) from by simp]
      exact flat_FB hbo (bx ++ by') r h'

/-- Completeness of the flat dispatch on `BinstrCast`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrCast {b : Bytes} {i : Instr} (h : BinstrCast b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | test bo bh ht hbo hh1 =>
      have h' : decFBbody 20 ((bh) ++ r) = .ok (Instr.refTest (.ref none ht), r) :=
        arg1_complete decHeaptype_complete _ r hh1
      rw [show bo ++ bh ++ r = bo ++ ((bh) ++ r) from by simp]
      exact flat_FB hbo (bh) r h'
  | testNull bo bh ht hbo hh1 =>
      have h' : decFBbody 21 ((bh) ++ r) = .ok (Instr.refTest (.ref (some .null) ht), r) :=
        arg1_complete decHeaptype_complete _ r hh1
      rw [show bo ++ bh ++ r = bo ++ ((bh) ++ r) from by simp]
      exact flat_FB hbo (bh) r h'
  | cast bo bh ht hbo hh1 =>
      have h' : decFBbody 22 ((bh) ++ r) = .ok (Instr.refCast (.ref none ht), r) :=
        arg1_complete decHeaptype_complete _ r hh1
      rw [show bo ++ bh ++ r = bo ++ ((bh) ++ r) from by simp]
      exact flat_FB hbo (bh) r h'
  | castNull bo bh ht hbo hh1 =>
      have h' : decFBbody 23 ((bh) ++ r) = .ok (Instr.refCast (.ref (some .null) ht), r) :=
        arg1_complete decHeaptype_complete _ r hh1
      rw [show bo ++ bh ++ r = bo ++ ((bh) ++ r) from by simp]
      exact flat_FB hbo (bh) r h'
  | brOnCast bo bc bl b₁ b₂ n₁ n₂ l ht₁ ht₂ hbo hh1 hh2 hh3 hh4 =>
      have h' : decFBbody 24 ((bc ++ bl ++ b₁ ++ b₂) ++ r) = .ok (Instr.brOnCast l (.ref n₁ ht₁) (.ref n₂ ht₂), r) :=
        arg4_complete decCastop_complete decIdx_complete decHeaptype_complete decHeaptype_complete _ r hh1 hh2 hh3 hh4
      rw [show bo ++ bc ++ bl ++ b₁ ++ b₂ ++ r = bo ++ ((bc ++ bl ++ b₁ ++ b₂) ++ r) from by simp]
      exact flat_FB hbo (bc ++ bl ++ b₁ ++ b₂) r h'
  | brOnCastFail bo bc bl b₁ b₂ n₁ n₂ l ht₁ ht₂ hbo hh1 hh2 hh3 hh4 =>
      have h' : decFBbody 25 ((bc ++ bl ++ b₁ ++ b₂) ++ r) = .ok (Instr.brOnCastFail l (.ref n₁ ht₁) (.ref n₂ ht₂), r) :=
        arg4_complete decCastop_complete decIdx_complete decHeaptype_complete decHeaptype_complete _ r hh1 hh2 hh3 hh4
      rw [show bo ++ bc ++ bl ++ b₁ ++ b₂ ++ r = bo ++ ((bc ++ bl ++ b₁ ++ b₂) ++ r) from by simp]
      exact flat_FB hbo (bc ++ bl ++ b₁ ++ b₂) r h'

/-- Completeness of the flat dispatch on `BinstrExtern`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrExtern {b : Bytes} {i : Instr} (h : BinstrExtern b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | anyConvertExtern =>
      rename_i hbo
      exact flat_FB hbo [] r rfl
  | externConvertAny =>
      rename_i hbo
      exact flat_FB hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrI31`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrI31 {b : Bytes} {i : Instr} (h : BinstrI31 b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | refI31 =>
      rename_i hbo
      exact flat_FB hbo [] r rfl
  | getS =>
      rename_i hbo
      exact flat_FB hbo [] r rfl
  | getU =>
      rename_i hbo
      exact flat_FB hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrNum`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrNum {b : Bytes} {i : Instr} (h : BinstrNum b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | i32Const bs n hh1 =>
      have h' : decOp1 0x41 ((bs) ++ r) = .ok (Instr.const .i32 n, r) :=
        arg1_complete decU32_complete _ r hh1
      exact flat_op1 (v := 0x41) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | i64Const bs n hh1 =>
      have h' : decOp1 0x42 ((bs) ++ r) = .ok (Instr.const .i64 n, r) :=
        arg1_complete decU64_complete _ r hh1
      exact flat_op1 (v := 0x42) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | f32Const bs p hh1 =>
      have h' : decOp1 0x43 ((bs) ++ r) = .ok (Instr.const .f32 p, r) :=
        arg1_complete decF32_complete _ r hh1
      exact flat_op1 (v := 0x43) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | f64Const bs p hh1 =>
      have h' : decOp1 0x44 ((bs) ++ r) = .ok (Instr.const .f64 p, r) :=
        arg1_complete decF64_complete _ r hh1
      exact flat_op1 (v := 0x44) (by decide) rfl (by decide) (by decide) (by decide)
        (bs) r h'
  | i32Eqz  =>
      exact flat_op0 (v := 0x45) (by decide) rfl r
  | i32Eq  =>
      exact flat_op0 (v := 0x46) (by decide) rfl r
  | i32Ne  =>
      exact flat_op0 (v := 0x47) (by decide) rfl r
  | i32LtS  =>
      exact flat_op0 (v := 0x48) (by decide) rfl r
  | i32LtU  =>
      exact flat_op0 (v := 0x49) (by decide) rfl r
  | i32GtS  =>
      exact flat_op0 (v := 0x4A) (by decide) rfl r
  | i32GtU  =>
      exact flat_op0 (v := 0x4B) (by decide) rfl r
  | i32LeS  =>
      exact flat_op0 (v := 0x4C) (by decide) rfl r
  | i32LeU  =>
      exact flat_op0 (v := 0x4D) (by decide) rfl r
  | i32GeS  =>
      exact flat_op0 (v := 0x4E) (by decide) rfl r
  | i32GeU  =>
      exact flat_op0 (v := 0x4F) (by decide) rfl r
  | i64Eqz  =>
      exact flat_op0 (v := 0x50) (by decide) rfl r
  | i64Eq  =>
      exact flat_op0 (v := 0x51) (by decide) rfl r
  | i64Ne  =>
      exact flat_op0 (v := 0x52) (by decide) rfl r
  | i64LtS  =>
      exact flat_op0 (v := 0x53) (by decide) rfl r
  | i64LtU  =>
      exact flat_op0 (v := 0x54) (by decide) rfl r
  | i64GtS  =>
      exact flat_op0 (v := 0x55) (by decide) rfl r
  | i64GtU  =>
      exact flat_op0 (v := 0x56) (by decide) rfl r
  | i64LeS  =>
      exact flat_op0 (v := 0x57) (by decide) rfl r
  | i64LeU  =>
      exact flat_op0 (v := 0x58) (by decide) rfl r
  | i64GeS  =>
      exact flat_op0 (v := 0x59) (by decide) rfl r
  | i64GeU  =>
      exact flat_op0 (v := 0x5A) (by decide) rfl r
  | f32Eq  =>
      exact flat_op0 (v := 0x5B) (by decide) rfl r
  | f32Ne  =>
      exact flat_op0 (v := 0x5C) (by decide) rfl r
  | f32Lt  =>
      exact flat_op0 (v := 0x5D) (by decide) rfl r
  | f32Gt  =>
      exact flat_op0 (v := 0x5E) (by decide) rfl r
  | f32Le  =>
      exact flat_op0 (v := 0x5F) (by decide) rfl r
  | f32Ge  =>
      exact flat_op0 (v := 0x60) (by decide) rfl r
  | f64Eq  =>
      exact flat_op0 (v := 0x61) (by decide) rfl r
  | f64Ne  =>
      exact flat_op0 (v := 0x62) (by decide) rfl r
  | f64Lt  =>
      exact flat_op0 (v := 0x63) (by decide) rfl r
  | f64Gt  =>
      exact flat_op0 (v := 0x64) (by decide) rfl r
  | f64Le  =>
      exact flat_op0 (v := 0x65) (by decide) rfl r
  | f64Ge  =>
      exact flat_op0 (v := 0x66) (by decide) rfl r
  | i32Clz  =>
      exact flat_op0 (v := 0x67) (by decide) rfl r
  | i32Ctz  =>
      exact flat_op0 (v := 0x68) (by decide) rfl r
  | i32Popcnt  =>
      exact flat_op0 (v := 0x69) (by decide) rfl r
  | i32Add  =>
      exact flat_op0 (v := 0x6A) (by decide) rfl r
  | i32Sub  =>
      exact flat_op0 (v := 0x6B) (by decide) rfl r
  | i32Mul  =>
      exact flat_op0 (v := 0x6C) (by decide) rfl r
  | i32DivS  =>
      exact flat_op0 (v := 0x6D) (by decide) rfl r
  | i32DivU  =>
      exact flat_op0 (v := 0x6E) (by decide) rfl r
  | i32RemS  =>
      exact flat_op0 (v := 0x6F) (by decide) rfl r
  | i32RemU  =>
      exact flat_op0 (v := 0x70) (by decide) rfl r
  | i32And  =>
      exact flat_op0 (v := 0x71) (by decide) rfl r
  | i32Or  =>
      exact flat_op0 (v := 0x72) (by decide) rfl r
  | i32Xor  =>
      exact flat_op0 (v := 0x73) (by decide) rfl r
  | i32Shl  =>
      exact flat_op0 (v := 0x74) (by decide) rfl r
  | i32ShrS  =>
      exact flat_op0 (v := 0x75) (by decide) rfl r
  | i32ShrU  =>
      exact flat_op0 (v := 0x76) (by decide) rfl r
  | i32Rotl  =>
      exact flat_op0 (v := 0x77) (by decide) rfl r
  | i32Rotr  =>
      exact flat_op0 (v := 0x78) (by decide) rfl r
  | i64Clz  =>
      exact flat_op0 (v := 0x79) (by decide) rfl r
  | i64Ctz  =>
      exact flat_op0 (v := 0x7A) (by decide) rfl r
  | i64Popcnt  =>
      exact flat_op0 (v := 0x7B) (by decide) rfl r
  | i32Extend8  =>
      exact flat_op0 (v := 0xC0) (by decide) rfl r
  | i32Extend16  =>
      exact flat_op0 (v := 0xC1) (by decide) rfl r
  | i64Extend8  =>
      exact flat_op0 (v := 0xC2) (by decide) rfl r
  | i64Extend16  =>
      exact flat_op0 (v := 0xC3) (by decide) rfl r
  | i64Extend32  =>
      exact flat_op0 (v := 0xC4) (by decide) rfl r
  | i64Add  =>
      exact flat_op0 (v := 0x7C) (by decide) rfl r
  | i64Sub  =>
      exact flat_op0 (v := 0x7D) (by decide) rfl r
  | i64Mul  =>
      exact flat_op0 (v := 0x7E) (by decide) rfl r
  | i64DivS  =>
      exact flat_op0 (v := 0x7F) (by decide) rfl r
  | i64DivU  =>
      exact flat_op0 (v := 0x80) (by decide) rfl r
  | i64RemS  =>
      exact flat_op0 (v := 0x81) (by decide) rfl r
  | i64RemU  =>
      exact flat_op0 (v := 0x82) (by decide) rfl r
  | i64And  =>
      exact flat_op0 (v := 0x83) (by decide) rfl r
  | i64Or  =>
      exact flat_op0 (v := 0x84) (by decide) rfl r
  | i64Xor  =>
      exact flat_op0 (v := 0x85) (by decide) rfl r
  | i64Shl  =>
      exact flat_op0 (v := 0x86) (by decide) rfl r
  | i64ShrS  =>
      exact flat_op0 (v := 0x87) (by decide) rfl r
  | i64ShrU  =>
      exact flat_op0 (v := 0x88) (by decide) rfl r
  | i64Rotl  =>
      exact flat_op0 (v := 0x89) (by decide) rfl r
  | i64Rotr  =>
      exact flat_op0 (v := 0x8A) (by decide) rfl r
  | f32Abs  =>
      exact flat_op0 (v := 0x8B) (by decide) rfl r
  | f32Neg  =>
      exact flat_op0 (v := 0x8C) (by decide) rfl r
  | f32Ceil  =>
      exact flat_op0 (v := 0x8D) (by decide) rfl r
  | f32Floor  =>
      exact flat_op0 (v := 0x8E) (by decide) rfl r
  | f32Trunc  =>
      exact flat_op0 (v := 0x8F) (by decide) rfl r
  | f32Nearest  =>
      exact flat_op0 (v := 0x90) (by decide) rfl r
  | f32Sqrt  =>
      exact flat_op0 (v := 0x91) (by decide) rfl r
  | f32Add  =>
      exact flat_op0 (v := 0x92) (by decide) rfl r
  | f32Sub  =>
      exact flat_op0 (v := 0x93) (by decide) rfl r
  | f32Mul  =>
      exact flat_op0 (v := 0x94) (by decide) rfl r
  | f32Div  =>
      exact flat_op0 (v := 0x95) (by decide) rfl r
  | f32Min  =>
      exact flat_op0 (v := 0x96) (by decide) rfl r
  | f32Max  =>
      exact flat_op0 (v := 0x97) (by decide) rfl r
  | f32Copysign  =>
      exact flat_op0 (v := 0x98) (by decide) rfl r
  | f64Abs  =>
      exact flat_op0 (v := 0x99) (by decide) rfl r
  | f64Neg  =>
      exact flat_op0 (v := 0x9A) (by decide) rfl r
  | f64Ceil  =>
      exact flat_op0 (v := 0x9B) (by decide) rfl r
  | f64Floor  =>
      exact flat_op0 (v := 0x9C) (by decide) rfl r
  | f64Trunc  =>
      exact flat_op0 (v := 0x9D) (by decide) rfl r
  | f64Nearest  =>
      exact flat_op0 (v := 0x9E) (by decide) rfl r
  | f64Sqrt  =>
      exact flat_op0 (v := 0x9F) (by decide) rfl r
  | f64Add  =>
      exact flat_op0 (v := 0xA0) (by decide) rfl r
  | f64Sub  =>
      exact flat_op0 (v := 0xA1) (by decide) rfl r
  | f64Mul  =>
      exact flat_op0 (v := 0xA2) (by decide) rfl r
  | f64Div  =>
      exact flat_op0 (v := 0xA3) (by decide) rfl r
  | f64Min  =>
      exact flat_op0 (v := 0xA4) (by decide) rfl r
  | f64Max  =>
      exact flat_op0 (v := 0xA5) (by decide) rfl r
  | f64Copysign  =>
      exact flat_op0 (v := 0xA6) (by decide) rfl r
  | i32WrapI64  =>
      exact flat_op0 (v := 0xA7) (by decide) rfl r
  | i32TruncF32S  =>
      exact flat_op0 (v := 0xA8) (by decide) rfl r
  | i32TruncF32U  =>
      exact flat_op0 (v := 0xA9) (by decide) rfl r
  | i32TruncF64S  =>
      exact flat_op0 (v := 0xAA) (by decide) rfl r
  | i32TruncF64U  =>
      exact flat_op0 (v := 0xAB) (by decide) rfl r
  | i64ExtendI32S  =>
      exact flat_op0 (v := 0xAC) (by decide) rfl r
  | i64ExtendI32U  =>
      exact flat_op0 (v := 0xAD) (by decide) rfl r
  | i64TruncF32S  =>
      exact flat_op0 (v := 0xAE) (by decide) rfl r
  | i64TruncF32U  =>
      exact flat_op0 (v := 0xAF) (by decide) rfl r
  | i64TruncF64S  =>
      exact flat_op0 (v := 0xB0) (by decide) rfl r
  | i64TruncF64U  =>
      exact flat_op0 (v := 0xB1) (by decide) rfl r
  | f32ConvertI32S  =>
      exact flat_op0 (v := 0xB2) (by decide) rfl r
  | f32ConvertI32U  =>
      exact flat_op0 (v := 0xB3) (by decide) rfl r
  | f32ConvertI64S  =>
      exact flat_op0 (v := 0xB4) (by decide) rfl r
  | f32ConvertI64U  =>
      exact flat_op0 (v := 0xB5) (by decide) rfl r
  | f32DemoteF64  =>
      exact flat_op0 (v := 0xB6) (by decide) rfl r
  | f64ConvertI32S  =>
      exact flat_op0 (v := 0xB7) (by decide) rfl r
  | f64ConvertI32U  =>
      exact flat_op0 (v := 0xB8) (by decide) rfl r
  | f64ConvertI64S  =>
      exact flat_op0 (v := 0xB9) (by decide) rfl r
  | f64ConvertI64U  =>
      exact flat_op0 (v := 0xBA) (by decide) rfl r
  | f32PromoteF64  =>
      exact flat_op0 (v := 0xBB) (by decide) rfl r
  | i32ReinterpretF32  =>
      exact flat_op0 (v := 0xBC) (by decide) rfl r
  | i64ReinterpretF64  =>
      exact flat_op0 (v := 0xBD) (by decide) rfl r
  | f32ReinterpretI32  =>
      exact flat_op0 (v := 0xBE) (by decide) rfl r
  | f64ReinterpretI64  =>
      exact flat_op0 (v := 0xBF) (by decide) rfl r
  | i32TruncSatF32S =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i32TruncSatF32U =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i32TruncSatF64S =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i32TruncSatF64U =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i64TruncSatF32S =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i64TruncSatF32U =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i64TruncSatF64S =>
      rename_i hbo
      exact flat_FC hbo [] r rfl
  | i64TruncSatF64U =>
      rename_i hbo
      exact flat_FC hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrVecMem`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecMem {b : Bytes} {i : Instr} (h : BinstrVecMem b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | v128Load bo bm x ao hbo hh1 =>
      have h' : decFDbody 0 ((bm) ++ r) = .ok (Instr.vload .v128 none x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load8x8S bo bm x ao hbo hh1 =>
      have h' : decFDbody 1 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s8 8 .s)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load8x8U bo bm x ao hbo hh1 =>
      have h' : decFDbody 2 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s8 8 .u)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load16x4S bo bm x ao hbo hh1 =>
      have h' : decFDbody 3 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s16 4 .s)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load16x4U bo bm x ao hbo hh1 =>
      have h' : decFDbody 4 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s16 4 .u)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load32x2S bo bm x ao hbo hh1 =>
      have h' : decFDbody 5 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s32 2 .s)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load32x2U bo bm x ao hbo hh1 =>
      have h' : decFDbody 6 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.shape .s32 2 .u)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load8Splat bo bm x ao hbo hh1 =>
      have h' : decFDbody 7 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.splat .s8)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load16Splat bo bm x ao hbo hh1 =>
      have h' : decFDbody 8 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.splat .s16)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load32Splat bo bm x ao hbo hh1 =>
      have h' : decFDbody 9 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.splat .s32)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load64Splat bo bm x ao hbo hh1 =>
      have h' : decFDbody 10 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.splat .s64)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Store bo bm x ao hbo hh1 =>
      have h' : decFDbody 11 ((bm) ++ r) = .ok (Instr.vstore .v128 x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load8Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 84 ((bm ++ bi) ++ r) = .ok (Instr.vloadLane .v128 .s8 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Load16Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 85 ((bm ++ bi) ++ r) = .ok (Instr.vloadLane .v128 .s16 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Load32Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 86 ((bm ++ bi) ++ r) = .ok (Instr.vloadLane .v128 .s32 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Load64Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 87 ((bm ++ bi) ++ r) = .ok (Instr.vloadLane .v128 .s64 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Store8Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 88 ((bm ++ bi) ++ r) = .ok (Instr.vstoreLane .v128 .s8 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Store16Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 89 ((bm ++ bi) ++ r) = .ok (Instr.vstoreLane .v128 .s16 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Store32Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 90 ((bm ++ bi) ++ r) = .ok (Instr.vstoreLane .v128 .s32 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Store64Lane bo bm bi x ao i hbo hh1 hh2 =>
      have h' : decFDbody 91 ((bm ++ bi) ++ r) = .ok (Instr.vstoreLane .v128 .s64 x ao i, r) :=
        arg2_complete decMemarg_complete decLaneIdx_complete _ r hh1 hh2
      rw [show bo ++ bm ++ bi ++ r = bo ++ ((bm ++ bi) ++ r) from by simp]
      exact flat_FD hbo (bm ++ bi) r h'
  | v128Load32Zero bo bm x ao hbo hh1 =>
      have h' : decFDbody 92 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.zero .s32)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Load64Zero bo bm x ao hbo hh1 =>
      have h' : decFDbody 93 ((bm) ++ r) = .ok (Instr.vload .v128 (some (.zero .s64)) x ao, r) :=
        arg1_complete decMemarg_complete _ r hh1
      rw [show bo ++ bm ++ r = bo ++ ((bm) ++ r) from by simp]
      exact flat_FD hbo (bm) r h'
  | v128Const bo bb bl c hbo hrep hc =>
      have h' : decFDbody 12 (bb ++ r) = .ok (Instr.vconst .v128 c, r) :=
        decV128Const_complete c bl bb r hrep hc
      rw [show bo ++ bb ++ r = bo ++ (bb ++ r) from by simp]
      exact flat_FD hbo bb r h'
  | i8x16Shuffle bo bl ls hbo hrep =>
      have h' : decFDbody 13 (bl ++ r) = .ok (Instr.vshuffle bshI8x16 ls, r) :=
        decShuffle_complete ls bl r hrep
      rw [show bo ++ bl ++ r = bo ++ (bl ++ r) from by simp]
      exact flat_FD hbo bl r h'
  | i8x16Swizzle =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16RelaxedSwizzle =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Splat =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16ExtractLaneS bo bi l hbo hh1 =>
      have h' : decFDbody 21 ((bi) ++ r) = .ok (Instr.vextractLane shI8x16 (some .s) l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i8x16ExtractLaneU bo bi l hbo hh1 =>
      have h' : decFDbody 22 ((bi) ++ r) = .ok (Instr.vextractLane shI8x16 (some .u) l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i8x16ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 23 ((bi) ++ r) = .ok (Instr.vreplaceLane shI8x16 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i16x8ExtractLaneS bo bi l hbo hh1 =>
      have h' : decFDbody 24 ((bi) ++ r) = .ok (Instr.vextractLane shI16x8 (some .s) l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i16x8ExtractLaneU bo bi l hbo hh1 =>
      have h' : decFDbody 25 ((bi) ++ r) = .ok (Instr.vextractLane shI16x8 (some .u) l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i16x8ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 26 ((bi) ++ r) = .ok (Instr.vreplaceLane shI16x8 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i32x4ExtractLane bo bi l hbo hh1 =>
      have h' : decFDbody 27 ((bi) ++ r) = .ok (Instr.vextractLane shI32x4 none l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i32x4ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 28 ((bi) ++ r) = .ok (Instr.vreplaceLane shI32x4 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i64x2ExtractLane bo bi l hbo hh1 =>
      have h' : decFDbody 29 ((bi) ++ r) = .ok (Instr.vextractLane shI64x2 none l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | i64x2ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 30 ((bi) ++ r) = .ok (Instr.vreplaceLane shI64x2 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | f32x4ExtractLane bo bi l hbo hh1 =>
      have h' : decFDbody 31 ((bi) ++ r) = .ok (Instr.vextractLane shF32x4 none l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | f32x4ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 32 ((bi) ++ r) = .ok (Instr.vreplaceLane shF32x4 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | f64x2ExtractLane bo bi l hbo hh1 =>
      have h' : decFDbody 33 ((bi) ++ r) = .ok (Instr.vextractLane shF64x2 none l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'
  | f64x2ReplaceLane bo bi l hbo hh1 =>
      have h' : decFDbody 34 ((bi) ++ r) = .ok (Instr.vreplaceLane shF64x2 l, r) :=
        arg1_complete decLaneIdx_complete _ r hh1
      rw [show bo ++ bi ++ r = bo ++ ((bi) ++ r) from by simp]
      exact flat_FD hbo (bi) r h'

/-- Completeness of the flat dispatch on `BinstrVecRel`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecRel {b : Bytes} {i : Instr} (h : BinstrVecRel b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | i8x16Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16LtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16LtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16GtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16GtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16LeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16LeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16GeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16GeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8LtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8LtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8GtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8GtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8LeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8LeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8GeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8GeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4LtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4LtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4GtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4GtU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4LeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4LeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4GeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4GeU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Lt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Gt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Le =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Ge =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Lt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Gt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Le =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Ge =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Eq =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Ne =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2LtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2GtS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2LeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2GeS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrVecV128`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecV128 {b : Bytes} {i : Instr} (h : BinstrVecV128 b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | not =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | and =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | andnot =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | or =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | xor =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | bitselect =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | anyTrue =>
      rename_i hbo
      exact flat_FD hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrVecInt8And16`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecInt8And16 {b : Bytes} {i : Instr} (h : BinstrVecInt8And16 b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | i8x16Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Popcnt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16AllTrue =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Bitmask =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16NarrowI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16NarrowI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Shl =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16ShrS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16ShrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16AddSatS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16AddSatU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16SubSatS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16SubSatU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16MinS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16MinU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16MaxS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16MaxU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16AvgrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtaddPairwiseI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtaddPairwiseI8x16U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Q15mulrSatS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8AddSatS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8AddSatU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8SubSatS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8SubSatU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Mul =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8MinS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8MinU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8MaxS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8MaxU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8AvgrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8RelaxedQ15mulrS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8AllTrue =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Bitmask =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8NarrowI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8NarrowI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtendLowI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtendHighI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtendLowI8x16U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtendHighI8x16U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8Shl =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ShrS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ShrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtmulLowI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtmulHighI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtmulLowI8x16U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8ExtmulHighI8x16U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8RelaxedDotI8x16S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrVecInt32And64`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecInt32And64 {b : Bytes} {i : Instr} (h : BinstrVecInt32And64 b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | i32x4ExtaddPairwiseI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtaddPairwiseI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4AllTrue =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Bitmask =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtendLowI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtendHighI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtendLowI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtendHighI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Shl =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ShrS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ShrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4Mul =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4MinS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4MinU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4MaxS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4MaxU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4DotI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtmulLowI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtmulHighI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtmulLowI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4ExtmulHighI16x8U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedDotAddI16x8S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2AllTrue =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Bitmask =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtendLowI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtendHighI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtendLowI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtendHighI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Shl =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ShrS =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ShrU =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2Mul =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtmulLowI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtmulHighI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtmulLowI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2ExtmulHighI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl

/-- Completeness of the flat dispatch on `BinstrVecFloat`: every production of
this fragment of the pinned grammar is decoded, to the value the grammar
gives it, consuming exactly the derivation's bytes. -/
theorem flat_BinstrVecFloat {b : Bytes} {i : Instr} (h : BinstrVecFloat b i) (r : Bytes) :
    decInstrFlat (b ++ r) = .ok (i, r) := by
  cases h with
  | f32x4Ceil =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Floor =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Trunc =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Nearest =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Sqrt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Mul =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Div =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Min =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Max =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Pmin =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4Pmax =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4RelaxedMin =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4RelaxedMax =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4RelaxedMadd =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4RelaxedNmadd =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Ceil =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Floor =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Trunc =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Nearest =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Abs =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Neg =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Sqrt =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Add =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Sub =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Mul =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Div =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Min =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Max =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Pmin =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2Pmax =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2RelaxedMin =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2RelaxedMax =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2RelaxedMadd =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2RelaxedNmadd =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i8x16RelaxedLaneselect =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i16x8RelaxedLaneselect =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedLaneselect =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i64x2RelaxedLaneselect =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4DemoteF64x2Zero =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2PromoteLowF32x4 =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4TruncSatF32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4TruncSatF32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4ConvertI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f32x4ConvertI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4TruncSatF64x2SZero =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4TruncSatF64x2UZero =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2ConvertLowI32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | f64x2ConvertLowI32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedTruncF32x4S =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedTruncF32x4U =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedTruncF64x2SZero =>
      rename_i hbo
      exact flat_FD hbo [] r rfl
  | i32x4RelaxedTruncF64x2UZero =>
      rename_i hbo
      exact flat_FD hbo [] r rfl

/-! ## No production of the pinned grammar derives `eps`

Not assumed: read off the fragment lemmas above.  If a fragment derived the
empty byte sequence, the decoder would have to accept the empty input, and
`decInstrFlat [] = .error .eof`. -/

theorem Binstr_ne_nil {b : Bytes} {i : Instr} (h : Binstr b i) : b ≠ [] := by
  cases h with
  | block => simp
  | loop => simp
  | ifThen => simp
  | ifElse => simp
  | tryTable => simp
  | ofParametric =>
      rename_i h'; intro hb
      have hx := flat_BinstrParametric h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofControl =>
      rename_i h'; intro hb
      have hx := flat_BinstrControl h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofLocal =>
      rename_i h'; intro hb
      have hx := flat_BinstrLocal h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofGlobal =>
      rename_i h'; intro hb
      have hx := flat_BinstrGlobal h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofTable =>
      rename_i h'; intro hb
      have hx := flat_BinstrTable h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofMemory =>
      rename_i h'; intro hb
      have hx := flat_BinstrMemory h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofRef =>
      rename_i h'; intro hb
      have hx := flat_BinstrRef h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofStruct =>
      rename_i h'; intro hb
      have hx := flat_BinstrStruct h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofArray =>
      rename_i h'; intro hb
      have hx := flat_BinstrArray h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofCast =>
      rename_i h'; intro hb
      have hx := flat_BinstrCast h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofExtern =>
      rename_i h'; intro hb
      have hx := flat_BinstrExtern h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofI31 =>
      rename_i h'; intro hb
      have hx := flat_BinstrI31 h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofNum =>
      rename_i h'; intro hb
      have hx := flat_BinstrNum h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecMem =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecMem h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecRel =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecRel h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecV128 =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecV128 h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecInt8And16 =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecInt8And16 h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecInt32And64 =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecInt32And64 h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx
  | ofVecFloat =>
      rename_i h'; intro hb
      have hx := flat_BinstrVecFloat h' ([] : Bytes); rw [hb] at hx
      simp [decInstrFlat] at hx

/-- An instruction sequence has no more instructions than it has bytes.  This is
what makes the length-derived fuel of `decInstrs` enough. -/
theorem Binstrs_length_le_aux : ∀ (n : Nat) (b : Bytes) (is : List Instr),
    b.length ≤ n → Binstrs b is → is.length ≤ b.length := by
  intro n
  induction n with
  | zero =>
      intro b is hn h
      cases h with
      | nil => simp
      | cons b₁ bs i₁ is₁ h1 _ =>
          exfalso
          have h0 : b₁ ≠ [] := Binstr_ne_nil h1
          have : b₁.length = 0 := by
            simp only [List.length_append] at hn; omega
          exact h0 (List.eq_nil_of_length_eq_zero this)
  | succ n ih =>
      intro b is hn h
      cases h with
      | nil => simp
      | cons b₁ bs i₁ is₁ h1 h2 =>
          have h0 : b₁ ≠ [] := Binstr_ne_nil h1
          have hb1 : 1 ≤ b₁.length := by
            cases b₁ with
            | nil => exact absurd rfl h0
            | cons _ _ => simp
          have hrec : is₁.length ≤ bs.length := by
            refine ih bs is₁ ?_ h2
            simp only [List.length_append] at hn; omega
          simp only [List.length_cons, List.length_append]
          omega

theorem Binstrs_length_le {b : Bytes} {is : List Instr} (h : Binstrs b is) :
    is.length ≤ b.length :=
  Binstrs_length_le_aux b.length b is (Nat.le_refl _) h

/-! ## `END` and `ELSE` are not opcodes -/

theorem decInstrFlat_error {c : Byte} {t : Bytes} {v : Nat} (hv : c.val = v)
    (h0 : op0 v = none) (h1 : ¬ (v = 0xFB)) (h2 : ¬ (v = 0xFC)) (h3 : ¬ (v = 0xFD))
    (h4 : decOp1 v t = .error .opcode) :
    decInstrFlat (c :: t) = .error .opcode := by
  rw [decInstrFlat, hv, h0]
  simp only [if_neg h1, if_neg h2, if_neg h3]
  exact h4

/-- The head byte of anything the flat dispatch accepts is not one of the four
block-shaped opcodes, so `decInstr` falls through to it. -/
theorem decInstrFlat_head {c : Byte} {t : Bytes} {i : Instr} {r : Bytes}
    (h : decInstrFlat (c :: t) = .ok (i, r)) :
    ¬ (c.val = 0x02) ∧ ¬ (c.val = 0x03) ∧ ¬ (c.val = 0x04) ∧ ¬ (c.val = 0x1F) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hc
  · rw [decInstrFlat_error hc rfl (by decide) (by decide) (by decide) rfl] at h; cases h
  · rw [decInstrFlat_error hc rfl (by decide) (by decide) (by decide) rfl] at h; cases h
  · rw [decInstrFlat_error hc rfl (by decide) (by decide) (by decide) rfl] at h; cases h
  · rw [decInstrFlat_error hc rfl (by decide) (by decide) (by decide) rfl] at h; cases h

theorem decInstr_of_flat {d : Nat} {c : Byte} {t : Bytes} {i : Instr} {r : Bytes}
    (hf : decInstrFlat (c :: t) = .ok (i, r)) : decInstr (d + 1) (c :: t) = .ok (i, r) := by
  obtain ⟨h2, h3, h4, h1f⟩ := decInstrFlat_head hf
  rw [decInstr]
  simp only [if_neg h2, if_neg h3, if_neg h4, if_neg h1f]
  exact hf

/-- Neither `END` nor `ELSE` begins an instruction the decoder accepts. -/
theorem decInstr_ne_end {d : Nat} {c : Byte} {t : Bytes} (hb : c.val = 0x0B ∨ c.val = 0x05)
    {i : Instr} {r : Bytes} : decInstr d (c :: t) ≠ .ok (i, r) := by
  cases d with
  | zero => rw [decInstr]; intro hx; cases hx
  | succ d =>
      have h2 : ¬ (c.val = 0x02) := by rcases hb with h | h <;> omega
      have h3 : ¬ (c.val = 0x03) := by rcases hb with h | h <;> omega
      have h4 : ¬ (c.val = 0x04) := by rcases hb with h | h <;> omega
      have h1f : ¬ (c.val = 0x1F) := by rcases hb with h | h <;> omega
      have hflat : decInstrFlat (c :: t) = .error .opcode := by
        rcases hb with h | h
        · exact decInstrFlat_error h rfl (by decide) (by decide) (by decide) rfl
        · exact decInstrFlat_error h rfl (by decide) (by decide) (by decide) rfl
      rw [decInstr]
      simp only [if_neg h2, if_neg h3, if_neg h4, if_neg h1f, hflat]
      intro hx; cases hx

/-! ## The recursive knot -/

/-- Completeness of `(in:Binstr)*`, given completeness of the instruction
decoder on every derivation short enough. -/
theorem decInstrs_complete_of (d M : Nat)
    (hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ M → Binstr b' i' →
        decInstr d (b' ++ r') = .ok (i', r')) :
    ∀ (n : Nat) (b : Bytes) (is : List Instr) (r : Bytes),
      Binstrs b is → b.length ≤ M → is.length ≤ n → isEndOrElse r = true →
      decInstrs (decInstr d) n (b ++ r) = .ok (is, r) := by
  intro n
  induction n with
  | zero =>
      intro b is r hbs hlen hn hr
      cases hbs with
      | nil => rw [decInstrs]; simp only [List.nil_append, hr, if_true]
      | cons b₁ bs i₁ is₁ _ _ => simp at hn
  | succ n ih =>
      intro b is r hbs hlen hn hr
      cases hbs with
      | nil => rw [decInstrs]; simp only [List.nil_append, hr, if_true]
      | cons b₁ bs i₁ is₁ h1 h2 =>
          have hl1 : b₁.length ≤ M := by
            simp only [List.length_append] at hlen; omega
          have hl2 : bs.length ≤ M := by
            simp only [List.length_append] at hlen; omega
          have e1 : decInstr d (b₁ ++ (bs ++ r)) = .ok (i₁, bs ++ r) :=
            hI b₁ i₁ (bs ++ r) hl1 h1
          have hne : isEndOrElse (b₁ ++ (bs ++ r)) = false := by
            cases hcons : (b₁ ++ (bs ++ r)) with
            | nil => rfl
            | cons c t =>
                rw [hcons] at e1
                by_cases hc : c.val = 0x0B
                · exact absurd e1 (decInstr_ne_end (Or.inl hc))
                · by_cases hc2 : c.val = 0x05
                  · exact absurd e1 (decInstr_ne_end (Or.inr hc2))
                  · simp [isEndOrElse, hc, hc2]
          have e2 : decInstrs (decInstr d) n (bs ++ r) = .ok (is₁, r) := by
            refine ih bs is₁ r h2 hl2 ?_ hr
            simp only [List.length_cons] at hn; omega
          have hne' : ¬ (isEndOrElse (b₁ ++ (bs ++ r)) = true) := by simp [hne]
          rw [List.append_assoc, decInstrs, if_neg hne']
          simp only [e1, e2]

/-- **COMPLETENESS OF THE INSTRUCTION DECODER.**  Every derivation of the pinned
`Binstr` -- the whole of `5.3-binary.instructions.spectec`, the `0xFB` and `0xFD`
spaces included -- is decoded, to the value the grammar gives it, consuming
exactly the derivation's bytes. -/
theorem decInstr_complete : ∀ (N d : Nat) (b : Bytes) (i : Instr) (r : Bytes),
    b.length ≤ N → b.length ≤ d → Binstr b i → decInstr d (b ++ r) = .ok (i, r) := by
  intro N
  induction N with
  | zero =>
      intro d b i r hN _ hb
      exact absurd (List.eq_nil_of_length_eq_zero (by omega)) (Binstr_ne_nil hb)
  | succ N ihN =>
      intro d b i r hN hd hb
      cases hb with
      | block bbt bin bt ins hbt hins =>
          have hlen : (tb 0x02 :: (bbt ++ bin ++ [tb 0x0B])).length
              = bbt.length + bin.length + 2 := by
            simp only [List.length_cons, List.length_append, List.length_nil]
            try omega
          cases d with
          | zero => rw [hlen] at hd; exfalso; omega
          | succ d =>
              have hassoc : (tb 0x02 :: (bbt ++ bin ++ [tb 0x0B])) ++ r
                  = tb 0x02 :: (bbt ++ (bin ++ (tb 0x0B :: r))) := by simp
              have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ bin.length →
                  Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
                intro b' i' r' hb' hbi
                refine ihN d b' i' r' ?_ ?_ hbi
                · rw [hlen] at hN; omega
                · rw [hlen] at hd; omega
              have hins' := decInstrs_complete_of d bin.length hI
                (bin ++ (tb 0x0B :: r)).length bin ins (tb 0x0B :: r) hins (by omega)
                (by have := Binstrs_length_le hins; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              rw [hassoc, decInstr]
              simp only [if_true, tb_val 0x02 (by decide), if_pos rfl,
                decBlocktype_complete bbt bt (bin ++ (tb 0x0B :: r)) hbt, hins',
                expectByte_eq 0x0B (by decide) r]
      | loop bbt bin bt ins hbt hins =>
          have hlen : (tb 0x03 :: (bbt ++ bin ++ [tb 0x0B])).length
              = bbt.length + bin.length + 2 := by
            simp only [List.length_cons, List.length_append, List.length_nil]
            try omega
          cases d with
          | zero => rw [hlen] at hd; exfalso; omega
          | succ d =>
              have hassoc : (tb 0x03 :: (bbt ++ bin ++ [tb 0x0B])) ++ r
                  = tb 0x03 :: (bbt ++ (bin ++ (tb 0x0B :: r))) := by simp
              have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ bin.length →
                  Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
                intro b' i' r' hb' hbi
                refine ihN d b' i' r' ?_ ?_ hbi
                · rw [hlen] at hN; omega
                · rw [hlen] at hd; omega
              have hins' := decInstrs_complete_of d bin.length hI
                (bin ++ (tb 0x0B :: r)).length bin ins (tb 0x0B :: r) hins (by omega)
                (by have := Binstrs_length_le hins; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              rw [hassoc, decInstr]
              simp only [if_true, tb_val 0x03 (by decide), if_neg (by decide : ¬ ((0x03 : Nat) = 0x02)),
                if_pos rfl, decBlocktype_complete bbt bt (bin ++ (tb 0x0B :: r)) hbt, hins',
                expectByte_eq 0x0B (by decide) r]
      | ifThen bbt bin bt ins hbt hins =>
          have hlen : (tb 0x04 :: (bbt ++ bin ++ [tb 0x0B])).length
              = bbt.length + bin.length + 2 := by
            simp only [List.length_cons, List.length_append, List.length_nil]
            try omega
          cases d with
          | zero => rw [hlen] at hd; exfalso; omega
          | succ d =>
              have hassoc : (tb 0x04 :: (bbt ++ bin ++ [tb 0x0B])) ++ r
                  = tb 0x04 :: (bbt ++ (bin ++ (tb 0x0B :: r))) := by simp
              have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ bin.length →
                  Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
                intro b' i' r' hb' hbi
                refine ihN d b' i' r' ?_ ?_ hbi
                · rw [hlen] at hN; omega
                · rw [hlen] at hd; omega
              have hins' := decInstrs_complete_of d bin.length hI
                (bin ++ (tb 0x0B :: r)).length bin ins (tb 0x0B :: r) hins (by omega)
                (by have := Binstrs_length_le hins; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              rw [hassoc, decInstr]
              simp only [if_true, tb_val 0x04 (by decide), if_neg (by decide : ¬ ((0x04 : Nat) = 0x02)),
                if_neg (by decide : ¬ ((0x04 : Nat) = 0x03)), if_pos rfl,
                decBlocktype_complete bbt bt (bin ++ (tb 0x0B :: r)) hbt, hins',
                tb_val 0x0B (by decide), if_pos rfl]
      | ifElse bbt b₁ b₂ bt ins₁ ins₂ hbt hin₁ hin₂ =>
          have hlen : (tb 0x04 :: (bbt ++ b₁ ++ [tb 0x05] ++ b₂ ++ [tb 0x0B])).length
              = bbt.length + b₁.length + b₂.length + 3 := by
            simp only [List.length_cons, List.length_append, List.length_nil]
            try omega
          cases d with
          | zero => rw [hlen] at hd; exfalso; omega
          | succ d =>
              have hassoc : (tb 0x04 :: (bbt ++ b₁ ++ [tb 0x05] ++ b₂ ++ [tb 0x0B])) ++ r
                  = tb 0x04 :: (bbt ++ (b₁ ++ (tb 0x05 :: (b₂ ++ (tb 0x0B :: r))))) := by simp
              have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes),
                  b'.length ≤ b₁.length + b₂.length →
                  Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
                intro b' i' r' hb' hbi
                refine ihN d b' i' r' ?_ ?_ hbi
                · rw [hlen] at hN; omega
                · rw [hlen] at hd; omega
              have e₁ := decInstrs_complete_of d (b₁.length + b₂.length) hI
                (b₁ ++ (tb 0x05 :: (b₂ ++ (tb 0x0B :: r)))).length b₁ ins₁
                (tb 0x05 :: (b₂ ++ (tb 0x0B :: r))) hin₁ (by omega)
                (by have := Binstrs_length_le hin₁; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              have e₂ := decInstrs_complete_of d (b₁.length + b₂.length) hI
                (b₂ ++ (tb 0x0B :: r)).length b₂ ins₂ (tb 0x0B :: r) hin₂ (by omega)
                (by have := Binstrs_length_le hin₂; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              rw [hassoc, decInstr]
              simp only [if_true, tb_val 0x04 (by decide), if_neg (by decide : ¬ ((0x04 : Nat) = 0x02)),
                if_neg (by decide : ¬ ((0x04 : Nat) = 0x03)), if_pos rfl,
                decBlocktype_complete bbt bt (b₁ ++ (tb 0x05 :: (b₂ ++ (tb 0x0B :: r)))) hbt,
                e₁, tb_val 0x05 (by decide),
                if_neg (by decide : ¬ ((0x05 : Nat) = 0x0B)), if_pos rfl, e₂,
                expectByte_eq 0x0B (by decide) r]
      | tryTable bbt bc bin bt cs ins hbt hcs hins =>
          have hlen : (tb 0x1F :: (bbt ++ bc ++ bin ++ [tb 0x0B])).length
              = bbt.length + bc.length + bin.length + 2 := by
            simp only [List.length_cons, List.length_append, List.length_nil]
            try omega
          cases d with
          | zero => rw [hlen] at hd; exfalso; omega
          | succ d =>
              have hassoc : (tb 0x1F :: (bbt ++ bc ++ bin ++ [tb 0x0B])) ++ r
                  = tb 0x1F :: (bbt ++ (bc ++ (bin ++ (tb 0x0B :: r)))) := by simp
              have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ bin.length →
                  Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
                intro b' i' r' hb' hbi
                refine ihN d b' i' r' ?_ ?_ hbi
                · rw [hlen] at hN; omega
                · rw [hlen] at hd; omega
              have hins' := decInstrs_complete_of d bin.length hI
                (bin ++ (tb 0x0B :: r)).length bin ins (tb 0x0B :: r) hins (by omega)
                (by have := Binstrs_length_le hins; simp only [List.length_append]; omega)
                (by simp [isEndOrElse, tb, Byte.ofNat])
              have hcsv : cs = ⟨cs.val, cs.property⟩ := rfl
              rw [hassoc, decInstr]
              simp only [if_true, tb_val 0x1F (by decide), if_neg (by decide : ¬ ((0x1F : Nat) = 0x02)),
                if_neg (by decide : ¬ ((0x1F : Nat) = 0x03)),
                if_neg (by decide : ¬ ((0x1F : Nat) = 0x04)), if_pos rfl,
                decBlocktype_complete bbt bt (bc ++ (bin ++ (tb 0x0B :: r))) hbt,
                decList_complete decCatch_complete bc cs.val (bin ++ (tb 0x0B :: r)) hcs,
                dif_pos cs.property, hins', expectByte_eq 0x0B (by decide) r]
      | ofParametric =>
          rename_i h'
          have hf := flat_BinstrParametric h' r
          have hne := Binstr_ne_nil (Binstr.ofParametric _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofControl =>
          rename_i h'
          have hf := flat_BinstrControl h' r
          have hne := Binstr_ne_nil (Binstr.ofControl _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofLocal =>
          rename_i h'
          have hf := flat_BinstrLocal h' r
          have hne := Binstr_ne_nil (Binstr.ofLocal _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofGlobal =>
          rename_i h'
          have hf := flat_BinstrGlobal h' r
          have hne := Binstr_ne_nil (Binstr.ofGlobal _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofTable =>
          rename_i h'
          have hf := flat_BinstrTable h' r
          have hne := Binstr_ne_nil (Binstr.ofTable _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofMemory =>
          rename_i h'
          have hf := flat_BinstrMemory h' r
          have hne := Binstr_ne_nil (Binstr.ofMemory _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofRef =>
          rename_i h'
          have hf := flat_BinstrRef h' r
          have hne := Binstr_ne_nil (Binstr.ofRef _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofStruct =>
          rename_i h'
          have hf := flat_BinstrStruct h' r
          have hne := Binstr_ne_nil (Binstr.ofStruct _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofArray =>
          rename_i h'
          have hf := flat_BinstrArray h' r
          have hne := Binstr_ne_nil (Binstr.ofArray _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofCast =>
          rename_i h'
          have hf := flat_BinstrCast h' r
          have hne := Binstr_ne_nil (Binstr.ofCast _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofExtern =>
          rename_i h'
          have hf := flat_BinstrExtern h' r
          have hne := Binstr_ne_nil (Binstr.ofExtern _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofI31 =>
          rename_i h'
          have hf := flat_BinstrI31 h' r
          have hne := Binstr_ne_nil (Binstr.ofI31 _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofNum =>
          rename_i h'
          have hf := flat_BinstrNum h' r
          have hne := Binstr_ne_nil (Binstr.ofNum _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecMem =>
          rename_i h'
          have hf := flat_BinstrVecMem h' r
          have hne := Binstr_ne_nil (Binstr.ofVecMem _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecRel =>
          rename_i h'
          have hf := flat_BinstrVecRel h' r
          have hne := Binstr_ne_nil (Binstr.ofVecRel _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecV128 =>
          rename_i h'
          have hf := flat_BinstrVecV128 h' r
          have hne := Binstr_ne_nil (Binstr.ofVecV128 _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecInt8And16 =>
          rename_i h'
          have hf := flat_BinstrVecInt8And16 h' r
          have hne := Binstr_ne_nil (Binstr.ofVecInt8And16 _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecInt32And64 =>
          rename_i h'
          have hf := flat_BinstrVecInt32And64 h' r
          have hne := Binstr_ne_nil (Binstr.ofVecInt32And64 _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf
      | ofVecFloat =>
          rename_i h'
          have hf := flat_BinstrVecFloat h' r
          have hne := Binstr_ne_nil (Binstr.ofVecFloat _ _ h')
          cases d with
          | zero =>
              exfalso
              cases b with
              | nil => exact hne rfl
              | cons _ _ => simp at hd
          | succ d =>
              cases b with
              | nil => exact absurd rfl hne
              | cons c t => exact decInstr_of_flat hf

/-- **COMPLETENESS OF THE INSTRUCTION DECODER**, in the `Complete`-at-fuel form
the layers above use. -/
theorem decInstr_completeD (d : Nat) (b : Bytes) (i : Instr) (r : Bytes)
    (hd : b.length ≤ d) (h : Binstr b i) : decInstr d (b ++ r) = .ok (i, r) :=
  decInstr_complete b.length d b i r (Nat.le_refl _) hd h

/-- **COMPLETENESS OF `Bexpr`.**  An `END`-terminated instruction sequence is
decoded exactly. -/
theorem decExpr_completeD (d : Nat) (b : Bytes) (e : Expr) (r : Bytes)
    (hd : b.length ≤ d) (h : Bexpr b e) : decExpr d (b ++ r) = .ok (e, r) := by
  cases h with
  | mk bs ins hins =>
      have hlen : (bs ++ [tb 0x0B]).length = bs.length + 1 := by simp
      have hassoc : (bs ++ [tb 0x0B]) ++ r = bs ++ (tb 0x0B :: r) := by simp
      have hI : ∀ (b' : Bytes) (i' : Instr) (r' : Bytes), b'.length ≤ bs.length →
          Binstr b' i' → decInstr d (b' ++ r') = .ok (i', r') := by
        intro b' i' r' hb' hbi
        refine decInstr_complete b'.length d b' i' r' (Nat.le_refl _) ?_ hbi
        rw [hlen] at hd; omega
      have hins' := decInstrs_complete_of d bs.length hI
        (bs ++ (tb 0x0B :: r)).length bs ins (tb 0x0B :: r) hins (Nat.le_refl _)
        (by have := Binstrs_length_le hins; simp only [List.length_append]; omega)
        (by simp [isEndOrElse, tb, Byte.ofNat])
      rw [hassoc, decExpr]
      simp only [hins', expectByte_eq 0x0B (by decide) r]

end WasmGemmGnaf.Wasm.Core.Decode
