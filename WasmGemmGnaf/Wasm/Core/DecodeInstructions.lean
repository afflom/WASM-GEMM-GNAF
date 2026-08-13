/-
  Wasm/Core/DecodeInstructions.lean --- the executable decoder for the
  non-vector, non-GC fragment of `5.3-binary.instructions.spectec`, proved SOUND
  against `Wasm/Core/BinaryGrammar/{Instructions,Expressions}.lean`.

  SCOPE, STATED EXACTLY.  The decoder implements every production of `Binstr`
  EXCEPT the `0xFB` (garbage collection) and `0xFD` (SIMD) opcode spaces.  The
  covered set is named by `Instr.covered`, a decidable predicate on the abstract
  syntax which is `false` on exactly the instruction constructors those two
  spaces produce.  It is a specification of the gap, not a theorem: nothing
  below is proved by appeal to it.

  * `decInstr_sound` is unconditional: whatever the decoder accepts really is
    derivable in the pinned grammar, for the WHOLE format.  A decoder that only
    implements part of the format is still sound on all of it, because the part
    it does not implement it rejects.
  * THERE IS NO `decInstr_complete`, and none is asserted.  Completeness of the
    instruction decoder against `Binstr` is an open obligation.  The operand
    grammars it would rest on -- `decBlocktype_complete`, `decCatch_complete`,
    `decMemarg_complete`, and every completeness lemma of `DecodeTypes.lean` and
    `DecodeParser.lean` -- are proved; the opcode dispatch and the recursive
    knot are not.  Omitting the theorem is the conforming representation of that
    gap.

  `Bprefixed` IS A `Bu32`, NOT A BYTE.  The `0xFC` selector is decoded with
  `decU32`, so `0xFC 0x8C 0x00` decodes as `TABLE.INIT` just as `0xFC 0x0C`
  does.  A byte-keyed opcode table would reject the first and be incomplete.

  FUEL.  `decInstr` is structurally recursive on a nesting-depth bound and
  `decInstrs` on an instruction-count bound; `decExpr` supplies both from the
  length of its input, which is always enough because every instruction and
  every nesting level consumes at least one byte.  There is no `partial`.
-/
import WasmGemmGnaf.Wasm.Core.DecodeTypes

set_option autoImplicit false
set_option maxRecDepth 100000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## The covered fragment -/

mutual

/-- The instruction constructors this decoder covers: everything the pinned
grammar produces outside the `0xFB` and `0xFD` opcode spaces. -/
def Instr.covered : Instr → Bool
  | .structNew _ | .structNewDefault _ | .structGet _ _ _ | .structSet _ _ => false
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ | .arrayNewData _ _
  | .arrayNewElem _ _ | .arrayGet _ _ | .arraySet _ | .arrayLen | .arrayFill _
  | .arrayCopy _ _ | .arrayInitData _ _ | .arrayInitElem _ _ => false
  | .refTest _ | .refCast _ | .brOnCast _ _ _ | .brOnCastFail _ _ _ => false
  | .anyConvertExtern | .externConvertAny | .refI31 | .i31Get _ => false
  | .callRef _ | .returnCallRef _ => false
  | .vconst _ _ | .vload _ _ _ _ | .vloadLane _ _ _ _ _ | .vstore _ _ _
  | .vstoreLane _ _ _ _ _ => false
  | .vvunop _ _ | .vvbinop _ _ | .vvternop _ _ | .vvtestop _ _ => false
  | .vunop _ _ | .vbinop _ _ | .vternop _ _ | .vtestop _ _ | .vrelop _ _
  | .vshiftop _ _ | .vbitmask _ | .vswizzlop _ _ | .vshuffle _ _
  | .vextunop _ _ _ | .vextbinop _ _ _ | .vextternop _ _ _ | .vnarrow _ _ _
  | .vcvtop _ _ _ | .vsplat _ | .vextractLane _ _ _ | .vreplaceLane _ _ => false
  | .block _ body => InstrSeq.covered body
  | .loop _ body => InstrSeq.covered body
  | .ifElse _ thn els => InstrSeq.covered thn && InstrSeq.covered els
  | .tryTable _ _ body => InstrSeq.covered body
  | _ => true

/-- `Instr.covered` on a sequence. -/
def InstrSeq.covered : InstrSeq → Bool
  | .nil => true
  | .cons i rest => Instr.covered i && InstrSeq.covered rest

end

/-- `Instr.covered` on an ordinary list. -/
def instrsCovered : List Instr → Bool
  | [] => true
  | i :: rest => Instr.covered i && instrsCovered rest

theorem instrsCovered_ofList : ∀ is : List Instr,
    InstrSeq.covered (InstrSeq.ofList is) = instrsCovered is := by
  intro is
  induction is with
  | nil => rfl
  | cons i rest ih => rw [InstrSeq.ofList, InstrSeq.covered, instrsCovered, ih]

/-! ## Opcode tables

Generated from the pinned productions: one entry per alternative of
`5.3-binary.instructions.spectec` that carries no immediate. -/

/-- Every one-byte opcode of the covered fragment that carries no immediate.
Read off `5.3-binary.instructions.spectec`, one entry per production. -/
def op0 : Nat → Option Instr
  | 0x00 => some .unreachable
  | 0x01 => some .nop
  | 0x0A => some .throwRef
  | 0x0F => some .ret
  | 0x1A => some .drop
  | 0x1B => some (.select none)
  | 0x45 => some (.testop .i32 (.int .eqz))
  | 0x46 => some (.relop .i32 (.int .eq))
  | 0x47 => some (.relop .i32 (.int .ne))
  | 0x48 => some (.relop .i32 (.int (.lt .s)))
  | 0x49 => some (.relop .i32 (.int (.lt .u)))
  | 0x4A => some (.relop .i32 (.int (.gt .s)))
  | 0x4B => some (.relop .i32 (.int (.gt .u)))
  | 0x4C => some (.relop .i32 (.int (.le .s)))
  | 0x4D => some (.relop .i32 (.int (.le .u)))
  | 0x4E => some (.relop .i32 (.int (.ge .s)))
  | 0x4F => some (.relop .i32 (.int (.ge .u)))
  | 0x50 => some (.testop .i64 (.int .eqz))
  | 0x51 => some (.relop .i64 (.int .eq))
  | 0x52 => some (.relop .i64 (.int .ne))
  | 0x53 => some (.relop .i64 (.int (.lt .s)))
  | 0x54 => some (.relop .i64 (.int (.lt .u)))
  | 0x55 => some (.relop .i64 (.int (.gt .s)))
  | 0x56 => some (.relop .i64 (.int (.gt .u)))
  | 0x57 => some (.relop .i64 (.int (.le .s)))
  | 0x58 => some (.relop .i64 (.int (.le .u)))
  | 0x59 => some (.relop .i64 (.int (.ge .s)))
  | 0x5A => some (.relop .i64 (.int (.ge .u)))
  | 0x5B => some (.relop .f32 (.float .eq))
  | 0x5C => some (.relop .f32 (.float .ne))
  | 0x5D => some (.relop .f32 (.float .lt))
  | 0x5E => some (.relop .f32 (.float .gt))
  | 0x5F => some (.relop .f32 (.float .le))
  | 0x60 => some (.relop .f32 (.float .ge))
  | 0x61 => some (.relop .f64 (.float .eq))
  | 0x62 => some (.relop .f64 (.float .ne))
  | 0x63 => some (.relop .f64 (.float .lt))
  | 0x64 => some (.relop .f64 (.float .gt))
  | 0x65 => some (.relop .f64 (.float .le))
  | 0x66 => some (.relop .f64 (.float .ge))
  | 0x67 => some (.unop .i32 (.int .clz))
  | 0x68 => some (.unop .i32 (.int .ctz))
  | 0x69 => some (.unop .i32 (.int .popcnt))
  | 0x6A => some (.binop .i32 (.int .add))
  | 0x6B => some (.binop .i32 (.int .sub))
  | 0x6C => some (.binop .i32 (.int .mul))
  | 0x6D => some (.binop .i32 (.int (.div .s)))
  | 0x6E => some (.binop .i32 (.int (.div .u)))
  | 0x6F => some (.binop .i32 (.int (.rem .s)))
  | 0x70 => some (.binop .i32 (.int (.rem .u)))
  | 0x71 => some (.binop .i32 (.int .and))
  | 0x72 => some (.binop .i32 (.int .or))
  | 0x73 => some (.binop .i32 (.int .xor))
  | 0x74 => some (.binop .i32 (.int .shl))
  | 0x75 => some (.binop .i32 (.int (.shr .s)))
  | 0x76 => some (.binop .i32 (.int (.shr .u)))
  | 0x77 => some (.binop .i32 (.int .rotl))
  | 0x78 => some (.binop .i32 (.int .rotr))
  | 0x79 => some (.unop .i64 (.int .clz))
  | 0x7A => some (.unop .i64 (.int .ctz))
  | 0x7B => some (.unop .i64 (.int .popcnt))
  | 0x7C => some (.binop .i64 (.int .add))
  | 0x7D => some (.binop .i64 (.int .sub))
  | 0x7E => some (.binop .i64 (.int .mul))
  | 0x7F => some (.binop .i64 (.int (.div .s)))
  | 0x80 => some (.binop .i64 (.int (.div .u)))
  | 0x81 => some (.binop .i64 (.int (.rem .s)))
  | 0x82 => some (.binop .i64 (.int (.rem .u)))
  | 0x83 => some (.binop .i64 (.int .and))
  | 0x84 => some (.binop .i64 (.int .or))
  | 0x85 => some (.binop .i64 (.int .xor))
  | 0x86 => some (.binop .i64 (.int .shl))
  | 0x87 => some (.binop .i64 (.int (.shr .s)))
  | 0x88 => some (.binop .i64 (.int (.shr .u)))
  | 0x89 => some (.binop .i64 (.int .rotl))
  | 0x8A => some (.binop .i64 (.int .rotr))
  | 0x8B => some (.unop .f32 (.float .abs))
  | 0x8C => some (.unop .f32 (.float .neg))
  | 0x8D => some (.unop .f32 (.float .ceil))
  | 0x8E => some (.unop .f32 (.float .floor))
  | 0x8F => some (.unop .f32 (.float .trunc))
  | 0x90 => some (.unop .f32 (.float .nearest))
  | 0x91 => some (.unop .f32 (.float .sqrt))
  | 0x92 => some (.binop .f32 (.float .add))
  | 0x93 => some (.binop .f32 (.float .sub))
  | 0x94 => some (.binop .f32 (.float .mul))
  | 0x95 => some (.binop .f32 (.float .div))
  | 0x96 => some (.binop .f32 (.float .min))
  | 0x97 => some (.binop .f32 (.float .max))
  | 0x98 => some (.binop .f32 (.float .copysign))
  | 0x99 => some (.unop .f64 (.float .abs))
  | 0x9A => some (.unop .f64 (.float .neg))
  | 0x9B => some (.unop .f64 (.float .ceil))
  | 0x9C => some (.unop .f64 (.float .floor))
  | 0x9D => some (.unop .f64 (.float .trunc))
  | 0x9E => some (.unop .f64 (.float .nearest))
  | 0x9F => some (.unop .f64 (.float .sqrt))
  | 0xA0 => some (.binop .f64 (.float .add))
  | 0xA1 => some (.binop .f64 (.float .sub))
  | 0xA2 => some (.binop .f64 (.float .mul))
  | 0xA3 => some (.binop .f64 (.float .div))
  | 0xA4 => some (.binop .f64 (.float .min))
  | 0xA5 => some (.binop .f64 (.float .max))
  | 0xA6 => some (.binop .f64 (.float .copysign))
  | 0xA7 => some (.cvtop .i32 .i64 (.ii .wrap))
  | 0xA8 => some (.cvtop .i32 .f32 (.fi (.trunc .s)))
  | 0xA9 => some (.cvtop .i32 .f32 (.fi (.trunc .u)))
  | 0xAA => some (.cvtop .i32 .f64 (.fi (.trunc .s)))
  | 0xAB => some (.cvtop .i32 .f64 (.fi (.trunc .u)))
  | 0xAC => some (.cvtop .i64 .i32 (.ii (.extend .s)))
  | 0xAD => some (.cvtop .i64 .i32 (.ii (.extend .u)))
  | 0xAE => some (.cvtop .i64 .f32 (.fi (.trunc .s)))
  | 0xAF => some (.cvtop .i64 .f32 (.fi (.trunc .u)))
  | 0xB0 => some (.cvtop .i64 .f64 (.fi (.trunc .s)))
  | 0xB1 => some (.cvtop .i64 .f64 (.fi (.trunc .u)))
  | 0xB2 => some (.cvtop .f32 .i32 (.ifl (.convert .s)))
  | 0xB3 => some (.cvtop .f32 .i32 (.ifl (.convert .u)))
  | 0xB4 => some (.cvtop .f32 .i64 (.ifl (.convert .s)))
  | 0xB5 => some (.cvtop .f32 .i64 (.ifl (.convert .u)))
  | 0xB6 => some (.cvtop .f32 .f64 (.ff .demote))
  | 0xB7 => some (.cvtop .f64 .i32 (.ifl (.convert .s)))
  | 0xB8 => some (.cvtop .f64 .i32 (.ifl (.convert .u)))
  | 0xB9 => some (.cvtop .f64 .i64 (.ifl (.convert .s)))
  | 0xBA => some (.cvtop .f64 .i64 (.ifl (.convert .u)))
  | 0xBB => some (.cvtop .f32 .f64 (.ff .promote))
  | 0xBC => some (.cvtop .i32 .f32 (.fi .reinterpret))
  | 0xBD => some (.cvtop .i64 .f64 (.fi .reinterpret))
  | 0xBE => some (.cvtop .f32 .i32 (.ifl .reinterpret))
  | 0xBF => some (.cvtop .f64 .i64 (.ifl .reinterpret))
  | 0xC0 => some (.unop .i32 (.int (.extend .s8)))
  | 0xC1 => some (.unop .i32 (.int (.extend .s16)))
  | 0xC2 => some (.unop .i64 (.int (.extend .s8)))
  | 0xC3 => some (.unop .i64 (.int (.extend .s16)))
  | 0xC4 => some (.unop .i64 (.int (.extend .s32)))
  | 0xD1 => some .refIsNull
  | 0xD3 => some .refEq
  | 0xD4 => some .refAsNonNull
  | _ => none

theorem op0_lt {v : Nat} {i : Instr} (h : op0 v = some i) : v < 0x100 := by
  unfold op0 at h; split at h <;> first | omega | simp at h

theorem op0_sound {v : Nat} {i : Instr} (h : op0 v = some i) : Binstr [tb v] i := by
  unfold op0 at h
  split at h
  · cases h; exact Binstr.ofParametric _ _ BinstrParametric.unreachable
  · cases h; exact Binstr.ofParametric _ _ BinstrParametric.nop
  · cases h; exact Binstr.ofControl _ _ BinstrControl.throwRef
  · cases h; exact Binstr.ofControl _ _ BinstrControl.ret
  · cases h; exact Binstr.ofParametric _ _ BinstrParametric.drop
  · cases h; exact Binstr.ofParametric _ _ BinstrParametric.select
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Eqz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Eq
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Ne
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32LtS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32LtU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32GtS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32GtU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32LeS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32LeU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32GeS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32GeU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Eqz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Eq
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Ne
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64LtS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64LtU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64GtS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64GtU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64LeS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64LeU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64GeS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64GeU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Eq
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Ne
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Lt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Gt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Le
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Ge
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Eq
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Ne
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Lt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Gt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Le
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Ge
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Clz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Ctz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Popcnt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Add
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Sub
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Mul
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32DivS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32DivU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32RemS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32RemU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32And
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Or
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Xor
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Shl
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32ShrS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32ShrU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Rotl
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Rotr
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Clz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Ctz
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Popcnt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Add
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Sub
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Mul
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64DivS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64DivU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64RemS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64RemU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64And
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Or
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Xor
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Shl
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64ShrS
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64ShrU
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Rotl
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Rotr
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Abs
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Neg
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Ceil
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Floor
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Trunc
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Nearest
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Sqrt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Add
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Sub
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Mul
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Div
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Min
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Max
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32Copysign
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Abs
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Neg
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Ceil
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Floor
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Trunc
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Nearest
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Sqrt
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Add
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Sub
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Mul
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Div
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Min
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Max
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64Copysign
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32WrapI64
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32TruncF32S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32TruncF32U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32TruncF64S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32TruncF64U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64ExtendI32S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64ExtendI32U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64TruncF32S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64TruncF32U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64TruncF64S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64TruncF64U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32ConvertI32S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32ConvertI32U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32ConvertI64S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32ConvertI64U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32DemoteF64
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64ConvertI32S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64ConvertI32U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64ConvertI64S
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64ConvertI64U
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32PromoteF64
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32ReinterpretF32
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64ReinterpretF64
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f32ReinterpretI32
  · cases h; exact Binstr.ofNum _ _ BinstrNum.f64ReinterpretI64
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Extend8
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i32Extend16
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Extend8
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Extend16
  · cases h; exact Binstr.ofNum _ _ BinstrNum.i64Extend32
  · cases h; exact Binstr.ofRef _ _ BinstrRef.isNull
  · cases h; exact Binstr.ofRef _ _ BinstrRef.eq
  · cases h; exact Binstr.ofRef _ _ BinstrRef.asNonNull
  · simp at h

/-- Every `0xFC k` opcode of the covered fragment that carries no immediate. -/
def opFC0 : Nat → Option Instr
  | 0 => some (.cvtop .i32 .f32 (.fi (.truncSat .s)))
  | 1 => some (.cvtop .i32 .f32 (.fi (.truncSat .u)))
  | 2 => some (.cvtop .i32 .f64 (.fi (.truncSat .s)))
  | 3 => some (.cvtop .i32 .f64 (.fi (.truncSat .u)))
  | 4 => some (.cvtop .i64 .f32 (.fi (.truncSat .s)))
  | 5 => some (.cvtop .i64 .f32 (.fi (.truncSat .u)))
  | 6 => some (.cvtop .i64 .f64 (.fi (.truncSat .s)))
  | 7 => some (.cvtop .i64 .f64 (.fi (.truncSat .u)))
  | _ => none

theorem opFC0_sound {k : Nat} {i : Instr} {bo : Bytes} (hk : opFC0 k = some i)
    (hb : Bprefixed 0xFC k bo) : Binstr bo i := by
  unfold opFC0 at hk
  split at hk
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i32TruncSatF32S bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i32TruncSatF32U bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i32TruncSatF64S bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i32TruncSatF64U bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i64TruncSatF32S bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i64TruncSatF32U bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i64TruncSatF64S bo hb)
  · cases hk; exact Binstr.ofNum _ _ (BinstrNum.i64TruncSatF64U bo hb)
  · simp at hk

/-! ## Shared operands -/

/-- `grammar Bblocktype : blocktype`.  The three alternatives are separated by
the first byte: `0x40` is the empty result, a non-negative `Bs33` starts below
`0x40` or at `0x80` and above (`Bs33_head`), and every `Bvaltype` byte lies
strictly between. -/
def decBlocktype (bs : Bytes) : Except Fault (BlockType × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x40 then .ok (.result none, r)
      else if b.val < 0x40 ∨ 0x80 ≤ b.val then
        (match decS33Idx bs with
         | .error e => .error e
         | .ok (x, r') => .ok (.idx x, r'))
      else
        (match decValtype bs with
         | .error e => .error e
         | .ok (t, r') => .ok (.result (some t), r'))

theorem decBlocktype_sound : Sound Bblocktype decBlocktype := by
  intro bs bt r h
  cases bs with
  | nil => simp [decBlocktype] at h
  | cons b bs =>
      rw [decBlocktype] at h
      split at h
      · rename_i hb
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← hr]; rfl, ?_⟩
        rw [← hv, byte_eq_tb (by decide) hb]
        exact Bblocktype.empty
      · split at h
        · split at h
          · simp at h
          · rename_i x r' hx
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, i, hbb, hs, hnn, hval⟩ := decS33Idx_sound hx
            exact ⟨bb, by rw [hbb, hr], by rw [← hv]; exact Bblocktype.idx bb i x hs hnn hval⟩
        · split at h
          · simp at h
          · rename_i t r' ht
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bb, hbb, hd⟩ := decValtype_sound (b :: bs) t r' ht
            exact ⟨bb, by rw [hbb, hr], by rw [← hv]; exact Bblocktype.val bb t hd⟩

/-- Every `Bvaltype` byte lies in `[0x40, 0x80)` and is not `0x40`. -/
theorem Bvaltype_head {bs : Bytes} {t : ValType} (h : Bvaltype bs t) :
    ∃ b u, bs = b :: u ∧ ¬ (b.val = 0x40) ∧ ¬ (b.val < 0x40 ∨ 0x80 ≤ b.val) := by
  cases h with
  | num nt hn => cases hn <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)
  | vec vt hv => cases hv <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)
  | ref rt hr =>
      cases hr with
      | null bs' ht _ => exact ⟨tb 0x63, bs', rfl, by decide, by decide⟩
      | nonNull bs' ht _ => exact ⟨tb 0x64, bs', rfl, by decide, by decide⟩
      | abs _bs ht ha => cases ha <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)

theorem decBlocktype_complete : Complete Bblocktype decBlocktype := by
  intro b bt r h
  cases h with
  | empty => rfl
  | val bs t hd =>
      obtain ⟨b0, u0, hb0, hne, hnr⟩ := Bvaltype_head hd
      subst hb0
      show decBlocktype (b0 :: (u0 ++ r)) = _
      have hstep : decValtype (b0 :: (u0 ++ r)) = .ok (t, r) :=
        decValtype_complete (b0 :: u0) t r hd
      rw [decBlocktype, if_neg hne, if_neg hnr]
      simp only [hstep]
  | idx bs i x hs hnn hval =>
      obtain ⟨b0, u0, hb0, hrange⟩ := Bs33_head hs hnn
      subst hb0
      show decBlocktype (b0 :: (u0 ++ r)) = _
      have hne : ¬ (b0.val = 0x40) := by omega
      have hstep : decS33Idx (b0 :: (u0 ++ r)) = .ok (x, r) :=
        decS33Idx_complete r hs hnn hval
      rw [decBlocktype, if_neg hne, if_pos hrange]
      simp only [hstep]

/-- `grammar Bcatch : catch`. -/
def decCatch (bs : Bytes) : Except Fault (Catch × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then
        (match decIdx r with
         | .error e => .error e
         | .ok (x, r₁) =>
             match decIdx r₁ with
             | .error e => .error e
             | .ok (l, r₂) => .ok (.tag x l, r₂))
      else if b.val = 0x01 then
        (match decIdx r with
         | .error e => .error e
         | .ok (x, r₁) =>
             match decIdx r₁ with
             | .error e => .error e
             | .ok (l, r₂) => .ok (.tagRef x l, r₂))
      else if b.val = 0x02 then
        (match decIdx r with
         | .error e => .error e
         | .ok (l, r₁) => .ok (.all l, r₁))
      else if b.val = 0x03 then
        (match decIdx r with
         | .error e => .error e
         | .ok (l, r₁) => .ok (.allRef l, r₁))
      else .error .opcode

theorem decCatch_sound : Sound Bcatch decCatch := by
  intro bs c r h
  cases bs with
  | nil => simp [decCatch] at h
  | cons b bs =>
      rw [decCatch] at h
      split at h
      · rename_i hb
        split at h
        · simp at h
        · rename_i x r₁ hx
          split at h
          · simp at h
          · rename_i l r₂ hl
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨b₁, hb₁, hd₁⟩ := decIdx_sound bs x r₁ hx
            obtain ⟨b₂, hb₂, hd₂⟩ := decIdx_sound r₁ l r₂ hl
            refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
            rw [← hv, byte_eq_tb (by decide) hb]
            exact Bcatch.tag b₁ b₂ x l hd₁ hd₂
      · split at h
        · rename_i hb
          split at h
          · simp at h
          · rename_i x r₁ hx
            split at h
            · simp at h
            · rename_i l r₂ hl
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨b₁, hb₁, hd₁⟩ := decIdx_sound bs x r₁ hx
              obtain ⟨b₂, hb₂, hd₂⟩ := decIdx_sound r₁ l r₂ hl
              refine ⟨b :: (b₁ ++ b₂), by rw [hb₁, hb₂, hr]; simp, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Bcatch.tagRef b₁ b₂ x l hd₁ hd₂
        · split at h
          · rename_i hb
            split at h
            · simp at h
            · rename_i l r₁ hl
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨b₁, hb₁, hd₁⟩ := decIdx_sound bs l r₁ hl
              refine ⟨b :: b₁, by rw [hb₁, hr]; rfl, ?_⟩
              rw [← hv, byte_eq_tb (by decide) hb]
              exact Bcatch.all b₁ l hd₁
          · split at h
            · rename_i hb
              split at h
              · simp at h
              · rename_i l r₁ hl
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                obtain ⟨b₁, hb₁, hd₁⟩ := decIdx_sound bs l r₁ hl
                refine ⟨b :: b₁, by rw [hb₁, hr]; rfl, ?_⟩
                rw [← hv, byte_eq_tb (by decide) hb]
                exact Bcatch.allRef b₁ l hd₁
            · simp at h

theorem decCatch_complete : Complete Bcatch decCatch := by
  intro b c r h
  cases h with
  | tag bx bl x l hx hl =>
      show decCatch (tb 0x00 :: ((bx ++ bl) ++ r)) = _
      rw [List.append_assoc]
      simp [decCatch, tb, Byte.ofNat, decIdx_complete bx x (bl ++ r) hx,
        decIdx_complete bl l r hl]
  | tagRef bx bl x l hx hl =>
      show decCatch (tb 0x01 :: ((bx ++ bl) ++ r)) = _
      rw [List.append_assoc]
      simp [decCatch, tb, Byte.ofNat, decIdx_complete bx x (bl ++ r) hx,
        decIdx_complete bl l r hl]
  | all bl l hl =>
      show decCatch (tb 0x02 :: (bl ++ r)) = _
      simp [decCatch, tb, Byte.ofNat, decIdx_complete bl l r hl]
  | allRef bl l hl =>
      show decCatch (tb 0x03 :: (bl ++ r)) = _
      simp [decCatch, tb, Byte.ofNat, decIdx_complete bl l r hl]

/-- `grammar Bmemarg : memidxop`.  The alignment field discriminates: below
`2^6` the memory index is `0` and absent from the encoding; in `[2^6, 2^7)` an
explicit `Bmemidx` follows and the alignment is `n - 2^6`. -/
def decMemarg (bs : Bytes) : Except Fault (MemIdxOp × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (n, r₁) =>
      if n.val < 2 ^ 6 then
        (match decU32 r₁ with
         | .error e => .error e
         | .ok (m, r₂) => .ok ((⟨0, two_pow_pos 32⟩, { align := n, offset := m }), r₂))
      else if hn : n.val < 2 ^ 7 then
        (match decIdx r₁ with
         | .error e => .error e
         | .ok (x, r₂) =>
             match decU32 r₂ with
             | .error e => .error e
             | .ok (m, r₃) =>
                 .ok ((x, { align := ⟨n.val - 2 ^ 6, by omega⟩, offset := m }), r₃))
      else .error .side

theorem decMemarg_sound : Sound Bmemarg decMemarg := by
  intro bs mo r h
  rw [decMemarg] at h
  split at h
  · simp at h
  · rename_i n r₁ hn
    obtain ⟨bn, hbn, hdn⟩ := decU32_sound bs n r₁ hn
    split at h
    · rename_i hlt
      split at h
      · simp at h
      · rename_i m r₂ hm
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨bm, hbm, hdm⟩ := decU32_sound r₁ m r₂ hm
        refine ⟨bn ++ bm, by rw [hbn, hbm, hr]; simp, ?_⟩
        rw [← hv]
        exact Bmemarg.mem0 bn bm n m ⟨0, two_pow_pos 32⟩ hdn hdm hlt rfl
    · rename_i hge
      split at h
      · rename_i hlt7
        split at h
        · simp at h
        · rename_i x r₂ hx
          split at h
          · simp at h
          · rename_i m r₃ hm
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bx, hbx, hdx⟩ := decIdx_sound r₁ x r₂ hx
            obtain ⟨bm, hbm, hdm⟩ := decU32_sound r₂ m r₃ hm
            refine ⟨bn ++ bx ++ bm, by rw [hbn, hbx, hbm, hr]; simp, ?_⟩
            rw [← hv]
            exact Bmemarg.memx bn bx bm n ⟨n.val - 2 ^ 6, by omega⟩ m x hdn hdx hdm
              (by omega) hlt7 rfl
      · simp at h

theorem decMemarg_complete : Complete Bmemarg decMemarg := by
  intro b mo r h
  cases h with
  | mem0 bn bm n m x hn hm hlt hx0 =>
      rw [List.append_assoc]
      have hx : (⟨0, two_pow_pos 32⟩ : MemIdx) = x := Subtype.ext hx0.symm
      simp [decMemarg, decU32_complete bn n (bm ++ r) hn, hlt,
        decU32_complete bm m r hm, hx]
  | memx bn bx bm n a m x hn hx hm hge hlt ha =>
      have hnot : ¬ (n.val < 2 ^ 6) := by omega
      have ha' : (⟨n.val - 2 ^ 6, by omega⟩ : U32) = a := Subtype.ext ha.symm
      rw [List.append_assoc, List.append_assoc]
      simp [decMemarg, decU32_complete bn n (bx ++ (bm ++ r)) hn, hnot, hlt,
        decIdx_complete bx x (bm ++ r) hx, decU32_complete bm m r hm, ha']

/-! ## Immediate shapes

Every remaining production is an opcode followed by one, two or three operand
grammars.  The three combinators below are proved sound and complete once, so
each opcode costs one line in the decoder and one in each proof. -/

/-- `0xNN x:BX => f x`. -/
def arg1 {α : Type} (p : Step α) (f : α → Instr) (r : Bytes) :
    Except Fault (Instr × Bytes) :=
  match p r with
  | .error e => .error e
  | .ok (x, r') => .ok (f x, r')

/-- `0xNN x:BX y:BY => f x y`. -/
def arg2 {α β : Type} (p : Step α) (q : Step β) (f : α → β → Instr) (r : Bytes) :
    Except Fault (Instr × Bytes) :=
  match p r with
  | .error e => .error e
  | .ok (x, r₁) =>
      match q r₁ with
      | .error e => .error e
      | .ok (y, r₂) => .ok (f x y, r₂)

theorem arg1_sound {α : Type} {G : Bytes → α → Prop} {p : Step α} (hp : Sound G p)
    (f : α → Instr) {r : Bytes} {i : Instr} {r' : Bytes}
    (h : arg1 p f r = .ok (i, r')) : ∃ b x, r = b ++ r' ∧ G b x ∧ i = f x := by
  rw [arg1] at h
  split at h
  · simp at h
  · rename_i x r₁ hx
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := hp r x r₁ hx
    exact ⟨b, x, by rw [hb, hr], hd, hv.symm⟩

theorem arg1_complete {α : Type} {G : Bytes → α → Prop} {p : Step α} (hp : Complete G p)
    (f : α → Instr) {b : Bytes} {x : α} (r : Bytes) (hx : G b x) :
    arg1 p f (b ++ r) = .ok (f x, r) := by
  simp only [arg1, hp b x r hx]

theorem arg2_sound {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {p : Step α} {q : Step β} (hp : Sound G p) (hq : Sound H q)
    (f : α → β → Instr) {r : Bytes} {i : Instr} {r' : Bytes}
    (h : arg2 p q f r = .ok (i, r')) :
    ∃ b₁ b₂ x y, r = b₁ ++ b₂ ++ r' ∧ G b₁ x ∧ H b₂ y ∧ i = f x y := by
  rw [arg2] at h
  split at h
  · simp at h
  · rename_i x r₁ hx
    split at h
    · simp at h
    · rename_i y r₂ hy
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨b₁, hb₁, hd₁⟩ := hp r x r₁ hx
      obtain ⟨b₂, hb₂, hd₂⟩ := hq r₁ y r₂ hy
      exact ⟨b₁, b₂, x, y, by rw [hb₁, hb₂, hr]; simp, hd₁, hd₂, hv.symm⟩

theorem arg2_complete {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {p : Step α} {q : Step β} (hp : Complete G p) (hq : Complete H q)
    (f : α → β → Instr) {b₁ b₂ : Bytes} {x : α} {y : β} (r : Bytes)
    (hx : G b₁ x) (hy : H b₂ y) : arg2 p q f (b₁ ++ b₂ ++ r) = .ok (f x y, r) := by
  rw [List.append_assoc]
  simp only [arg2, hp b₁ x (b₂ ++ r) hx, hq b₂ y r hy]

/-! ## Single-byte opcodes with immediates -/

/-- Every one-byte opcode of the covered fragment that carries an immediate,
dispatched on the opcode byte and applied to the bytes after it. -/
def decOp1 (v : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match v with
  | 0x08 => arg1 decIdx (fun x => Instr.throw x) r
  | 0x0C => arg1 decIdx (fun l => Instr.br l) r
  | 0x0D => arg1 decIdx (fun l => Instr.brIf l) r
  | 0x0E => arg2 (decList decIdx) decIdx (fun ls l => Instr.brTable ls l) r
  | 0x10 => arg1 decIdx (fun x => Instr.call x) r
  | 0x11 => arg2 decIdx decIdx (fun y x => Instr.callIndirect x (.idx y)) r
  | 0x12 => arg1 decIdx (fun x => Instr.returnCall x) r
  | 0x13 => arg2 decIdx decIdx (fun y x => Instr.returnCallIndirect x (.idx y)) r
  | 0x1C => arg1 (decList decValtype) (fun ts => Instr.select (some ts)) r
  | 0x20 => arg1 decIdx (fun x => Instr.localGet x) r
  | 0x21 => arg1 decIdx (fun x => Instr.localSet x) r
  | 0x22 => arg1 decIdx (fun x => Instr.localTee x) r
  | 0x23 => arg1 decIdx (fun x => Instr.globalGet x) r
  | 0x24 => arg1 decIdx (fun x => Instr.globalSet x) r
  | 0x25 => arg1 decIdx (fun x => Instr.tableGet x) r
  | 0x26 => arg1 decIdx (fun x => Instr.tableSet x) r
  | 0x28 => arg1 decMemarg (fun m => Instr.load .i32 none m.1 m.2) r
  | 0x29 => arg1 decMemarg (fun m => Instr.load .i64 none m.1 m.2) r
  | 0x2A => arg1 decMemarg (fun m => Instr.load .f32 none m.1 m.2) r
  | 0x2B => arg1 decMemarg (fun m => Instr.load .f64 none m.1 m.2) r
  | 0x2C => arg1 decMemarg (fun m => Instr.load .i32 (some { sz := .s8, sx := .s }) m.1 m.2) r
  | 0x2D => arg1 decMemarg (fun m => Instr.load .i32 (some { sz := .s8, sx := .u }) m.1 m.2) r
  | 0x2E => arg1 decMemarg (fun m => Instr.load .i32 (some { sz := .s16, sx := .s }) m.1 m.2) r
  | 0x2F => arg1 decMemarg (fun m => Instr.load .i32 (some { sz := .s16, sx := .u }) m.1 m.2) r
  | 0x30 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s8, sx := .s }) m.1 m.2) r
  | 0x31 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s8, sx := .u }) m.1 m.2) r
  | 0x32 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s16, sx := .s }) m.1 m.2) r
  | 0x33 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s16, sx := .u }) m.1 m.2) r
  | 0x34 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s32, sx := .s }) m.1 m.2) r
  | 0x35 => arg1 decMemarg (fun m => Instr.load .i64 (some { sz := .s32, sx := .u }) m.1 m.2) r
  | 0x36 => arg1 decMemarg (fun m => Instr.store .i32 none m.1 m.2) r
  | 0x37 => arg1 decMemarg (fun m => Instr.store .i64 none m.1 m.2) r
  | 0x38 => arg1 decMemarg (fun m => Instr.store .f32 none m.1 m.2) r
  | 0x39 => arg1 decMemarg (fun m => Instr.store .f64 none m.1 m.2) r
  | 0x3A => arg1 decMemarg (fun m => Instr.store .i32 (some { sz := .s8 }) m.1 m.2) r
  | 0x3B => arg1 decMemarg (fun m => Instr.store .i32 (some { sz := .s16 }) m.1 m.2) r
  | 0x3C => arg1 decMemarg (fun m => Instr.store .i64 (some { sz := .s8 }) m.1 m.2) r
  | 0x3D => arg1 decMemarg (fun m => Instr.store .i64 (some { sz := .s16 }) m.1 m.2) r
  | 0x3E => arg1 decMemarg (fun m => Instr.store .i64 (some { sz := .s32 }) m.1 m.2) r
  | 0x3F => arg1 decIdx (fun x => Instr.memorySize x) r
  | 0x40 => arg1 decIdx (fun x => Instr.memoryGrow x) r
  | 0x41 => arg1 decU32 (fun n => Instr.const .i32 n) r
  | 0x42 => arg1 decU64 (fun n => Instr.const .i64 n) r
  | 0x43 => arg1 decF32 (fun p => Instr.const .f32 p) r
  | 0x44 => arg1 decF64 (fun p => Instr.const .f64 p) r
  | 0xD0 => arg1 decHeaptype (fun ht => Instr.refNull ht) r
  | 0xD2 => arg1 decIdx (fun x => Instr.refFunc x) r
  | 0xD5 => arg1 decIdx (fun l => Instr.brOnNull l) r
  | 0xD6 => arg1 decIdx (fun l => Instr.brOnNonNull l) r
  | _ => Except.error Fault.opcode

theorem decOp1_sound {v : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decOp1 v r = .ok (i, r')) : ∃ bb, r = bb ++ r' ∧ Binstr (tb v :: bb) i := by
  unfold decOp1 at h
  split at h
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.throw bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.br bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.brIf bb x hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound (decList_sound decIdx_sound) decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.brTable b₁ b₂ x y hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.call bb x hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.callIndirect b₁ b₂ x y hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.returnCall bb x hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControl.returnCallIndirect b₁ b₂ x y hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound (decList_sound decValtype_sound) _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofParametric _ _ (BinstrParametric.selectT bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofLocal _ _ (BinstrLocal.get bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofLocal _ _ (BinstrLocal.set bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofLocal _ _ (BinstrLocal.tee bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofGlobal _ _ (BinstrGlobal.get bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofGlobal _ _ (BinstrGlobal.set bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.get bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.set bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Load bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.f32Load bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.f64Load bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Load8S bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Load8U bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Load16S bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Load16U bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load8S bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load8U bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load16S bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load16U bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load32S bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Load32U bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Store bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Store bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.f32Store bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.f64Store bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Store8 bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i32Store16 bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Store8 bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Store16 bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decMemarg_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.i64Store32 bb x.1 x.2 hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.size bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.grow bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decU32_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofNum _ _ (BinstrNum.i32Const bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decU64_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofNum _ _ (BinstrNum.i64Const bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decF32_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofNum _ _ (BinstrNum.f32Const bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decF64_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofNum _ _ (BinstrNum.f64Const bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decHeaptype_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.null bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.func bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.brOnNull bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.brOnNonNull bb x hg)⟩
  · cases h

/-- Every `0xFC k` opcode of the covered fragment that carries an immediate. -/
def decFC (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match k with
  | 8 => arg2 decIdx decIdx (fun y x => Instr.memoryInit x y) r
  | 9 => arg1 decIdx (fun y => Instr.dataDrop y) r
  | 10 => arg2 decIdx decIdx (fun x₁ x₂ => Instr.memoryCopy x₁ x₂) r
  | 11 => arg1 decIdx (fun x => Instr.memoryFill x) r
  | 12 => arg2 decIdx decIdx (fun y x => Instr.tableInit x y) r
  | 13 => arg1 decIdx (fun x => Instr.elemDrop x) r
  | 14 => arg2 decIdx decIdx (fun x₁ x₂ => Instr.tableCopy x₁ x₂) r
  | 15 => arg1 decIdx (fun x => Instr.tableGrow x) r
  | 16 => arg1 decIdx (fun x => Instr.tableSize x) r
  | 17 => arg1 decIdx (fun x => Instr.tableFill x) r
  | _ => Except.error Fault.opcode

theorem decFC_sound {k : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decFC k r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ ∀ bo, Bprefixed 0xFC k bo → Binstr (bo ++ bb) i := by
  unfold decFC at h
  split at h
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb],
      fun bo hbo => by rw [hi, ← List.append_assoc]; exact Binstr.ofMemory _ _ (BinstrMemory.init bo b₁ b₂ x y hbo hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.dataDrop bo bb x hbo hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb],
      fun bo hbo => by rw [hi, ← List.append_assoc]; exact Binstr.ofMemory _ _ (BinstrMemory.copy bo b₁ b₂ x y hbo hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofMemory _ _ (BinstrMemory.fill bo bb x hbo hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb],
      fun bo hbo => by rw [hi, ← List.append_assoc]; exact Binstr.ofTable _ _ (BinstrTable.init bo b₁ b₂ x y hbo hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.elemDrop bo bb x hbo hg)⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb],
      fun bo hbo => by rw [hi, ← List.append_assoc]; exact Binstr.ofTable _ _ (BinstrTable.copy bo b₁ b₂ x y hbo hg₁ hg₂)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.grow bo bb x hbo hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.size bo bb x hbo hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, fun bo hbo => by rw [hi]; exact Binstr.ofTable _ _ (BinstrTable.fill bo bb x hbo hg)⟩
  · cases h

/-! ## The recursive knot

`Binstrs` is not terminated by anything of its own: the enclosing production
supplies `0x0B` (`END`) or `0x05` (`ELSE`).  Neither byte is an instruction
opcode, so stopping at them is a fact about the grammar rather than a decoder
convention. -/

/-- Does the input begin with `END` or `ELSE`? -/
def isEndOrElse : Bytes → Bool
  | [] => false
  | b :: _ => b.val = 0x0B || b.val = 0x05

/-- `(in:Binstr)*`, bounded by an instruction count. -/
def decInstrs (decI : Bytes → Except Fault (Instr × Bytes)) :
    Nat → Bytes → Except Fault (List Instr × Bytes)
  | 0, bs => if isEndOrElse bs then .ok ([], bs) else .error .eof
  | n + 1, bs =>
      if isEndOrElse bs then .ok ([], bs)
      else
        match decI bs with
        | .error e => .error e
        | .ok (i, bs₁) =>
            match decInstrs decI n bs₁ with
            | .error e => .error e
            | .ok (is, bs₂) => .ok (i :: is, bs₂)

/-- `grammar Binstr : instr`, bounded by a block-nesting depth. -/
def decInstr : Nat → Bytes → Except Fault (Instr × Bytes)
  | 0, _ => .error .eof
  | d + 1, bs =>
      match bs with
      | [] => Except.error Fault.eof
      | b :: r =>
          match op0 b.val with
          | some i => Except.ok (i, r)
          | none =>
              if b.val = 0x02 then
                (match decBlocktype r with
                 | .error e => .error e
                 | .ok (bt, r₁) =>
                     match decInstrs (decInstr d) r₁.length r₁ with
                     | .error e => .error e
                     | .ok (is, r₂) =>
                         match expectByte 0x0B r₂ with
                         | .error e => .error e
                         | .ok r₃ => .ok (Instr.block bt (InstrSeq.ofList is), r₃))
              else if b.val = 0x03 then
                (match decBlocktype r with
                 | .error e => .error e
                 | .ok (bt, r₁) =>
                     match decInstrs (decInstr d) r₁.length r₁ with
                     | .error e => .error e
                     | .ok (is, r₂) =>
                         match expectByte 0x0B r₂ with
                         | .error e => .error e
                         | .ok r₃ => .ok (Instr.loop bt (InstrSeq.ofList is), r₃))
              else if b.val = 0x04 then
                (match decBlocktype r with
                 | .error e => .error e
                 | .ok (bt, r₁) =>
                     match decInstrs (decInstr d) r₁.length r₁ with
                     | .error e => .error e
                     | .ok (is, r₂) =>
                         match r₂ with
                         | [] => Except.error Fault.eof
                         | c :: r₃ =>
                             if c.val = 0x0B then
                               Except.ok (Instr.ifElse bt (InstrSeq.ofList is) .nil, r₃)
                             else if c.val = 0x05 then
                               (match decInstrs (decInstr d) r₃.length r₃ with
                                | .error e => .error e
                                | .ok (is₂, r₄) =>
                                    match expectByte 0x0B r₄ with
                                    | .error e => .error e
                                    | .ok r₅ =>
                                        .ok (Instr.ifElse bt (InstrSeq.ofList is)
                                          (InstrSeq.ofList is₂), r₅))
                             else Except.error Fault.opcode)
              else if b.val = 0x1F then
                (match decBlocktype r with
                 | .error e => .error e
                 | .ok (bt, r₁) =>
                     match decList decCatch r₁ with
                     | .error e => .error e
                     | .ok (cs, r₂) =>
                         if hcs : cs.length < 2 ^ 32 then
                           (match decInstrs (decInstr d) r₂.length r₂ with
                            | .error e => .error e
                            | .ok (is, r₃) =>
                                match expectByte 0x0B r₃ with
                                | .error e => .error e
                                | .ok r₄ =>
                                    .ok (Instr.tryTable bt ⟨cs, hcs⟩ (InstrSeq.ofList is), r₄))
                         else Except.error Fault.side)
              else if b.val = 0xFC then
                (match decU32 r with
                 | .error e => .error e
                 | .ok (k, r₁) =>
                     match opFC0 k.val with
                     | some i => Except.ok (i, r₁)
                     | none => decFC k.val r₁)
              else decOp1 b.val r

/-- `grammar Bexpr : expr = | (in:Binstr)* 0x0B => in*`. -/
def decExpr (d : Nat) (bs : Bytes) : Except Fault (Expr × Bytes) :=
  match decInstrs (decInstr d) bs.length bs with
  | .error e => .error e
  | .ok (is, r) =>
      match expectByte 0x0B r with
      | .error e => .error e
      | .ok r' => .ok (InstrSeq.ofList is, r')

/-! ## Soundness -/

theorem decInstrs_sound {decI : Bytes → Except Fault (Instr × Bytes)}
    (hI : Sound Binstr decI) (n : Nat) : Sound Binstrs (decInstrs decI n) := by
  induction n with
  | zero =>
      intro bs is r h
      rw [decInstrs] at h
      split at h
      · obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨[], by simp [hr], by rw [← hv]; exact Binstrs.nil⟩
      · cases h
  | succ n ih =>
      intro bs is r h
      rw [decInstrs] at h
      split at h
      · obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨[], by simp [hr], by rw [← hv]; exact Binstrs.nil⟩
      · split at h
        · cases h
        · rename_i i bs₁ hi
          split at h
          · cases h
          · rename_i is' bs₂ his
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨b₁, hb₁, hd₁⟩ := hI bs i bs₁ hi
            obtain ⟨b₂, hb₂, hd₂⟩ := ih bs₁ is' bs₂ his
            refine ⟨b₁ ++ b₂, by rw [hb₁, hb₂, hr]; simp, ?_⟩
            rw [← hv]
            exact Binstrs.cons b₁ b₂ i is' hd₁ hd₂

theorem decInstr_sound : ∀ d : Nat, Sound Binstr (decInstr d) := by
  intro d
  induction d with
  | zero => intro bs i r h; cases h
  | succ d ih =>
      intro bs i r h
      cases bs with
      | nil => cases h
      | cons b bs =>
          rw [decInstr] at h
          split at h
          · rename_i i' hi'
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            refine ⟨[b], by rw [← hr]; rfl, ?_⟩
            have hb : b = tb b.val := byte_eq_tb b.property rfl
            rw [← hv, hb]
            exact op0_sound hi'
          · split at h
            · -- 0x02 BLOCK
              rename_i hb
              split at h
              · cases h
              · rename_i bt r₁ hbt
                split at h
                · cases h
                · rename_i is r₂ his
                  split at h
                  · cases h
                  · rename_i r₃ hr₃
                    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                    obtain ⟨bbt, hbbt, hdbt⟩ := decBlocktype_sound bs bt r₁ hbt
                    obtain ⟨bin, hbin, hdin⟩ := decInstrs_sound ih r₁.length r₁ is r₂ his
                    have hr₂ := expectByte_ok (by decide) hr₃
                    refine ⟨b :: (bbt ++ bin ++ [tb 0x0B]), ?_, ?_⟩
                    · rw [hbbt, hbin, hr₂, hr]; simp
                    · rw [← hv, byte_eq_tb (by decide) hb]
                      exact Binstr.block bbt bin bt is hdbt hdin
            · split at h
              · -- 0x03 LOOP
                rename_i hb
                split at h
                · cases h
                · rename_i bt r₁ hbt
                  split at h
                  · cases h
                  · rename_i is r₂ his
                    split at h
                    · cases h
                    · rename_i r₃ hr₃
                      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                      obtain ⟨bbt, hbbt, hdbt⟩ := decBlocktype_sound bs bt r₁ hbt
                      obtain ⟨bin, hbin, hdin⟩ := decInstrs_sound ih r₁.length r₁ is r₂ his
                      have hr₂ := expectByte_ok (by decide) hr₃
                      refine ⟨b :: (bbt ++ bin ++ [tb 0x0B]), ?_, ?_⟩
                      · rw [hbbt, hbin, hr₂, hr]; simp
                      · rw [← hv, byte_eq_tb (by decide) hb]
                        exact Binstr.loop bbt bin bt is hdbt hdin
              · split at h
                · -- 0x04 IF
                  rename_i hb
                  split at h
                  · cases h
                  · rename_i bt r₁ hbt
                    split at h
                    · cases h
                    · rename_i is r₂ his
                      obtain ⟨bbt, hbbt, hdbt⟩ := decBlocktype_sound bs bt r₁ hbt
                      obtain ⟨bin, hbin, hdin⟩ := decInstrs_sound ih r₁.length r₁ is r₂ his
                      split at h
                      · cases h
                      · rename_i _ c r₃
                        split at h
                        · rename_i hc
                          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                          refine ⟨b :: (bbt ++ bin ++ [tb 0x0B]), ?_, ?_⟩
                          · rw [hbbt, hbin, hr, byte_eq_tb (by decide) hc]; simp
                          · rw [← hv, byte_eq_tb (by decide) hb]
                            exact Binstr.ifThen bbt bin bt is hdbt hdin
                        · split at h
                          · rename_i hc
                            split at h
                            · cases h
                            · rename_i is₂ r₄ his₂
                              split at h
                              · cases h
                              · rename_i r₅ hr₅
                                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                                obtain ⟨bin₂, hbin₂, hdin₂⟩ :=
                                  decInstrs_sound ih r₃.length r₃ is₂ r₄ his₂
                                have hr₄ := expectByte_ok (by decide) hr₅
                                refine ⟨b :: (bbt ++ bin ++ [tb 0x05] ++ bin₂ ++ [tb 0x0B]),
                                  ?_, ?_⟩
                                · rw [hbbt, hbin, hbin₂, hr₄, hr,
                                    byte_eq_tb (by decide : (0x05 : Nat) < 0x100) hc]
                                  simp
                                · rw [← hv, byte_eq_tb (by decide) hb]
                                  exact Binstr.ifElse bbt bin bin₂ bt is is₂ hdbt hdin hdin₂
                          · cases h
                · split at h
                  · -- 0x1F TRY_TABLE
                    rename_i hb
                    split at h
                    · cases h
                    · rename_i bt r₁ hbt
                      split at h
                      · cases h
                      · rename_i cs r₂ hcs
                        split at h
                        · rename_i hlen
                          split at h
                          · cases h
                          · rename_i is r₃ his
                            split at h
                            · cases h
                            · rename_i r₄ hr₄
                              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                              obtain ⟨bbt, hbbt, hdbt⟩ := decBlocktype_sound bs bt r₁ hbt
                              obtain ⟨bc, hbc, hdc⟩ :=
                                decList_sound decCatch_sound r₁ cs r₂ hcs
                              obtain ⟨bin, hbin, hdin⟩ :=
                                decInstrs_sound ih r₂.length r₂ is r₃ his
                              have hr₃ := expectByte_ok (by decide) hr₄
                              refine ⟨b :: (bbt ++ bc ++ bin ++ [tb 0x0B]), ?_, ?_⟩
                              · rw [hbbt, hbc, hbin, hr₃, hr]; simp
                              · rw [← hv, byte_eq_tb (by decide) hb]
                                exact Binstr.tryTable bbt bc bin bt ⟨cs, hlen⟩ is hdbt hdc hdin
                        · cases h
                  · split at h
                    · -- 0xFC prefix
                      rename_i hb
                      split at h
                      · cases h
                      · rename_i k r₁ hk
                        obtain ⟨bk, hbk, hdk⟩ := decU32_sound bs k r₁ hk
                        have hpref : Bprefixed 0xFC k.val (b :: bk) := by
                          rw [byte_eq_tb (by decide) hb]
                          exact ⟨bk, rfl, ⟨k, hdk, rfl⟩⟩
                        split at h
                        · rename_i i' hi'
                          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                          refine ⟨b :: bk, by rw [hbk, hr]; rfl, ?_⟩
                          rw [← hv]
                          exact opFC0_sound hi' hpref
                        · obtain ⟨bb, hbb, hfc⟩ := decFC_sound h
                          refine ⟨b :: bk ++ bb, by rw [hbk, hbb]; simp, ?_⟩
                          exact hfc (b :: bk) hpref
                    · -- everything else
                      obtain ⟨bb, hbb, hd⟩ := decOp1_sound h
                      refine ⟨b :: bb, by rw [hbb]; rfl, ?_⟩
                      rw [byte_eq_tb b.property rfl]
                      exact hd

theorem decExpr_sound (d : Nat) : Sound Bexpr (decExpr d) := by
  intro bs e r h
  rw [decExpr] at h
  split at h
  · cases h
  · rename_i is r₁ his
    split at h
    · cases h
    · rename_i r₂ hr₂
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨bin, hbin, hdin⟩ := decInstrs_sound (decInstr_sound d) bs.length bs is r₁ his
      have hr₁ := expectByte_ok (by decide) hr₂
      refine ⟨bin ++ [tb 0x0B], by rw [hbin, hr₁, hr]; simp, ?_⟩
      rw [← hv]
      exact Bexpr.mk bin is hdin

end WasmGemmGnaf.Wasm.Core.Decode
