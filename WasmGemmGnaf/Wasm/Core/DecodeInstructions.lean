/-
  Wasm/Core/DecodeInstructions.lean --- the executable decoder for
  `5.3-binary.instructions.spectec`, proved SOUND against
  `Wasm/Core/BinaryGrammar/{Instructions,Expressions}.lean`.

  SCOPE, STATED EXACTLY.  The decoder implements every production of `Binstr`:
  the unprefixed opcode space, the `0xFC` space, the `0xFB` garbage collection
  space and the 256 `0xFD` SIMD productions.  Nothing is excluded and no
  `covered` predicate carves out a fragment; an earlier revision of this file
  omitted the `0xFB` and `0xFD` spaces and said so here, and that gap is closed.

  * `decInstr_sound` is unconditional: whatever the decoder accepts really is
    derivable in the pinned grammar.
  * `decInstr_complete` is in `Wasm/Core/DecodeInstrComplete.lean`, which
    imports this file rather than the other way round, so no proof here can
    appeal to it.  It is what makes the scope claim above checkable: a
    production this file failed to implement would be a `Binstr` derivation the
    decoder rejected, and completeness says there is none.

  `Bprefixed` IS A `Bu32`, NOT A BYTE.  The `0xFB` / `0xFC` / `0xFD` selectors
  are decoded with `decU32`, so `0xFC 0x8C 0x00` decodes as `TABLE.INIT` just as
  `0xFC 0x0C` does.  In the `0xFD` space it is not even a matter of accepting
  non-minimal encodings: the pinned source writes the selectors in decimal and
  they run up to 275, so `RELAXED_SWIZZLE` (selector 256) is `0xFD 0x80 0x02`
  and has no one-byte form.  A byte-keyed opcode table would be incomplete on
  both counts.

  FUEL.  `decInstr` is structurally recursive on a nesting-depth bound and
  `decInstrs` on an instruction-count bound; `decExpr` supplies both from the
  length of its input, which is always enough because every instruction and
  every nesting level consumes at least one byte.  There is no `partial`.
-/
import WasmGemmGnaf.Wasm.Core.DecodeTypes

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Opcode tables

Generated from the pinned productions: one entry per alternative of
`5.3-binary.instructions.spectec` that carries no immediate. -/

/-- Every one-byte opcode of the unprefixed space that carries no immediate.
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

/-- Corrected no-immediate opcode dispatch for AMD-008. -/
def op0' (v : Nat) : Option Instr :=
  if v = 0xBB then some (.cvtop .f64 .f32 (.ff .promote)) else op0 v

@[simp] theorem op0'_promote :
    op0' 0xBB = some (.cvtop .f64 .f32 (.ff .promote)) := rfl

theorem op0'_of_ne {v : Nat} (h : v ≠ 0xBB) : op0' v = op0 v := by
  simp [op0', h]

/-- Soundness of the amended no-immediate table against the amended grammar
instance. -/
theorem op0'_sound {v : Nat} {i : Instr} (h : op0' v = some i) :
    BinstrA [tb v] i := by
  letI : BinaryAuthority := amendedBinaryAuthority
  unfold op0' at h
  split at h
  · rename_i hv
    subst v
    cases h
    exact Binstr.ofNum _ _ BinstrNum'.f64PromoteF32
  · rename_i hv
    unfold op0 at h
    split at h
    · cases h; exact Binstr.ofParametric _ _ BinstrParametric.unreachable
    · cases h; exact Binstr.ofParametric _ _ BinstrParametric.nop
    · cases h; exact Binstr.ofControl _ _ (BinstrControl'.ofPinned _ _ BinstrControl.throwRef)
    · cases h; exact Binstr.ofControl _ _ (BinstrControl'.ofPinned _ _ BinstrControl.ret)
    · cases h; exact Binstr.ofParametric _ _ BinstrParametric.drop
    · cases h; exact Binstr.ofParametric _ _ BinstrParametric.select
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Eqz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Eq (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Ne (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32LtS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32LtU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32GtS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32GtU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32LeS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32LeU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32GeS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32GeU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Eqz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Eq (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Ne (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64LtS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64LtU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64GtS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64GtU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64LeS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64LeU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64GeS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64GeU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Eq (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Ne (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Lt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Gt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Le (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Ge (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Eq (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Ne (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Lt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Gt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Le (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Ge (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Clz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Ctz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Popcnt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Add (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Sub (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Mul (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32DivS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32DivU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32RemS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32RemU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32And (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Or (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Xor (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Shl (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32ShrS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32ShrU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Rotl (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Rotr (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Clz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Ctz (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Popcnt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Add (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Sub (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Mul (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64DivS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64DivU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64RemS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64RemU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64And (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Or (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Xor (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Shl (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64ShrS (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64ShrU (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Rotl (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Rotr (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Abs (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Neg (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Ceil (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Floor (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Trunc (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Nearest (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Sqrt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Add (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Sub (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Mul (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Div (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Min (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Max (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32Copysign (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Abs (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Neg (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Ceil (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Floor (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Trunc (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Nearest (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Sqrt (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Add (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Sub (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Mul (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Div (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Min (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Max (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64Copysign (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32WrapI64 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32TruncF32S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32TruncF32U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32TruncF64S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32TruncF64U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64ExtendI32S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64ExtendI32U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64TruncF32S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64TruncF32U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64TruncF64S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64TruncF64U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32ConvertI32S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32ConvertI32U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32ConvertI64S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32ConvertI64U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32DemoteF64 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64ConvertI32S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64ConvertI32U (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64ConvertI64S (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64ConvertI64U (by decide))
    · cases h; contradiction
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32ReinterpretF32 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64ReinterpretF64 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f32ReinterpretI32 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.f64ReinterpretI64 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Extend8 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i32Extend16 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Extend8 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Extend16 (by decide))
    · cases h; exact Binstr.ofNum _ _ (BinstrNum'.ofPinned _ _ BinstrNum.i64Extend32 (by decide))
    · cases h; exact Binstr.ofRef _ _ BinstrRef.isNull
    · cases h; exact Binstr.ofRef _ _ BinstrRef.eq
    · cases h; exact Binstr.ofRef _ _ BinstrRef.asNonNull
    · simp at h

/-- The no-immediate table selected by the current binary authority. -/
def op0For [authority : BinaryAuthority] (v : Nat) : Option Instr :=
  match authority.revision with
  | .pinned => op0 v
  | .amended => op0' v

theorem op0For_lt [authority : BinaryAuthority] {v : Nat} {i : Instr}
    (h : op0For v = some i) : v < 0x100 := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact op0_lt h
      | amended =>
          change op0' v = some i at h
          unfold op0' at h
          split at h
          · omega
          · exact op0_lt h

theorem op0For_sound [authority : BinaryAuthority] {v : Nat} {i : Instr}
    (h : op0For v = some i) : Binstr [tb v] i := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact op0_sound h
      | amended =>
          change op0' v = some i at h
          exact op0'_sound h

@[simp] theorem op0For_pinned :
    @op0For pinnedBinaryAuthority = op0 := rfl

@[simp] theorem op0For_amended :
    @op0For amendedBinaryAuthority = op0' := rfl

/-- Away from the single corrected opcode, authority selection reuses the
pinned no-immediate table definitionally. -/
theorem op0For_of_ne [authority : BinaryAuthority] {v : Nat}
    (hne : v ≠ 0xBB) : op0For v = op0 v := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => rfl
      | amended => exact op0'_of_ne hne

/-- Every `0xFC k` opcode of `5.3-binary.instructions.spectec` that carries no
immediate. -/
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

theorem opFC0_sound [authority : BinaryAuthority]
    {k : Nat} {i : Instr} {bo : Bytes} (hk : opFC0 k = some i)
    (hb : Bprefixed 0xFC k bo) : Binstr bo i := by
  unfold opFC0 at hk
  split at hk
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i32TruncSatF32S bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i32TruncSatF32U bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i32TruncSatF64S bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i32TruncSatF64U bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i64TruncSatF32S bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i64TruncSatF32U bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i64TruncSatF64S bo hb) (by decide))
  · cases hk; exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i64TruncSatF64U bo hb) (by decide))
  · simp at hk

/-! ## Shared operands -/

/-- `grammar Bblocktype : blocktype`.  The three alternatives are separated by
the first byte: `0x40` is the empty result, a non-negative `Bs33` starts below
`0x40` or at `0x80` and above (`Bs33_head`), and every `Bvaltype` byte lies
strictly between. -/
def decBlocktype [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (BlockType × Bytes) :=
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

theorem decBlocktype_sound [authority : BinaryAuthority] :
    Sound Bblocktype decBlocktype := by
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
theorem Bvaltype_head [authority : BinaryAuthority]
    {bs : Bytes} {t : ValType} (h : Bvaltype bs t) :
    ∃ b u, bs = b :: u ∧ ¬ (b.val = 0x40) ∧ ¬ (b.val < 0x40 ∨ 0x80 ≤ b.val) := by
  cases h with
  | num nt hn => cases hn <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)
  | vec vt hv => cases hv <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)
  | ref rt hr =>
      cases hr with
      | null bs' ht _ => exact ⟨tb 0x63, bs', rfl, by decide, by decide⟩
      | nonNull bs' ht _ => exact ⟨tb 0x64, bs', rfl, by decide, by decide⟩
      | abs _bs ht ha => cases ha <;> (refine ⟨_, [], rfl, ?_, ?_⟩ <;> decide)

theorem decBlocktype_complete [authority : BinaryAuthority] :
    Complete Bblocktype decBlocktype := by
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
      obtain ⟨b0, u0, hb0, hrange⟩ := Bs33For_head hs hnn
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

/-- `grammar Bcastop : castop`, the two-bit null-flag pair of `BR_ON_CAST`. -/
def decCastop (bs : Bytes) : Except Fault (CastOp × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x00 then .ok ((none, none), r)
      else if b.val = 0x01 then .ok ((some .null, none), r)
      else if b.val = 0x02 then .ok ((none, some .null), r)
      else if b.val = 0x03 then .ok ((some .null, some .null), r)
      else .error .opcode

theorem decCastop_sound : Sound Bcastop decCastop := by
  intro bs c r h
  cases bs with
  | nil => simp [decCastop] at h
  | cons b bs =>
      rw [decCastop] at h
      split at h
      · rename_i hb
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨[b], by rw [← hr]; rfl,
          by rw [← hv, byte_eq_tb (by decide) hb]; exact Bcastop.nn⟩
      · split at h
        · rename_i hb
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          exact ⟨[b], by rw [← hr]; rfl,
            by rw [← hv, byte_eq_tb (by decide) hb]; exact Bcastop.yn⟩
        · split at h
          · rename_i hb
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            exact ⟨[b], by rw [← hr]; rfl,
              by rw [← hv, byte_eq_tb (by decide) hb]; exact Bcastop.ny⟩
          · split at h
            · rename_i hb
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              exact ⟨[b], by rw [← hr]; rfl,
                by rw [← hv, byte_eq_tb (by decide) hb]; exact Bcastop.yy⟩
            · simp at h

theorem decCastop_complete : Complete Bcastop decCastop := by
  intro b c r h
  cases h with
  | nn => show decCastop (tb 0x00 :: r) = _; simp [decCastop, tb, Byte.ofNat]
  | yn => show decCastop (tb 0x01 :: r) = _; simp [decCastop, tb, Byte.ofNat]
  | ny => show decCastop (tb 0x02 :: r) = _; simp [decCastop, tb, Byte.ofNat]
  | yy => show decCastop (tb 0x03 :: r) = _; simp [decCastop, tb, Byte.ofNat]

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

/-- `0xNN x:BX y:BY z:BZ => f x y z`. -/
def arg3 {α β γ : Type} (p : Step α) (q : Step β) (s : Step γ)
    (f : α → β → γ → Instr) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match p r with
  | .error e => .error e
  | .ok (x, r₁) =>
      match q r₁ with
      | .error e => .error e
      | .ok (y, r₂) =>
          match s r₂ with
          | .error e => .error e
          | .ok (z, r₃) => .ok (f x y z, r₃)

/-- `0xNN x:BX y:BY z:BZ w:BW => f x y z w`. -/
def arg4 {α β γ δ : Type} (p : Step α) (q : Step β) (s : Step γ) (t : Step δ)
    (f : α → β → γ → δ → Instr) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match p r with
  | .error e => .error e
  | .ok (x, r₁) =>
      match q r₁ with
      | .error e => .error e
      | .ok (y, r₂) =>
          match s r₂ with
          | .error e => .error e
          | .ok (z, r₃) =>
              match t r₃ with
              | .error e => .error e
              | .ok (w, r₄) => .ok (f x y z w, r₄)

theorem arg3_sound {α β γ : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {K : Bytes → γ → Prop} {p : Step α} {q : Step β} {s : Step γ}
    (hp : Sound G p) (hq : Sound H q) (hs : Sound K s)
    (f : α → β → γ → Instr) {r : Bytes} {i : Instr} {r' : Bytes}
    (h : arg3 p q s f r = .ok (i, r')) :
    ∃ b₁ b₂ b₃ x y z, r = b₁ ++ b₂ ++ b₃ ++ r' ∧ G b₁ x ∧ H b₂ y ∧ K b₃ z ∧
      i = f x y z := by
  rw [arg3] at h
  split at h
  · simp at h
  · rename_i x r₁ hx
    split at h
    · simp at h
    · rename_i y r₂ hy
      split at h
      · simp at h
      · rename_i z r₃ hz
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨b₁, hb₁, hd₁⟩ := hp r x r₁ hx
        obtain ⟨b₂, hb₂, hd₂⟩ := hq r₁ y r₂ hy
        obtain ⟨b₃, hb₃, hd₃⟩ := hs r₂ z r₃ hz
        exact ⟨b₁, b₂, b₃, x, y, z, by rw [hb₁, hb₂, hb₃, hr]; simp, hd₁, hd₂, hd₃,
          hv.symm⟩

theorem arg3_complete {α β γ : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {K : Bytes → γ → Prop} {p : Step α} {q : Step β} {s : Step γ}
    (hp : Complete G p) (hq : Complete H q) (hs : Complete K s)
    (f : α → β → γ → Instr) {b₁ b₂ b₃ : Bytes} {x : α} {y : β} {z : γ} (r : Bytes)
    (hx : G b₁ x) (hy : H b₂ y) (hz : K b₃ z) :
    arg3 p q s f (b₁ ++ b₂ ++ b₃ ++ r) = .ok (f x y z, r) := by
  simp only [List.append_assoc]
  simp only [arg3, hp b₁ x (b₂ ++ (b₃ ++ r)) hx, hq b₂ y (b₃ ++ r) hy, hs b₃ z r hz]

theorem arg4_sound {α β γ δ : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {K : Bytes → γ → Prop} {L : Bytes → δ → Prop}
    {p : Step α} {q : Step β} {s : Step γ} {t : Step δ}
    (hp : Sound G p) (hq : Sound H q) (hs : Sound K s) (ht : Sound L t)
    (f : α → β → γ → δ → Instr) {r : Bytes} {i : Instr} {r' : Bytes}
    (h : arg4 p q s t f r = .ok (i, r')) :
    ∃ b₁ b₂ b₃ b₄ x y z w, r = b₁ ++ b₂ ++ b₃ ++ b₄ ++ r' ∧
      G b₁ x ∧ H b₂ y ∧ K b₃ z ∧ L b₄ w ∧ i = f x y z w := by
  rw [arg4] at h
  split at h
  · simp at h
  · rename_i x r₁ hx
    split at h
    · simp at h
    · rename_i y r₂ hy
      split at h
      · simp at h
      · rename_i z r₃ hz
        split at h
        · simp at h
        · rename_i w r₄ hw
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨b₁, hb₁, hd₁⟩ := hp r x r₁ hx
          obtain ⟨b₂, hb₂, hd₂⟩ := hq r₁ y r₂ hy
          obtain ⟨b₃, hb₃, hd₃⟩ := hs r₂ z r₃ hz
          obtain ⟨b₄, hb₄, hd₄⟩ := ht r₃ w r₄ hw
          exact ⟨b₁, b₂, b₃, b₄, x, y, z, w, by rw [hb₁, hb₂, hb₃, hb₄, hr]; simp,
            hd₁, hd₂, hd₃, hd₄, hv.symm⟩

theorem arg4_complete {α β γ δ : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {K : Bytes → γ → Prop} {L : Bytes → δ → Prop}
    {p : Step α} {q : Step β} {s : Step γ} {t : Step δ}
    (hp : Complete G p) (hq : Complete H q) (hs : Complete K s) (ht : Complete L t)
    (f : α → β → γ → δ → Instr) {b₁ b₂ b₃ b₄ : Bytes} {x : α} {y : β} {z : γ} {w : δ}
    (r : Bytes) (hx : G b₁ x) (hy : H b₂ y) (hz : K b₃ z) (hw : L b₄ w) :
    arg4 p q s t f (b₁ ++ b₂ ++ b₃ ++ b₄ ++ r) = .ok (f x y z w, r) := by
  simp only [List.append_assoc]
  simp only [arg4, hp b₁ x (b₂ ++ (b₃ ++ (b₄ ++ r))) hx,
    hq b₂ y (b₃ ++ (b₄ ++ r)) hy, hs b₃ z (b₄ ++ r) hz, ht b₄ w r hw]

/-! ## Single-byte opcodes with immediates -/

section ImmediateAuthority

variable [authority : BinaryAuthority]

/-- Every one-byte opcode of the unprefixed space that carries an immediate,
dispatched on the opcode byte and applied to the bytes after it. -/
def decOp1Base (v : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
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

theorem decOp1Base_sound {v : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decOp1Base v r = .ok (i, r')) : ∃ bb, r = bb ++ r' ∧ Binstr (tb v :: bb) i := by
  unfold decOp1Base at h
  split at h
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.throw bb x hg))⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.br bb x hg))⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.brIf bb x hg))⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound (decList_sound decIdx_sound) decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.brTable b₁ b₂ x y hg₁ hg₂))⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.call bb x hg))⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.callIndirect b₁ b₂ x y hg₁ hg₂))⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.returnCall bb x hg))⟩
  · obtain ⟨b₁, b₂, x, y, hb, hg₁, hg₂, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    exact ⟨b₁ ++ b₂, by simp [hb], by rw [hi]; exact Binstr.ofControl _ _ (BinstrControlFor.ofPinned (BinstrControl.returnCallIndirect b₁ b₂ x y hg₁ hg₂))⟩
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
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i32Const bb x hg) (by intro hbad; cases hbad))
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decU64_sound _ h
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.i64Const bb x hg) (by intro hbad; cases hbad))
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decF32_sound _ h
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.f32Const bb x hg) (by intro hbad; cases hbad))
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decF64_sound _ h
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact Binstr.ofNum _ _
      (BinstrNumFor.ofPinned (BinstrNum.f64Const bb x hg) (by intro hbad; cases hbad))
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decHeaptype_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.null bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.func bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.brOnNull bb x hg)⟩
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    exact ⟨bb, hb, by rw [hi]; exact Binstr.ofRef _ _ (BinstrRef.brOnNonNull bb x hg)⟩
  · cases h

end ImmediateAuthority

/-- The explicit pinned one-immediate decoder. -/
abbrev decOp1 : Nat → Bytes → Except Fault (Instr × Bytes) :=
  @decOp1Base pinnedBinaryAuthority

theorem decOp1_sound {v : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decOp1 v r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ BinstrPinned (tb v :: bb) i :=
  @decOp1Base_sound pinnedBinaryAuthority v r i r' h

/-- Corrected one-immediate dispatch, adding the two AMD-010 typed-reference
call opcodes while reusing the authority-parameterized base table. -/
def decOp1' (v : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match v with
  | 0x14 => arg1 decIdx (fun x => Instr.callRef (.idx x)) r
  | 0x15 => arg1 decIdx (fun x => Instr.returnCallRef (.idx x)) r
  | _ => @decOp1Base amendedBinaryAuthority v r

theorem decOp1'_sound {v : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decOp1' v r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ BinstrA (tb v :: bb) i := by
  unfold decOp1' at h
  split at h
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact @Binstr.ofControl amendedBinaryAuthority _ _
      (@BinstrControl'.callRef bb x hg)
  · obtain ⟨bb, x, hb, hg, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, ?_⟩
    rw [hi]
    exact @Binstr.ofControl amendedBinaryAuthority _ _
      (@BinstrControl'.returnCallRef bb x hg)
  · exact @decOp1Base_sound amendedBinaryAuthority v r i r' h

theorem decOp1'_callRef_complete {bs r : Bytes} {x : TypeIdx}
    (h : Btypeidx bs x) :
    decOp1' 0x14 (bs ++ r) = .ok (.callRef (.idx x), r) := by
  simp only [decOp1', arg1, decIdx_complete bs x r h]

theorem decOp1'_returnCallRef_complete {bs r : Bytes} {x : TypeIdx}
    (h : Btypeidx bs x) :
    decOp1' 0x15 (bs ++ r) = .ok (.returnCallRef (.idx x), r) := by
  simp only [decOp1', arg1, decIdx_complete bs x r h]

theorem decOp1'_of_other {v : Nat} (h14 : v ≠ 0x14) (h15 : v ≠ 0x15)
    (r : Bytes) : decOp1' v r = @decOp1Base amendedBinaryAuthority v r := by
  unfold decOp1'
  split <;> simp_all

/-- The one-immediate table selected by the current binary authority. -/
def decOp1For [authority : BinaryAuthority]
    (v : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match authority.revision with
  | .pinned => decOp1 v r
  | .amended => decOp1' v r

theorem decOp1For_sound [authority : BinaryAuthority]
    {v : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decOp1For v r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ Binstr (tb v :: bb) i := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact decOp1_sound h
      | amended =>
          change decOp1' v r = .ok (i, r') at h
          exact decOp1'_sound h

@[simp] theorem decOp1For_pinned :
    @decOp1For pinnedBinaryAuthority = decOp1 := rfl

@[simp] theorem decOp1For_amended :
    @decOp1For amendedBinaryAuthority = decOp1' := rfl

/-- Away from the two added typed-call opcodes, the selected one-immediate
dispatcher is the authority-parameterized base table. -/
theorem decOp1For_of_other [authority : BinaryAuthority]
    {v : Nat} (h14 : v ≠ 0x14) (h15 : v ≠ 0x15) (r : Bytes) :
    decOp1For v r = decOp1Base v r := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => rfl
      | amended => exact decOp1'_of_other h14 h15 r

/-- Every `0xFC k` opcode of `5.3-binary.instructions.spectec` that carries an
immediate. -/
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

theorem decFC_sound [authority : BinaryAuthority]
    {k : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
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


/-! ## The `0xFB` (garbage collection) and `0xFD` (SIMD) opcode spaces

`5.3-binary.instructions.spectec` writes 31 productions under the `0xFB` prefix
and 256 under `0xFD`.  Both selectors are `Bu32`s rather than bytes, and the
pinned source writes them in DECIMAL, so this is not a stylistic point:
`0xFD 256:Bu32 => VSWIZZLOP (I8 X `16) RELAXED_SWIZZLE` has a selector that does
not fit in a byte at all, and is encoded `0xFD 0x80 0x02`.  Nor is a single
minimal encoding enough: `0xFD 35:Bu32 => VRELOP (I8 X `16) EQ` is `0xFD 0x23`
and equally `0xFD 0xA3 0x00`, because a `Bu32` admits its non-minimal encodings.
Both tables below are therefore keyed on the DECODED `Bu32` value, never on a
byte.  Two `0xFD` productions do not fit the `argN` shapes and get their own
decoders. -/

/-- `| 0xFD 12:Bu32 (b:Bbyte)^16 => VCONST V128 $inv_ibytes_(`128, (b)^16)`.
`$inv_ibytes_` is the little-endian reading `leNat` of `BinaryGrammar/Values.lean`;
the range check is discharged rather than assumed. -/
def decV128Const (r : Bytes) : Except Fault (Instr × Bytes) :=
  match decBytes 16 r with
  | .error e => .error e
  | .ok (bl, r') =>
      if h : leNat bl < 2 ^ 128 then
        .ok (Instr.vconst .v128 ⟨leNat bl, h⟩, r')
      else .error .range

theorem decV128Const_sound [authority : BinaryAuthority]
    {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decV128Const r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ ∀ bo, Bprefixed 0xFD 12 bo → Binstr (bo ++ bb) i := by
  rw [decV128Const] at h
  split at h
  · simp at h
  · rename_i bl r'' hbl
    split at h
    · rename_i hlt
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨bb, hbb, hd⟩ := decBytes_sound 16 r bl r'' hbl
      refine ⟨bb, by rw [hbb, hr], fun bo hbo => ?_⟩
      rw [← hv]
      exact Binstr.ofVecMem _ _
        (BinstrVecMem.v128Const bo bb bl ⟨leNat bl, hlt⟩ hbo hd rfl)
    · simp at h

/-- `| 0xFD 13:Bu32 (l:Blaneidx)^16 => VSHUFFLE (I8 X `16) l^16`. -/
def decShuffle (r : Bytes) : Except Fault (Instr × Bytes) :=
  match decRep decLaneIdx 16 r with
  | .error e => .error e
  | .ok (ls, r') => .ok (Instr.vshuffle bshI8x16 ls, r')

theorem decShuffle_sound [authority : BinaryAuthority]
    {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decShuffle r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ ∀ bo, Bprefixed 0xFD 13 bo → Binstr (bo ++ bb) i := by
  rw [decShuffle] at h
  split at h
  · simp at h
  · rename_i ls r'' hls
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨bb, hbb, hd⟩ := decRep_sound decLaneIdx_sound 16 r ls r'' hls
    refine ⟨bb, by rw [hbb, hr], fun bo hbo => ?_⟩
    rw [← hv]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Shuffle bo bb ls hbo hd)

/-- Every `0xFB k` opcode of `5.3-binary.instructions.spectec` that carries no
immediate, one entry per production. -/
def opFB0 : Nat → Option Instr
  | 15 => some (Instr.arrayLen)
  | 26 => some (Instr.anyConvertExtern)
  | 27 => some (Instr.externConvertAny)
  | 28 => some (Instr.refI31)
  | 29 => some (Instr.i31Get .s)
  | 30 => some (Instr.i31Get .u)
  | _ => none

theorem opFB0_sound [authority : BinaryAuthority]
    {k : Nat} {i : Instr} {bo : Bytes} (hk : opFB0 k = some i)
    (hbo : Bprefixed 0xFB k bo) : Binstr bo i := by
  unfold opFB0 at hk
  split at hk
  · cases hk; exact Binstr.ofArray _ _ (BinstrArray.len bo hbo)
  · cases hk; exact Binstr.ofExtern _ _ (BinstrExtern.anyConvertExtern bo hbo)
  · cases hk; exact Binstr.ofExtern _ _ (BinstrExtern.externConvertAny bo hbo)
  · cases hk; exact Binstr.ofI31 _ _ (BinstrI31.refI31 bo hbo)
  · cases hk; exact Binstr.ofI31 _ _ (BinstrI31.getS bo hbo)
  · cases hk; exact Binstr.ofI31 _ _ (BinstrI31.getU bo hbo)
  · cases hk


/-- Every `0xFB k` opcode of `5.3-binary.instructions.spectec` that carries an
immediate, dispatched on the `Bu32` selector. -/
def decFB [authority : BinaryAuthority]
    (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match k with
  | 0 => arg1 decIdx (fun x => Instr.structNew x) r
  | 1 => arg1 decIdx (fun x => Instr.structNewDefault x) r
  | 2 => arg2 decIdx decU32 (fun x y => Instr.structGet none x y) r
  | 3 => arg2 decIdx decU32 (fun x y => Instr.structGet (some .s) x y) r
  | 4 => arg2 decIdx decU32 (fun x y => Instr.structGet (some .u) x y) r
  | 5 => arg2 decIdx decU32 (fun x y => Instr.structSet x y) r
  | 6 => arg1 decIdx (fun x => Instr.arrayNew x) r
  | 7 => arg1 decIdx (fun x => Instr.arrayNewDefault x) r
  | 8 => arg2 decIdx decU32 (fun x y => Instr.arrayNewFixed x y) r
  | 9 => arg2 decIdx decIdx (fun x y => Instr.arrayNewData x y) r
  | 10 => arg2 decIdx decIdx (fun x y => Instr.arrayNewElem x y) r
  | 11 => arg1 decIdx (fun x => Instr.arrayGet none x) r
  | 12 => arg1 decIdx (fun x => Instr.arrayGet (some .s) x) r
  | 13 => arg1 decIdx (fun x => Instr.arrayGet (some .u) x) r
  | 14 => arg1 decIdx (fun x => Instr.arraySet x) r
  | 16 => arg1 decIdx (fun x => Instr.arrayFill x) r
  | 17 => arg2 decIdx decIdx (fun x y => Instr.arrayCopy x y) r
  | 18 => arg2 decIdx decIdx (fun x y => Instr.arrayInitData x y) r
  | 19 => arg2 decIdx decIdx (fun x y => Instr.arrayInitElem x y) r
  | 20 => arg1 decHeaptype (fun x => Instr.refTest (.ref none x)) r
  | 21 => arg1 decHeaptype (fun x => Instr.refTest (.ref (some .null) x)) r
  | 22 => arg1 decHeaptype (fun x => Instr.refCast (.ref none x)) r
  | 23 => arg1 decHeaptype (fun x => Instr.refCast (.ref (some .null) x)) r
  | 24 => arg4 decCastop decIdx decHeaptype decHeaptype (fun x y z w => Instr.brOnCast y (.ref x.1 z) (.ref x.2 w)) r
  | 25 => arg4 decCastop decIdx decHeaptype decHeaptype (fun x y z w => Instr.brOnCastFail y (.ref x.1 z) (.ref x.2 w)) r
  | _ => Except.error Fault.opcode

theorem decFB_sound [authority : BinaryAuthority]
    {k : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decFB k r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ ∀ bo, Bprefixed 0xFB k bo → Binstr (bo ++ bb) i := by
  unfold decFB at h
  split at h
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofStruct _ _ (BinstrStruct.new bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofStruct _ _ (BinstrStruct.newDefault bo bb x hbo hg1)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decU32_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofStruct _ _ (BinstrStruct.get bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decU32_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofStruct _ _ (BinstrStruct.getS bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decU32_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofStruct _ _ (BinstrStruct.getU bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decU32_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofStruct _ _ (BinstrStruct.set bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.new bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.newDefault bo bb x hbo hg1)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decU32_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.newFixed bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.newData bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.newElem bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.get bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.getS bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.getU bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.set bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofArray _ _ (BinstrArray.fill bo bb x hbo hg1)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.copy bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.initData bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decIdx_sound decIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofArray _ _ (BinstrArray.initElem bo b1 b2 x y hbo hg1 hg2)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decHeaptype_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofCast _ _ (BinstrCast.test bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decHeaptype_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofCast _ _ (BinstrCast.testNull bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decHeaptype_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofCast _ _ (BinstrCast.cast bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decHeaptype_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofCast _ _ (BinstrCast.castNull bo bb x hbo hg1)
  · obtain ⟨b1, b2, b3, b4, x, y, z, w, hb, hg1, hg2, hg3, hg4, hi⟩ := arg4_sound decCastop_sound decIdx_sound decHeaptype_sound decHeaptype_sound _ h
    refine ⟨b1 ++ b2 ++ b3 ++ b4, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofCast _ _ (BinstrCast.brOnCast bo b1 b2 b3 b4 x.1 x.2 y z w hbo hg1 hg2 hg3 hg4)
  · obtain ⟨b1, b2, b3, b4, x, y, z, w, hb, hg1, hg2, hg3, hg4, hi⟩ := arg4_sound decCastop_sound decIdx_sound decHeaptype_sound decHeaptype_sound _ h
    refine ⟨b1 ++ b2 ++ b3 ++ b4, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofCast _ _ (BinstrCast.brOnCastFail bo b1 b2 b3 b4 x.1 x.2 y z w hbo hg1 hg2 hg3 hg4)
  · cases h

/-- Every `0xFD k` opcode that carries no immediate, selected by the finite
binary authority.  AMD-012 changes only selector 275's operand shape. -/
def opFD0For [authority : BinaryAuthority] : Nat → Option Instr
  | 14 => some (Instr.vswizzlop bshI8x16 .swizzle)
  | 256 => some (Instr.vswizzlop bshI8x16 .relaxedSwizzle)
  | 15 => some (Instr.vsplat shI8x16)
  | 16 => some (Instr.vsplat shI16x8)
  | 17 => some (Instr.vsplat shI32x4)
  | 18 => some (Instr.vsplat shI64x2)
  | 19 => some (Instr.vsplat shF32x4)
  | 20 => some (Instr.vsplat shF64x2)
  | 35 => some (Instr.vrelop shI8x16 (.int .eq))
  | 36 => some (Instr.vrelop shI8x16 (.int .ne))
  | 37 => some (Instr.vrelop shI8x16 (.int (.lt .s)))
  | 38 => some (Instr.vrelop shI8x16 (.int (.lt .u)))
  | 39 => some (Instr.vrelop shI8x16 (.int (.gt .s)))
  | 40 => some (Instr.vrelop shI8x16 (.int (.gt .u)))
  | 41 => some (Instr.vrelop shI8x16 (.int (.le .s)))
  | 42 => some (Instr.vrelop shI8x16 (.int (.le .u)))
  | 43 => some (Instr.vrelop shI8x16 (.int (.ge .s)))
  | 44 => some (Instr.vrelop shI8x16 (.int (.ge .u)))
  | 45 => some (Instr.vrelop shI16x8 (.int .eq))
  | 46 => some (Instr.vrelop shI16x8 (.int .ne))
  | 47 => some (Instr.vrelop shI16x8 (.int (.lt .s)))
  | 48 => some (Instr.vrelop shI16x8 (.int (.lt .u)))
  | 49 => some (Instr.vrelop shI16x8 (.int (.gt .s)))
  | 50 => some (Instr.vrelop shI16x8 (.int (.gt .u)))
  | 51 => some (Instr.vrelop shI16x8 (.int (.le .s)))
  | 52 => some (Instr.vrelop shI16x8 (.int (.le .u)))
  | 53 => some (Instr.vrelop shI16x8 (.int (.ge .s)))
  | 54 => some (Instr.vrelop shI16x8 (.int (.ge .u)))
  | 55 => some (Instr.vrelop shI32x4 (.int .eq))
  | 56 => some (Instr.vrelop shI32x4 (.int .ne))
  | 57 => some (Instr.vrelop shI32x4 (.int (.lt .s)))
  | 58 => some (Instr.vrelop shI32x4 (.int (.lt .u)))
  | 59 => some (Instr.vrelop shI32x4 (.int (.gt .s)))
  | 60 => some (Instr.vrelop shI32x4 (.int (.gt .u)))
  | 61 => some (Instr.vrelop shI32x4 (.int (.le .s)))
  | 62 => some (Instr.vrelop shI32x4 (.int (.le .u)))
  | 63 => some (Instr.vrelop shI32x4 (.int (.ge .s)))
  | 64 => some (Instr.vrelop shI32x4 (.int (.ge .u)))
  | 65 => some (Instr.vrelop shF32x4 (.float .eq))
  | 66 => some (Instr.vrelop shF32x4 (.float .ne))
  | 67 => some (Instr.vrelop shF32x4 (.float .lt))
  | 68 => some (Instr.vrelop shF32x4 (.float .gt))
  | 69 => some (Instr.vrelop shF32x4 (.float .le))
  | 70 => some (Instr.vrelop shF32x4 (.float .ge))
  | 71 => some (Instr.vrelop shF64x2 (.float .eq))
  | 72 => some (Instr.vrelop shF64x2 (.float .ne))
  | 73 => some (Instr.vrelop shF64x2 (.float .lt))
  | 74 => some (Instr.vrelop shF64x2 (.float .gt))
  | 75 => some (Instr.vrelop shF64x2 (.float .le))
  | 76 => some (Instr.vrelop shF64x2 (.float .ge))
  | 214 => some (Instr.vrelop shI64x2 (.int .eq))
  | 215 => some (Instr.vrelop shI64x2 (.int .ne))
  | 216 => some (Instr.vrelop shI64x2 (.int (.lt .s)))
  | 217 => some (Instr.vrelop shI64x2 (.int (.gt .s)))
  | 218 => some (Instr.vrelop shI64x2 (.int (.le .s)))
  | 219 => some (Instr.vrelop shI64x2 (.int (.ge .s)))
  | 77 => some (Instr.vvunop .v128 .not)
  | 78 => some (Instr.vvbinop .v128 .and)
  | 79 => some (Instr.vvbinop .v128 .andnot)
  | 80 => some (Instr.vvbinop .v128 .or)
  | 81 => some (Instr.vvbinop .v128 .xor)
  | 82 => some (Instr.vvternop .v128 .bitselect)
  | 83 => some (Instr.vvtestop .v128 .anyTrue)
  | 96 => some (Instr.vunop shI8x16 (.int .abs))
  | 97 => some (Instr.vunop shI8x16 (.int .neg))
  | 98 => some (Instr.vunop shI8x16 (.int .popcnt))
  | 99 => some (Instr.vtestop shI8x16 (.int .allTrue))
  | 100 => some (Instr.vbitmask ishI8x16)
  | 101 => some (Instr.vnarrow ishI8x16 ishI16x8 .s)
  | 102 => some (Instr.vnarrow ishI8x16 ishI16x8 .u)
  | 107 => some (Instr.vshiftop ishI8x16 .shl)
  | 108 => some (Instr.vshiftop ishI8x16 (.shr .s))
  | 109 => some (Instr.vshiftop ishI8x16 (.shr .u))
  | 110 => some (Instr.vbinop shI8x16 (.int .add))
  | 111 => some (Instr.vbinop shI8x16 (.int (.addSat .s)))
  | 112 => some (Instr.vbinop shI8x16 (.int (.addSat .u)))
  | 113 => some (Instr.vbinop shI8x16 (.int .sub))
  | 114 => some (Instr.vbinop shI8x16 (.int (.subSat .s)))
  | 115 => some (Instr.vbinop shI8x16 (.int (.subSat .u)))
  | 118 => some (Instr.vbinop shI8x16 (.int (.min .s)))
  | 119 => some (Instr.vbinop shI8x16 (.int (.min .u)))
  | 120 => some (Instr.vbinop shI8x16 (.int (.max .s)))
  | 121 => some (Instr.vbinop shI8x16 (.int (.max .u)))
  | 123 => some (Instr.vbinop shI8x16 (.int (.avgr .u)))
  | 124 => some (Instr.vextunop ishI16x8 ishI8x16 (.extaddPairwise .s))
  | 125 => some (Instr.vextunop ishI16x8 ishI8x16 (.extaddPairwise .u))
  | 128 => some (Instr.vunop shI16x8 (.int .abs))
  | 129 => some (Instr.vunop shI16x8 (.int .neg))
  | 130 => some (Instr.vbinop shI16x8 (.int (.q15mulrSat .s)))
  | 142 => some (Instr.vbinop shI16x8 (.int .add))
  | 143 => some (Instr.vbinop shI16x8 (.int (.addSat .s)))
  | 144 => some (Instr.vbinop shI16x8 (.int (.addSat .u)))
  | 145 => some (Instr.vbinop shI16x8 (.int .sub))
  | 146 => some (Instr.vbinop shI16x8 (.int (.subSat .s)))
  | 147 => some (Instr.vbinop shI16x8 (.int (.subSat .u)))
  | 149 => some (Instr.vbinop shI16x8 (.int .mul))
  | 150 => some (Instr.vbinop shI16x8 (.int (.min .s)))
  | 151 => some (Instr.vbinop shI16x8 (.int (.min .u)))
  | 152 => some (Instr.vbinop shI16x8 (.int (.max .s)))
  | 153 => some (Instr.vbinop shI16x8 (.int (.max .u)))
  | 155 => some (Instr.vbinop shI16x8 (.int (.avgr .u)))
  | 273 => some (Instr.vbinop shI16x8 (.int (.relaxedQ15mulr .s)))
  | 131 => some (Instr.vtestop shI16x8 (.int .allTrue))
  | 132 => some (Instr.vbitmask ishI16x8)
  | 133 => some (Instr.vnarrow ishI16x8 ishI32x4 .s)
  | 134 => some (Instr.vnarrow ishI16x8 ishI32x4 .u)
  | 135 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .low .s)))
  | 136 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .high .s)))
  | 137 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .low .u)))
  | 138 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .high .u)))
  | 139 => some (Instr.vshiftop ishI16x8 .shl)
  | 140 => some (Instr.vshiftop ishI16x8 (.shr .s))
  | 141 => some (Instr.vshiftop ishI16x8 (.shr .u))
  | 156 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .low .s))
  | 157 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .high .s))
  | 158 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .low .u))
  | 159 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .high .u))
  | 274 => some (Instr.vextbinop ishI16x8 ishI8x16 (.relaxedDot .s))
  | 126 => some (Instr.vextunop ishI32x4 ishI16x8 (.extaddPairwise .s))
  | 127 => some (Instr.vextunop ishI32x4 ishI16x8 (.extaddPairwise .u))
  | 160 => some (Instr.vunop shI32x4 (.int .abs))
  | 161 => some (Instr.vunop shI32x4 (.int .neg))
  | 163 => some (Instr.vtestop shI32x4 (.int .allTrue))
  | 164 => some (Instr.vbitmask ishI32x4)
  | 167 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .low .s)))
  | 168 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .high .s)))
  | 169 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .low .u)))
  | 170 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .high .u)))
  | 171 => some (Instr.vshiftop ishI32x4 .shl)
  | 172 => some (Instr.vshiftop ishI32x4 (.shr .s))
  | 173 => some (Instr.vshiftop ishI32x4 (.shr .u))
  | 174 => some (Instr.vbinop shI32x4 (.int .add))
  | 177 => some (Instr.vbinop shI32x4 (.int .sub))
  | 181 => some (Instr.vbinop shI32x4 (.int .mul))
  | 182 => some (Instr.vbinop shI32x4 (.int (.min .s)))
  | 183 => some (Instr.vbinop shI32x4 (.int (.min .u)))
  | 184 => some (Instr.vbinop shI32x4 (.int (.max .s)))
  | 185 => some (Instr.vbinop shI32x4 (.int (.max .u)))
  | 186 => some (Instr.vextbinop ishI32x4 ishI16x8 (.dot .s))
  | 188 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .low .s))
  | 189 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .high .s))
  | 190 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .low .u))
  | 191 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .high .u))
  | 275 =>
      match authority.revision with
      | .pinned => some (Instr.vextternop ishI32x4 ishI16x8 (.relaxedDotAdd .s))
      | .amended => some (Instr.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s))
  | 192 => some (Instr.vunop shI64x2 (.int .abs))
  | 193 => some (Instr.vunop shI64x2 (.int .neg))
  | 195 => some (Instr.vtestop shI64x2 (.int .allTrue))
  | 196 => some (Instr.vbitmask ishI64x2)
  | 199 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .low .s)))
  | 200 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .high .s)))
  | 201 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .low .u)))
  | 202 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .high .u)))
  | 203 => some (Instr.vshiftop ishI64x2 .shl)
  | 204 => some (Instr.vshiftop ishI64x2 (.shr .s))
  | 205 => some (Instr.vshiftop ishI64x2 (.shr .u))
  | 206 => some (Instr.vbinop shI64x2 (.int .add))
  | 209 => some (Instr.vbinop shI64x2 (.int .sub))
  | 213 => some (Instr.vbinop shI64x2 (.int .mul))
  | 220 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .low .s))
  | 221 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .high .s))
  | 222 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .low .u))
  | 223 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .high .u))
  | 103 => some (Instr.vunop shF32x4 (.float .ceil))
  | 104 => some (Instr.vunop shF32x4 (.float .floor))
  | 105 => some (Instr.vunop shF32x4 (.float .trunc))
  | 106 => some (Instr.vunop shF32x4 (.float .nearest))
  | 224 => some (Instr.vunop shF32x4 (.float .abs))
  | 225 => some (Instr.vunop shF32x4 (.float .neg))
  | 227 => some (Instr.vunop shF32x4 (.float .sqrt))
  | 228 => some (Instr.vbinop shF32x4 (.float .add))
  | 229 => some (Instr.vbinop shF32x4 (.float .sub))
  | 230 => some (Instr.vbinop shF32x4 (.float .mul))
  | 231 => some (Instr.vbinop shF32x4 (.float .div))
  | 232 => some (Instr.vbinop shF32x4 (.float .min))
  | 233 => some (Instr.vbinop shF32x4 (.float .max))
  | 234 => some (Instr.vbinop shF32x4 (.float .pmin))
  | 235 => some (Instr.vbinop shF32x4 (.float .pmax))
  | 269 => some (Instr.vbinop shF32x4 (.float .relaxedMin))
  | 270 => some (Instr.vbinop shF32x4 (.float .relaxedMax))
  | 261 => some (Instr.vternop shF32x4 (.float .relaxedMadd))
  | 262 => some (Instr.vternop shF32x4 (.float .relaxedNmadd))
  | 116 => some (Instr.vunop shF64x2 (.float .ceil))
  | 117 => some (Instr.vunop shF64x2 (.float .floor))
  | 122 => some (Instr.vunop shF64x2 (.float .trunc))
  | 148 => some (Instr.vunop shF64x2 (.float .nearest))
  | 236 => some (Instr.vunop shF64x2 (.float .abs))
  | 237 => some (Instr.vunop shF64x2 (.float .neg))
  | 239 => some (Instr.vunop shF64x2 (.float .sqrt))
  | 240 => some (Instr.vbinop shF64x2 (.float .add))
  | 241 => some (Instr.vbinop shF64x2 (.float .sub))
  | 242 => some (Instr.vbinop shF64x2 (.float .mul))
  | 243 => some (Instr.vbinop shF64x2 (.float .div))
  | 244 => some (Instr.vbinop shF64x2 (.float .min))
  | 245 => some (Instr.vbinop shF64x2 (.float .max))
  | 246 => some (Instr.vbinop shF64x2 (.float .pmin))
  | 247 => some (Instr.vbinop shF64x2 (.float .pmax))
  | 271 => some (Instr.vbinop shF64x2 (.float .relaxedMin))
  | 272 => some (Instr.vbinop shF64x2 (.float .relaxedMax))
  | 263 => some (Instr.vternop shF64x2 (.float .relaxedMadd))
  | 264 => some (Instr.vternop shF64x2 (.float .relaxedNmadd))
  | 265 => some (Instr.vternop shI8x16 (.int .relaxedLaneselect))
  | 266 => some (Instr.vternop shI16x8 (.int .relaxedLaneselect))
  | 267 => some (Instr.vternop shI32x4 (.int .relaxedLaneselect))
  | 268 => some (Instr.vternop shI64x2 (.int .relaxedLaneselect))
  | 94 => some (Instr.vcvtop shF32x4 shF64x2 (.ff (.demote .zero)))
  | 95 => some (Instr.vcvtop shF64x2 shF32x4 (.ff (.promote .low)))
  | 248 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.truncSat .s none)))
  | 249 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.truncSat .u none)))
  | 250 => some (Instr.vcvtop shF32x4 shI32x4 (.jf (.convert none .s)))
  | 251 => some (Instr.vcvtop shF32x4 shI32x4 (.jf (.convert none .u)))
  | 252 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.truncSat .s (some .zero))))
  | 253 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.truncSat .u (some .zero))))
  | 254 => some (Instr.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .s)))
  | 255 => some (Instr.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .u)))
  | 257 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .s none)))
  | 258 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .u none)))
  | 259 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .s (some .zero))))
  | 260 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .u (some .zero))))
  | _ => none

/-- The verbatim pinned no-immediate SIMD table. -/
def opFD0 : Nat → Option Instr := @opFD0For pinnedBinaryAuthority

@[simp] theorem opFD0For_pinned :
    @opFD0For pinnedBinaryAuthority = opFD0 := rfl

theorem opFD0For_sound [authority : BinaryAuthority]
    {k : Nat} {i : Instr} {bo : Bytes} (hk : opFD0For k = some i)
    (hbo : Bprefixed 0xFD k bo) : Binstr bo i := by
  unfold opFD0For at hk
  split at hk
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Swizzle bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16RelaxedSwizzle bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2Splat bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Lt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Gt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Le bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Ge bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Lt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Gt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Le bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Ge bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2GeS bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.not bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.and bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.andnot bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.or bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.xor bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.bitselect bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.anyTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Abs bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Neg bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Popcnt bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AllTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Bitmask bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16NarrowI16x8S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16NarrowI16x8U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Shl bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16ShrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16ShrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Add bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AddSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AddSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Sub bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16SubSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16SubSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MinS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MinU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MaxS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MaxU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AvgrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtaddPairwiseI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtaddPairwiseI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Abs bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Neg bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Q15mulrSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Add bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AddSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AddSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Sub bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8SubSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8SubSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Mul bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MinS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MinU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MaxS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MaxU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AvgrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8RelaxedQ15mulrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AllTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Bitmask bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8NarrowI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8NarrowI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendLowI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendHighI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendLowI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendHighI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Shl bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ShrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ShrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulLowI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulHighI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulLowI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulHighI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8RelaxedDotI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtaddPairwiseI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtaddPairwiseI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Abs bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Neg bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4AllTrue bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Bitmask bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendLowI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendHighI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendLowI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendHighI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Shl bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ShrS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ShrU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Add bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Sub bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Mul bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MinS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MinU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MaxS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MaxU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4DotI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulLowI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulHighI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulLowI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulHighI16x8U bo hbo) (by decide))
  ·
    cases authority with
    | mk revision =>
        cases revision with
        | pinned =>
            cases hk
            exact @Binstr.ofVecInt32And64 pinnedBinaryAuthority _ _
              (BinstrVecInt32And64.i32x4RelaxedDotAddI16x8S bo hbo)
        | amended =>
            cases hk
            exact @Binstr.ofVecInt32And64 amendedBinaryAuthority _ _
              (BinstrVecInt32And64For.correctedRelaxedDotAdd hbo)
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Abs bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Neg bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2AllTrue bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Bitmask bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendLowI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendHighI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendLowI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendHighI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Shl bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ShrS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ShrU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Add bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Sub bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Mul bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulLowI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulHighI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulLowI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulHighI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Ceil bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Floor bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Trunc bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Nearest bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Abs bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Neg bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Sqrt bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Add bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Sub bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Mul bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Div bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Min bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Max bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Pmin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Pmax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedNmadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Ceil bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Floor bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Trunc bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Nearest bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Abs bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Neg bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Sqrt bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Add bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Sub bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Mul bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Div bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Min bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Max bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Pmin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Pmax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedNmadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i8x16RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i16x8RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i64x2RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4DemoteF64x2Zero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2PromoteLowF32x4 bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4ConvertI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4ConvertI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF64x2SZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF64x2UZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2ConvertLowI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2ConvertLowI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF64x2SZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF64x2UZero bo hbo)
  · cases hk


/-- Every `0xFD k` opcode of `5.3-binary.instructions.spectec` that carries an
immediate, dispatched on the `Bu32` selector. -/
def decFD (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match k with
  | 0 => arg1 decMemarg (fun x => Instr.vload .v128 none x.1 x.2) r
  | 1 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s8 8 .s)) x.1 x.2) r
  | 2 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s8 8 .u)) x.1 x.2) r
  | 3 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s16 4 .s)) x.1 x.2) r
  | 4 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s16 4 .u)) x.1 x.2) r
  | 5 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s32 2 .s)) x.1 x.2) r
  | 6 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.shape .s32 2 .u)) x.1 x.2) r
  | 7 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.splat .s8)) x.1 x.2) r
  | 8 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.splat .s16)) x.1 x.2) r
  | 9 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.splat .s32)) x.1 x.2) r
  | 10 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.splat .s64)) x.1 x.2) r
  | 11 => arg1 decMemarg (fun x => Instr.vstore .v128 x.1 x.2) r
  | 84 => arg2 decMemarg decLaneIdx (fun x y => Instr.vloadLane .v128 .s8 x.1 x.2 y) r
  | 85 => arg2 decMemarg decLaneIdx (fun x y => Instr.vloadLane .v128 .s16 x.1 x.2 y) r
  | 86 => arg2 decMemarg decLaneIdx (fun x y => Instr.vloadLane .v128 .s32 x.1 x.2 y) r
  | 87 => arg2 decMemarg decLaneIdx (fun x y => Instr.vloadLane .v128 .s64 x.1 x.2 y) r
  | 88 => arg2 decMemarg decLaneIdx (fun x y => Instr.vstoreLane .v128 .s8 x.1 x.2 y) r
  | 89 => arg2 decMemarg decLaneIdx (fun x y => Instr.vstoreLane .v128 .s16 x.1 x.2 y) r
  | 90 => arg2 decMemarg decLaneIdx (fun x y => Instr.vstoreLane .v128 .s32 x.1 x.2 y) r
  | 91 => arg2 decMemarg decLaneIdx (fun x y => Instr.vstoreLane .v128 .s64 x.1 x.2 y) r
  | 92 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.zero .s32)) x.1 x.2) r
  | 93 => arg1 decMemarg (fun x => Instr.vload .v128 (some (.zero .s64)) x.1 x.2) r
  | 21 => arg1 decLaneIdx (fun x => Instr.vextractLane shI8x16 (some .s) x) r
  | 22 => arg1 decLaneIdx (fun x => Instr.vextractLane shI8x16 (some .u) x) r
  | 23 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shI8x16 x) r
  | 24 => arg1 decLaneIdx (fun x => Instr.vextractLane shI16x8 (some .s) x) r
  | 25 => arg1 decLaneIdx (fun x => Instr.vextractLane shI16x8 (some .u) x) r
  | 26 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shI16x8 x) r
  | 27 => arg1 decLaneIdx (fun x => Instr.vextractLane shI32x4 none x) r
  | 28 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shI32x4 x) r
  | 29 => arg1 decLaneIdx (fun x => Instr.vextractLane shI64x2 none x) r
  | 30 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shI64x2 x) r
  | 31 => arg1 decLaneIdx (fun x => Instr.vextractLane shF32x4 none x) r
  | 32 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shF32x4 x) r
  | 33 => arg1 decLaneIdx (fun x => Instr.vextractLane shF64x2 none x) r
  | 34 => arg1 decLaneIdx (fun x => Instr.vreplaceLane shF64x2 x) r
  | 12 => decV128Const r
  | 13 => decShuffle r
  | _ => Except.error Fault.opcode

theorem decFD_sound [authority : BinaryAuthority]
    {k : Nat} {r : Bytes} {i : Instr} {r' : Bytes}
    (h : decFD k r = .ok (i, r')) :
    ∃ bb, r = bb ++ r' ∧ ∀ bo, Bprefixed 0xFD k bo → Binstr (bo ++ bb) i := by
  unfold decFD at h
  split at h
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8x8S bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8x8U bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16x4S bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16x4U bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32x2S bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32x2U bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8Splat bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16Splat bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Splat bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Splat bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store bo bb x.1 x.2 hbo hg1)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store8Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store16Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store32Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨b1, b2, x, y, hb, hg1, hg2, hi⟩ := arg2_sound decMemarg_sound decLaneIdx_sound _ h
    refine ⟨b1 ++ b2, by simp [hb], fun bo hbo => ?_⟩
    rw [hi]
    simp only [← List.append_assoc]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store64Lane bo b1 b2 x.1 x.2 y hbo hg1 hg2)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Zero bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decMemarg_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Zero bo bb x.1 x.2 hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ExtractLaneS bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ExtractLaneU bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ReplaceLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ExtractLaneS bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ExtractLaneU bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ReplaceLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4ExtractLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4ReplaceLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2ExtractLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2ReplaceLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4ExtractLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4ReplaceLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2ExtractLane bo bb x hbo hg1)
  · obtain ⟨bb, x, hb, hg1, hi⟩ := arg1_sound decLaneIdx_sound _ h
    refine ⟨bb, hb, fun bo hbo => ?_⟩
    rw [hi]
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2ReplaceLane bo bb x hbo hg1)
  · exact decV128Const_sound h
  · exact decShuffle_sound h
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

/-! ## The non-recursive dispatch

Every production of `Binstr` except the five that recur into it -- `BLOCK`,
`LOOP`, the two forms of `IF`, and `TRY_TABLE` -- is decoded here, in one
function.  Splitting it out is what lets the recursive knot below be five cases
rather than five hundred, and it is what makes the completeness proof of
`DecodeInstrComplete.lean` a case analysis on nineteen non-recursive fragments
plus five recursive constructors. -/

/-- The `0xFB` opcode space, table and immediates together. -/
def decFBbody [authority : BinaryAuthority]
    (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match opFB0 k with
  | some i => .ok (i, r)
  | none => decFB k r

/-- The `0xFC` opcode space, table and immediates together. -/
def decFCbody (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match opFC0 k with
  | some i => .ok (i, r)
  | none => decFC k r

/-- The `0xFD` opcode space, table and immediates together. -/
def decFDbody [authority : BinaryAuthority]
    (k : Nat) (r : Bytes) : Except Fault (Instr × Bytes) :=
  match opFD0For k with
  | some i => .ok (i, r)
  | none => decFD k r

/-- Every production of `Binstr` that does not recur into `Binstr`. -/
def decInstrFlat [authority : BinaryAuthority]
    (bs : Bytes) : Except Fault (Instr × Bytes) :=
  match bs with
  | [] => Except.error Fault.eof
  | b :: r =>
      match op0For b.val with
      | some i => Except.ok (i, r)
      | none =>
          if b.val = 0xFB then
            (match decU32 r with
             | .error e => .error e
             | .ok (k, r₁) => decFBbody k.val r₁)
          else if b.val = 0xFC then
            (match decU32 r with
             | .error e => .error e
             | .ok (k, r₁) => decFCbody k.val r₁)
          else if b.val = 0xFD then
            (match decU32 r with
             | .error e => .error e
             | .ok (k, r₁) => decFDbody k.val r₁)
          else decOp1For b.val r

theorem decInstrFlat_sound [authority : BinaryAuthority] :
    Sound Binstr decInstrFlat := by
  intro bs i r h
  cases bs with
  | nil => cases h
  | cons b bs =>
      rw [decInstrFlat] at h
      split at h
      · rename_i i' hi'
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨[b], by rw [← hr]; rfl, ?_⟩
        have hb : b = tb b.val := byte_eq_tb b.property rfl
        rw [← hv, hb]
        exact op0For_sound hi'
      · split at h
        · -- 0xFB prefix
          rename_i hb
          split at h
          · cases h
          · rename_i k r₁ hk
            obtain ⟨bk, hbk, hdk⟩ := decU32_sound bs k r₁ hk
            have hpref : Bprefixed 0xFB k.val (b :: bk) := by
              rw [byte_eq_tb (by decide) hb]
              exact ⟨bk, rfl, ⟨k, hdk, rfl⟩⟩
            rw [decFBbody] at h
            split at h
            · rename_i i' hi'
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              refine ⟨b :: bk, by rw [hbk, hr]; rfl, ?_⟩
              rw [← hv]
              exact opFB0_sound hi' hpref
            · obtain ⟨bb, hbb, hfb⟩ := decFB_sound h
              refine ⟨b :: bk ++ bb, by rw [hbk, hbb]; simp, ?_⟩
              exact hfb (b :: bk) hpref
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
              rw [decFCbody] at h
              split at h
              · rename_i i' hi'
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                refine ⟨b :: bk, by rw [hbk, hr]; rfl, ?_⟩
                rw [← hv]
                exact opFC0_sound hi' hpref
              · obtain ⟨bb, hbb, hfc⟩ := decFC_sound h
                refine ⟨b :: bk ++ bb, by rw [hbk, hbb]; simp, ?_⟩
                exact hfc (b :: bk) hpref
          · split at h
            · -- 0xFD prefix
              rename_i hb
              split at h
              · cases h
              · rename_i k r₁ hk
                obtain ⟨bk, hbk, hdk⟩ := decU32_sound bs k r₁ hk
                have hpref : Bprefixed 0xFD k.val (b :: bk) := by
                  rw [byte_eq_tb (by decide) hb]
                  exact ⟨bk, rfl, ⟨k, hdk, rfl⟩⟩
                rw [decFDbody] at h
                split at h
                · rename_i i' hi'
                  obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                  refine ⟨b :: bk, by rw [hbk, hr]; rfl, ?_⟩
                  rw [← hv]
                  exact opFD0For_sound hi' hpref
                · obtain ⟨bb, hbb, hfd⟩ := decFD_sound h
                  refine ⟨b :: bk ++ bb, by rw [hbk, hbb]; simp, ?_⟩
                  exact hfd (b :: bk) hpref
            · -- everything else
              obtain ⟨bb, hbb, hd⟩ := decOp1For_sound h
              refine ⟨b :: bb, by rw [hbb]; rfl, ?_⟩
              rw [byte_eq_tb b.property rfl]
              exact hd

/-- `grammar Binstr : instr`, bounded by a block-nesting depth. -/
def decInstr [authority : BinaryAuthority] :
    Nat → Bytes → Except Fault (Instr × Bytes)
  | 0, _ => .error .eof
  | d + 1, bs =>
      match bs with
      | [] => Except.error Fault.eof
      | b :: r =>
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
              else decInstrFlat (b :: r)

/-- `grammar Bexpr : expr = | (in:Binstr)* 0x0B => in*`. -/
def decExpr [authority : BinaryAuthority]
    (d : Nat) (bs : Bytes) : Except Fault (Expr × Bytes) :=
  match decInstrs (decInstr d) bs.length bs with
  | .error e => .error e
  | .ok (is, r) =>
      match expectByte 0x0B r with
      | .error e => .error e
      | .ok r' => .ok (InstrSeq.ofList is, r')

/-- Explicit pinned and amended instances of the one recursive decoder family. -/
abbrev decInstrPinned : Nat → Bytes → Except Fault (Instr × Bytes) :=
  @decInstr pinnedBinaryAuthority

abbrev decInstrA : Nat → Bytes → Except Fault (Instr × Bytes) :=
  @decInstr amendedBinaryAuthority

abbrev decExprPinned : Nat → Bytes → Except Fault (Expr × Bytes) :=
  @decExpr pinnedBinaryAuthority

abbrev decExprA : Nat → Bytes → Except Fault (Expr × Bytes) :=
  @decExpr amendedBinaryAuthority

/-! ## Soundness -/

theorem decInstrs_sound [authority : BinaryAuthority]
    {decI : Bytes → Except Fault (Instr × Bytes)}
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

theorem decInstr_sound [authority : BinaryAuthority] :
    ∀ d : Nat, Sound Binstr (decInstr d) := by
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
                · -- every non-recursive production
                  exact decInstrFlat_sound (b :: bs) i r h

theorem decExpr_sound [authority : BinaryAuthority]
    (d : Nat) : Sound Bexpr (decExpr d) := by
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

theorem decInstrA_sound (d : Nat) : Sound BinstrA (decInstrA d) :=
  @decInstr_sound amendedBinaryAuthority d

theorem decExprA_sound (d : Nat) : Sound BexprA (decExprA d) :=
  @decExpr_sound amendedBinaryAuthority d

end WasmGemmGnaf.Wasm.Core.Decode
