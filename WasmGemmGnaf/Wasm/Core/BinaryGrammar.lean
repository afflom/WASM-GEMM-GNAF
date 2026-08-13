/-
  Wasm/Core/BinaryGrammar.lean --- the declarative binary format of the pinned
  WebAssembly Core 3.0 front end.

  This module is the entry point for

      vendor/wasm-spec/specification/wasm-3.0/5.1-binary.values.spectec
      vendor/wasm-spec/specification/wasm-3.0/5.2-binary.types.spectec
      vendor/wasm-spec/specification/wasm-3.0/5.3-binary.instructions.spectec
      vendor/wasm-spec/specification/wasm-3.0/5.4-binary.modules.spectec

  transcribed at the pinned commit.  The parts are split to mirror those four
  files, plus `BinaryGrammar/Vector.lean` (the 256 `0xFD` productions of `5.3`)
  and `BinaryGrammar/Expressions.lean` (the five alternatives of `5.3` that recur
  into `Binstr`, and the union of all fragments).

  WHY THIS EXISTS AND WHAT IT IS FOR.  An external audit rejected this
  repository's `Wasm.decode_sound` and `Wasm.decode_complete` on the ground that
  they proved an equivalence with the repository's OWN encoding rather than with
  the pinned Core 3.0 binary grammar.  A soundness theorem stated against the
  decoder that is supposed to satisfy it is `rfl` wearing a theorem's name.  So
  the grammar comes first and separately:

  * `Bmodule : Bytes -> Module -> Prop` is a RELATION between byte sequences and
    abstract syntax, read off the pinned SpecTec productions, one Lean
    constructor per source alternative;
  * NO module under `BinaryGrammar/` imports a decoder, and none mentions one.
    The import graph is `Core/Modules.lean` (the abstract syntax) and nothing
    else from `Wasm/`;
  * consequently a future `decode_sound` / `decode_complete` proved against
    `Bmodule` has content: the two sides were written from different documents,
    and neither can be adjusted to make the other true without visibly changing
    a transcription of the vendored file.

  WHAT IS AND IS NOT CLAIMED.  This module claims that the pinned binary
  grammar's productions have been transcribed, that they carry the pinned
  opcode bytes, and that the transcription elaborates.  It does NOT claim that
  the transcription is correct -- only a proof relating it to something else can
  say that, and no such proof is asserted here.  Three places where the pinned
  source disagrees with itself or with the prose specification are flagged in
  doc comments rather than quietly corrected: the `BsN` continuation
  (`BinaryGrammar/Values.lean`), the `0xBB` conversion opcode
  (`BinaryGrammar/Instructions.lean`), and the missing `$free_instr` equations
  for the exception instructions (`BinaryGrammar/Modules.lean`).

  NOT DONE HERE, deliberately: there is no decoder, and no `decode_sound` or
  `decode_complete`.  Landing the grammar is the deliverable; the executable
  side is a later stage and belongs in a different module.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Modules

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

/-! ## Sanity checks

These are kernel-checked derivations, not tests.  Each one pins down a property
of the pinned grammar that the repository's previous, rejected codec did not
have, so that a reader can see the difference rather than take it on trust. -/

/-- BOUNDED PERMISSIVE LEB128, POSITIVELY.  `0x80 0x00` is a two-byte, NON-MINIMAL
encoding of `0`, and the pinned `Bu32` derives it: the second alternative of
`BuN` fires on any byte `>= 2^7`, with no minimality condition anywhere.  A codec
that accepts only `0x00` here is strictly narrower than Core 3.0, which is one
of the grounds on which `decode_complete` was rejected. -/
example : Bu32 [tb 0x80, tb 0x00] ⟨0, two_pow_pos 32⟩ :=
  BuN.more 32 (tb 0x80) [tb 0x00] 0 (by decide) (by decide)
    (BuN.last 25 (tb 0x00) (by decide) (by decide))

/-- ... and the canonical encoding of the same value is derivable too, so the
grammar really does relate one value to many byte sequences. -/
example : Bu32 [tb 0x00] ⟨0, two_pow_pos 32⟩ :=
  BuN.last 32 (tb 0x00) (by decide) (by decide)

/-- THE SELECTOR OF A PREFIXED OPCODE IS A `Bu32`, NOT A BYTE.  `0xFC 0x8C 0x00`
is `TABLE.INIT`'s prefix with a non-minimal selector, and the grammar accepts
it.  An implementation that switches on the single byte after `0xFC` rejects
this byte sequence and is therefore incomplete. -/
example : Bprefixed 0xFC 12 [tb 0xFC, tb 0x8C, tb 0x00] :=
  ⟨[tb 0x8C, tb 0x00], rfl,
    ⟨⟨12, by decide⟩,
      BuN.more 32 (tb 0x8C) [tb 0x00] 0 (by decide) (by decide)
        (BuN.last 25 (tb 0x00) (by decide) (by decide)),
      rfl⟩⟩

/-- EVERY SECTION IS OPTIONAL.  `Bsection_(N, BX)` has an `eps` alternative, so
the empty byte sequence is a derivation of an absent type section -- distinct
from a present type section whose list happens to be empty. -/
example : Btypesec [] [] := Bsection.absent

/-- ... while a present but empty type section is a different byte sequence
(`0x01` for the section id, then a `Bu32` length of `1`, then the `Bu32` count
`0`), and derives the same abstract value.  This is the ambiguity the binary
format really has; a decoder is free to emit one of them, but must accept
both. -/
example : Btypesec [tb 0x01, tb 0x01, tb 0x00] [] :=
  Bsection.present [tb 0x01] [tb 0x00] ⟨1, by decide⟩ []
    (BuN.last 32 (tb 0x01) (by decide) (by decide))
    (Blist.mk [tb 0x00] [] ⟨0, two_pow_pos 32⟩ []
      (BuN.last 32 (tb 0x00) (by decide) (by decide)) Rep.nil)
    rfl

/-- AN EXPRESSION IS `END`-TERMINATED.  The empty expression is the single byte
`0x0B`, and `0x0B` is part of the grammar rather than a decoder's loop
condition. -/
example : Bexpr [tb 0x0B] .nil := Bexpr.mk [] [] Binstrs.nil

end WasmGemmGnaf.Wasm.Core.Binary
