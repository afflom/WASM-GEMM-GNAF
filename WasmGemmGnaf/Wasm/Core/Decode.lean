/-
  Wasm/Core/Decode.lean --- the executable Core 3.0 decoder and its soundness
  theorem.

  WHAT THIS IS.  `decode` is a total, computable function from a `ByteArray` to
  a `module` of the pinned Core 3.0 abstract syntax, and `decode_sound` says
  that whenever it succeeds, the input really is a derivation of `Bmodule` --
  the DECLARATIVE binary grammar of `Wasm/Core/BinaryGrammar/`, transcribed from

      vendor/wasm-spec/specification/wasm-3.0/5.*-binary.*.spectec

  and mentioning no decoder anywhere in its import graph.

  WHY THAT MATTERS.  An external audit rejected this repository's earlier
  `Wasm.decode_sound` / `Wasm.decode_complete` because they were proved by
  routing through the repository's OWN encoder: a decoder proved inverse to its
  own encoder says nothing about the pinned format.  `decode_sound` below is
  proved against `Bmodule` and never mentions an encoder; the two sides were
  written from different documents and neither can be adjusted to make the other
  true without visibly changing a transcription of a vendored file.

  COMPLETENESS, AND WHY IT IS THE DIRECTION THAT MATTERS.  `decode_complete`
  below is the converse: every derivation of `Bmodule` is decoded, to the module
  the derivation produces.  Soundness alone is satisfied by a decoder that
  rejects everything, and a decoder that silently rejected a valid module would
  SHRINK the set of programs the release optimality statement quantifies over.
  The proof is in `Wasm/Core/DecodeInstrComplete.lean` (the instruction format,
  including both prefixed opcode spaces) and `Wasm/Core/DecodeModulesComplete.lean`
  (the section structure and the three starred side conditions), and it routes
  through no encoder: there is no encoder in this import graph at all.

  `decode_complete` is an executable-witness name under SPEC 4, so its axiom
  closure is `[propext, Quot.sound]` -- choice free.

  SCOPE OF THE DECODER.  `decode` implements the whole module format -- real
  opcode bytes, custom sections at all fourteen positions, the function/code
  split, the data count section, bounded PERMISSIVE LEB128 (non-minimal
  encodings inside the width bound are accepted, as the pinned `BuN` accepts
  them), UTF-8 names, `END`-terminated expressions and compressed locals --
  with the instruction set of `Wasm/Core/DecodeInstructions.lean`, which now
  covers the `0xFB` (garbage collection) and `0xFD` (SIMD) opcode spaces as well
  as the unprefixed and `0xFC` spaces.  `decode_complete` is what makes that
  claim of coverage checkable: a production the decoder failed to implement
  would be a `Bmodule` derivation it rejected, and the theorem says there is
  none.
-/
import WasmGemmGnaf.Wasm.Core.DecodeModulesComplete

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace WasmGemmGnaf.Wasm.Core

open WasmGemmGnaf.Wasm.Core.Binary

/-- Why a decode failed. -/
abbrev DecodeFault : Type := Decode.Fault

/-- A `ByteArray` read as the grammar's `byte*`.  Every `UInt8` is below
`0x100`, so this is the identity on values. -/
def ByteArray.toBytes (ba : ByteArray) : Bytes :=
  ba.toList.map (fun u => Byte.ofNat u.toNat)

/-- The executable decoder for the pinned WebAssembly Core 3.0 binary format. -/
def decode (bytes : ByteArray) : Except DecodeFault Module :=
  Decode.decModule (ByteArray.toBytes bytes)

/-- The executable decoder for the exact AMD-007/008/010 authority revision. -/
def decodeA (bytes : ByteArray) : Except DecodeFault Module :=
  Decode.decModuleA (ByteArray.toBytes bytes)

/-- The historical `decode` name is definitionally the explicit pinned decoder. -/
theorem decode_eq_pinned (bytes : ByteArray) :
    decode bytes = Decode.decModulePinned (ByteArray.toBytes bytes) :=
  rfl

/-- SOUNDNESS, against the declarative grammar and not against an encoder:
whatever `decode` accepts is derivable in the pinned binary format, and the
module it returns is the one the derivation produces. -/
theorem decode_sound {bytes : ByteArray} {m : Module}
    (h : decode bytes = .ok m) : Bmodule (ByteArray.toBytes bytes) m :=
  Decode.decModule_sound _ m h

/-- COMPLETENESS, against the declarative grammar and not against an encoder:
everything the pinned binary format derives, the decoder accepts, and returns
the module the derivation produces.  This is the direction a rejecting decoder
would fail. -/
theorem decode_complete {bytes : ByteArray} {m : Module}
    (h : Bmodule (ByteArray.toBytes bytes) m) : decode bytes = .ok m :=
  Decode.decModule_complete _ m h

/-- The two directions together: `decode` and the pinned `Bmodule` accept
exactly the same byte sequences and agree on the value. -/
theorem decode_iff_Bmodule {bytes : ByteArray} {m : Module} :
    decode bytes = .ok m ↔ Bmodule (ByteArray.toBytes bytes) m :=
  ⟨decode_sound, decode_complete⟩

/-- Soundness of `decodeA` against the exact amended grammar instantiation. -/
theorem decode_soundA {bytes : ByteArray} {m : Module}
    (h : decodeA bytes = .ok m) : BmoduleA (ByteArray.toBytes bytes) m :=
  Decode.decModule_soundA _ m h

/-- Completeness of `decodeA` against the exact amended grammar instantiation. -/
theorem decode_completeA {bytes : ByteArray} {m : Module}
    (h : BmoduleA (ByteArray.toBytes bytes) m) : decodeA bytes = .ok m :=
  Decode.decModule_completeA _ m h

/-- The amended executable decoder and amended grammar accept exactly the same
byte sequences and agree on the decoded module. -/
theorem decode_iff_BmoduleA {bytes : ByteArray} {m : Module} :
    decodeA bytes = .ok m ↔ BmoduleA (ByteArray.toBytes bytes) m :=
  ⟨decode_soundA, decode_completeA⟩

/-! ## Kernel-checked derivations

These are not tests: each is a closed term the kernel checks, pinning down a
property of the decoder that a reader can compare against the grammar.  They are
stated on `Decode.decModule` and an explicit `byte*` rather than on `decode` and
a `ByteArray`, because `ByteArray.toList` does not reduce in the kernel; `decode`
is `decModule` composed with that conversion. -/

/-- A `byte*` written as a list of numerals. -/
def bytesOf (l : List Nat) : Bytes := l.map Byte.ofNat

/-- The empty module, as a value. -/
def emptyModule : Module :=
  { types := [], imports := [], tags := [], globals := [], mems := [], tables := [],
    funcs := [], datas := [], elems := [], start := none, exports := [] }

/-- The smallest module: magic and version and nothing else. -/
example :
    Decode.decModule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]) =
      .ok emptyModule := by
  rfl

/-- ... and it really is a `Bmodule` derivation, by soundness. -/
example :
    Bmodule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]) emptyModule :=
  Decode.decModule_sound _ _ (by rfl)

/-- A bad magic number is rejected rather than guessed at. -/
example :
    Decode.decModule (bytesOf [0x01, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]) =
      .error .opcode := by
  rfl

/-- BOUNDED PERMISSIVE LEB128, POSITIVELY.  `0x81 0x00` is a NON-MINIMAL two-byte
encoding of `1`, and the pinned `Bu32` derives it; so does the decoder.  Here it
is the length field of an empty type section, which the previous, rejected codec
would have refused. -/
example :
    Decode.decModule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
                               0x01, 0x81, 0x00, 0x00]) = .ok emptyModule := by
  rfl

/-- ... and the same byte sequence is a `Bmodule` derivation. -/
example :
    Bmodule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
                      0x01, 0x81, 0x00, 0x00]) emptyModule :=
  Decode.decModule_sound _ _ (by rfl)

/-- A CUSTOM SECTION BEFORE THE TYPE SECTION is accepted and carries no
information into the module, exactly as `Bcustom` says. -/
example :
    Decode.decModule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
                               0x00, 0x02, 0x01, 0x41]) = .ok emptyModule := by
  rfl

/-- A custom section whose name is not valid UTF-8 has no derivation, and the
decoder rejects it. -/
example :
    Decode.decModule (bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
                               0x00, 0x02, 0x01, 0xFF]) = .error .utf8 := by
  rfl

/-! ### The two prefixed opcode spaces

The `0xFB` (garbage collection) and `0xFD` (SIMD) spaces were the omission an
external audit named.  `decode_complete` is the general statement that nothing
is omitted; these are three concrete points a reader can check against
`5.3-binary.instructions.spectec` without reading a proof. -/

/-- `| 0xFD 256:Bu32 => VSWIZZLOP (I8 X `16) RELAXED_SWIZZLE`.  The pinned
selector is 256 DECIMAL, which has no one-byte LEB128 form at all: the encoding
is `0xFD 0x80 0x02`.  A byte-keyed opcode table could not express this
production, and the SIMD selectors run to 275. -/
example : (Decode.decInstr 8 (bytesOf [0xFD, 0x80, 0x02])).isOk = true := by
  rfl

/-- ... and it is a derivation of the pinned `Binstr`, by soundness. -/
example : ∃ i : Instr, Binstr (bytesOf [0xFD, 0x80, 0x02]) i := by
  obtain ⟨i, hi⟩ : ∃ i : Instr,
      Decode.decInstr 8 (bytesOf [0xFD, 0x80, 0x02]) = .ok (i, []) := ⟨_, rfl⟩
  obtain ⟨b, hb, hd⟩ := Decode.decInstr_sound 8 _ i [] hi
  simp only [List.append_nil] at hb
  exact ⟨i, hb ▸ hd⟩

/-- `| 0xFD 35:Bu32 => VRELOP (I8 X `16) EQ`.  The selector is a `Bu32`, so the
non-minimal `0xA3 0x00` is the same instruction as the minimal `0x23` -- not a
different one, and not a rejection. -/
example :
    Decode.decInstr 8 (bytesOf [0xFD, 0x23]) =
      Decode.decInstr 8 (bytesOf [0xFD, 0xA3, 0x00]) := by
  rfl

/-- `| 0xFB 30:Bu32 => I31.GET U`, the last production of the garbage collection
space. -/
example : ∃ i : Instr, Binstr (bytesOf [0xFB, 0x1E]) i := by
  obtain ⟨i, hi⟩ : ∃ i : Instr,
      Decode.decInstr 8 (bytesOf [0xFB, 0x1E]) = .ok (i, []) := ⟨_, rfl⟩
  obtain ⟨b, hb, hd⟩ := Decode.decInstr_sound 8 _ i [] hi
  simp only [List.append_nil] at hb
  exact ⟨i, hb ▸ hd⟩

end WasmGemmGnaf.Wasm.Core
