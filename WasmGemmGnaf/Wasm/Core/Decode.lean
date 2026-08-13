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

  WHAT IS NOT CLAIMED.  There is no `decode_complete` here, and none is
  asserted.  Completeness of the decoder against `Bmodule` is an open
  obligation; the component-level completeness lemmas that a proof of it would
  need (`decU32_complete`, `decName_complete`, `decValtype_complete`,
  `decRectype_complete`, `decExterntype_complete`, ...) are proved in the layers
  below, and what is missing is the instruction and module level.  Omitting the
  theorem is the conforming representation of that gap.

  SCOPE OF THE DECODER.  `decode` implements the whole module format -- real
  opcode bytes, custom sections at all fourteen positions, the function/code
  split, the data count section, bounded PERMISSIVE LEB128 (non-minimal
  encodings inside the width bound are accepted, as the pinned `BuN` accepts
  them), UTF-8 names, `END`-terminated expressions and compressed locals --
  with the instruction set of `Wasm/Core/DecodeInstructions.lean`, which covers
  everything outside the `0xFB` (GC) and `0xFD` (SIMD) opcode spaces.  Since
  soundness is a statement about what the decoder ACCEPTS, that restriction
  does not weaken `decode_sound`: an instruction the decoder does not implement
  is one it rejects.
-/
import WasmGemmGnaf.Wasm.Core.DecodeModules

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

/-- SOUNDNESS, against the declarative grammar and not against an encoder:
whatever `decode` accepts is derivable in the pinned binary format, and the
module it returns is the one the derivation produces. -/
theorem decode_sound {bytes : ByteArray} {m : Module}
    (h : decode bytes = .ok m) : Bmodule (ByteArray.toBytes bytes) m :=
  Decode.decModule_sound _ m h

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

end WasmGemmGnaf.Wasm.Core
