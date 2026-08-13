/-
  Wasm/CoreFrontEnd.lean --- the release front end, over `Wasm.Core`.

  ## What this file is

  The public names `Wasm.decode`, `Wasm.DeclarativeBinaryRelation`,
  `Wasm.decode_sound` and `Wasm.decode_complete` used to denote the SUBSET codec
  of `Wasm/Binary.lean` and the subset grammar of `Wasm/Declarative.lean`.  They
  no longer do.  Here they denote the pinned WebAssembly Core 3.0 decoder of
  `Wasm/Core/Decode.lean` and the pinned binary grammar `Wasm.Core.Binary.Bmodule`
  of `Wasm/Core/BinaryGrammar/`, transcribed from

      vendor/wasm-spec/specification/wasm-3.0/5.*-binary.*.spectec

  at the pinned commit.  The subset codec survives, still proved, under
  `Wasm.Subset.*`, where its type says what it is.

  ## Why the names moved

  `xtask independence` rejected the old `Wasm.decode_sound` and
  `Wasm.decode_complete`:

  > its proof term `WasmGemmGnaf.Wasm.decode_sound` mentions the executable
  > `WasmGemmGnaf.Wasm.decode_is_encode` -- a decoder proved inverse to its own
  > encoder says nothing about the pinned binary format

  That was exact.  `Wasm.Subset.declarativeBinaryRelation_iff_encode` equates the
  subset grammar with `bytes = Subset.encode module`, so both directions were
  round-trip lemmas about one codec and its own inverse.  `xtask claims required`
  demoted both names to CIRCULAR and they counted as outstanding.

  The two theorems below are proved by `Wasm.Core.decode_sound` and
  `Wasm.Core.decode_complete`, which are proved against `Bmodule`.  There is no
  encoder anywhere in that import graph -- `Wasm/Core/` contains none -- so the
  two sides were written from different documents and neither can be adjusted to
  make the other true without visibly changing a transcription of a vendored file.

  ## What is NOT claimed here

  * Not that the released ARTIFACT bytes are produced by a Core 3.0 encoder.
    `Artifact.emit` is still `Wasm.Subset.encode`, and `Artifact.decode_emit` is
    now bound as WEAKER for exactly that reason: there is no Core 3.0 encoder in
    this repository, so `Wasm.decode (Artifact.emit m) = .ok m` is not available.
    The demotion is recorded rather than papered over.
  * Not that `Wasm.Module` is `Wasm.Core.Module`.  It is not, and
    `Wasm/CoreGap.lean` proves no total map between them exists.  The release
    path's module type is a separate, still-outstanding migration step; what
    moved here is the front end SPEC section 7.3 states its two theorems over.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Foundation.Bytes
import WasmGemmGnaf.Wasm.Core.Decode

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## The decoder -/

/-- Why a decode of the pinned Core 3.0 binary format failed. -/
abbrev CoreDecodeFault : Type := Core.DecodeFault

/-- **The release decoder.**  The executable decoder for the complete pinned
WebAssembly Core 3.0 binary format, as SPEC section 7.2 requires: "The decoder
SHALL recognize the complete pinned Core 3.0 binary grammar."  It is
`Wasm.Core.decode`, under the public name SPEC section 7.3 states its theorems
over. -/
def decode (bytes : ByteArray) : Except CoreDecodeFault Core.Module :=
  Core.decode bytes

/-- **The declarative binary relation.**  `DeclarativeBinaryRelation bytes m`
holds exactly when the pinned Core 3.0 binary grammar derives `bytes` with
synthesized attribute `m`.

Its definition mentions no decoding function, and nothing in the import graph of
`Wasm.Core.Binary.Bmodule` mentions one either: `Wasm/Core/BinaryGrammar/` is a
transcription of `5.*-binary.*.spectec` and imports only the Core syntax. -/
def DeclarativeBinaryRelation (bytes : ByteArray) (module : Core.Module) : Prop :=
  Core.Binary.Bmodule (Core.ByteArray.toBytes bytes) module

/-! ## SPEC section 7.3 / 15 -/

/-- **SPEC section 15, `Wasm.decode_sound`.**  Everything the executable decoder
accepts is derivable in the pinned Core 3.0 binary grammar, and the module it
returns is the one the derivation produces.

Proved by `Wasm.Core.decode_sound`, against `Bmodule` and not against an
encoder. -/
theorem decode_sound {bytes : ByteArray} {module : Core.Module}
    (h : decode bytes = .ok module) : DeclarativeBinaryRelation bytes module :=
  Core.decode_sound h

/-- **SPEC section 15, `Wasm.decode_complete`.**  Everything the pinned Core 3.0
binary grammar derives, the executable decoder accepts, returning exactly the
module the derivation produces.

This is the direction a rejecting decoder would fail, and the direction that
matters for the release claim: a decoder that silently rejected a valid module
would SHRINK the set of programs the optimality statement quantifies over.

Proved by `Wasm.Core.decode_complete`, whose axiom closure is
`[propext, Quot.sound]` -- choice free. -/
theorem decode_complete {bytes : ByteArray} {module : Core.Module}
    (h : DeclarativeBinaryRelation bytes module) : decode bytes = .ok module :=
  Core.decode_complete h

/-- The two directions together: `Wasm.decode` and the pinned grammar accept
exactly the same byte sequences and agree on the value. -/
theorem decode_iff_declarative {bytes : ByteArray} {module : Core.Module} :
    decode bytes = .ok module ↔ DeclarativeBinaryRelation bytes module :=
  ⟨decode_sound, decode_complete⟩

/-! ## Non-vacuity

The two theorems above would be worthless if the relation held of everything or
of nothing.  Both facts below are kernel-checked closed terms. -/

/-- The pinned preamble --- magic and version --- as a `ByteArray`. -/
def preambleBytes : ByteArray :=
  Bytes.pack [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- `Wasm.decode` accepts the pinned preamble and returns the empty module. -/
theorem decode_preambleBytes : decode preambleBytes = .ok Core.emptyModule := by
  show Core.Decode.decModule (Core.ByteArray.toBytes preambleBytes) = _
  have h : Core.ByteArray.toBytes preambleBytes =
      Core.bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00] := by
    simp [Core.ByteArray.toBytes, preambleBytes, Core.bytesOf]
  rw [h]
  rfl

/-- **The relation is not empty.**  It holds of the pinned preamble and the
empty module. -/
theorem declarative_preamble :
    DeclarativeBinaryRelation preambleBytes Core.emptyModule :=
  decode_sound decode_preambleBytes

/-- **The relation is not everything.**  It does not hold of the empty byte
string: the pinned grammar requires the magic and version words. -/
theorem not_declarative_empty :
    ¬ DeclarativeBinaryRelation (Bytes.pack []) Core.emptyModule := by
  intro h
  have hd := decode_complete h
  have he : decode (Bytes.pack []) = .error .eof := by
    show Core.Decode.decModule (Core.ByteArray.toBytes (Bytes.pack [])) = _
    have h0 : Core.ByteArray.toBytes (Bytes.pack []) = [] := by
      simp [Core.ByteArray.toBytes]
    rw [h0]
    rfl
  rw [he] at hd
  exact absurd hd (by simp)

end WasmGemmGnaf.Wasm
