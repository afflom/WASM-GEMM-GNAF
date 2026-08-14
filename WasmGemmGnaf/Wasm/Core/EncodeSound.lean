/-
  Wasm/Core/EncodeSound.lean --- the ROUND TRIP: decoding what the canonical
  encoder emits returns the module it was given.

  WHAT THIS IS.  This is the ONLY file in the repository that puts a Core 3.0
  decoder and a Core 3.0 encoder in one import graph, and it does nothing but
  compose two theorems that were proved apart:

      Wasm.Core.Binary.encodeBytes_Bmodule : encodable m = true ->
                                             Bmodule (encodeBytes m) m
      Wasm.Core.decode_complete            : Bmodule (ByteArray.toBytes b) m ->
                                             decode b = .ok m

  giving `decode (encode m) = .ok m` under the explicit decidable precondition
  `encodable m = true`.

  WHY THE COMPOSITION IS NOT CIRCULAR.  An external audit rejected an earlier
  round trip because the decoder had been proved inverse to the repository's own
  encoder: `decode_is_encode` made `decode_sound` say nothing about the pinned
  format.  Nothing of that shape happens here.  `Wasm/Core/Decode.lean` and
  `Wasm/Core/Encode.lean` do not import one another and neither is mentioned in
  the other's proofs; both are proved against `Bmodule`, the transcription of

      vendor/wasm-spec/specification/wasm-3.0/5.*-binary.*.spectec

  in `Wasm/Core/BinaryGrammar/`, which imports neither of them.  The round trip
  below is a corollary of two independent statements about that grammar, and
  `xtask independence` still sees the decoder theorems' proof terms free of any
  encoder.

  WHAT IS AND IS NOT CLAIMED ABOUT CANONICITY.

  * PROVED HERE: `decode (encode m) = .ok m` for every module the encoder
    accepts.
  * PROVED IN `Wasm/Core/Encode.lean`: minimal LEB128 (`lebU_minimal`: no
    `BuN` derivation of a value is shorter than the one `lebU` emits), and no
    custom section (all fourteen `Bcustomsec*` positions of `Bmodule` are
    instantiated with the empty sequence, visibly, in `encModule_Bmodule`).
  * NOT CLAIMED, BECAUSE IT IS FALSE: `decode bytes = .ok m -> encode m = bytes`.
    The pinned `Bu32` admits non-minimal LEB128, every section is optional, a
    custom section may appear at fourteen positions, and several constructs have
    two derivations, so a module has many encodings and only one of them is the
    canonical one.  No theorem of that shape is stated anywhere in this
    repository.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Core.Decode
import WasmGemmGnaf.Wasm.Core.Encode

set_option autoImplicit false
set_option maxRecDepth 4000000

namespace WasmGemmGnaf.Wasm.Core

open WasmGemmGnaf.Wasm.Core.Binary

/-! ## The two byte representations agree

`Wasm/Core/Decode.lean` reads a `ByteArray` as the grammar's `byte*` through
`ByteArray.toBytes`; `Wasm/Core/Encode.lean` writes the grammar's `byte*` into a
`ByteArray` through `Foundation.Bytes.pack`.  The two are inverse, which is the
only plumbing this file needs. -/

/-- A `byte` survives the trip through `UInt8`: `byte` is `{n // n < 0x100}`, so
the reduction modulo `2^8` in both directions is the identity. -/
theorem byte_uint8_roundTrip (b : Byte) : Byte.ofNat (UInt8.ofNat b.val).toNat = b := by
  have hb : b.val < 0x100 := b.property
  apply Subtype.ext
  show (UInt8.ofNat b.val).toNat % 0x100 = b.val
  have h : (UInt8.ofNat b.val).toNat = b.val % 256 := by simp
  rw [h]
  omega

/-- `ByteArray.toBytes` undoes the packing `Wasm.Core.Binary.encode` does. -/
theorem toBytes_pack (bs : Bytes) :
    ByteArray.toBytes
        (WasmGemmGnaf.Foundation.Bytes.pack (bs.map (fun b => UInt8.ofNat b.val))) = bs := by
  unfold ByteArray.toBytes
  rw [WasmGemmGnaf.Foundation.Bytes.toList_pack, List.map_map]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, Function.comp_apply, byte_uint8_roundTrip]
      rw [ih]

/-- The bytes the Core encoder produces, read back as the grammar's `byte*`,
are the bytes `encodeBytes` chose. -/
theorem toBytes_encode (m : Module) :
    ByteArray.toBytes (Binary.encode m) = Binary.encodeBytes m :=
  toBytes_pack _

/-! ## SPEC section 7.2 / 7.3: the round trip -/

/-- **The encoder's output is a derivation of the pinned binary grammar.**  The
precondition is explicit and decidable: `encodable m` is a `Bool` computed from
`m`, and `Wasm/Core/Encode.lean` says exactly which modules it is `false` on. -/
theorem encode_Bmodule (m : Module) (h : Binary.encodable m = true) :
    Binary.Bmodule (ByteArray.toBytes (Binary.encode m)) m := by
  rw [toBytes_encode]
  exact Binary.encodeBytes_Bmodule m h

/-- **THE ROUND TRIP.**  The decoder of the complete pinned Core 3.0 binary
format accepts the canonical encoding of a module and returns that module.

Proved by composing `encode_Bmodule` with `Wasm.Core.decode_complete`; neither
half mentions the other's executable side. -/
theorem decode_encode (m : Module) (h : Binary.encodable m = true) :
    decode (Binary.encode m) = .ok m :=
  decode_complete (encode_Bmodule m h)

/-- **THE ENCODER IS INJECTIVE** on the modules it accepts: two modules with the
same canonical encoding are the same module.  This is the canonicity statement
that is TRUE and useful; its converse, `decode bytes = .ok m -> encode m =
bytes`, is false for the reasons listed at the head of this file. -/
theorem encode_injective {m m' : Module} (h : Binary.encodable m = true)
    (h' : Binary.encodable m' = true) (he : Binary.encode m = Binary.encode m') :
    m = m' := by
  have h1 : decode (Binary.encode m') = .ok m := by rw [← he]; exact decode_encode m h
  have h2 : decode (Binary.encode m') = .ok m' := decode_encode m' h'
  rw [h1] at h2
  injection h2 with h2

end WasmGemmGnaf.Wasm.Core
