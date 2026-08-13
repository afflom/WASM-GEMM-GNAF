import WasmGemmGnaf.Wasm.Binary

set_option autoImplicit false

/-!
# Artifact: the emitter (SPEC §11.4)

SPEC §11.4 asks for

```lean
def Artifact.emit : Wasm.Module → ByteArray
theorem decode_emit : Wasm.decode (Artifact.emit m) = .ok m
```

## What this file proves, and where it falls short of that

`Wasm/Binary.lean` owns the verified SUBSET codec and proves
`Wasm.Subset.encode_decode_roundtrip`.  The emitter is *defined* to be that
encoder — it is not a second, independently written serializer that would have
to be re-verified — and `Artifact.decode_emit` is that round trip transported
along the definition.

**The shortfall, stated rather than hidden.**  Since the front-end migration,
`Wasm.decode` is the decoder of the complete pinned Core 3.0 binary format
(`Wasm/CoreFrontEnd.lean`), so SPEC's `decode_emit` above is a statement about
the Core decoder, and what is proved below is the same statement about
`Wasm.Subset.decode`.  `Conformance/RequiredSignatures.lean` therefore binds
`Artifact.decode_emit` as `-- spec-signature-weaker:` and `xtask claims required`
reports it OUTSTANDING.

Closing it needs a Core 3.0 ENCODER carrying a `Bmodule` derivation for every
Core module; this repository has none, and `Wasm/CoreGap.lean` proves no total
map `Wasm.Module → Wasm.Core.Module` exists along which the subset emitter could
be transported instead.

SPEC §11.4 further insists that "the emitter constructs byte candidates
produced from GNAF plans.  Universal selection, however, ranges over raw byte
strings and SHALL retain the exact winning bytes.  A permissively valid winner
is not silently decoded and re-encoded."  Nothing in this file decodes and
re-encodes anything: `emit` is a one-way map from a module to its canonical
bytes, and `emit_injective` shows distinct modules never share bytes.  The
retention of *selected* bytes is the selection layer's obligation, not the
emitter's, and no theorem here licenses replacing selected bytes by
`emit (Wasm.Subset.decode bytes)`.

Every declaration in this file is proved.  Nothing is assumed.
-/

namespace WasmGemmGnaf.Artifact

/-- **SPEC §11.4.**  The artifact emitter: the canonical binary encoding of a
module. -/
def emit (m : Wasm.Module) : ByteArray := Wasm.Subset.encode m

/-- **SPEC §11.4, `decode_emit`.**  Decoding an emitted artifact returns
exactly the module it was emitted from. -/
theorem decode_emit (m : Wasm.Module) : Wasm.Subset.decode (emit m) = .ok m :=
  Wasm.Subset.encode_decode_roundtrip m

/-- Distinct modules emit distinct artifacts. -/
theorem emit_injective : Function.Injective emit :=
  Wasm.Subset.encode_injective

/-- The emitted bytes are exactly the canonical encoding's bytes. -/
theorem emit_toList (m : Wasm.Module) : (emit m).toList = Wasm.Subset.encodeList m :=
  Wasm.Subset.toList_encode m

/-- The emitted artifact is not empty: it always carries the pinned preamble. -/
theorem emit_prefix (m : Wasm.Module) :
    ∃ t : List UInt8, (emit m).toList = Wasm.magicBytes ++ t := by
  rw [emit_toList]; exact Wasm.Subset.encodeList_prefix m

/-- Emitting is the *only* way to obtain bytes that decode: any byte string
that decodes to `m` is exactly `emit m`.  Together with `decode_emit` this makes
`emit` and `Wasm.Subset.decode` mutually inverse on decodable byte strings. -/
theorem eq_emit_of_decode {b : ByteArray} {m : Wasm.Module}
    (h : Wasm.Subset.decode b = .ok m) : b = emit m :=
  Wasm.Subset.decode_is_encode h

/-- Two artifacts that decode to the same module are byte-identical. -/
theorem emit_bytes_unique {b c : ByteArray} {m : Wasm.Module}
    (hb : Wasm.Subset.decode b = .ok m) (hc : Wasm.Subset.decode c = .ok m) : b = c :=
  Wasm.Subset.decode_injective hb hc

end WasmGemmGnaf.Artifact
