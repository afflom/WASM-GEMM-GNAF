/-
  Artifact/Emit.lean --- the public amended-Core encoding endpoint.

  The emitter is the public amended Core 3.0 encoder.  Its round trip is proved
  through the independently transcribed declarative binary grammar.  No claim
  identifies canonical output with every permissively valid encoding of the
  same abstract module.  This is a generic module encoder only: no
  `Release.artifactBytes`, selected byte string, or committed release artifact
  follows from it.
-/
import WasmGemmGnaf.Wasm.CoreBackEnd

set_option autoImplicit false

namespace WasmGemmGnaf.Artifact

/-- Emit the canonical amended-Core encoding of a representable public module.
This generic endpoint does not select a release artifact. -/
def emit (module : Wasm.Module) : ByteArray := Wasm.encode module

/-- **SPEC section 11.4, `decode_emit`.**  The public amended Core decoder
returns exactly the module from which an artifact was emitted. -/
theorem decode_emit (module : Wasm.Module) :
    Wasm.decode (emit module) = .ok module :=
  Wasm.encode_decode_roundtrip module

end WasmGemmGnaf.Artifact
