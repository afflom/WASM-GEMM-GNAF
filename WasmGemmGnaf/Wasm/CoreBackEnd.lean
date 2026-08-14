/-
  Wasm/CoreBackEnd.lean --- the release encoder for representable amended
  WebAssembly Core 3.0 modules.

  The decoder-only public front end remains a separate import boundary.  This
  file is the deliberate join point: it combines the independently proved
  amended grammar completeness of the decoder and encoder to obtain the public
  round trip.
-/
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Core.BinaryWellFormed
import WasmGemmGnaf.Wasm.Core.EncodeComplete
import WasmGemmGnaf.Wasm.Core.EncodeSound

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-! ## Public amended Core encoder -/

/-- **The release encoder.**  This is a total, computational function on the
public carrier.  Its result depends only on the underlying Core AST; the
carrier's grammar proof is used only to prove the laws below. -/
def encode (module : Module) : ByteArray := Core.Binary.encodeA module.core

/-- Packing the amended encoder's grammar bytes and reading them back is the
identity. -/
theorem toBytes_encode (module : Module) :
    Core.ByteArray.toBytes (encode module) = Core.Binary.encodeBytesA module.core := by
  unfold encode Core.Binary.encodeA
  exact Core.toBytes_pack _

/-- Construct the public carrier from a Core AST only after the amended
encoder has proved that it can emit that AST.  This is the backend boundary a
verified compiler uses: no source bytes are stored, no decoder is consulted,
and a failed encoder cannot be hidden behind a fallback module. -/
def Module.ofEncodableCore (core : Core.Module)
    (h : Core.Binary.encodableA core = true) : Module :=
  ⟨core, ⟨Core.Binary.encodeBytesA core,
    Core.Binary.encodeA_BmoduleA core h⟩⟩

@[simp] theorem Module.ofEncodableCore_core (core : Core.Module)
    (h : Core.Binary.encodableA core = true) :
    (Module.ofEncodableCore core h).core = core := rfl

/-- The public carrier's Core AST satisfies every intrinsic Core syntax side
condition. -/
theorem Module.core_wf (module : Module) : Core.Module.wf module.core = true := by
  obtain ⟨_, hmodule⟩ := module.representable
  exact Core.Binary.BmoduleA.wf_of hmodule

/-- The amended encoder succeeds on every value of the public carrier. -/
theorem Module.encodable (module : Module) :
    Core.Binary.encodableA module.core = true := by
  obtain ⟨_, hmodule⟩ := module.representable
  exact Core.Binary.BmoduleA_encodableA hmodule

/-- The bytes emitted by `Wasm.encode` derive the amended declarative Core
binary grammar for the module they encode. -/
theorem encode_declarative (module : Module) :
    DeclarativeBinaryRelation (encode module) module := by
  unfold DeclarativeBinaryRelation
  rw [toBytes_encode]
  obtain ⟨_, hmodule⟩ := module.representable
  exact Core.Binary.BmoduleA_encodeA_BmoduleA hmodule

/-- **SPEC section 7.3.**  Decoding the public encoder's output returns exactly
the represented amended Core module. -/
theorem encode_decode_roundtrip (module : Module) :
    decode (encode module) = .ok module :=
  decode_complete (encode_declarative module)

end WasmGemmGnaf.Wasm
