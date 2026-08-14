/-
  Wasm/Fault.lean --- a fault sum for the legacy subset machine.

  This declaration joins the legacy subset `DecodeFault` of
  `Wasm/Binary.lean` with the legacy `InstantiationFault` of
  `Wasm/Config.lean`.  It is not the public fault type required by SPEC
  §7.1: public `Wasm.decode` uses `CoreDecodeFault` and the public
  amended-Core machine interface has not been assembled here.

  The concrete model keeps the two failure domains as separate inductives —
  `DecodeFault` in `Wasm/Binary.lean` (malformed bytes) and
  `InstantiationFault` in `Wasm/Config.lean` (allocation and export failures) —
  because they are genuinely different sets of outcomes.  This module joins
  them without either legacy module depending on the other.

  Both injections are proved injective and their images provably disjoint, so a
  decoding failure can never be silently reported as an instantiation failure.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Config

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-- A legacy subset-machine fault: either subset bytes failed to decode or a
subset module failed to instantiate. -/
inductive Fault
  /-- The byte sequence did not decode under the legacy subset codec. -/
  | decoding (fault : DecodeFault)
  /-- The decoded subset module did not instantiate in the legacy machine. -/
  | instantiation (fault : InstantiationFault)
  deriving DecidableEq, Repr, Inhabited

namespace Fault

theorem decoding_injective {a b : DecodeFault}
    (h : Fault.decoding a = Fault.decoding b) : a = b := by
  cases h; rfl

theorem instantiation_injective {a b : InstantiationFault}
    (h : Fault.instantiation a = Fault.instantiation b) : a = b := by
  cases h; rfl

/-- The two failure domains are disjoint: no fault is both. -/
theorem decoding_ne_instantiation (a : DecodeFault) (b : InstantiationFault) :
    Fault.decoding a ≠ Fault.instantiation b := by
  intro h; cases h

/-- Which phase failed. -/
def isDecoding : Fault → Bool
  | .decoding _ => true
  | .instantiation _ => false

@[simp] theorem isDecoding_decoding (a : DecodeFault) :
    (Fault.decoding a).isDecoding = true := rfl

@[simp] theorem isDecoding_instantiation (b : InstantiationFault) :
    (Fault.instantiation b).isDecoding = false := rfl

end Fault

end WasmGemmGnaf.Wasm
