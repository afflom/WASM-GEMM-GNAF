/-
  Wasm/CoreFrontEnd.lean --- the release front end, over `Wasm.Core`.

  ## What this file is

  The public names `Wasm.decode`, `Wasm.DeclarativeBinaryRelation`,
  `Wasm.decode_sound` and `Wasm.decode_complete` used to denote the SUBSET codec
  of `Wasm/Binary.lean` and the subset grammar of `Wasm/Declarative.lean`.  They
  no longer do.  Here they denote the amended WebAssembly Core 3.0 decoder
  `Wasm.Core.decodeA` and grammar `Wasm.Core.Binary.BmoduleA`.  These are the
  single recursively propagated interpretation of the pinned grammar after
  applying the exact authority set AMD-007, AMD-008, AMD-010, and AMD-012 to

      vendor/wasm-spec/specification/wasm-3.0/5.*-binary.*.spectec

  at the pinned commit.  The byte-identical pinned decoder and grammar remain
  explicit Core audit objects; they are not the public release interpretation.
  The subset codec survives, still proved, under
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

  The two theorems below are proved by `Wasm.Core.decode_soundA` and
  `Wasm.Core.decode_completeA`, against `BmoduleA`.  The authority selector is
  finite and explicit, and there is no encoder in that import graph, so the two
  sides remain independently implemented.

  ## What is NOT claimed here

  * Not that `Wasm.Subset.Module` is `Wasm.Module`.  The former is the legacy
    executable subset.  The latter, defined below, is one public carrier for a
    Core AST that the amended declarative binary grammar can actually represent.
    There is no coercion or total bridge between the two.

  The public encoder is deliberately defined in `Wasm/CoreBackEnd.lean`, which
  imports this decoder-only boundary rather than weakening its independence.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Foundation.Bytes
import WasmGemmGnaf.Wasm.Core.Decode

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## The one public module carrier

`Core.Module` is the raw Core abstract-syntax sort.  That sort also contains
terms which the binary grammar cannot synthesize because its `/syn` invariants
and side conditions are not intrinsic to the Lean structure.  SPEC section 7.3
requires an unconditional encoder round trip on `Wasm.Module`; the exact
carrier is therefore the image of the amended declarative grammar.

Only the Core AST and the proposition that some grammar derivation produces it
are retained.  In particular, a decoded module does not retain its source bytes:
the Core format is permissive, and Universal selection must retain winning raw
bytes separately. -/

/-- A representable amended Core 3.0 module.  The proof field is propositionally
irrelevant; equality of public modules is exactly equality of their Core ASTs. -/
structure Module where
  core : Core.Module
  representable : ∃ bs : Core.Binary.Bytes, Core.Binary.BmoduleA bs core

/-- Public module equality is Core AST equality. -/
@[ext]
theorem Module.ext {left right : Module} (h : left.core = right.core) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

instance : DecidableEq Module := fun left right =>
  if h : left.core = right.core then
    isTrue (Module.ext h)
  else
    isFalse (fun h' => h (congrArg Module.core h'))

/-- Printing a public module prints its Core AST and never attempts to print a
grammar proof. -/
instance : Repr Module := ⟨fun m prec => reprPrec m.core prec⟩

/-! ## The decoder -/

/-- Why a decode of the amended Core 3.0 binary format failed. -/
abbrev CoreDecodeFault : Type := Core.DecodeFault

/-- Lift a proof-producing decoder into the public carrier.  Abstracting the
decoder result is proof-engineering as well as factoring: the downstream laws
reduce this small match rather than the complete Core decoder and the large
grammar proof stored in its successful branch. -/
private def liftDecoded (result : Except CoreDecodeFault Core.Module)
    (representable : ∀ m, result = .ok m →
      ∃ bs : Core.Binary.Bytes, Core.Binary.BmoduleA bs m) :
    Except CoreDecodeFault Module :=
  match result with
  | .error fault => .error fault
  | .ok m => .ok ⟨m, representable m rfl⟩

private theorem liftDecoded_map_core (result : Except CoreDecodeFault Core.Module)
    (representable : ∀ m, result = .ok m →
      ∃ bs : Core.Binary.Bytes, Core.Binary.BmoduleA bs m) :
    (liftDecoded result representable).map Module.core = result := by
  cases result <;> rfl

private theorem liftDecoded_complete
    (result : Except CoreDecodeFault Core.Module)
    (representable : ∀ m, result = .ok m →
      ∃ bs : Core.Binary.Bytes, Core.Binary.BmoduleA bs m)
    (module : Module) (h : result = .ok module.core) :
    liftDecoded result representable = .ok module := by
  subst result
  apply congrArg Except.ok
  exact Module.ext rfl

private theorem liftDecoded_error
    (result : Except CoreDecodeFault Core.Module)
    (representable : ∀ m, result = .ok m →
      ∃ bs : Core.Binary.Bytes, Core.Binary.BmoduleA bs m)
    (fault : CoreDecodeFault) (h : result = .error fault) :
    liftDecoded result representable = .error fault := by
  subst result
  rfl

/-- **The release decoder.**  The executable decoder for the complete amended
WebAssembly Core 3.0 binary format required by SPEC section 7.3.  Its four
binary repairs are selected explicitly rather than through the pinned default
instance. -/
def decode (bytes : ByteArray) : Except CoreDecodeFault Module :=
  liftDecoded (Core.decodeA bytes) (fun m h =>
    ⟨Core.ByteArray.toBytes bytes, Core.decode_soundA (m := m) h⟩)

/-- Erasing the proof field recovers the independent Core decoder exactly. -/
theorem map_core_decode (bytes : ByteArray) :
    (decode bytes).map Module.core = Core.decodeA bytes :=
  liftDecoded_map_core _ _

/-- **The declarative binary relation.**  `DeclarativeBinaryRelation bytes m`
holds exactly when the amended Core 3.0 binary grammar derives `bytes` with
synthesized attribute `m`.

Its definition mentions no decoding function, and nothing in the import graph of
`Wasm.Core.Binary.BmoduleA` mentions one either: `Wasm/Core/BinaryGrammar/` is a
transcription of `5.*-binary.*.spectec` and imports only the Core syntax. -/
def DeclarativeBinaryRelation (bytes : ByteArray) (module : Module) : Prop :=
  Core.Binary.BmoduleA (Core.ByteArray.toBytes bytes) module.core

/-! ## SPEC section 7.3 / 15 -/

/-- **SPEC section 15, `Wasm.decode_sound`.**  Everything the executable decoder
accepts is derivable in the amended Core 3.0 binary grammar, and the module it
returns is the one the derivation produces.

Proved by `Wasm.Core.decode_soundA`, against `BmoduleA` and not against an
encoder. -/
theorem decode_sound {bytes : ByteArray} {module : Module}
    (h : decode bytes = .ok module) : DeclarativeBinaryRelation bytes module := by
  apply Core.decode_soundA
  rw [← map_core_decode bytes, h]
  rfl

/-- **SPEC section 15, `Wasm.decode_complete`.**  Everything the amended Core 3.0
binary grammar derives, the executable decoder accepts, returning exactly the
module the derivation produces.

This is the direction a rejecting decoder would fail, and the direction that
matters for the release claim: a decoder that silently rejected a valid module
would SHRINK the set of programs the optimality statement quantifies over.

Proved by `Wasm.Core.decode_completeA`, whose axiom closure is
`[propext, Quot.sound]` -- choice free. -/
theorem decode_complete {bytes : ByteArray} {module : Module}
    (h : DeclarativeBinaryRelation bytes module) : decode bytes = .ok module := by
  unfold decode
  apply liftDecoded_complete
  exact Core.decode_completeA h

/-- The two directions together: `Wasm.decode` and the amended grammar accept
exactly the same byte sequences and agree on the value. -/
theorem decode_iff_declarative {bytes : ByteArray} {module : Module} :
    decode bytes = .ok module ↔ DeclarativeBinaryRelation bytes module :=
  ⟨decode_sound, decode_complete⟩

/-! ## Positive non-vacuity

The closed derivation below shows that the public relation is inhabited. -/

/-- The pinned preamble --- magic and version --- as a `ByteArray`. -/
def preambleBytes : ByteArray :=
  Bytes.pack [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- The underlying amended Core decoder accepts the pinned preamble and returns the
empty Core AST. -/
theorem core_decode_preambleBytes : Core.decodeA preambleBytes = .ok Core.emptyModule := by
  show Core.Decode.decModuleA (Core.ByteArray.toBytes preambleBytes) = _
  have h : Core.ByteArray.toBytes preambleBytes =
      Core.bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00] := by
    simp [Core.ByteArray.toBytes, preambleBytes, Core.bytesOf]
  rw [h]
  rfl

/-- The public empty module, constructed from the preamble's grammar
derivation.  No byte sequence is stored in the value. -/
def emptyModule : Module :=
  ⟨Core.emptyModule,
   ⟨Core.ByteArray.toBytes preambleBytes,
    Core.decode_soundA core_decode_preambleBytes⟩⟩

@[simp] theorem emptyModule_core : emptyModule.core = Core.emptyModule := rfl

instance : Inhabited Module := ⟨emptyModule⟩

/-- `Wasm.decode` accepts the pinned preamble and returns the public empty
module. -/
theorem decode_preambleBytes : decode preambleBytes = .ok emptyModule :=
  decode_complete (Core.decode_soundA core_decode_preambleBytes)

/-- **The relation is not empty.**  It holds of the pinned preamble and the
empty module. -/
theorem declarative_preamble :
    DeclarativeBinaryRelation preambleBytes emptyModule :=
  decode_sound decode_preambleBytes

/-- The underlying Core decoder rejects the empty byte string before parsing a
module: the pinned format requires the magic and version words. -/
theorem core_decode_emptyBytes :
    Core.decodeA (Bytes.pack []) = .error .eof := by
  show Core.Decode.decModuleA (Core.ByteArray.toBytes (Bytes.pack [])) = _
  have h : Core.ByteArray.toBytes (Bytes.pack []) = [] := by
    simp [Core.ByteArray.toBytes]
  rw [h]
  rfl

/-- The public decoder likewise rejects the empty byte string.  Together with
`decode_complete`, this is the computational negative non-vacuity fact without
forcing Lean to normalize the large `Bmodule` constructor in a negated theorem
statement. -/
theorem decode_emptyBytes : decode (Bytes.pack []) = .error .eof := by
  unfold decode liftDecoded
  apply liftDecoded_error
  exact core_decode_emptyBytes

end WasmGemmGnaf.Wasm
