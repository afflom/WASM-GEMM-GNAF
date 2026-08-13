/-
  Wasm/Core/ProfileBinary.lean --- profile admission at the BINARY layer.

  SPEC section 7.2, in one sentence: "disabled forms decode when grammatically
  valid and then fail profile validation".  `Wasm/Core/Profile.lean` proves the
  second half over the abstract syntax; this file joins it to the first half by
  going through the pinned decoder of `Wasm/Core/Decode.lean`, and settles the
  two rejected families that the pinned Core 3.0 ABSTRACT syntax cannot express
  at all.

  Four statements, each about actual bytes:

  * `memory64_decodes_then_is_rejected` --- an `I64` memory section is
    grammatically valid Core 3.0, the decoder accepts it, and no profile admits
    the module it produces.  This is SPEC section 7.2's sentence, verbatim, as a
    theorem.
  * `relaxedSwizzle_decodes_then_is_rejected` --- the same for `0xFD 256`,
    `VSWIZZLOP (I8 X 16) RELAXED_SWIZZLE`.
  * `sharedMemoryLimits_not_decodable` --- the shared-memory limits flag `0x03`
    of the threads proposal has NO production in the pinned `Blimits`, which
    admits `0x00`, `0x01`, `0x04` and `0x05` and nothing else, so the rejection
    of shared memories happens in the grammar rather than in the profile.
  * `componentBinary_not_decodable` --- a component-model binary carries version
    `0x0D 0x00` and layer `0x01 0x00` where a core module carries
    `0x01 0x00 0x00 0x00`, and the decoder rejects it at the preamble.

  The last two are the honest discharge of "shared memories, atomics, threads"
  and "component-model binaries and post-Core-3 proposals" being rejected: they
  are not forms of `Wasm.Core.Module` at all (`Instr.requiredFeature_ne_shared`
  and `…_ne_componentModel` in `Wasm/Core/Profile.lean` prove no construct is
  ever attributed to them), so there is nothing for a syntactic predicate to
  reject and the obligation lands here.

  The statements are on `Decode.decModule` and an explicit `byte*` rather than
  on `decode` and a `ByteArray`, for the reason `Wasm/Core/Decode.lean` gives:
  `ByteArray.toList` does not reduce in the kernel, and `decode` is `decModule`
  composed with that conversion.

  Every declaration in this file is proved.  Nothing is assumed, and no
  declaration here carries a Core 3.0 coverage marker.
-/
import WasmGemmGnaf.Wasm.Core.Decode
import WasmGemmGnaf.Wasm.Core.Profile

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace WasmGemmGnaf.Wasm.Core

open WasmGemmGnaf.Wasm.Core.Binary

/-! ## The module-byte limit

`ResourceLimits.maxModuleBytes` is the one limit of SPEC section 7.2 that is a
property of the ENCODING rather than of the module, so it is enforced here
rather than in `Module.withinLimits`. -/

/-- **The released profile admits these bytes**: they decode under the pinned
Core 3.0 binary grammar, the module they decode to is admitted, and the encoding
is inside the profile's stored module-byte limit. -/
def admitsBytes (P : Profile) (bs : ByteArray) : Bool :=
  decide (bs.size ≤ P.body.limits.maxModuleBytes) &&
  (match decode bs with
   | .ok m => Module.admittedBy P m
   | .error _ => false)

/-- Admitted bytes decode. -/
theorem decode_isOk_of_admitsBytes {P : Profile} {bs : ByteArray}
    (h : admitsBytes P bs = true) : ∃ m : Module, decode bs = .ok m := by
  unfold admitsBytes at h
  simp only [Bool.and_eq_true] at h
  cases hd : decode bs with
  | ok m => exact ⟨m, rfl⟩
  | error e => rw [hd] at h; exact absurd h.2 (by simp)

/-- ... and the module they decode to is admitted. -/
theorem admittedBy_of_admitsBytes {P : Profile} {bs : ByteArray} {m : Module}
    (h : admitsBytes P bs = true) (hd : decode bs = .ok m) :
    Module.AdmittedBy P m := by
  unfold admitsBytes at h
  simp only [Bool.and_eq_true] at h
  rw [hd] at h
  exact h.2

/-! ## `decode, then fail profile validation`

The two rejected families the pinned abstract syntax CAN express, exhibited as
byte sequences the pinned grammar derives. -/

/-- A module whose memory section declares an `I64` memory:

    00 61 73 6D 01 00 00 00   magic, version
    05 03                     memory section, three payload bytes
    01                        one memory
    04 01                     Blimits: flag 0x04 = I64 with no maximum, min 1

`0x04` is the pinned `Blimits/i64-min` production of
`5.2-binary.types.spectec`; it is grammatically valid Core 3.0 and it is
memory64. -/
def memory64Bytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
           0x05, 0x03, 0x01, 0x04, 0x01]

/-- **SPEC section 7.2's sentence as a theorem.**  The memory64 encoding decodes
--- the grammar really does derive it --- and the module it decodes to is
admitted by no profile. -/
theorem memory64_decodes_then_is_rejected :
    ∃ m : Module,
      Decode.decModule memory64Bytes = .ok m ∧
      FeatureFamily.memory64 ∈ Module.requiredFeatures m ∧
      ∀ P : Profile, ¬ Module.AdmittedBy P m := by
  refine ⟨_, rfl, ?_, fun P => ?_⟩
  · decide
  · exact Module.not_admittedBy_of_rejected (f := FeatureFamily.memory64) P _
      (by decide) (by decide)

/-- ... and it really is a derivation of the pinned binary grammar, by
`decode_sound`, so the "decodes" half is a statement about `Bmodule` and not
about this repository's decoder. -/
theorem memory64_Bmodule :
    ∃ m : Module, Bmodule memory64Bytes m := by
  obtain ⟨m, hm⟩ : ∃ m : Module, Decode.decModule memory64Bytes = .ok m := ⟨_, rfl⟩
  exact ⟨m, Decode.decModule_sound _ _ hm⟩

/-- A module whose single function body is `0xFD 256`, i.e.
`VSWIZZLOP (I8 X 16) RELAXED_SWIZZLE`:

    00 61 73 6D 01 00 00 00   magic, version
    01 04 01 60 00 00         type section: one `FUNC eps -> eps`
    03 02 01 00               function section: one function, type 0
    0A 07 01 05 00 FD 80 02 0B  code section: one body, no locals,
                                RELAXED_SWIZZLE then END

`256` has no one-byte LEB128 form, which is why the selector is `0x80 0x02`. -/
def relaxedSwizzleBytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
           0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
           0x03, 0x02, 0x01, 0x00,
           0x0A, 0x07, 0x01, 0x05, 0x00, 0xFD, 0x80, 0x02, 0x0B]

/-- The relaxed SIMD half of the same sentence. -/
theorem relaxedSwizzle_decodes_then_is_rejected :
    ∃ m : Module,
      Decode.decModule relaxedSwizzleBytes = .ok m ∧
      FeatureFamily.relaxedSimd ∈ Module.requiredFeatures m ∧
      ∀ P : Profile, ¬ Module.AdmittedBy P m := by
  refine ⟨_, rfl, ?_, fun P => ?_⟩
  · decide
  · exact Module.not_admittedBy_of_rejected (f := FeatureFamily.relaxedSimd) P _
      (by decide) (by decide)

theorem relaxedSwizzle_Bmodule :
    ∃ m : Module, Bmodule relaxedSwizzleBytes m := by
  obtain ⟨m, hm⟩ : ∃ m : Module,
      Decode.decModule relaxedSwizzleBytes = .ok m := ⟨_, rfl⟩
  exact ⟨m, Decode.decModule_sound _ _ hm⟩

/-! ## The two families the pinned grammar does not have

`Blimits` of `5.2-binary.types.spectec` has exactly four productions --- flags
`0x00`, `0x01`, `0x04`, `0x05` --- and the threads proposal's shared flags
`0x02`/`0x03` are not among them.  The core preamble is `\0asm` followed by
version `0x01 0x00 0x00 0x00`, and a component binary carries `0x0D 0x00 0x01
0x00` there instead.  Neither decodes, so neither reaches profile validation at
all; stating the rejection as a decoder fact is the only honest place to state
it. -/

/-- The same memory section as `memory64Bytes` with the SHARED limits flag
`0x03` (min and max, shared) in place of `0x04`. -/
def sharedMemoryBytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
           0x05, 0x04, 0x01, 0x03, 0x01, 0x01]

/-- **Shared memories are rejected by the pinned grammar.**  `0x03` is not a
`Blimits` flag at the pin, so the bytes have no `Bmodule` derivation and the
decoder returns a fault. -/
theorem sharedMemoryLimits_not_decodable :
    ∃ e : DecodeFault, Decode.decModule sharedMemoryBytes = .error e :=
  ⟨_, rfl⟩

/-- THE CONTROL for the previous theorem: the same memory section with the
pinned `0x01` flag (I32, minimum and maximum) in place of `0x03`.  It decodes,
so `sharedMemoryLimits_not_decodable` fails on the FLAG BYTE and not on the
section shape or size. -/
def boundedMemoryBytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
           0x05, 0x04, 0x01, 0x01, 0x01, 0x01]

theorem boundedMemoryLimits_decodable :
    ∃ m : Module, Decode.decModule boundedMemoryBytes = .ok m := ⟨_, rfl⟩

/-- A component-model binary preamble: `\0asm` then version `0x0D 0x00` and
layer `0x01 0x00`, where a core module carries version `0x01 0x00 0x00 0x00`. -/
def componentBytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00]

/-- **Component-model binaries are rejected at the preamble.** -/
theorem componentBinary_not_decodable :
    ∃ e : DecodeFault, Decode.decModule componentBytes = .error e :=
  ⟨_, rfl⟩

/-- The atomic instructions of the threads proposal live in the `0xFE` prefixed
opcode space, which the pinned `Binstr` does not have. -/
theorem atomicOpcodeSpace_not_decodable :
    ∃ e : DecodeFault, Decode.decInstr 8 (bytesOf [0xFE, 0x00]) = .error e :=
  ⟨_, rfl⟩

/-- THE CONTROL: the `0xFC` prefixed space, which the pin DOES have, decodes at
the same shape --- so the previous theorem is about `0xFE` and not about
prefixed opcodes in general. -/
theorem bulkOpcodeSpace_decodable :
    ∃ i : Instr, Decode.decInstr 8 (bytesOf [0xFC, 0x00]) = .ok (i, []) :=
  ⟨_, rfl⟩

/-! ## Anti-vacuity at the binary layer

`admitsBytes` must accept something, or every theorem above is about the empty
set of byte sequences. -/

/-- The released baseline shape of SPEC section 7.2, encoded:

    00 61 73 6D 01 00 00 00        magic, version
    01 07 01 60 02 7F 7F 01 7F     type section: `FUNC (I32 I32) -> (I32)`
    03 02 01 00                    function section: one function, type 0
    05 03 01 00 01                 memory section: one wasm32 memory, min 1
    07 10 02 06 6D 65 6D 6F 72 79 02 00 04 67 65 6D 6D 00 00
                                   export section: `memory` (mem 0), `gemm` (func 0)
    0A 06 01 04 00 20 00 0B        code section: one body, `LOCAL.GET 0`, END -/
def releaseBaselineBytes : Bytes :=
  bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
           0x01, 0x07, 0x01, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F,
           0x03, 0x02, 0x01, 0x00,
           0x05, 0x03, 0x01, 0x00, 0x01,
           0x07, 0x11, 0x02,
             0x06, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00,
             0x04, 0x67, 0x65, 0x6D, 0x6D, 0x00, 0x00,
           0x0A, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0B]

/-- **The anti-vacuity witness at the binary layer.**  These bytes decode under
the pinned grammar, and every profile admits the module they decode to. -/
theorem releaseBaselineBytes_decodes_and_is_admitted :
    ∃ m : Module,
      Decode.decModule releaseBaselineBytes = .ok m ∧
      ∀ P : Profile, Module.AdmittedBy P m := by
  refine ⟨_, rfl, fun P => ?_⟩
  rw [Module.admittedBy_iff_release]
  decide

end WasmGemmGnaf.Wasm.Core
