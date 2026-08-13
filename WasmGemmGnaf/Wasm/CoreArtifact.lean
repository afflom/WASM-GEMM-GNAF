/-
  Wasm/CoreArtifact.lean --- the released module as PINNED CORE 3.0 BYTES.

  ## What this file is for

  The release path is byte indexed.  `Universal.ProfileValid`, the competitor
  universe, the selection layer and `GlobalOptimal` all quantify over
  `ByteArray`, and every artifact theorem is ultimately a statement about a byte
  string.  Until now nothing on the Core 3.0 side had any bytes at all:
  `Wasm/Core/Profile.lean` builds `Wasm.Core.releaseBaselineModule` as abstract
  syntax and proves it admitted, and `Wasm/Core/ProfileAmendment.lean` proves it
  valid under every profile, but no byte string in this repository was ever
  shown to *be* that module under the pinned decoder.

  This file supplies exactly that missing link, as a checked literal:

      Wasm.decode Wasm.Core.releaseArtifactBytes = .ok Wasm.Core.releaseBaselineModule

  `Wasm.decode` here is the decoder of the complete pinned Core 3.0 binary
  format (`Wasm/CoreFrontEnd.lean`), so the equation above is a fact about the
  pinned grammar and not about any encoder written here --- there is no encoder
  written here.  `releaseArtifactBytes` is 53 hand-written bytes; the decoder
  either accepts them and returns that exact module or it does not, and the
  kernel decides which.

  ## What follows from it

  * `releaseArtifactBytes_declarative` --- through `Wasm.decode_sound`, the
    bytes are DERIVABLE in `Wasm.Core.Binary.Bmodule`, the transcription of
    `5.*-binary.*.spectec`.  So this is a statement about the pinned grammar,
    reached through a theorem that was checked for reflection independence.
  * `releaseArtifactBytes_validUnder` --- the module those bytes denote is valid
    under every lawful profile in the sense `Wasm/Core/ProfileAmendment.lean`
    fixes: well typed in the amended Core 3.0 judgment AND admitted by the
    released profile's own feature matrix, limit table, closed import policy and
    exported ABI.

  ## Anti-vacuity, in both directions

  A byte literal that decoded to *anything* admitted would prove nothing about
  admission, so `releaseArtifactBytes_mutated_not_admitted` takes the same
  literal with ONE byte changed --- `gemm` becomes `gemn` --- shows the pinned
  decoder still accepts it, and shows the released profile then REJECTS the
  module, because the required `gemm` export is gone.  Admission is therefore
  doing work on these bytes rather than passing everything the decoder returns.

  ## What this file does NOT claim

  * Not that these are the bytes the release path SELECTS.  `Release.artifactBytes`
    does not exist, `Artifact.baselineBytes` is the subset codec's output, and
    `Artifact.core_rejects_baselineBytes` in `Artifact/Baseline.lean` proves the
    pinned decoder rejects it.  Which byte string the release path commits to is
    the selection layer's business and is still open.
  * Not that `Wasm.Core.releaseBaselineModule` computes a GEMM.  Its body is
    `local.get 0`.  It is the released ABI SHAPE, and every theorem here is
    about that shape.
  * Not that `Universal.ProfileValid` ranges over these bytes.  It does not:
    that predicate still decodes with `Wasm.Subset.decode`, and moving it is
    blocked on the Core execution layer, not on this file.

  Every declaration in this file is proved.  Nothing is assumed, and no
  declaration here carries a Core 3.0 coverage marker: this file transcribes no
  pinned rule.
-/
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Core.ProfileAmendment

set_option autoImplicit false
set_option maxRecDepth 4000000

namespace WasmGemmGnaf.Wasm.Core

open WasmGemmGnaf.Foundation

/-! ## The byte literal

The pinned Core 3.0 module encoding of `Wasm.Core.releaseBaselineModule`, laid
out section by section.  Nothing here is generated: the bytes are written down
and the decoder is asked what they mean.

```
00 61 73 6D  01 00 00 00        magic, version
01 07  01  60 02 7F 7F 01 7F    type    : one rectype, FUNC (i32 i32) -> (i32)
03 02  01 00                    function: one function, type index 0
05 03  01  00 01                memory  : one wasm32 memory, min 1, no max
07 11  02                       export  : two exports
       06 6D 65 6D 6F 72 79  02 00      "memory" -> mem 0
       04 67 65 6D 6D        00 00      "gemm"   -> func 0
0A 06  01  04  00 20 00 0B      code    : one body, no locals, `local.get 0`
```
-/

/-- **The released Core 3.0 artifact bytes.**  53 bytes of the pinned binary
format. -/
def releaseArtifactBytes : ByteArray :=
  Bytes.pack
    [ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00
    , 0x01, 0x07, 0x01, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F
    , 0x03, 0x02, 0x01, 0x00
    , 0x05, 0x03, 0x01, 0x00, 0x01
    , 0x07, 0x11, 0x02
    , 0x06, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00
    , 0x04, 0x67, 0x65, 0x6D, 0x6D, 0x00, 0x00
    , 0x0A, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0B ]

/-- The literal's length, so a silent truncation cannot pass unnoticed. -/
theorem releaseArtifactBytes_size : releaseArtifactBytes.size = 53 := by
  simp [releaseArtifactBytes]

/-! ## The decode

The only step that is not a computation is turning the `ByteArray` into the
grammar's `Bytes`; after that the kernel runs the pinned decoder. -/

theorem releaseArtifactBytes_toBytes :
    ByteArray.toBytes releaseArtifactBytes =
      bytesOf
        [ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00
        , 0x01, 0x07, 0x01, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F
        , 0x03, 0x02, 0x01, 0x00
        , 0x05, 0x03, 0x01, 0x00, 0x01
        , 0x07, 0x11, 0x02
        , 0x06, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00
        , 0x04, 0x67, 0x65, 0x6D, 0x6D, 0x00, 0x00
        , 0x0A, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0B ] := by
  simp [ByteArray.toBytes, releaseArtifactBytes, bytesOf]

/-- **The link the release path was missing.**  The decoder of the complete
pinned Core 3.0 binary format accepts `releaseArtifactBytes` and returns exactly
`Wasm.Core.releaseBaselineModule` --- the module `Wasm/Core/Profile.lean` proves
the released profile admits. -/
theorem decode_releaseArtifactBytes :
    Wasm.decode releaseArtifactBytes = .ok releaseBaselineModule := by
  show Decode.decModule (ByteArray.toBytes releaseArtifactBytes) = _
  rw [releaseArtifactBytes_toBytes]
  rfl

/-- **The bytes are derivable in the pinned grammar.**  Through
`Wasm.decode_sound`, which `xtask independence` checks is not a statement about
an encoder, `releaseArtifactBytes` is a `Bmodule` derivation of
`releaseBaselineModule` --- a fact about `5.*-binary.*.spectec` at the pinned
commit. -/
theorem releaseArtifactBytes_declarative :
    Wasm.DeclarativeBinaryRelation releaseArtifactBytes releaseBaselineModule :=
  Wasm.decode_sound decode_releaseArtifactBytes

/-! ## Validity under the released profile -/

/-- **The decoded module is valid under every lawful profile**, in the sense
`Wasm/Core/ProfileAmendment.lean` fixes: well typed in the amended Core 3.0
judgment, and admitted by the profile's stored feature matrix, limits, closed
import policy and exported ABI. -/
theorem releaseArtifactBytes_validUnder (P : Wasm.Profile) :
    Module.ValidUnder P releaseBaselineModule :=
  releaseBaselineModule_validUnder P

/-- The two halves of validity, at the bytes: the decoded module is admitted,
and it is a well-typed Core 3.0 module. -/
theorem releaseArtifactBytes_admitted (P : Wasm.Profile) :
    Module.AdmittedBy P releaseBaselineModule :=
  releaseBaselineModule_admitted P

/-- Decode and admission in one statement over the bytes, which is the shape a
profile-validity predicate stated over the pinned decoder would need. -/
theorem releaseArtifactBytes_decode_and_validUnder (P : Wasm.Profile) :
    ∃ m : Module,
      Wasm.decode releaseArtifactBytes = .ok m ∧
        Module.ValidUnder P m ∧ m.imports = [] :=
  ⟨releaseBaselineModule, decode_releaseArtifactBytes,
   releaseBaselineModule_validUnder P, rfl⟩

/-! ## Anti-vacuity: admission is not passing everything the decoder returns

One byte differs --- `0x6D` (`m`) becomes `0x6E` (`n`) in the `gemm` export
name.  The pinned decoder still accepts the result, so this is a live module of
the same format; the released profile rejects it, because SPEC section 7.2's
required `gemm` export is no longer present. -/

/-- The same literal with the final letter of the `gemm` export changed. -/
def mutatedArtifactBytes : ByteArray :=
  Bytes.pack
    [ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00
    , 0x01, 0x07, 0x01, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F
    , 0x03, 0x02, 0x01, 0x00
    , 0x05, 0x03, 0x01, 0x00, 0x01
    , 0x07, 0x11, 0x02
    , 0x06, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00
    , 0x04, 0x67, 0x65, 0x6D, 0x6E, 0x00, 0x00
    , 0x0A, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0B ]

/-- The mutated literal differs from the released one. -/
theorem mutatedArtifactBytes_ne :
    mutatedArtifactBytes.toList ≠ releaseArtifactBytes.toList := by
  simp [mutatedArtifactBytes, releaseArtifactBytes]

theorem mutatedArtifactBytes_toBytes :
    ByteArray.toBytes mutatedArtifactBytes =
      bytesOf
        [ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00
        , 0x01, 0x07, 0x01, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F
        , 0x03, 0x02, 0x01, 0x00
        , 0x05, 0x03, 0x01, 0x00, 0x01
        , 0x07, 0x11, 0x02
        , 0x06, 0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00
        , 0x04, 0x67, 0x65, 0x6D, 0x6E, 0x00, 0x00
        , 0x0A, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0B ] := by
  simp [ByteArray.toBytes, mutatedArtifactBytes, bytesOf]

/-- The module the mutated bytes denote: the released shape with the `gemm`
export renamed. -/
def mutatedArtifactModule : Module :=
  { releaseBaselineModule with
    exports := [ { name := memoryExportName, externidx := .mem idx0 }
               , { name := asciiName [0x67, 0x65, 0x6D, 0x6E],
                   externidx := .func idx0 } ] }

/-- The pinned decoder accepts the mutated bytes too: the rejection below is the
PROFILE's, not the format's. -/
theorem decode_mutatedArtifactBytes :
    Wasm.decode mutatedArtifactBytes = .ok mutatedArtifactModule := by
  show Decode.decModule (ByteArray.toBytes mutatedArtifactBytes) = _
  rw [mutatedArtifactBytes_toBytes]
  rfl

/-- **The released profile rejects the mutated module.**  So
`releaseArtifactBytes_admitted` is not a property of every byte string the
decoder accepts. -/
theorem mutatedArtifactModule_not_admitted (P : Wasm.Profile) :
    ¬ Module.AdmittedBy P mutatedArtifactModule := by
  rw [Module.admittedBy_iff_release]
  decide

/-- ... and therefore the mutated module is not valid under any profile either,
even though it is a perfectly ordinary Core 3.0 module. -/
theorem mutatedArtifactModule_not_validUnder (P : Wasm.Profile) :
    ¬ Module.ValidUnder P mutatedArtifactModule :=
  fun h => mutatedArtifactModule_not_admitted P h.2

end WasmGemmGnaf.Wasm.Core
