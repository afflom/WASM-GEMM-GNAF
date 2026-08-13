/-
  Wasm/CoreGap.lean --- why the release path cannot be BRIDGED onto `Wasm.Core`,
  and must therefore be REPLACED by it.

  ## What this file is for

  The migration brief for the release path offered two routes:

  > Deleting the old model is preferred over bridging it.  If a bridge is
  > genuinely necessary, it must be a TOTAL semantics-preserving map with a
  > proof, not a coercion.

  This file settles which of the two is available, by proof rather than by
  assertion.  It proves that **no such total map exists**: `Wasm.Module` is not
  a sub-language of `Wasm.Core.Module`, so a bridge cannot be written at all and
  the migration has to be a replacement of the type.

  ## The two obstructions, and why they are structural

  `Wasm/Syntax.lean` spells every index as a `Nat` and every name as a raw
  `List UInt8`.  The pinned Core 3.0 syntax does neither:

  * `2-syntax.values.spectec` fixes `syntax idx = u32`, so
    `Wasm.Core.TypeIdx` is `{ n : Nat // n < 2 ^ 32 }` and **no** Core function
    can carry the type index `2 ^ 32`.
  * `syntax name = char*  -- if |$utf8(char*)| < 2^32` fixes a Core name as a
    list of Unicode scalar values, so the byte strings a `Wasm.Core.Name`
    denotes are exactly the well-formed UTF-8 ones.  `0xFF` is not a UTF-8 byte
    in any position, so **no** Core export can be named `[0xFF]`.

  Both are one-directional: the old model admits modules the pinned syntax
  cannot express.  That is the opposite of the situation a bridge needs.  An
  embedding `Wasm.Module -> Wasm.Core.Module` would have to either fail on those
  modules (so it is partial, not total) or silently change the index or the name
  (so it is not semantics preserving, and every theorem transported along it
  would be about a different module than the one the release path selected).

  ## The gap is REACHABLE, not merely present in the type

  `release_decoder_leaves_core` closes the obvious escape --- "the bad modules
  are unreachable, so a map defined on the decoder's image would do".  They are
  reachable: `Wasm.Subset.decode` really does return `gapIndexModule`, because
  `Wasm/Binary.lean`'s `decULEB` is *unbounded*.  It reads LEB128 groups until a
  byte below `0x80` and multiplies up in `Nat`, with no width test at all,
  whereas the pinned `Bu32` of `5.1-binary.values.spectec` admits at most five
  bytes with the last below `2 ^ 4`.  So the release decoder accepts index
  encodings the pinned grammar rejects, and returns modules the pinned syntax
  cannot hold.

  This is stated about the *index reader*, which is what the witness exercises.
  It is not a claim that every disagreement between the two decoders is of this
  shape.

  ## A third fact the replacement has to plan for

  `core_decode_not_injective_in_bytes` is not an obstruction to the migration but
  a bill it will present: the pinned format is not canonical, so
  `Artifact.eq_emit_of_decode` --- "the only bytes that decode to `m` are
  `emit m`" --- is false of the Core decoder and cannot be carried across.  It is
  stated here so the next step budgets for restating it rather than discovering
  it when a proof stops closing.

  ## What this file does NOT claim

  It does not claim the old model is unsound, nor that `Wasm.Subset.decode` is
  wrong about any byte string both decoders accept.  It claims exactly one thing: the
  function `Wasm.Module -> Wasm.Core.Module` that a bridge would need does not
  exist, so `Wasm.Module` has to go.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Core.Decode

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-! ## 1. The witnesses -/

/-- A module of the release path's syntax whose single function names the type
index `2 ^ 32`.  `Wasm.Func.type` is a `Nat`, so this is a perfectly ordinary
term of `Wasm.Module`. -/
def gapIndexModule : Module :=
  { Module.empty with funcs := [{ type := 2 ^ 32, locals := [], body := .nil }] }

/-- A module of the release path's syntax with one export whose name is the
single byte `0xFF`.  `Wasm.Name` is `List UInt8`, so this too is an ordinary
term. -/
def gapNameModule : Module :=
  { Module.empty with exports := [{ name := [(0xFF : UInt8)], desc := .func 0 }] }

/-! ## 2. The index obstruction -/

/-- No map from the release path's modules to Core modules preserves function
type indices.  The witness is `gapIndexModule`: its index is `2 ^ 32`, and
`Wasm.Core.TypeIdx` is `u32`. -/
theorem no_typeidx_preserving_map :
    ¬ ∃ f : Module → Core.Module,
        ∀ m : Module,
          (f m).funcs.map (fun g => g.typeidx.val) = m.funcs.map Func.type := by
  rintro ⟨f, hf⟩
  have h := hf gapIndexModule
  have hr : gapIndexModule.funcs.map Func.type = [2 ^ 32] := rfl
  rw [hr] at h
  cases hfs : (f gapIndexModule).funcs with
  | nil => rw [hfs] at h; simp at h
  | cons g gs =>
      rw [hfs] at h
      simp only [List.map_cons, List.cons.injEq] at h
      exact absurd h.1 (Nat.ne_of_lt g.typeidx.property)

/-! ## 3. The name obstruction

`$utf8` never emits `0xFF`: the largest byte it can produce is `0xF4`, from the
four-byte form at the top of the scalar range. -/

/-- Every byte of a Core `$utf8` encoding of one scalar value is below `0xF5`;
in particular none of them is `0xFF`. -/
theorem gap_utf8Char_ne_ff {c : Core.UChar} {b : Core.Byte}
    (hb : b ∈ Core.utf8Char c) : b.val ≠ 0xFF := by
  have hc := c.property
  simp only [Core.utf8Char] at hb
  split at hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb; simp only [Core.Byte.ofNat]; omega
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> (simp only [Core.Byte.ofNat]; omega)
    · split at hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> (simp only [Core.Byte.ofNat]; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> (simp only [Core.Byte.ofNat]; omega)

/-- No Core name denotes the one-byte string `0xFF`. -/
theorem gap_utf8_ne_ff (n : Core.Name) :
    (Core.utf8 n.val).map (fun b => b.val) ≠ [0xFF] := by
  intro h
  cases hu : Core.utf8 n.val with
  | nil => rw [hu] at h; simp at h
  | cons b rest =>
      have hmem : b ∈ Core.utf8 n.val := by rw [hu]; exact List.mem_cons_self ..
      have hval : b.val = 0xFF := by
        rw [hu] at h
        simp only [List.map_cons, List.cons.injEq] at h
        exact h.1
      have := List.mem_flatMap.mp hmem
      obtain ⟨c, _, hbc⟩ := this
      exact gap_utf8Char_ne_ff hbc hval

/-- No map from the release path's modules to Core modules preserves export
names as byte strings.  The witness is `gapNameModule`. -/
theorem no_name_preserving_map :
    ¬ ∃ f : Module → Core.Module,
        ∀ m : Module,
          (f m).exports.map (fun e => (Core.utf8 e.name.val).map (fun b => b.val)) =
            m.exports.map (fun e => e.name.map UInt8.toNat) := by
  rintro ⟨f, hf⟩
  have h := hf gapNameModule
  have hr : gapNameModule.exports.map (fun e => e.name.map UInt8.toNat) = [[0xFF]] := rfl
  rw [hr] at h
  cases hfs : (f gapNameModule).exports with
  | nil => rw [hfs] at h; simp at h
  | cons e es =>
      rw [hfs] at h
      simp only [List.map_cons, List.cons.injEq] at h
      exact gap_utf8_ne_ff e.name h.1

/-! ## 4. The gap is reachable through the release decoder -/

/-- **The escape hatch is closed.**  `gapIndexModule` is not a term nobody can
reach: the release decoder returns it, from bytes the release encoder produces.
No Core function carries its type index.  A bridge defined only on the decoder's
image would therefore still have to be partial. -/
theorem release_decoder_leaves_core :
    Subset.decode (Subset.encode gapIndexModule) = .ok gapIndexModule ∧
      ∀ g : Core.Func, g.typeidx.val ≠ 2 ^ 32 :=
  ⟨Subset.encode_decode_roundtrip gapIndexModule, fun g => Nat.ne_of_lt g.typeidx.property⟩

/-! ## 5. What the migration costs on the artifact side

The release path does not only ask its decoder for soundness and completeness.
`Artifact/Emit.lean` also proves `eq_emit_of_decode` --- *every* byte string
that decodes to `m` is `emit m` --- and `Artifact/Baseline.lean` uses it for
`baseline_bytes_unique`, "the baseline artifact names one byte string and not a
class of them".

That property is an artefact of the subset codec, which accepts only its own
canonical output.  The pinned Core 3.0 format is not canonical: `Bu32` admits
non-minimal LEB128 inside the width bound, and `Bcustom` admits a custom section
at every one of the fourteen positions.  So the moment `Wasm.decode` becomes the
Core decoder, `eq_emit_of_decode` becomes false and everything resting on it has
to be restated --- as "`emit` is *a* canonical encoding", not "the only
decodable bytes".  This is that fact as a theorem, so the next migration step
does not discover it by finding a proof that no longer closes. -/

/-- The pinned Core 3.0 binary format is not canonical: two different byte
strings decode to the same module.  The second carries an empty custom section,
which `5.4-binary.modules.spectec`'s `Bcustom` admits and which contributes
nothing to the module. -/
theorem core_decode_not_injective_in_bytes :
    ∃ b c : Core.Binary.Bytes, b ≠ c ∧
      Core.Decode.decModule b = .ok Core.emptyModule ∧
      Core.Decode.decModule c = .ok Core.emptyModule := by
  refine ⟨Core.bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00],
          Core.bytesOf [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,
                        0x00, 0x02, 0x01, 0x41],
          ?_, rfl, rfl⟩
  intro h
  have hl := congrArg List.length h
  simp [Core.bytesOf] at hl

end WasmGemmGnaf.Wasm
