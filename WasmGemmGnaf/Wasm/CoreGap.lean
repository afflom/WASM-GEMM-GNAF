/-
  Wasm/CoreGap.lean --- why the release path cannot be BRIDGED onto `Wasm.Core`,
  and must therefore be REPLACED by it.

  ## What this file is for

  The migration brief for the release path offered two routes:

  > Deleting the old model is preferred over bridging it.  If a bridge is
  > genuinely necessary, it must be a TOTAL semantics-preserving map with a
  > proof, not a coercion.

  This file proves that no total map preserves all represented function type
  indices, and no total map preserves all represented export-name bytes.
  Arbitrary total functions `Wasm.Subset.Module → Wasm.Core.Module` plainly
  exist (a constant function is one); what the theorems exclude is the
  index/name-preserving bridge the release migration would need.

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
  bridge preserving those indices and name bytes would have to either fail on
  those modules (so it is partial) or silently change the index or name (so it
  cannot justify transporting the existing semantics).

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
  a constraint on the public backend: the pinned format is not injective in its
  byte representation.  The current `Artifact.decode_emit` states the valid
  one-way round trip — decoding the amended encoder's chosen bytes returns the
  represented public module.  It deliberately makes no converse claim that all
  bytes decoding to that module equal the encoder's output.

  ## What this file does NOT claim

  It does not claim the old model is unsound, nor that `Wasm.Subset.decode` is
  wrong about any byte string both decoders accept.  It claims exactly that the
  intended total index/name-preserving bridge does not exist.  It does not deny
  arbitrary total functions between the two carrier types.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Core.Decode

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-! ## 1. The witnesses -/

/-- A module of the release path's syntax whose single function names the type
index `2 ^ 32`.  `Wasm.Func.type` is a `Nat`, so this is a perfectly ordinary
term of `Wasm.Subset.Module`. -/
def gapIndexModule : Subset.Module :=
  { Subset.Module.empty with funcs := [{ type := 2 ^ 32, locals := [], body := .nil }] }

/-- A module of the release path's syntax with one export whose name is the
single byte `0xFF`.  `Wasm.Name` is `List UInt8`, so this too is an ordinary
term. -/
def gapNameModule : Subset.Module :=
  { Subset.Module.empty with exports := [{ name := [(0xFF : UInt8)], desc := .func 0 }] }

/-! ## 2. The index obstruction -/

/-- No map from the release path's modules to Core modules preserves function
type indices.  The witness is `gapIndexModule`: its index is `2 ^ 32`, and
`Wasm.Core.TypeIdx` is `u32`. -/
theorem no_typeidx_preserving_map :
    ¬ ∃ f : Subset.Module → Core.Module,
        ∀ m : Subset.Module,
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
    ¬ ∃ f : Subset.Module → Core.Module,
        ∀ m : Subset.Module,
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

/-- `gapIndexModule` is not a term nobody can reach: the subset decoder returns
it from bytes the subset encoder produces.  No Core function carries its type
index, so even on this decoder image no total bridge can preserve every function
type index. -/
theorem release_decoder_leaves_core :
    Subset.decode (Subset.encode gapIndexModule) = .ok gapIndexModule ∧
      ∀ g : Core.Func, g.typeidx.val ≠ 2 ^ 32 :=
  ⟨Subset.encode_decode_roundtrip gapIndexModule, fun g => Nat.ne_of_lt g.typeidx.property⟩

/-! ## 5. Non-injectivity of Core bytes

The public amended Core backend supplies an encoder and proves the exact
round trip `Wasm.decode (Wasm.encode m) = .ok m` for every representable public
module.  That is compatible with the pinned Core 3.0 format being
non-injective: `Bu32` admits non-minimal LEB128 inside the width bound, and
`Bcustom` admits a custom section at every one of the fourteen positions.
The encoder therefore chooses a canonical encoding, while the decoder may
accept other byte strings denoting the same module.  The theorem below records
that distinction and supports no byte-uniqueness or release-selection claim. -/

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
