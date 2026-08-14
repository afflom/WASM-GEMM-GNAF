/-
  The coverage-neutral AMD-007 / DEV-007 repair of signed LEB128.

  `BinaryGrammar/Values.lean` remains the byte-identical transcription of the
  pinned source, whose continuation branch accidentally recurses into `BuN`.
  The release semantics identity names the authority-amendment set, so its
  signed relation is the intended recursive `BsN'` below.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Values
import WasmGemmGnaf.Wasm.AuthorityAmendments

set_option autoImplicit false
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Binary

/-- The amended `grammar BsN(N)`: the continuation is signed recursively. -/
inductive BsN' : Nat → Bytes → Int → Prop where
  | pos (N : Nat) (n : Byte) :
      n.val < 2 ^ 6 → n.val < 2 ^ (N - 1) → BsN' N [n] (n.val : Int)
  | neg (N : Nat) (n : Byte) :
      2 ^ 6 ≤ n.val → n.val < 2 ^ 7 →
      (2 : Int) ^ 7 - (2 : Int) ^ (N - 1) ≤ (n.val : Int) →
      BsN' N [n] ((n.val : Int) - (2 : Int) ^ 7)
  | more (N : Nat) (n : Byte) (bs : Bytes) (i : Int) :
      2 ^ 7 ≤ n.val → 7 < N → BsN' (N - 7) bs i →
      BsN' N (n :: bs)
        ((2 : Int) ^ 7 * i + ((n.val : Int) - (2 : Int) ^ 7))

/-- The amended signed-33 relation used by heap and block type indices. -/
def Bs33' (bs : Bytes) (i : Int) : Prop := BsN' 33 bs i

/-! ## Authority selection

The complete binary grammar is one family, selected by this finite authority
revision.  Keeping the selector finite is important: an instance can choose
the byte-identical pinned transcription or the exact adopted amendment set,
but it cannot inject an unrelated relation into the grammar.
-/

/-- The two exact Core binary-grammar authorities carried by this repository. -/
inductive BinaryAuthorityRevision where
  /-- The byte-identical transcription of the pinned Core 3.0 SpecTec tree. -/
  | pinned
  /-- The pinned tree with AMD-007, AMD-008, and AMD-010 applied. -/
  | amended
deriving DecidableEq

/-- An implicit selector threaded through the single declarative binary grammar
hierarchy.  The only global instance is `pinnedBinaryAuthority`, preserving the
existing API; amended consumers pass `amendedBinaryAuthority` explicitly. -/
class BinaryAuthority where
  revision : BinaryAuthorityRevision

/-- The default, byte-identical pinned authority. -/
@[reducible] def pinnedBinaryAuthority : BinaryAuthority :=
  { revision := .pinned }

/-- The exact release authority after AMD-007, AMD-008, and AMD-010. -/
@[reducible] def amendedBinaryAuthority : BinaryAuthority :=
  { revision := .amended }

/-- Existing unqualified grammar uses remain pinned. -/
instance : BinaryAuthority := pinnedBinaryAuthority

/-- The signed-33 leaf selected by the current grammar authority. -/
def Bs33For [authority : BinaryAuthority] (bs : Bytes) (i : Int) : Prop :=
  match authority.revision with
  | .pinned => Bs33 bs i
  | .amended => Bs33' bs i

@[simp] theorem Bs33For_pinned :
    @Bs33For pinnedBinaryAuthority = Bs33 := rfl

@[simp] theorem Bs33For_amended :
    @Bs33For amendedBinaryAuthority = Bs33' := rfl

/-- A two-byte witness on which the pinned and amended continuations visibly
disagree.  The amended signed recursion yields `-129`. -/
theorem BsN'_two_byte_negative :
    BsN' 14 [Byte.ofNat 0xFF, Byte.ofNat 0x7E] (-129) := by
  apply BsN'.more 14 (Byte.ofNat 0xFF) [Byte.ofNat 0x7E] (-2)
  · decide
  · decide
  · apply BsN'.neg
    · decide
    · decide
    · decide

/-- The verbatim pinned recursion sends the same bytes through `BuN` and
therefore derives the unrelated positive value `16255`. -/
theorem BsN_pinned_two_byte_positive :
    BsN 14 [Byte.ofNat 0xFF, Byte.ofNat 0x7E] 16255 := by
  apply BsN.more 14 (Byte.ofNat 0xFF) [Byte.ofNat 0x7E] 126
  · decide
  · decide
  · apply BuN.last <;> decide

/-- The amendment data names the corrected signed relation. -/
theorem signedLebAmendment_target :
    core3SignedLebAuthorityAmendment.patches.flatMap
        AuthorityPatchBody.amendedLeanDeclarations =
      ["WasmGemmGnaf.Wasm.Core.Binary.BsN'",
       "WasmGemmGnaf.Wasm.Core.Decode.decSN'"] := rfl

end WasmGemmGnaf.Wasm.Core.Binary
