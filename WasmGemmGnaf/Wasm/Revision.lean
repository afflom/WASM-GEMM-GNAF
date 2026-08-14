/-
  Wasm/Revision.lean --- the pinned WebAssembly Core revision identity.

  Normative source: SPEC.md section 4 (pinned authority) and section 7.2
  (released portable profile).  The revision is a *checked literal*: the
  commit is written out here and every property of it that the release gate
  needs is proved, never assumed.

  It also carries the identity of the **vendored copy** of that revision:
  `core3VendoredTree` records the path, file count and digest-of-digests of
  `vendor/wasm-spec/`, so `profile_matches_pinned_revision` binds the model to
  content rather than to a commit string alone.  `xtask vendor` recomputes that
  digest from the bytes on disk; see the section comment below for exactly where
  the kernel stops and the tool starts.

  This file also carries the small byte-encoding helpers that the rest of the
  `Wasm` layer needs on top of `Foundation/Bytes.lean` (strings and lists of
  naturals).  They live here because `Revision.lean` is the bottom of the
  `Wasm` import order.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Foundation.Identity

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

/-! ## Encoding helpers

`Foundation/Bytes.lean` supplies prefix-free encoders for `Nat`, `ByteArray`,
pairs, sums, lists and options.  The `Wasm` layer additionally needs `String`
(module, export and rule-identifier names) and `List Nat` (first-order records
whose fields are all counts). -/

namespace Enc

/-- `String` is a structure over its UTF-8 `ByteArray` together with a
proof-irrelevant validity field, so the byte array determines the string. -/
theorem toByteArray_injective : Function.Injective String.toByteArray := by
  intro s t h
  cases s
  cases t
  cases h
  rfl

/-- Prefix-free encoding of a `String`: the length-prefixed UTF-8 bytes. -/
def stringBytes (s : String) : List UInt8 :=
  Bytes.byteArrayBytes s.toByteArray

theorem stringBytes_prefixFree : Bytes.PrefixFree stringBytes :=
  Bytes.byteArrayBytes_prefixFree.comp toByteArray_injective

theorem stringBytes_injective : Function.Injective stringBytes :=
  stringBytes_prefixFree.injective

/-- Prefix-free encoding of a list of naturals: the shape used to encode a
first-order record all of whose fields are counts. -/
def natsBytes (l : List Nat) : List UInt8 :=
  Bytes.listBytes Bytes.natBytes l

theorem natsBytes_prefixFree : Bytes.PrefixFree natsBytes :=
  Bytes.listBytes_prefixFree Bytes.natBytes_prefixFree

theorem natsBytes_injective : Function.Injective natsBytes :=
  natsBytes_prefixFree.injective

/-- Prefix-free encoding of a list of strings. -/
def stringsBytes (l : List String) : List UInt8 :=
  Bytes.listBytes stringBytes l

theorem stringsBytes_prefixFree : Bytes.PrefixFree stringsBytes :=
  Bytes.listBytes_prefixFree stringBytes_prefixFree

/-- The bytes of an ASCII schema-tag name, for `TypeTag.leaf`. -/
def nameBytes (s : String) : List UInt8 :=
  s.toByteArray.toList

theorem nameBytes_injective : Function.Injective nameBytes := by
  intro left right h
  apply toByteArray_injective
  exact Bytes.toList_injective h

end Enc

/-! ## The pinned revision -/

/-- The identity of a pinned upstream source revision.  First-order: no
functions, no proofs (SPEC section 6.2). -/
structure RevisionBody where
  /-- Human-readable authority name, e.g. `WebAssembly Core`. -/
  authority : String
  /-- The pinned branch or working-group designation, e.g. `wg-3.0`. -/
  branch : String
  /-- The full 40-hex-digit commit identifier. -/
  commit : String
  deriving DecidableEq, Repr, Inhabited

namespace RevisionBody

/-- Lowercase hexadecimal digit test on a character code. -/
def isLowerHexDigit (c : Char) : Bool :=
  (48 ≤ c.toNat && c.toNat ≤ 57) || (97 ≤ c.toNat && c.toNat ≤ 102)

/-- A commit identifier is exactly forty lowercase hex digits. -/
def IsCommitDigest (s : String) : Bool :=
  s.toList.length == 40 && s.toList.all isLowerHexDigit

/-- Prefix-free canonical encoding. -/
def bytes (r : RevisionBody) : List UInt8 :=
  Enc.stringBytes r.authority ++
    (Enc.stringBytes r.branch ++ Enc.stringBytes r.commit)

theorem bytes_prefixFree : Bytes.PrefixFree bytes := by
  intro x y r s h
  simp only [bytes, List.append_assoc] at h
  obtain ⟨h1, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  obtain ⟨h3, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  refine ⟨?_, h⟩
  cases x
  cases y
  simp_all

theorem bytes_injective : Function.Injective bytes :=
  bytes_prefixFree.injective

/-- The frozen canonical schema of a pinned revision (SPEC section 6.2). -/
def identitySchema : CanonicalSchema RevisionBody :=
  CanonicalSchema.ofPrefixFree 1 .authority
    (TypeTag.leaf (Enc.nameBytes "wasm.revision.body/1"))
    (TypeTag.leaf_size_pos _)
    bytes bytes_prefixFree

/-- The erased canonical identity of a pinned revision. -/
def identity (r : RevisionBody) : CanonicalObjectId :=
  CanonicalObjectId.ofTyped (Identity identitySchema r)

theorem identity_eq_iff {a b : RevisionBody} :
    identity a = identity b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff identitySchema

end RevisionBody

/-- The pinned WebAssembly Core revision of SPEC section 4: the official
`wg-3.0` source at commit `9d36019973201a19f9c9ebb0f10828b2fe2374aa`. -/
def core3Revision : RevisionBody :=
  { authority := "WebAssembly Core"
    branch := "wg-3.0"
    commit := "9d36019973201a19f9c9ebb0f10828b2fe2374aa" }

/-- The pinned commit, as a standalone literal for the profile body. -/
def core3RevisionCommit : String :=
  "9d36019973201a19f9c9ebb0f10828b2fe2374aa"

theorem core3Revision_commit :
    core3Revision.commit = core3RevisionCommit := rfl

theorem core3Revision_authority :
    core3Revision.authority = "WebAssembly Core" := rfl

theorem core3Revision_branch :
    core3Revision.branch = "wg-3.0" := rfl

/-- The pinned commit really is a forty-digit lowercase hex identifier. -/
theorem core3Revision_commit_isDigest :
    RevisionBody.IsCommitDigest core3Revision.commit = true := by decide

theorem core3RevisionCommit_length :
    core3RevisionCommit.toList.length = 40 := by decide

theorem core3RevisionCommit_utf8_size :
    core3RevisionCommit.toByteArray.size = 40 := by decide

/-- Distinct revisions have distinct canonical identities; identical ones do
not.  This is what makes `profile_matches_pinned_revision` a real binding. -/
theorem core3Revision_identity_eq_iff (r : RevisionBody) :
    RevisionBody.identity r = RevisionBody.identity core3Revision ↔
      r = core3Revision :=
  RevisionBody.identity_eq_iff

/-! ## The vendored copy of the pinned revision

A commit *string* names a revision; it does not name any bytes this repository
can read.  SPEC section 5 requires offline verification to recompute a pin from
CONTENT rather than trust a checksum string, so the pinned revision is also
vendored under `vendor/wasm-spec/` and every vendored file's digest is recorded
in `vendor/wasm-spec/SHA256SUMS`.  `VendoredTreeBody` is the Lean record of that
vendored copy, and `manifestSha256` is the digest **of the digest manifest** ---
a digest of digests over the whole vendored tree.

Two boundaries, stated rather than glossed:

* Lean does not read the tree.  `core3VendoredTree` is a checked literal in the
  sense the rest of this development uses that phrase: `xtask vendor` recomputes
  the manifest digest from the bytes on disk (and rechecks `SHA256SUMS` itself
  against all 374 files) and fails the gate when the literal has drifted.  The
  theorems below stand on the literal; the tool exists so that a literal which
  no longer describes the tree cannot pass.
* Nothing here assumes collision resistance.  `identity` is the structural
  canonical identity of `Foundation/Identity.lean`, whose injectivity is proved
  from prefix-free encoding, not from a hash.  `manifestSha256` is carried as
  *data* that names the vendored bytes for the tool; no proof concludes
  anything from its being a SHA-256. -/

/-- The identity of the vendored copy of a pinned upstream revision.
First-order: no functions, no proofs (SPEC section 6.2). -/
structure VendoredTreeBody where
  /-- Repository-relative path of the vendored tree root. -/
  root : String
  /-- Repository-relative path of the per-file digest manifest. -/
  digestManifest : String
  /-- The commit the tree was vendored at. -/
  commit : String
  /-- How many files the digest manifest lists. -/
  fileCount : Nat
  /-- Lowercase-hex SHA-256 of the digest manifest: a digest of digests over
  the whole vendored tree. -/
  manifestSha256 : String
  deriving DecidableEq, Repr, Inhabited

namespace VendoredTreeBody

/-- A SHA-256 digest is exactly sixty-four lowercase hex digits. -/
def IsSha256Digest (s : String) : Bool :=
  s.toList.length == 64 && s.toList.all RevisionBody.isLowerHexDigit

/-- Prefix-free canonical encoding. -/
def bytes (t : VendoredTreeBody) : List UInt8 :=
  Enc.stringBytes t.root ++
    (Enc.stringBytes t.digestManifest ++
      (Enc.stringBytes t.commit ++
        (Bytes.natBytes t.fileCount ++ Enc.stringBytes t.manifestSha256)))

theorem bytes_prefixFree : Bytes.PrefixFree bytes := by
  intro x y r s h
  simp only [bytes, List.append_assoc] at h
  obtain ⟨h1, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  obtain ⟨h3, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  obtain ⟨h4, h⟩ := Bytes.natBytes_prefixFree _ _ _ _ h
  obtain ⟨h5, h⟩ := Enc.stringBytes_prefixFree _ _ _ _ h
  refine ⟨?_, h⟩
  cases x
  cases y
  simp_all

theorem bytes_injective : Function.Injective bytes :=
  bytes_prefixFree.injective

/-- The frozen canonical schema of a vendored tree (SPEC section 6.2). -/
def identitySchema : CanonicalSchema VendoredTreeBody :=
  CanonicalSchema.ofPrefixFree 1 .authority
    (TypeTag.leaf (Enc.nameBytes "wasm.vendored.tree.body/1"))
    (TypeTag.leaf_size_pos _)
    bytes bytes_prefixFree

/-- The erased canonical identity of a vendored tree. -/
def identity (t : VendoredTreeBody) : CanonicalObjectId :=
  CanonicalObjectId.ofTyped (Identity identitySchema t)

theorem identity_eq_iff {a b : VendoredTreeBody} :
    identity a = identity b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff identitySchema

end VendoredTreeBody

/-- The digest of `vendor/wasm-spec/SHA256SUMS`, which is itself the list of
SHA-256 digests of every one of the 374 vendored files.  `xtask vendor`
recomputes both halves from the bytes on disk and fails if either differs from
what is written here. -/
def core3VendorManifestSha256 : String :=
  "490d6070d2a99026c636b1c9072fa6168ca8bdc94de5c7ea354887bd34795b80"

/--
The digest of `vendor/wasm-spec/BLOBS`, the list of **git blob object ids** of
every vendored file.

This is the stronger of the two bindings and the reason both exist.
`SHA256SUMS` is a file this repository wrote: recomputing it proves the vendored
tree has not changed since we recorded it, not that the tree is the one the
pinned commit names.  A git blob id is `sha1("blob " ++ len ++ "\0" ++ content)`
--- a function of the bytes alone --- and it is exactly the identity commit
`core3RevisionCommit`'s tree lists each file under.  `xtask vendor` recomputes
every one of them offline, with no network and no `git`.

SHA-1 appears here as a CONTENT ADDRESS, never as a security primitive: SPEC
§19 forbids resting a claim on a cryptographic collision assumption, and a
colliding blob would still have to satisfy `SHA256SUMS`.
-/
def core3VendorBlobManifestSha256 : String :=
  "b3136f7fd5839b38f8806d623ef0bcd41698ac1fcf1a4c1c29aa3c36ff384d37"

/--
The vendored copy of the pinned WebAssembly Core revision.

Three parts, 374 files, every one verified against the pinned commit's tree by
its git blob id:

* `specification/wasm-3.0/` — the **35 normative SpecTec sources**.  These are
  where the grammar and typing rule *bodies* live: `5.3-binary.instructions`
  carries the actual opcode bytes (`| 0x00 => UNREACHABLE`), `2.3-validation.
  instructions` the typing rules including stack polymorphism.  The rendered
  `.rst` prose only *references* them, as `$${grammar: ...}` macros.  Vendoring
  the `.rst` alone --- which is what this tree used to hold --- left every rule
  body outside the repository, so no transcription could be checked against
  anything.  An external audit was right to reject that.
* `document/core/{binary,valid,exec,syntax,appendix}/` — the 39 rendered
  normative sources the conformance map cites by label.
* `test/core/` — the **299 official conformance test files**, including the
  `simd`, `gc`, `exceptions`, `bulk-memory`, `multi-memory`, `memory64` and
  `relaxed-simd` suites.
-/
def core3VendoredTree : VendoredTreeBody :=
  { root := "vendor/wasm-spec/"
    digestManifest := "vendor/wasm-spec/SHA256SUMS"
    commit := core3RevisionCommit
    fileCount := 374
    manifestSha256 := core3VendorManifestSha256 }

/-- **The vendored tree and the pinned revision are the same revision.** -/
theorem core3VendoredTree_commit :
    core3VendoredTree.commit = core3Revision.commit := rfl

theorem core3VendoredTree_root :
    core3VendoredTree.root = "vendor/wasm-spec/" := rfl

theorem core3VendoredTree_digestManifest :
    core3VendoredTree.digestManifest = "vendor/wasm-spec/SHA256SUMS" := rfl

theorem core3VendoredTree_fileCount : core3VendoredTree.fileCount = 374 := rfl

theorem core3VendoredTree_manifestSha256 :
    core3VendoredTree.manifestSha256 = core3VendorManifestSha256 := rfl

/-- The recorded digest of digests really is a sixty-four-digit lowercase hex
string, so a truncated or upper-cased literal cannot sit here unnoticed. -/
theorem core3VendorManifestSha256_isDigest :
    VendoredTreeBody.IsSha256Digest core3VendorManifestSha256 = true := by decide

theorem core3VendorManifestSha256_length :
    core3VendorManifestSha256.toList.length = 64 := by decide

/--
Distinct vendored trees have distinct canonical identities.

Changing a byte of a *listed* vendored file changes `SHA256SUMS`, hence its
digest, hence this identity --- which is what makes the binding below a binding
to the vendored CONTENT and not merely to a commit string.

**This sentence used to be written without the word "listed", and as written it
was false.**  An adversarial review demonstrated the consequence live: while
`xtask vendor` walked only the lines of `SHA256SUMS`, 334 files were added to
`vendor/wasm-spec/` and the checker went on reporting "40 files rechecked from
content (0 digest failures)" and passing.  Bytes in an unlisted file changed no
digest anywhere.  The checker now enumerates the directory and requires the two
sets to agree in both directions --- an unlisted file and a listed-but-absent
file are each a finding --- and `M13` plants exactly that fault to keep it doing
so.  With that half in place the sentence holds for the tree as a whole.
-/
theorem core3VendoredTree_identity_eq_iff (t : VendoredTreeBody) :
    VendoredTreeBody.identity t = VendoredTreeBody.identity core3VendoredTree ↔
      t = core3VendoredTree :=
  VendoredTreeBody.identity_eq_iff

end WasmGemmGnaf.Wasm
