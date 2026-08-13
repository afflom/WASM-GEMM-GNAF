import WasmGemmGnaf.Atlas.Seal

set_option autoImplicit false

/-!
# Atlas: the seal verifier reconstructs every retained preimage (SPEC §12.1, §15)

SPEC §15 requires `Atlas.seal_verifier_reconstructs_every_preimage`.  SPEC states
no fenced theorem for it; the governing text is SPEC §12.1

> The deterministic checkers define `canonicalSealCheckResultId` by storing the
> complete checker input, result, and retained preimages in canonical form.

together with SPEC §20.2 item 10, "the Atlas seal reconstructs from retained
canonical objects", and the `retentionComplete` field of `Atlas.SealCertificate`.

## What is proved here, and what a "verifier" is allowed to be given

The one way to make this name vacuous is to hand the verifier the object and let
it check that the object hashes to the recorded identity.  That is a consistency
check on the *caller*, not a reconstruction by the *seal*.  So the verifier
defined here is a function

  `Atlas.sealVerifierPreimages : Atlas.SealIdentity → Option (List PreimageEntry)`

whose only input is the seal identity — one `ObjectId (SealCore × SealCertificateBody)`.
It receives no state, no object graph, no preimage and no proof.  It is a total
executable parser: it opens the seal identity into the certificate body, reads
the *recorded* `retentionCheckResultId` out of that body, opens that identity
into the checker record, and returns the record's retained preimages.

`Atlas.seal_verifier_reconstructs_every_preimage` then says that what comes back
is exactly the retained preimage list of the sealed state, and that every
identity the seal's own retention root names is answered with the exact bytes
recorded for it.

## Why reconstruction is decoding, stated honestly

Under SPEC §6.2 a canonical identity *carries* its canonical body bytes
(`CanonicalObjectId.canonicalBodyBytes`); SPEC §6.2 says so on purpose — "a
SHA-256 digest MAY index an object, but equality and proof reconstruction SHALL
compare the canonical body.  No proof may assume cryptographic collision
resistance."  So opening an identity is decoding, not inverting a hash, and this
file claims nothing about digests.  What it adds over the schemas' *injectivity*
is effectiveness: injectivity says a mathematician could in principle tell two
bodies apart, and gives no way to produce one.  The readers below are total
functions that produce it, and `…_inverts` proves each one is a left inverse of
the canonical encoder it decodes.  That is the difference between "the seal
determines the preimages" and "a verifier can reconstruct them".

## Scope: this is NOT coverage, of any kind

Everything reconstructed here is drawn from `state.retainedObjects.graph.preimages`
— a finite list that the sealed state itself records.  No statement in this file
quantifies over `ByteArray`, over profile-valid modules, over competitors, or
over anything not already written down in the seal.  A seal that retains three
objects satisfies every theorem below, exactly as a seal that retains a million
does.  In particular nothing here contradicts, weakens or routes around
`Atlas.universalCoverCompleteCheck_scope_blind` (`Atlas/CoverageScope.lean`):
that lemma is about `universalCoverCompleteCheck`, which appears nowhere in this
file, and `Atlas.seal_implies_universal_coverage` remains absent and
underivable.  Reconstructing what a seal records is not evidence that the seal
records enough.
-/

namespace WasmGemmGnaf.Atlas

open WasmGemmGnaf.Foundation

/-! ## A byte-list reader algebra

A `Reader α` consumes a prefix of a byte list and returns the value together
with the unconsumed remainder.  `Inverts p enc` is the correctness statement
that makes readers composable: `p` recovers `a` from `enc a ++ rest` and hands
back exactly `rest`.  This is the effective counterpart of `Bytes.PrefixFree`,
which only says that such an `a` and `rest` are *determined*. -/

/-- A parser over canonical byte lists. -/
abbrev Reader (α : Type) := List UInt8 → Option (α × List UInt8)

/-- `p` decodes everything `enc` encodes, and stops exactly where `enc` stops. -/
def Inverts {α : Type} (p : Reader α) (enc : α → List UInt8) : Prop :=
  ∀ (a : α) (rest : List UInt8), p (enc a ++ rest) = some (a, rest)

/-- Read a pair by reading its two components in order. -/
def pairR {α β : Type} (p : Reader α) (q : Reader β) : Reader (α × β) := fun l =>
  match p l with
  | none => none
  | some (a, l') =>
    match q l' with
    | none => none
    | some (b, l'') => some ((a, b), l'')

theorem pairR_inverts {α β : Type} {p : Reader α} {q : Reader β}
    {f : α → List UInt8} {g : β → List UInt8}
    (hp : Inverts p f) (hq : Inverts q g) :
    Inverts (pairR p q) (Bytes.pairBytes f g) := by
  intro a rest
  obtain ⟨x, y⟩ := a
  simp only [Bytes.pairBytes, List.append_assoc, pairR, hp x (g y ++ rest), hq y rest]

/-- Post-process a reader's value. -/
def mapR {α β : Type} (f : α → β) (p : Reader α) : Reader β := fun l =>
  match p l with
  | none => none
  | some (a, l') => some (f a, l')

/-- Transport `Inverts` along a retraction: `g` flattens `β` into the shape `p`
reads, `f` rebuilds it, and `enc₂` is `enc₁` on the flattening. -/
theorem mapR_inverts {α β : Type} {p : Reader α} {enc₁ : α → List UInt8}
    {f : α → β} {enc₂ : β → List UInt8}
    (hp : Inverts p enc₁) (g : β → α)
    (hg : ∀ b, f (g b) = b) (henc : ∀ b, enc₂ b = enc₁ (g b)) :
    Inverts (mapR f p) enc₂ := by
  intro b rest
  rw [henc b]
  simp only [mapR, hp (g b) rest, hg b]

/-- Read a natural number in `Bytes.natBytes` form: little-endian base 128 with
the high bit set on every byte but the last. -/
def natR : Reader Nat
  | [] => none
  | b :: rest =>
      if b.toNat < 128 then some (b.toNat, rest)
      else
        match natR rest with
        | none => none
        | some (m, rest') => some (b.toNat - 128 + 128 * m, rest')

theorem natR_inverts : Inverts natR Bytes.natBytes := by
  have hsize : UInt8.size = 256 := rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rest
    by_cases h : n < 128
    · have hn : (UInt8.ofNat n).toNat = n := UInt8.toNat_ofNat_of_lt' (by omega)
      rw [Bytes.natBytes_lt h]
      simp only [List.singleton_append, natR, hn, if_pos h]
    · have hn : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 :=
        UInt8.toNat_ofNat_of_lt' (by omega)
      have hrec := ih (n / 128) (by omega) rest
      have harith : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
      rw [Bytes.natBytes_ge h]
      simp only [List.cons_append, natR, hn, if_neg (by omega : ¬ n % 128 + 128 < 128),
        hrec, harith]

/-- Read exactly `n` raw bytes. -/
def takeR (n : Nat) : Reader (List UInt8) := fun l =>
  if n ≤ l.length then some (l.take n, l.drop n) else none

theorem takeR_inverts (l rest : List UInt8) :
    takeR l.length (l ++ rest) = some (l, rest) := by
  simp only [takeR, List.length_append, Nat.le_add_right, if_pos, List.take_left,
    List.drop_left]

/-- Read a length-prefixed raw byte string (`Bytes.stringBytes`). -/
def stringR : Reader (List UInt8) := fun l =>
  match natR l with
  | none => none
  | some (n, l') => takeR n l'

theorem stringR_inverts : Inverts stringR Bytes.stringBytes := by
  intro l rest
  simp only [Bytes.stringBytes, List.append_assoc, stringR,
    natR_inverts l.length (l ++ rest), takeR_inverts l rest]

/-- Read a length-prefixed `ByteArray` (`Bytes.byteArrayBytes`). -/
def byteArrayR : Reader ByteArray := mapR Bytes.pack stringR

theorem byteArrayR_inverts : Inverts byteArrayR Bytes.byteArrayBytes :=
  mapR_inverts stringR_inverts ByteArray.toList
    (fun b => Bytes.pack_toList b) (fun _ => rfl)

/-- Read a boolean (`Bytes.boolBytes`). -/
def boolR : Reader Bool
  | [] => none
  | b :: rest =>
      if b.toNat = 0 then some (false, rest)
      else if b.toNat = 1 then some (true, rest)
      else none

theorem boolR_inverts : Inverts boolR Bytes.boolBytes := by
  intro b rest
  cases b <;> rfl

/-- The inverse of `CanonicalDomainTag.index`. -/
def domainOfIndex : Nat → Option CanonicalDomainTag
  | 0 => some .wasmProfile
  | 1 => some .gemmProblem
  | 2 => some .costObjective
  | 3 => some .atlasState
  | 4 => some .atlasSealCheck
  | 5 => some .delta
  | 6 => some .request
  | 7 => some .queryResult
  | 8 => some .manifest
  | 9 => some .authority
  | 10 => some .artifact
  | 11 => some .generic
  | _ => none

/-- Read a canonical domain tag (`CanonicalDomainTag.bytes`). -/
def domainR : Reader CanonicalDomainTag
  | [] => none
  | b :: rest =>
      match domainOfIndex b.toNat with
      | none => none
      | some d => some (d, rest)

theorem domainR_inverts : Inverts domainR CanonicalDomainTag.bytes := by
  intro d rest
  cases d <;> rfl

/-- Read a type-erased canonical identity (`CanonicalObjectId.bytes`). -/
def canonicalIdR : Reader CanonicalObjectId := fun l =>
  match natR l with
  | none => none
  | some (v, l₁) =>
    match domainR l₁ with
    | none => none
    | some (d, l₂) =>
      match byteArrayR l₂ with
      | none => none
      | some (tag, l₃) =>
        match byteArrayR l₃ with
        | none => none
        | some (body, l₄) => some (⟨v, d, tag, body⟩, l₄)

theorem canonicalIdR_inverts : Inverts canonicalIdR CanonicalObjectId.bytes := by
  intro id rest
  obtain ⟨v, d, tag, body⟩ := id
  simp only [CanonicalObjectId.bytes, List.append_assoc, canonicalIdR,
    natR_inverts v (CanonicalDomainTag.bytes d ++
      (Bytes.byteArrayBytes tag ++ (Bytes.byteArrayBytes body ++ rest))),
    domainR_inverts d (Bytes.byteArrayBytes tag ++ (Bytes.byteArrayBytes body ++ rest)),
    byteArrayR_inverts tag (Bytes.byteArrayBytes body ++ rest),
    byteArrayR_inverts body rest]

/-- Retype an erased identity.  This is the inverse of
`CanonicalObjectId.ofTyped` on the nose: both are field copies. -/
def ofErased {α : Type} (id : CanonicalObjectId) : ObjectId α where
  schemaVersion := id.schemaVersion
  domain := id.domain
  typeTag := id.typeTag
  canonicalBodyBytes := id.canonicalBodyBytes

/-- Read a typed identity (`Atlas.objectIdBytes`). -/
def typedIdR (α : Type) : Reader (ObjectId α) := mapR ofErased canonicalIdR

theorem typedIdR_inverts (α : Type) :
    Inverts (typedIdR α) (objectIdBytes (α := α)) :=
  mapR_inverts canonicalIdR_inverts CanonicalObjectId.ofTyped
    (fun i => by cases i; rfl) (fun _ => rfl)

/-- Read exactly `n` consecutive values (`Bytes.concatBytes`). -/
def countR {α : Type} (p : Reader α) : Nat → Reader (List α)
  | 0 => fun l => some ([], l)
  | n + 1 => fun l =>
    match p l with
    | none => none
    | some (a, l') =>
      match countR p n l' with
      | none => none
      | some (as, l'') => some (a :: as, l'')

theorem countR_inverts {α : Type} {p : Reader α} {f : α → List UInt8}
    (hp : Inverts p f) :
    ∀ (xs : List α) (rest : List UInt8),
      countR p xs.length (Bytes.concatBytes f xs ++ rest) = some (xs, rest) := by
  intro xs
  induction xs with
  | nil => intro rest; rfl
  | cons x xs ih =>
    intro rest
    simp only [Bytes.concatBytes, List.append_assoc, countR,
      hp x (Bytes.concatBytes f xs ++ rest), ih rest]

/-- Read a length-prefixed list (`Bytes.listBytes`). -/
def listR {α : Type} (p : Reader α) : Reader (List α) := fun l =>
  match natR l with
  | none => none
  | some (n, l') => countR p n l'

theorem listR_inverts {α : Type} {p : Reader α} {f : α → List UInt8}
    (hp : Inverts p f) : Inverts (listR p) (Bytes.listBytes f) := by
  intro xs rest
  simp only [Bytes.listBytes, List.append_assoc, listR,
    natR_inverts xs.length (Bytes.concatBytes f xs ++ rest), countR_inverts hp xs rest]

/-- Read a whole byte list, demanding that the reader consume all of it. -/
def runR {α : Type} (p : Reader α) (l : List UInt8) : Option α :=
  match p l with
  | some (a, []) => some a
  | _ => none

theorem runR_encode {α : Type} {p : Reader α} {enc : α → List UInt8}
    (hp : Inverts p enc) (a : α) : runR p (enc a) = some a := by
  have h := hp a []
  rw [List.append_nil] at h
  simp only [runR, h]

/-! ## Readers for the Atlas canonical bodies (SPEC §12.1)

Each reader below is paired with the exact encoder of `Atlas/State.lean` or
`Atlas/Certificate.lean` that it inverts. -/

/-- Read a retained preimage entry. -/
def preimageEntryR : Reader PreimageEntry :=
  mapR (fun p => ⟨p.1, p.2⟩) (pairR canonicalIdR byteArrayR)

theorem preimageEntryR_inverts : Inverts preimageEntryR PreimageEntry.bytes :=
  mapR_inverts (pairR_inverts canonicalIdR_inverts byteArrayR_inverts)
    PreimageEntry.toTuple (fun e => by cases e; rfl) (fun _ => rfl)

def closureRootR : Reader ClosureRoot := mapR ClosureRoot.mk (listR canonicalIdR)

theorem closureRootR_inverts : Inverts closureRootR ClosureRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) ClosureRoot.factIds
    (fun r => by cases r; rfl) (fun _ => rfl)

def attentionRootR : Reader AttentionRoot := mapR AttentionRoot.mk (listR byteArrayR)

theorem attentionRootR_inverts : Inverts attentionRootR AttentionRoot.bytes :=
  mapR_inverts (listR_inverts byteArrayR_inverts) AttentionRoot.signatures
    (fun r => by cases r; rfl) (fun _ => rfl)

def dependencyRootR : Reader DependencyRoot :=
  mapR DependencyRoot.mk (listR canonicalIdR)

theorem dependencyRootR_inverts : Inverts dependencyRootR DependencyRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) DependencyRoot.edgeIds
    (fun r => by cases r; rfl) (fun _ => rfl)

def partitionCoverRootR : Reader PartitionCoverRoot :=
  mapR PartitionCoverRoot.mk (listR canonicalIdR)

theorem partitionCoverRootR_inverts :
    Inverts partitionCoverRootR PartitionCoverRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) PartitionCoverRoot.partitionIds
    (fun r => by cases r; rfl) (fun _ => rfl)

def envelopeRootR : Reader EnvelopeRoot := mapR EnvelopeRoot.mk (listR canonicalIdR)

theorem envelopeRootR_inverts : Inverts envelopeRootR EnvelopeRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) EnvelopeRoot.regionIds
    (fun r => by cases r; rfl) (fun _ => rfl)

def certificateRootR : Reader CertificateRoot :=
  mapR CertificateRoot.mk (listR canonicalIdR)

theorem certificateRootR_inverts : Inverts certificateRootR CertificateRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) CertificateRoot.certificateIds
    (fun r => by cases r; rfl) (fun _ => rfl)

def retentionRootR : Reader RetentionRoot := mapR RetentionRoot.mk (listR canonicalIdR)

theorem retentionRootR_inverts : Inverts retentionRootR RetentionRoot.bytes :=
  mapR_inverts (listR_inverts canonicalIdR_inverts) RetentionRoot.retainedIds
    (fun r => by cases r; rfl) (fun _ => rfl)

/-- Read a seal check tag. -/
def sealCheckTagOfIndex : Nat → Option SealCheckTag
  | 0 => some .closureLeast
  | 1 => some .attentionComplete
  | 2 => some .dependenciesComplete
  | 3 => some .universalCoverComplete
  | 4 => some .envelopeExact
  | 5 => some .certificatesSound
  | 6 => some .retentionComplete
  | _ => none

def sealCheckTagR : Reader SealCheckTag
  | [] => none
  | b :: rest =>
      match sealCheckTagOfIndex b.toNat with
      | none => none
      | some t => some (t, rest)

theorem sealCheckTagR_inverts : Inverts sealCheckTagR SealCheckTag.bytes := by
  intro t rest
  cases t <;> rfl

/-! ### The checker record (SPEC §12.1) -/

/-- Rebuild a checker record from the flat tuple its encoder is defined over. -/
def sealCheckResultBodyOfTuple :
    Nat × SealCheckTag × CanonicalObjectId × CanonicalObjectId × ByteArray ×
      ByteArray × List PreimageEntry × Bool → SealCheckResultBody
  | (version, tag, stateId, coreId, stateBodyBytes, coreBytes, retainedPreimages,
     outcome) =>
    { version, tag, stateId, coreId, stateBodyBytes, coreBytes, retainedPreimages,
      outcome }

/-- Read a complete checker record (`Atlas.SealCheckResultBody`). -/
def sealCheckResultBodyR : Reader SealCheckResultBody :=
  mapR sealCheckResultBodyOfTuple
    (pairR natR
     (pairR sealCheckTagR
      (pairR canonicalIdR
       (pairR canonicalIdR
        (pairR byteArrayR
         (pairR byteArrayR
          (pairR (listR preimageEntryR) boolR)))))))

theorem sealCheckResultBodyR_inverts :
    Inverts sealCheckResultBodyR SealCheckResultBody.bytes :=
  mapR_inverts
    (pairR_inverts natR_inverts
     (pairR_inverts sealCheckTagR_inverts
      (pairR_inverts canonicalIdR_inverts
       (pairR_inverts canonicalIdR_inverts
        (pairR_inverts byteArrayR_inverts
         (pairR_inverts byteArrayR_inverts
          (pairR_inverts (listR_inverts preimageEntryR_inverts) boolR_inverts)))))))
    SealCheckResultBody.toTuple (fun b => by cases b; rfl) (fun _ => rfl)

/-! ### The seal core (SPEC §12.1) -/

/-- Rebuild a seal core from the flat tuple its encoder is defined over. -/
def sealCoreOfTuple :
    CanonicalObjectId × CanonicalObjectId × CanonicalObjectId × CanonicalObjectId ×
      ClosureRoot × AttentionRoot × DependencyRoot × PartitionCoverRoot ×
      EnvelopeRoot × CertificateRoot × RetentionRoot × Nat → SealCore
  | (stateId, profileId, problemId, objectiveId, closureRoot, attentionRoot,
     dependencyRoot, partitionCoverRoot, envelopeRoot, certificateRoot,
     retentionRoot, baselineScore) =>
    { stateId, profileId, problemId, objectiveId, closureRoot, attentionRoot,
      dependencyRoot, partitionCoverRoot, envelopeRoot, certificateRoot,
      retentionRoot, baselineScore }

/-- Read a complete seal core (`Atlas.SealCore`). -/
def sealCoreR : Reader SealCore :=
  mapR sealCoreOfTuple
    (pairR canonicalIdR
     (pairR canonicalIdR
      (pairR canonicalIdR
       (pairR canonicalIdR
        (pairR closureRootR
         (pairR attentionRootR
          (pairR dependencyRootR
           (pairR partitionCoverRootR
            (pairR envelopeRootR
             (pairR certificateRootR
              (pairR retentionRootR natR)))))))))))

theorem sealCoreR_inverts : Inverts sealCoreR SealCore.bytes :=
  mapR_inverts
    (pairR_inverts canonicalIdR_inverts
     (pairR_inverts canonicalIdR_inverts
      (pairR_inverts canonicalIdR_inverts
       (pairR_inverts canonicalIdR_inverts
        (pairR_inverts closureRootR_inverts
         (pairR_inverts attentionRootR_inverts
          (pairR_inverts dependencyRootR_inverts
           (pairR_inverts partitionCoverRootR_inverts
            (pairR_inverts envelopeRootR_inverts
             (pairR_inverts certificateRootR_inverts
              (pairR_inverts retentionRootR_inverts natR_inverts)))))))))))
    SealCore.toTuple (fun c => by cases c; rfl) (fun _ => rfl)

/-! ### The seal certificate body (SPEC §12.1) -/

/-- Rebuild a certificate body from the flat tuple its encoder is defined
over. -/
def sealCertificateBodyOfTuple :
    Nat × SealCoreIdentity × CanonicalObjectId × CanonicalObjectId ×
      CanonicalObjectId × CanonicalObjectId × ClosureRoot × AttentionRoot ×
      DependencyRoot × PartitionCoverRoot × EnvelopeRoot × CertificateRoot ×
      RetentionRoot × CanonicalObjectId × CanonicalObjectId × CanonicalObjectId ×
      CanonicalObjectId × CanonicalObjectId × CanonicalObjectId ×
      CanonicalObjectId → SealCertificateBody
  | (version, coreId, stateId, profileId, problemId, objectiveId, closureRoot,
     attentionRoot, dependencyRoot, partitionCoverRoot, envelopeRoot,
     certificateRoot, retentionRoot, closureCheckResultId, attentionCheckResultId,
     dependencyCheckResultId, partitionCheckResultId, envelopeCheckResultId,
     certificateStoreCheckResultId, retentionCheckResultId) =>
    { version, coreId, stateId, profileId, problemId, objectiveId, closureRoot,
      attentionRoot, dependencyRoot, partitionCoverRoot, envelopeRoot,
      certificateRoot, retentionRoot, closureCheckResultId, attentionCheckResultId,
      dependencyCheckResultId, partitionCheckResultId, envelopeCheckResultId,
      certificateStoreCheckResultId, retentionCheckResultId }

/-- Read a complete seal certificate body (`Atlas.SealCertificateBody`). -/
def sealCertificateBodyR : Reader SealCertificateBody :=
  mapR sealCertificateBodyOfTuple
    (pairR natR
     (pairR (typedIdR SealCore)
      (pairR canonicalIdR
       (pairR canonicalIdR
        (pairR canonicalIdR
         (pairR canonicalIdR
          (pairR closureRootR
           (pairR attentionRootR
            (pairR dependencyRootR
             (pairR partitionCoverRootR
              (pairR envelopeRootR
               (pairR certificateRootR
                (pairR retentionRootR
                 (pairR canonicalIdR
                  (pairR canonicalIdR
                   (pairR canonicalIdR
                    (pairR canonicalIdR
                     (pairR canonicalIdR
                      (pairR canonicalIdR canonicalIdR)))))))))))))))))))

theorem sealCertificateBodyR_inverts :
    Inverts sealCertificateBodyR SealCertificateBody.bytes :=
  mapR_inverts
    (pairR_inverts natR_inverts
     (pairR_inverts (typedIdR_inverts SealCore)
      (pairR_inverts canonicalIdR_inverts
       (pairR_inverts canonicalIdR_inverts
        (pairR_inverts canonicalIdR_inverts
         (pairR_inverts canonicalIdR_inverts
          (pairR_inverts closureRootR_inverts
           (pairR_inverts attentionRootR_inverts
            (pairR_inverts dependencyRootR_inverts
             (pairR_inverts partitionCoverRootR_inverts
              (pairR_inverts envelopeRootR_inverts
               (pairR_inverts certificateRootR_inverts
                (pairR_inverts retentionRootR_inverts
                 (pairR_inverts canonicalIdR_inverts
                  (pairR_inverts canonicalIdR_inverts
                   (pairR_inverts canonicalIdR_inverts
                    (pairR_inverts canonicalIdR_inverts
                     (pairR_inverts canonicalIdR_inverts
                      (pairR_inverts canonicalIdR_inverts
                        canonicalIdR_inverts)))))))))))))))))))
    SealCertificateBody.toTuple (fun b => by cases b; rfl) (fun _ => rfl)

/-! ## Opening a recorded identity

An identity carries the canonical bytes of the body it names (SPEC §6.2), so
opening it is running the matching reader over those bytes and demanding that
the reader consume all of them. -/

/-- Reconstruct the checker record a recorded checker-result identity names. -/
def sealCheckRecordOfId (id : CanonicalObjectId) : Option SealCheckResultBody :=
  runR sealCheckResultBodyR id.canonicalBodyBytes.toList

/-- **The recorded checker-result identity opens to the checker's own record.**
Not to something that merely hashes the same: to the exact record
`canonicalSealCheckResultBody` stored, complete with its retained preimages. -/
theorem sealCheckRecordOfId_canonical (state : UnsealedState) (core : SealCore)
    (tag : SealCheckTag) :
    sealCheckRecordOfId (canonicalSealCheckResultId state core tag) =
      some (canonicalSealCheckResultBody state core tag) := by
  show runR sealCheckResultBodyR
      (Bytes.pack (SealCheckResultBody.bytes
        (canonicalSealCheckResultBody state core tag))).toList = _
  rw [Bytes.toList_pack]
  exact runR_encode sealCheckResultBodyR_inverts _

/-- Reconstruct the certificate body a seal identity names.  The seal identity
frames the core's canonical bytes and the certificate body's canonical bytes
(`Foundation.CanonicalSchema.product`), so the reader skips the first frame and
opens the second. -/
def sealCertificateBodyOfSealId (sealId : SealIdentity) :
    Option SealCertificateBody :=
  match runR (pairR byteArrayR byteArrayR) sealId.canonicalBodyBytes.toList with
  | none => none
  | some (_, bodyBytes) => runR sealCertificateBodyR bodyBytes.toList

/-- **A seal identity opens to the certificate body it seals.** -/
theorem sealCertificateBodyOfSealId_eq (core : SealCore)
    (body : SealCertificateBody) :
    sealCertificateBodyOfSealId (SealId core body) = some body := by
  have hframe :
      runR (pairR byteArrayR byteArrayR)
          (SealId core body).canonicalBodyBytes.toList =
        some (SealCore.identitySchema.encode core,
          SealCertificateBody.identitySchema.encode body) := by
    show runR (pairR byteArrayR byteArrayR)
        (Bytes.pack (Bytes.pairBytes (Bytes.framed SealCore.identitySchema.encode)
          (Bytes.framed SealCertificateBody.identitySchema.encode)
          (core, body))).toList = _
    rw [Bytes.toList_pack]
    exact runR_encode (pairR_inverts byteArrayR_inverts byteArrayR_inverts)
      (SealCore.identitySchema.encode core,
        SealCertificateBody.identitySchema.encode body)
  rw [sealCertificateBodyOfSealId, hframe]
  show runR sealCertificateBodyR
      (Bytes.pack (SealCertificateBody.bytes body)).toList = _
  rw [Bytes.toList_pack]
  exact runR_encode sealCertificateBodyR_inverts body

/-- Reconstruct the seal core a seal identity names: the first of the two frames
`Foundation.CanonicalSchema.product` lays down. -/
def sealCoreOfSealId (sealId : SealIdentity) : Option SealCore :=
  match runR (pairR byteArrayR byteArrayR) sealId.canonicalBodyBytes.toList with
  | none => none
  | some (coreBytes, _) => runR sealCoreR coreBytes.toList

/-- **A seal identity opens to the core it seals.**  With
`sealCertificateBodyOfSealId_eq`, *no* component of a seal identity is an opaque
digest: both halves of the pair it is taken over are recovered. -/
theorem sealCoreOfSealId_eq (core : SealCore) (body : SealCertificateBody) :
    sealCoreOfSealId (SealId core body) = some core := by
  have hframe :
      runR (pairR byteArrayR byteArrayR)
          (SealId core body).canonicalBodyBytes.toList =
        some (SealCore.identitySchema.encode core,
          SealCertificateBody.identitySchema.encode body) := by
    show runR (pairR byteArrayR byteArrayR)
        (Bytes.pack (Bytes.pairBytes (Bytes.framed SealCore.identitySchema.encode)
          (Bytes.framed SealCertificateBody.identitySchema.encode)
          (core, body))).toList = _
    rw [Bytes.toList_pack]
    exact runR_encode (pairR_inverts byteArrayR_inverts byteArrayR_inverts)
      (SealCore.identitySchema.encode core,
        SealCertificateBody.identitySchema.encode body)
  rw [sealCoreOfSealId, hframe]
  show runR sealCoreR (Bytes.pack (SealCore.bytes core)).toList = _
  rw [Bytes.toList_pack]
  exact runR_encode sealCoreR_inverts core

/-! ## The seal verifier (SPEC §12.1, §20.2 item 10)

Input: one seal identity.  No state, no object graph, no preimage, no proof. -/

/-- Every retained preimage the seal commits to, reconstructed from the seal
identity alone. -/
def sealVerifierPreimages (sealId : SealIdentity) : Option (List PreimageEntry) :=
  match sealCertificateBodyOfSealId sealId with
  | none => none
  | some body =>
    match sealCheckRecordOfId body.retentionCheckResultId with
    | none => none
    | some record => some record.retainedPreimages

/-- The identities the seal records as retained, reconstructed from the seal
identity alone.  A verifier does not have to be told which preimages to ask
for. -/
def sealVerifierRetainedIds (sealId : SealIdentity) :
    Option (List CanonicalObjectId) :=
  match sealCertificateBodyOfSealId sealId with
  | none => none
  | some body => some body.retentionRoot.retainedIds

/-- The preimage of one recorded identity, reconstructed from the seal identity
alone. -/
def sealVerifierPreimage (sealId : SealIdentity) (id : CanonicalObjectId) :
    Option ByteArray :=
  match sealVerifierPreimages sealId with
  | none => none
  | some entries =>
    (entries.find? (fun e => decide (e.objectId = id))).map PreimageEntry.preimageBytes

/-- The canonical bytes of the state body, reconstructed from the seal identity
alone.  By `CanonicalSchema.encode_injective` these bytes determine the state
body itself, so the seal commits to the state it was taken over. -/
def sealVerifierStateBodyBytes (sealId : SealIdentity) : Option ByteArray :=
  match sealCertificateBodyOfSealId sealId with
  | none => none
  | some body =>
    match sealCheckRecordOfId body.retentionCheckResultId with
    | none => none
    | some record => some record.stateBodyBytes

/-- **The verifier is a real parser.**  It rejects an identity whose recorded
bytes are not a canonical seal encoding — so the theorems below are statements
about a function that can fail, not about a constant.  A "reconstruction" that
answered every identity would be answering none of them. -/
theorem sealVerifierPreimages_rejects_malformed :
    sealVerifierPreimages
        ⟨0, CanonicalDomainTag.atlasState, ByteArray.empty, ByteArray.empty⟩ = none := by
  have h : (ByteArray.empty : ByteArray).toList = [] := by
    rw [Bytes.byteArray_toList]; rfl
  simp only [sealVerifierPreimages, sealCertificateBodyOfSealId, h, runR, pairR,
    byteArrayR, mapR, stringR, natR]

/-! ### Reconstruction -/

/-- The retention record a sealed state's identity opens to is the checker's own
record for that state and core. -/
theorem sealedState_retentionRecord (sealed : SealedState) :
    sealCertificateBodyOfSealId sealed.sealId = some sealed.certificate.body ∧
    sealCheckRecordOfId sealed.certificate.body.retentionCheckResultId =
      some (canonicalSealCheckResultBody sealed.state sealed.core .retentionComplete) := by
  have hcanon : sealed.certificate.body =
      canonicalSealCertificateBody sealed.state sealed.core :=
    SealCertificate.body_eq_canonical sealed.certificate
  refine ⟨?_, ?_⟩
  · rw [sealed.sealIdEq]
    exact sealCertificateBodyOfSealId_eq sealed.core sealed.certificate.body
  · rw [hcanon]
    exact sealCheckRecordOfId_canonical sealed.state sealed.core .retentionComplete

/--
**SPEC §15, `Atlas.seal_verifier_reconstructs_every_preimage`.**

From the seal identity alone — no state, no object graph, no preimage handed in
— the verifier reconstructs

1. exactly the list of retained preimages the sealed state holds, and
2. for every identity the seal's own retention root records, the exact bytes
   retained for that identity.

The quantifier in (2) ranges over what the SEAL records (`core.retentionRoot`),
not over what the caller supplies, and the reconstructed entry is proved to be a
member of the state's retained graph — so the seal names real recorded objects,
not opaque digests.

**This is not a coverage claim.**  It says every identity the seal *records* can
be opened; it says nothing whatever about which objects were recorded, and a
seal retaining three objects satisfies it.  Nothing here mentions
`universalCoverCompleteCheck`, `ByteArray` competitors, partitions or
optimality, and `Atlas.seal_implies_universal_coverage` stays absent
(`Atlas/CoverageScope.lean`).

Not vacuous: `Atlas.SealedState` is inhabited — `Atlas.derivedSealedState`
(`Atlas/Rebuild.lean`) builds one whose seven checker fields are discharged by
proved checker results.  This module does not import it, to keep the statement
independent of the rebuild layer.
-/
theorem seal_verifier_reconstructs_every_preimage (sealed : SealedState) :
    sealVerifierPreimages sealed.sealId =
        some sealed.state.retainedObjects.graph.preimages ∧
      ∀ id ∈ sealed.core.retentionRoot.retainedIds,
        ∃ preimage : ByteArray,
          sealVerifierPreimage sealed.sealId id = some preimage ∧
          PreimageEntry.mk id preimage ∈ sealed.state.retainedObjects.graph.preimages := by
  obtain ⟨hbody, hrecord⟩ := sealedState_retentionRecord sealed
  have hpre : sealVerifierPreimages sealed.sealId =
      some sealed.state.retainedObjects.graph.preimages := by
    simp only [sealVerifierPreimages, hbody, hrecord]
    rfl
  refine ⟨hpre, ?_⟩
  intro id hid
  have hroot : sealed.core.retentionRoot = sealed.state.retentionRoot :=
    ResolvesEveryReferencedPreimage.rootEq sealed.certificate.retentionComplete
  have hmem : id ∈ sealed.state.retainedObjects.graph.retainedIds := by
    rw [hroot] at hid
    exact hid
  have hex : ∃ e ∈ sealed.state.retainedObjects.graph.preimages, e.objectId = id := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    exact ⟨e, he, heq⟩
  cases hfind :
      sealed.state.retainedObjects.graph.preimages.find?
        (fun e => decide (e.objectId = id)) with
  | none =>
    obtain ⟨e, he, heq⟩ := hex
    exact absurd (List.find?_eq_none.mp hfind e he) (by simp [heq])
  | some e =>
    have hp : e.objectId = id := by
      have := List.find?_some hfind
      simpa using this
    refine ⟨e.preimageBytes, ?_, ?_⟩
    · simp only [sealVerifierPreimage, hpre, hfind, Option.map_some]
    · have hmem' : e ∈ sealed.state.retainedObjects.graph.preimages :=
        List.mem_of_find?_eq_some hfind
      obtain ⟨eid, ebytes⟩ := e
      simp only at hp
      rw [hp] at hmem'
      exact hmem'

/-- **A sealed state's identity opens completely**: both halves of the pair it is
taken over come back, so the quantification domain of
`seal_verifier_reconstructs_every_preimage` — the core's retention root — is
itself something the verifier recovers rather than something it is told. -/
theorem seal_verifier_opens_seal (sealed : SealedState) :
    sealCoreOfSealId sealed.sealId = some sealed.core ∧
    sealCertificateBodyOfSealId sealed.sealId = some sealed.certificate.body := by
  rw [sealed.sealIdEq]
  exact ⟨sealCoreOfSealId_eq sealed.core sealed.certificate.body,
    sealCertificateBodyOfSealId_eq sealed.core sealed.certificate.body⟩

/-- The verifier does not need to be told which identities to open: the seal
identity yields the recorded retention list, and it is exactly the state's. -/
theorem seal_verifier_reconstructs_retained_ids (sealed : SealedState) :
    sealVerifierRetainedIds sealed.sealId =
      some sealed.state.retainedObjects.graph.retainedIds := by
  obtain ⟨hbody, -⟩ := sealedState_retentionRecord sealed
  have hcanon : sealed.certificate.body =
      canonicalSealCertificateBody sealed.state sealed.core :=
    SealCertificate.body_eq_canonical sealed.certificate
  have hroot : sealed.core.retentionRoot = sealed.state.retentionRoot :=
    ResolvesEveryReferencedPreimage.rootEq sealed.certificate.retentionComplete
  simp only [sealVerifierRetainedIds, hbody, hcanon]
  show some (sealed.core.retentionRoot.retainedIds) = _
  rw [hroot]
  rfl

/-- Every identity the state *references* is in particular reconstructible: the
retention condition of `Atlas.SealCertificate` puts it in the retained set. -/
theorem seal_verifier_reconstructs_referenced_preimage (sealed : SealedState)
    {id : CanonicalObjectId} (hid : id ∈ sealed.state.body.referencedObjects) :
    ∃ preimage : ByteArray,
      sealVerifierPreimage sealed.sealId id = some preimage ∧
      PreimageEntry.mk id preimage ∈ sealed.state.retainedObjects.graph.preimages := by
  refine (seal_verifier_reconstructs_every_preimage sealed).2 id ?_
  rw [ResolvesEveryReferencedPreimage.rootEq sealed.certificate.retentionComplete]
  exact UnsealedState.referenced_mem_retained sealed.state id hid

/-- The seal also opens to the exact canonical bytes of the state body, which
determine that body uniquely (`CanonicalSchema.encode_injective`).  So the
reconstructed preimages are the preimages of *this* state, not of some other
state with the same retention root. -/
theorem seal_verifier_reconstructs_state_body_bytes (sealed : SealedState) :
    sealVerifierStateBodyBytes sealed.sealId =
      some (StateBody.identitySchema.encode sealed.state.body) := by
  obtain ⟨hbody, hrecord⟩ := sealedState_retentionRecord sealed
  simp only [sealVerifierStateBodyBytes, hbody, hrecord]
  rfl

/-- Two sealed states whose reconstructed state-body bytes agree have the same
state body.  This is the sense in which the seal *identifies* its state. -/
theorem stateBody_eq_of_sealVerifier_eq (s t : SealedState)
    (h : sealVerifierStateBodyBytes s.sealId = sealVerifierStateBodyBytes t.sealId) :
    s.state.body = t.state.body := by
  rw [seal_verifier_reconstructs_state_body_bytes s,
    seal_verifier_reconstructs_state_body_bytes t] at h
  exact StateBody.identitySchema.encode_injective (Option.some.inj h)

end WasmGemmGnaf.Atlas
