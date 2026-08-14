/-
  Wasm/Core/Encode.lean --- the CANONICAL binary ENCODER for pinned WebAssembly
  Core 3.0 modules, and the proof that its output is a derivation of the pinned
  binary grammar.

  WHAT THIS IS.  `Wasm.Core.Binary.encode : Module -> ByteArray` is a total,
  computable map from a Core 3.0 module to bytes, and

      encModule_Bmodule   : encModule m = some bs -> Bmodule bs m
      encodeBytes_Bmodule : encodable m = true -> Bmodule (encodeBytes m) m

  say the bytes it produces are DERIVABLE in `Bmodule`, the declarative binary
  grammar of `Wasm/Core/BinaryGrammar/`, transcribed from

      vendor/wasm-spec/specification/wasm-3.0/5.*-binary.*.spectec

  Composed with `Wasm.Core.decode_complete` in `Wasm/Core/EncodeSound.lean` --
  the only file that puts a decoder and an encoder in one import graph -- this
  gives `Wasm.Core.decode_encode : decode (encode m) = .ok m`, and, on the
  released artifact, `encode releaseBaselineModule = releaseArtifactBytes`.

  WHY THE PROOF IS AGAINST THE GRAMMAR AND NOT AGAINST THE DECODER.  An external
  audit rejected an earlier round trip because the decoder was proved inverse to
  the repository's own encoder.  Nothing of that shape happens here: THIS FILE
  IMPORTS NO DECODER.  Its import graph is `BinaryGrammar/`, i.e. the pinned
  syntax plus the transcription of `5.*-binary.*.spectec`.  The encoder mirrors
  the grammar clause for clause and every lemma below names the production it
  discharges; the round trip is then the composition of two independently proved
  statements about `Bmodule`.

  TOTALITY, AND THE PRECONDITION.  `encode` is total: it is
  `(encModule m).getD []` packed into a `ByteArray`.  `encModule` is a
  computable `Option`-valued function, so `encodable m := (encModule m).isSome`
  is an explicit DECIDABLE precondition -- a `Bool` computed from the module,
  discharged by `decide` on any concrete one.  `encModule m = none` has the
  grammar-forced causes below; they are stated here rather than hidden:

  1. THE FORMAT'S OWN `2^32` BOUNDS.  `Blist` counts a list with a `Bu32`,
     `Bsection_` measures a section with a `Bu32`, `Bcode` measures a function
     body with a `Bu32`, and `Bfunc` carries `-- if |$concat_(local, loc**)| <
     2^32`.  A module with `2^32` or more functions, a section of `2^32` bytes or
     more, or a function with `2^32` or more locals therefore has NO `Bmodule`
     derivation at all.  Returning `none` there is forced by the pinned grammar,
     not a limitation of this encoder.

  2. VALUES THE GRAMMAR CANNOT NAME.  A `/sem` form (`BOT`, a `deftype`, a
     `REC n`), a `memarg` whose alignment is `>= 2^6` (the pinned `Bmemarg`
     stores the alignment in six bits), an element segment whose ACTIVE mode
     carries an element type other than `REF NULL FUNC` or `REF FUNC` (`Belem`'s
     alternatives 4 and 6 fix it to `REF NULL FUNC`, alternative 0 to `REF FUNC`
     at table `0` with `REF.FUNC` initialisers, and alternative 2 reaches only
     `REF NULL FUNC` through `Belemkind`), and a float literal outside the image
     of `$inv_fbytes_`.  Under the pinned authority, this also includes
     `CALL_REF` and `RETURN_CALL_REF`, for which the pinned instruction grammar
     has no production; the amended authority encodes them at `0x14` and
     `0x15`.  Every rejection is therefore selected by the same finite
     authority as the corresponding `Bmodule` relation.

  3. AN ACTIVE `REF FUNC` ELEMENT SEGMENT AWAY FROM ALTERNATIVE 0's SHAPE.
     Alternative 0 is the only one whose element type is the non-nullable
     `REF FUNC`, and it pins the table index to `0` AND the initialisers to
     `(REF.FUNC y)*`.  An active `REF FUNC` segment at another table, or one
     whose initialiser is anything but a single `REF.FUNC`, is a shape the
     pinned grammar cannot express, not one this encoder declines to write.

  The complete `0xFD` vector binary grammar, including its relaxed-SIMD
  productions, is encoded below.  Those relaxed forms are grammar-recognized
  but rejected by the release profile at validation (SPEC section 7.2); binary
  grammar coverage does not admit them to that profile.  The opcode table and
  its proof are local to this decoder-free file, so the subsequent round-trip
  theorem does not obtain its encoder-side premise from the decoder.

  CANONICITY, PRECISELY.  `decode bytes = .ok m -> encode m = bytes` is FALSE
  for Core 3.0 and is NOT stated anywhere: `Bu32` admits non-minimal LEB128,
  every section is optional, custom sections may appear at fourteen positions,
  and several constructs have two derivations.  What IS true of this encoder is
  that it makes one canonical choice at each of those points:

  * `lebU` emits MINIMAL LEB128 -- `lebU_minimal` shows that NO `BuN` derivation
    of a value is shorter than the one `lebU` emits, which is exactly the
    non-minimality (`0x80 0x00` for `0`) that a permissive `BuN` would otherwise
    admit;
  * NO CUSTOM SECTION is emitted -- all fourteen `Bcustomsec*` positions of
    `Bmodule` are instantiated with the empty sequence, visibly, in
    `encModule_Bmodule`, and `starNil` is that derivation;
  * an EMPTY SECTION IS OMITTED rather than emitted empty (`Bsection.absent`);
  * the SHORTHAND alternative is taken wherever the grammar offers one: a
    nullable abstract reference type is one byte, a final `SUB` with no
    supertype is a bare `comptype`, a singleton `rectype` is a bare `subtype`,
    an `IF` with an empty `ELSE` uses the short form, a table whose initialiser
    is `REF.NULL` of its own element type uses `Btable`'s first alternative, and
    an active element or data segment at index `0` uses the `0:Bu32` tag rather
    than the `2:Bu32`/`6:Bu32` one that repeats the index;
  * the DATA COUNT SECTION is emitted exactly when it is needed -- when there is
    a data segment, or when some function body mentions a data index, which is
    the pinned `-- if (n? =/= eps \/ $dataidx_funcs(func*) = eps)` -- and omitted
    otherwise.

  LOCALS USE CANONICAL ADJACENT-EQUAL RUNS.  Zero-count witness runs are
  dropped and adjacent equal positive runs are merged.  The guarded aggregate
  nonexpansion theorem in `EncodeComplete.lean` proves that this canonical RLE
  remains within every derivable `Bfunc` body's `2^32` payload bound.

  THE ENCODING IS KERNEL-COMPUTABLE.  `lebU` is defined by STRUCTURAL recursion
  on an explicit fuel rather than by well-founded recursion, because a
  `WellFounded.fix` never reduces in the kernel and every closed encoding
  checked by `rfl` or `decide` -- including `encode releaseBaselineModule =
  releaseArtifactBytes` in `Wasm/Core/EncodeSound.lean` -- would be unavailable.
  `lebUAux_irrel` shows the fuel is not part of what `lebU` means.

  NO CHOICE.  SPEC 4 bars `Classical.choice` from executable witnesses; the
  axiom closure of `encode`, `encModule_Bmodule` and `decode_encode` is
  `[propext, Quot.sound]`.
-/
import WasmGemmGnaf.Foundation.Bytes
import WasmGemmGnaf.Wasm.Core.BinaryGrammar

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

/-! ## Optional byte sequences

The encoder is `Option`-valued so that the four failure modes listed in the
header are visible in its type rather than hidden behind a junk value.  These
two combinators and their inversion lemmas are the whole of the plumbing. -/

/-- Concatenation, propagating failure. -/
def catO (x y : Option Bytes) : Option Bytes :=
  match x, y with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- A leading terminal byte, propagating failure. -/
def consO (b : Byte) (x : Option Bytes) : Option Bytes :=
  match x with
  | some a => some (b :: a)
  | none => none

theorem catO_eq {x y : Option Bytes} {bs : Bytes} (h : catO x y = some bs) :
    ∃ a b, x = some a ∧ y = some b ∧ bs = a ++ b := by
  unfold catO at h
  split at h
  · exact ⟨_, _, rfl, rfl, by injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

theorem consO_eq {b : Byte} {x : Option Bytes} {bs : Bytes}
    (h : consO b x = some bs) : ∃ a, x = some a ∧ bs = b :: a := by
  unfold consO at h
  split at h
  · exact ⟨_, rfl, by injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

/-! ## Minimal unsigned LEB128

`BuN(N)` is the bounded PERMISSIVE LEB128 of `5.1-binary.values.spectec`: it
admits non-minimal encodings inside the width bound.  The encoder emits the
minimal one. -/

/-- Minimal unsigned LEB128, with an explicit STRUCTURAL fuel.

The fuel is not a bound on the encoder: `lebU` below passes `n + 1`, which is
always more than the number of groups `n` has, and `lebUAux_irrel` shows the
result does not depend on which sufficient fuel is passed.  It is here so that
the definition reduces IN THE KERNEL: a well-founded recursion is compiled to
`WellFounded.fix`, whose `Acc.rec` never reduces on an opaque accessibility
proof, and every concrete encoding checked by `rfl` or `decide` at the end of
this file would be unavailable. -/
def lebUAux : Nat → Nat → Bytes
  | 0, _ => []
  | fuel + 1, n =>
      if n < 0x80 then [Byte.ofNat n]
      else Byte.ofNat (0x80 + n % 0x80) :: lebUAux fuel (n / 0x80)

/-- Minimal unsigned LEB128 of a natural number: seven bits per byte, least
significant group first, continuation bit set on every byte but the last. -/
def lebU (n : Nat) : Bytes := lebUAux (n + 1) n

/-- Any two sufficient fuels give the same encoding, so `lebU`'s choice of
`n + 1` is not part of what it means. -/
theorem lebUAux_irrel : ∀ (f g n : Nat), n < f → n < g → lebUAux f n = lebUAux g n := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
    intro g n hf hg
    match f, g with
    | 0, _ => omega
    | _, 0 => omega
    | f + 1, g + 1 =>
      show (if n < 0x80 then [Byte.ofNat n]
            else Byte.ofNat (0x80 + n % 0x80) :: lebUAux f (n / 0x80))
         = (if n < 0x80 then [Byte.ofNat n]
            else Byte.ofNat (0x80 + n % 0x80) :: lebUAux g (n / 0x80))
      rcases Nat.lt_or_ge n 0x80 with h | h
      · rw [if_pos h, if_pos h]
      · rw [if_neg (by omega), if_neg (by omega)]
        have hlt : n / 0x80 < n := Nat.div_lt_self (by omega) (by omega)
        rw [ih f (by omega) g (n / 0x80) (by omega) (by omega)]

/-- The defining equation of the minimal LEB128 encoding, fuel eliminated.
Every proof below reasons through this and never through `lebUAux`. -/
theorem lebU_eq (n : Nat) : lebU n =
    if n < 0x80 then [Byte.ofNat n]
    else Byte.ofNat (0x80 + n % 0x80) :: lebU (n / 0x80) := by
  show (if n < 0x80 then [Byte.ofNat n]
        else Byte.ofNat (0x80 + n % 0x80) :: lebUAux n (n / 0x80)) = _
  rcases Nat.lt_or_ge n 0x80 with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (by omega), if_neg (by omega)]
    have hlt : n / 0x80 < n := Nat.div_lt_self (by omega) (by omega)
    show _ :: lebUAux n (n / 0x80) = _ :: lebUAux (n / 0x80 + 1) (n / 0x80)
    rw [lebUAux_irrel n (n / 0x80 + 1) (n / 0x80) (by omega) (by omega)]

/-- `Byte.ofNat` is the identity on values below `0x100`. -/
theorem Byte_ofNat_val {n : Nat} (h : n < 0x100) : (Byte.ofNat n).val = n :=
  Nat.mod_eq_of_lt h

/-- **`grammar BuN(N)`.**  The minimal LEB128 encoding of a natural number that
fits in `uN(N)` is a derivation of `BuN(N)` for that number. -/
theorem lebU_BuN : ∀ (n N : Nat), n < 2 ^ N → BuN N (lebU n) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro N hN
    rw [lebU_eq]
    rcases Nat.lt_or_ge n 0x80 with h | h
    · rw [if_pos h]
      have hv : (Byte.ofNat n).val = n := Byte_ofNat_val (by omega)
      have hlast := BuN.last N (Byte.ofNat n) (by rw [hv]; omega) (by rw [hv]; exact hN)
      rwa [hv] at hlast
    · rw [if_neg (by omega)]
      have hmod : n % 0x80 < 0x80 := Nat.mod_lt _ (by omega)
      have hv : (Byte.ofNat (0x80 + n % 0x80)).val = 0x80 + n % 0x80 :=
        Byte_ofNat_val (by omega)
      have h128 : (2 : Nat) ^ 7 = 128 := by decide
      have hN7 : 7 < N := by
        rcases Nat.lt_or_ge 7 N with h7 | h7
        · exact h7
        · exact absurd hN (by
            have hle : (2 : Nat) ^ N ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) h7
            omega)
      have hdiv : n / 0x80 < 2 ^ (N - 7) := by
        have hsplit : (2 : Nat) ^ 7 * 2 ^ (N - 7) = 2 ^ N := by
          rw [← Nat.pow_add]; congr 1; omega
        have h1 : n / 0x80 * 0x80 ≤ n := Nat.div_mul_le_self n 0x80
        rcases Nat.lt_or_ge (n / 0x80) (2 ^ (N - 7)) with hc | hc
        · exact hc
        · exact absurd hN (by
            have hmul : 2 ^ (N - 7) * 0x80 ≤ n / 0x80 * 0x80 :=
              Nat.mul_le_mul hc (Nat.le_refl 0x80)
            omega)
      have hstep := BuN.more N (Byte.ofNat (0x80 + n % 0x80)) (lebU (n / 0x80))
        (n / 0x80) (by rw [hv]; omega) hN7
        (ih (n / 0x80) (Nat.div_lt_self (by omega) (by omega)) (N - 7) hdiv)
      have hval :
          2 ^ 7 * (n / 0x80) + ((Byte.ofNat (0x80 + n % 0x80)).val - 2 ^ 7) = n := by
        rw [hv]
        have hdm := Nat.div_add_mod n 0x80
        omega
      rwa [hval] at hstep

/-- The `u32` case: a `Bu32` derivation for any `u32`. -/
theorem encU32_Bu32 (x : U32) : Bu32 (lebU x.val) x :=
  lebU_BuN x.val 32 x.property

/-- The `u64` case: a `Bu64` derivation for any `u64`. -/
theorem encU64_Bu64 (x : U64) : Bu64 (lebU x.val) x :=
  lebU_BuN x.val 64 x.property

/-- **MINIMALITY OF THE LEB128 THIS ENCODER EMITS.**  The pinned `BuN` is
PERMISSIVE: `0x80 0x00` is one of its derivations of `0`, and so is
`0x80 0x80 0x80 0x80 0x00`.  This says that no derivation of a value is SHORTER
than the encoding `lebU` picks for it, which is exactly the canonicity claim
that "`encode` emits minimal LEB128" makes -- stated over the grammar, not over
this encoder's own notion of minimal. -/
theorem lebU_minimal : ∀ {N : Nat} {bs : Bytes} {v : Nat}, BuN N bs v →
    (lebU v).length ≤ bs.length := by
  intro N bs v h
  have h128 : (2 : Nat) ^ 7 = 128 := by decide
  induction h with
  | last N n h1 h2 =>
      rw [lebU_eq, if_pos (by omega)]
      simp
  | more N n bs m h1 h2 _ ih =>
      have hn : n.val < 0x100 := n.property
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [lebU_eq, if_pos (by omega)]
        simp
      · have hv : ¬ (2 ^ 7 * m + (n.val - 2 ^ 7) < 0x80) := by omega
        have hdiv : (2 ^ 7 * m + (n.val - 2 ^ 7)) / 0x80 = m := by omega
        rw [lebU_eq, if_neg hv, hdiv]
        simpa using ih

/-- `k:Bu32` with `k` a numeral -- the selector of a prefixed opcode or the tag
of an element or data segment. -/
theorem lebU_Bu32lit (k : Nat) (h : k < 2 ^ 32) : Bu32lit k (lebU k) :=
  ⟨⟨k, h⟩, lebU_BuN k 32 h, rfl⟩

/-- `0xPP k:Bu32`, the shape of every `0xFB` / `0xFC` opcode. -/
def pre (p k : Nat) : Bytes := tb p :: lebU k

/-- **`Bprefixed`.** -/
theorem pre_Bprefixed (p k : Nat) (h : k < 2 ^ 32) : Bprefixed p k (pre p k) :=
  ⟨lebU k, rfl, lebU_Bu32lit k h⟩

/-! ## Minimal signed LEB128, at the two places the format uses it

`Bs33` occurs in `Bheaptype` and `Bblocktype`, and both guard the value with
`0 <= i`, so only non-negative values are ever encoded. -/

/-- Minimal signed LEB128 of a NON-NEGATIVE value.  The pinned `BsN`'s
continuation alternative recurses into `BuN`, not into `BsN` (a defect recorded
at `BsN` itself); the encoding below is a derivation of the relation as
transcribed. -/
def lebSPinned (n : Nat) : Bytes :=
  if n < 0x40 then [Byte.ofNat n]
  else Byte.ofNat (0x80 + n % 0x80) :: lebU (n / 0x80)

/-- Positive signed LEB128 with a genuinely signed recursive tail.  Five
rounds suffice for every `u32` value used at the two signed-33 leaves. -/
def lebSAmendedAux : Nat → Nat → Bytes
  | 0, n => [Byte.ofNat n]
  | fuel + 1, n =>
      if n < 0x40 then [Byte.ofNat n]
      else Byte.ofNat (0x80 + n % 0x80) :: lebSAmendedAux fuel (n / 0x80)

def lebSAmended (n : Nat) : Bytes := lebSAmendedAux 5 n

/-- The signed encoding selected by the finite binary authority. -/
def lebS (n : Nat) : Bytes :=
  match authority.revision with
  | .pinned => lebSPinned n
  | .amended => lebSAmended n

/-- **`grammar Bs33`**, on a non-negative value that fits in a `u32`. -/
theorem lebSPinned_Bs33 (n : Nat) (h : n < 2 ^ 32) :
    Bs33 (lebSPinned n) (n : Int) := by
  unfold lebSPinned Bs33
  rcases Nat.lt_or_ge n 0x40 with hs | hs
  · rw [if_pos hs]
    have hv : (Byte.ofNat n).val = n := Byte_ofNat_val (by omega)
    have h6 : (2 : Nat) ^ 6 = 64 := by decide
    have h32 : (2 : Nat) ^ (33 - 1) = 4294967296 := by decide
    have hpos := BsN.pos 33 (Byte.ofNat n) (by rw [hv]; omega) (by rw [hv]; omega)
    rwa [hv] at hpos
  · rw [if_neg (by omega)]
    have hmod : n % 0x80 < 0x80 := Nat.mod_lt _ (by omega)
    have hv : (Byte.ofNat (0x80 + n % 0x80)).val = 0x80 + n % 0x80 :=
      Byte_ofNat_val (by omega)
    have h128 : (2 : Nat) ^ 7 = 128 := by decide
    have hdiv : n / 0x80 < 2 ^ (33 - 7) := by
      have h26 : (2 : Nat) ^ (33 - 7) = 67108864 := by decide
      have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      omega
    have hstep := BsN.more 33 (Byte.ofNat (0x80 + n % 0x80)) (lebU (n / 0x80))
      (n / 0x80) (by rw [hv]; omega) (by omega)
      (lebU_BuN (n / 0x80) (33 - 7) hdiv)
    have hval :
        (2 : Int) ^ 7 * ((n / 0x80 : Nat) : Int) +
          (((Byte.ofNat (0x80 + n % 0x80)).val : Int) - (2 : Int) ^ 7)
            = (n : Int) := by
      rw [hv]
      have hdm : 0x80 * (n / 0x80) + n % 0x80 = n := Nat.div_add_mod n 0x80
      have hcast : ((0x80 * (n / 0x80) + n % 0x80 : Nat) : Int) = (n : Int) := by
        rw [hdm]
      push_cast at hcast
      have h7 : (2 : Int) ^ 7 = 128 := by decide
      omega
    rwa [hval] at hstep

theorem BsN'_more_nat {N n : Nat} {tail : Bytes}
    (hN : 7 < N) (hn : 0x40 ≤ n)
    (ht : BsN' (N - 7) tail (n / 0x80 : Nat)) :
    BsN' N (Byte.ofNat (0x80 + n % 0x80) :: tail) (n : Int) := by
  have hmod : n % 0x80 < 0x80 := Nat.mod_lt _ (by omega)
  have hv : (Byte.ofNat (0x80 + n % 0x80)).val = 0x80 + n % 0x80 :=
    Byte_ofNat_val (by omega)
  have hstep := BsN'.more N (Byte.ofNat (0x80 + n % 0x80)) tail
    (n / 0x80 : Nat) (by rw [hv]; omega) hN ht
  have hdm : 0x80 * (n / 0x80) + n % 0x80 = n := Nat.div_add_mod n 0x80
  have h7 : (2 : Int) ^ 7 = 128 := by decide
  have hval :
      (2 : Int) ^ 7 * ((n / 0x80 : Nat) : Int) +
          (((Byte.ofNat (0x80 + n % 0x80)).val : Int) - (2 : Int) ^ 7) =
        (n : Int) := by
    rw [hv, h7]
    have hcast : ((0x80 * (n / 0x80) + n % 0x80 : Nat) : Int) = (n : Int) := by
      rw [hdm]
    push_cast at hcast
    omega
  rwa [hval] at hstep

theorem BsN'_pos_nat {N n : Nat} (h64 : n < 0x40)
    (hN : n < 2 ^ (N - 1)) : BsN' N [Byte.ofNat n] (n : Int) := by
  have hv : (Byte.ofNat n).val = n := Byte_ofNat_val (by omega)
  have h := BsN'.pos N (Byte.ofNat n) (by rw [hv]; omega) (by rw [hv]; exact hN)
  rwa [hv] at h

/-- The amended positive signed encoder derives the corrected recursive
relation for every value admitted by a signed-33 index. -/
theorem lebSAmended_Bs33' (n : Nat) (h : n < 2 ^ 32) :
    Bs33' (lebSAmended n) (n : Int) := by
  unfold lebSAmended Bs33'
  simp only [lebSAmendedAux]
  by_cases h0 : n < 0x40
  · rw [if_pos h0]
    exact BsN'_pos_nat h0 (by simpa using h)
  · rw [if_neg h0]
    apply BsN'_more_nat (by decide) (by omega)
    have h1 : n / 0x80 < 2 ^ 25 := by
      have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      have h25 : (2 : Nat) ^ 25 = 33554432 := by decide
      omega
    by_cases q1 : n / 0x80 < 0x40
    · rw [if_pos q1]
      exact BsN'_pos_nat q1 (by simpa using h1)
    · rw [if_neg q1]
      apply BsN'_more_nat (by decide) (by omega)
      have h2 : n / 0x80 / 0x80 < 2 ^ 18 := by
        have h25' : (2 : Nat) ^ 25 = 33554432 := by decide
        have h18 : (2 : Nat) ^ 18 = 262144 := by decide
        omega
      by_cases q2 : n / 0x80 / 0x80 < 0x40
      · rw [if_pos q2]
        exact BsN'_pos_nat q2 (by simpa using h2)
      · rw [if_neg q2]
        apply BsN'_more_nat (by decide) (by omega)
        have h3 : n / 0x80 / 0x80 / 0x80 < 2 ^ 11 := by
          have h18' : (2 : Nat) ^ 18 = 262144 := by decide
          have h11 : (2 : Nat) ^ 11 = 2048 := by decide
          omega
        by_cases q3 : n / 0x80 / 0x80 / 0x80 < 0x40
        · rw [if_pos q3]
          exact BsN'_pos_nat q3 (by simpa using h3)
        · rw [if_neg q3]
          apply BsN'_more_nat (by decide) (by omega)
          have h4 : n / 0x80 / 0x80 / 0x80 / 0x80 < 2 ^ 4 := by
            have h11' : (2 : Nat) ^ 11 = 2048 := by decide
            omega
          rw [if_pos (by omega)]
          exact BsN'_pos_nat (by omega) (by simpa using h4)

/-- The selected signed encoding is sound for either finite authority. -/
theorem lebS_Bs33For (n : Nat) (h : n < 2 ^ 32) :
    Bs33For (lebS n) (n : Int) := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact lebSPinned_Bs33 n h
      | amended => exact lebSAmended_Bs33' n h

/-! ## Repetition, lists and sections

`X^n`, `list(BX)` and `Bsection_(N, BX)` of `X.4-notation.binary.spectec` and
`5.4-binary.modules.spectec`. -/

/-- `(el:BX)^n`, for the `n` that is the length of the list. -/
def encRep {α : Type} (f : α → Option Bytes) : List α → Option Bytes
  | [] => some []
  | a :: as => catO (f a) (encRep f as)

/-- **`(el:BX)^n`.** -/
theorem encRep_Rep {α : Type} {G : Bytes → α → Prop} {f : α → Option Bytes}
    (hf : ∀ a b, f a = some b → G b a) :
    ∀ (xs : List α) (bs : Bytes), encRep f xs = some bs → Rep G xs.length bs xs := by
  intro xs
  induction xs with
  | nil => intro bs h; injection h with h; subst h; exact Rep.nil
  | cons a as ih =>
      intro bs h
      obtain ⟨b, r, hb, hr, hbs⟩ := catO_eq h
      subst hbs
      exact Rep.cons b a r as as.length (hf a b hb) (ih r hr)

/-- `grammar Blist(grammar BX : el) : el* = | n:Bu32 (el:BX)^n => el^n`.
`none` when the list is too long to be counted by a `u32`; the pinned grammar
has no derivation for such a list either. -/
def encList {α : Type} (f : α → Option Bytes) (xs : List α) : Option Bytes :=
  if h : xs.length < 2 ^ 32 then catO (some (lebU xs.length)) (encRep f xs)
  else none

/-- **`grammar Blist`.** -/
theorem encList_Blist {α : Type} {G : Bytes → α → Prop} {f : α → Option Bytes}
    (hf : ∀ a b, f a = some b → G b a) (xs : List α) (bs : Bytes)
    (h : encList f xs = some bs) : Blist G bs xs := by
  unfold encList at h
  split at h
  · rename_i hlen
    obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
    injection ha with ha
    subst hbs; subst ha
    exact Blist.mk (lebU xs.length) b ⟨xs.length, hlen⟩ xs
      (lebU_BuN xs.length 32 hlen) (encRep_Rep hf xs b hb)
  · exact absurd h (by simp)

/-- `grammar Bsection_(N, BX)`, the `present` alternative: the section id, the
byte length of the payload as a `Bu32`, and the payload. -/
def encSectionBody (N : Nat) (payload : Bytes) : Option Bytes :=
  if h : payload.length < 2 ^ 32 then
    some (tb N :: (lebU payload.length ++ payload))
  else none

/-- **`grammar Bsection_`, the `present` alternative.** -/
theorem encSectionBody_Bsection {α : Type} {N : Nat} {G : Bytes → List α → Prop}
    {payload bs : Bytes} {xs : List α} (hG : G payload xs)
    (h : encSectionBody N payload = some bs) : Bsection N G bs xs := by
  unfold encSectionBody at h
  split at h
  · rename_i hlen
    injection h with h; subst h
    exact Bsection.present (lebU payload.length) payload ⟨payload.length, hlen⟩ xs
      (lebU_BuN payload.length 32 hlen) hG rfl
  · exact absurd h (by simp)

/-- A section holding a `list(BX)`: absent when the list is empty, which is the
shorter of the two derivations the grammar offers. -/
def encListSection {α : Type} (N : Nat) (f : α → Option Bytes)
    (xs : List α) : Option Bytes :=
  match xs with
  | [] => some []
  | _ :: _ =>
      match encList f xs with
      | some p => encSectionBody N p
      | none => none

/-- **`grammar Bsection_(N, Blist(BX))`.** -/
theorem encListSection_Bsection {α : Type} {G : Bytes → α → Prop}
    {f : α → Option Bytes} (hf : ∀ a b, f a = some b → G b a) (N : Nat)
    (xs : List α) (bs : Bytes) (h : encListSection N f xs = some bs) :
    Bsection N (Blist G) bs xs := by
  unfold encListSection at h
  split at h
  · injection h with h; subst h; exact Bsection.absent
  · split at h
    · rename_i p hp
      exact encSectionBody_Bsection (encList_Blist hf _ p hp) h
    · exact absurd h (by simp)


/-! ## Floating-point literals

`grammar BfN(N) : fN(N) = b*:Bbyte^(N/8) => $inv_fbytes_(N, b*)`.
`BinaryGrammar/Values.lean` defines `$inv_fbytes_` as the IEEE 754 interchange
decoding read little-endian; the encoder below is its right inverse on exactly
the values that are in its image.  A magnitude the decoding cannot produce -- a
significand at or above `2^M`, an exponent outside `[1, 2^E-2]` for a `NORM`, a
`NAN` with a zero payload -- has NO `BfN` derivation at all, so `none` there is
forced by the grammar. -/

/-- `k` bytes of a natural number, least significant first: the inverse of
`leNat` at each fixed width. -/
def bytesLE : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => Byte.ofNat (n % 0x100) :: bytesLE k (n / 0x100)

theorem bytesLE_length : ∀ (k n : Nat), (bytesLE k n).length = k
  | 0, _ => rfl
  | k + 1, n => by
      show (bytesLE k (n / 0x100)).length + 1 = k + 1
      rw [bytesLE_length k (n / 0x100)]

theorem leNat_bytesLE : ∀ (k n : Nat), n < 0x100 ^ k → leNat (bytesLE k n) = n
  | 0, n, h => by
      have : (0x100 : Nat) ^ 0 = 1 := by decide
      show 0 = n
      omega
  | k + 1, n, h => by
      have hrec : n / 0x100 < 0x100 ^ k := by
        have hpow : (0x100 : Nat) ^ (k + 1) = 0x100 ^ k * 0x100 := by
          rw [Nat.pow_succ]
        rcases Nat.lt_or_ge (n / 0x100) (0x100 ^ k) with hc | hc
        · exact hc
        · exact absurd h (by
            have hmul : 0x100 ^ k * 0x100 ≤ n / 0x100 * 0x100 :=
              Nat.mul_le_mul hc (Nat.le_refl 0x100)
            have h1 : n / 0x100 * 0x100 ≤ n := Nat.div_mul_le_self n 0x100
            omega)
      show (Byte.ofNat (n % 0x100)).val + 0x100 * leNat (bytesLE k (n / 0x100)) = n
      rw [leNat_bytesLE k (n / 0x100) hrec,
        Byte_ofNat_val (Nat.mod_lt _ (by decide))]
      have := Nat.div_add_mod n 0x100
      omega

/-- `b*:Bbyte^n`: any byte list derives itself. -/
theorem Rep_Bbyte : ∀ (l : List Byte), Rep Bbyte l.length l l
  | [] => Rep.nil
  | b :: l => by
      have h := Rep.cons [b] b l l l.length (Bbyte.mk b) (Rep_Bbyte l)
      simpa using h

/-- The magnitude `$inv_fbytes_(32, -)` reads off a biased exponent field and a
significand field. -/
def magOf32 (e m : Nat) : FNMag 32 :=
  if e = 0 then .subnorm m
  else if e = 2 ^ 8 - 1 then (if m = 0 then .inf else .nan m)
  else .norm m ((e : Int) - ((2 ^ (8 - 1) - 1 : Nat) : Int))

/-- The magnitude `$inv_fbytes_(64, -)` reads off. -/
def magOf64 (e m : Nat) : FNMag 64 :=
  if e = 0 then .subnorm m
  else if e = 2 ^ 11 - 1 then (if m = 0 then .inf else .nan m)
  else .norm m ((e : Int) - ((2 ^ (11 - 1) - 1 : Nat) : Int))

/-- **`$inv_fbytes_(32, b*)`**, computed on a sign / exponent / significand
triple. -/
theorem invFbytes32_of (s e m : Nat) (hs : s < 2) (he : e < 2 ^ 8) (hm : m < 2 ^ 23) :
    invFbytes 32 (bytesLE 4 (s * 2 ^ 31 + e * 2 ^ 23 + m)) =
      some (if s = 0 then .pos (magOf32 e m) else .neg (magOf32 e m)) := by
  have hn : s * 2 ^ 31 + e * 2 ^ 23 + m < 0x100 ^ 4 := by
    have h1 : (2 : Nat) ^ 31 = 2147483648 := by decide
    have h2 : (2 : Nat) ^ 23 = 8388608 := by decide
    have h3 : (2 : Nat) ^ 8 = 256 := by decide
    have h4 : (0x100 : Nat) ^ 4 = 4294967296 := by decide
    have h5 : e * 8388608 ≤ 255 * 8388608 := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have h6 : s * 2147483648 ≤ 1 * 2147483648 := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    omega
  have hlen : (bytesLE 4 (s * 2 ^ 31 + e * 2 ^ 23 + m)).length = 32 / 8 :=
    bytesLE_length 4 _
  have hle : leNat (bytesLE 4 (s * 2 ^ 31 + e * 2 ^ 23 + m)) =
      s * 2 ^ 31 + e * 2 ^ 23 + m := leNat_bytesLE 4 _ hn
  have h1 : (2 : Nat) ^ 31 = 2147483648 := by decide
  have h2 : (2 : Nat) ^ 23 = 8388608 := by decide
  have h3 : (2 : Nat) ^ 8 = 256 := by decide
  have hm' : (s * 2 ^ 31 + e * 2 ^ 23 + m) % 2 ^ 23 = m := by omega
  have he' : (s * 2 ^ 31 + e * 2 ^ 23 + m) / 2 ^ 23 % 2 ^ 8 = e := by omega
  have hs' : (s * 2 ^ 31 + e * 2 ^ 23 + m) / 2 ^ (23 + 8) % 2 = s := by
    have : (23 : Nat) + 8 = 31 := by decide
    rw [this]
    omega
  unfold invFbytes
  simp only [signif, expon, hlen, if_pos, hle, hm', he', hs', magOf32]

/-- **`$inv_fbytes_(64, b*)`**, computed on a sign / exponent / significand
triple. -/
theorem invFbytes64_of (s e m : Nat) (hs : s < 2) (he : e < 2 ^ 11) (hm : m < 2 ^ 52) :
    invFbytes 64 (bytesLE 8 (s * 2 ^ 63 + e * 2 ^ 52 + m)) =
      some (if s = 0 then .pos (magOf64 e m) else .neg (magOf64 e m)) := by
  have h1 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have h2 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  have h3 : (2 : Nat) ^ 11 = 2048 := by decide
  have hn : s * 2 ^ 63 + e * 2 ^ 52 + m < 0x100 ^ 8 := by
    have h4 : (0x100 : Nat) ^ 8 = 18446744073709551616 := by decide
    have h5 : e * 4503599627370496 ≤ 2047 * 4503599627370496 :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have h6 : s * 9223372036854775808 ≤ 1 * 9223372036854775808 :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    omega
  have hlen : (bytesLE 8 (s * 2 ^ 63 + e * 2 ^ 52 + m)).length = 64 / 8 :=
    bytesLE_length 8 _
  have hle : leNat (bytesLE 8 (s * 2 ^ 63 + e * 2 ^ 52 + m)) =
      s * 2 ^ 63 + e * 2 ^ 52 + m := leNat_bytesLE 8 _ hn
  have hm' : (s * 2 ^ 63 + e * 2 ^ 52 + m) % 2 ^ 52 = m := by omega
  have he' : (s * 2 ^ 63 + e * 2 ^ 52 + m) / 2 ^ 52 % 2 ^ 11 = e := by omega
  have hs' : (s * 2 ^ 63 + e * 2 ^ 52 + m) / 2 ^ (52 + 11) % 2 = s := by
    have : (52 : Nat) + 11 = 63 := by decide
    rw [this]
    omega
  unfold invFbytes
  simp only [signif, expon, hlen, if_pos, hle, hm', he', hs', magOf64]


/-- The fields of a `NORM` `f32` magnitude.  The exponent parameter is declared
at `Int` rather than at the abbreviation `exp`, so that the side conditions
below are `Int` inequalities that `omega` can read. -/
def f32NormFields (sg m : Nat) (e : Int) : Option (Nat × Nat × Nat) :=
  if m < 2 ^ 23 ∧ 1 ≤ e + 127 ∧ e + 127 ≤ 254 then some (sg, (e + 127).toNat, m)
  else none

/-- The fields of a `NORM` `f64` magnitude; see `f32NormFields`. -/
def f64NormFields (sg m : Nat) (e : Int) : Option (Nat × Nat × Nat) :=
  if m < 2 ^ 52 ∧ 1 ≤ e + 1023 ∧ e + 1023 ≤ 2046 then some (sg, (e + 1023).toNat, m)
  else none

/-- The sign, biased exponent and significand fields of an `f32` magnitude, or
`none` when the magnitude is outside the image of `$inv_fbytes_(32, -)`. -/
def f32Mag (sg : Nat) : FNMag 32 → Option (Nat × Nat × Nat)
  | .subnorm m => if m < 2 ^ 23 then some (sg, 0, m) else none
  | .inf => some (sg, 255, 0)
  | .nan m => if 0 < m ∧ m < 2 ^ 23 then some (sg, 255, m) else none
  | .norm m e => f32NormFields sg m e

/-- The three fields of an `f32`. -/
def f32Fields : F32 → Option (Nat × Nat × Nat)
  | .pos g => f32Mag 0 g
  | .neg g => f32Mag 1 g

/-- The sign, biased exponent and significand fields of an `f64` magnitude. -/
def f64Mag (sg : Nat) : FNMag 64 → Option (Nat × Nat × Nat)
  | .subnorm m => if m < 2 ^ 52 then some (sg, 0, m) else none
  | .inf => some (sg, 2047, 0)
  | .nan m => if 0 < m ∧ m < 2 ^ 52 then some (sg, 2047, m) else none
  | .norm m e => f64NormFields sg m e

/-- The three fields of an `f64`. -/
def f64Fields : F64 → Option (Nat × Nat × Nat)
  | .pos g => f64Mag 0 g
  | .neg g => f64Mag 1 g

theorem f32Mag_spec (sg : Nat) (g : FNMag 32) (s e m : Nat)
    (h : f32Mag sg g = some (s, e, m)) :
    s = sg ∧ e < 2 ^ 8 ∧ m < 2 ^ 23 ∧ magOf32 e m = g := by
  have h255 : (2 : Nat) ^ 8 - 1 = 255 := by decide
  have h127 : ((2 ^ (8 - 1) - 1 : Nat) : Int) = 127 := by decide
  cases g with
  | subnorm m0 =>
      simp only [f32Mag] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf32
        rw [if_pos (by omega)]
        rw [hm]
      · exact absurd h (by simp)
  | inf =>
      simp only [f32Mag] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, he, hm⟩ := h
      refine ⟨hs.symm, by omega, by omega, ?_⟩
      unfold magOf32
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  | nan m0 =>
      simp only [f32Mag] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf32
        rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), hm]
      · exact absurd h (by simp)
  | norm m0 e0 =>
      obtain ⟨ei, hei⟩ : ∃ ei : Int, ei = e0 := ⟨e0, rfl⟩
      subst hei
      simp only [f32Mag, f32NormFields] at h
      split at h
      · rename_i hlt
        obtain ⟨hlt1, hlt2, hlt3⟩ := hlt
        have hcast : ((ei + 127).toNat : Int) = ei + 127 := Int.toNat_of_nonneg (by omega)
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        subst hm
        have hcast' : ((e : Nat) : Int) = ei + 127 := by rw [← he]; exact hcast
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf32
        rw [if_neg (by omega), if_neg (by omega), h127]
        congr 1
        show ((e : Nat) : Int) - 127 = ei
        omega
      · exact absurd h (by simp)

theorem f64Mag_spec (sg : Nat) (g : FNMag 64) (s e m : Nat)
    (h : f64Mag sg g = some (s, e, m)) :
    s = sg ∧ e < 2 ^ 11 ∧ m < 2 ^ 52 ∧ magOf64 e m = g := by
  have h2047 : (2 : Nat) ^ 11 - 1 = 2047 := by decide
  have h1023 : ((2 ^ (11 - 1) - 1 : Nat) : Int) = 1023 := by decide
  cases g with
  | subnorm m0 =>
      simp only [f64Mag] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf64
        rw [if_pos (by omega), hm]
      · exact absurd h (by simp)
  | inf =>
      simp only [f64Mag] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, he, hm⟩ := h
      refine ⟨hs.symm, by omega, by omega, ?_⟩
      unfold magOf64
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  | nan m0 =>
      simp only [f64Mag] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf64
        rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), hm]
      · exact absurd h (by simp)
  | norm m0 e0 =>
      obtain ⟨ei, hei⟩ : ∃ ei : Int, ei = e0 := ⟨e0, rfl⟩
      subst hei
      simp only [f64Mag, f64NormFields] at h
      split at h
      · rename_i hlt
        obtain ⟨hlt1, hlt2, hlt3⟩ := hlt
        have hcast : ((ei + 1023).toNat : Int) = ei + 1023 :=
          Int.toNat_of_nonneg (by omega)
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, he, hm⟩ := h
        subst hm
        have hcast' : ((e : Nat) : Int) = ei + 1023 := by rw [← he]; exact hcast
        refine ⟨hs.symm, by omega, by omega, ?_⟩
        unfold magOf64
        rw [if_neg (by omega), if_neg (by omega), h1023]
        congr 1
        show ((e : Nat) : Int) - 1023 = ei
        omega
      · exact absurd h (by simp)

/-- `grammar Bf32 : f32`, as an encoder. -/
def encF32 (v : F32) : Option Bytes :=
  (f32Fields v).map (fun p => bytesLE 4 (p.1 * 2 ^ 31 + p.2.1 * 2 ^ 23 + p.2.2))

/-- `grammar Bf64 : f64`, as an encoder. -/
def encF64 (v : F64) : Option Bytes :=
  (f64Fields v).map (fun p => bytesLE 8 (p.1 * 2 ^ 63 + p.2.1 * 2 ^ 52 + p.2.2))

/-- **`grammar Bf32 : f32 = p:BfN(32) => p`.** -/
theorem encF32_Bf32 (v : F32) (bs : Bytes) (h : encF32 v = some bs) : Bf32 bs v := by
  have hdiv : (32 : Nat) / 8 = 4 := by decide
  unfold encF32 at h
  cases hp : f32Fields v with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨s, em⟩ := p
    obtain ⟨e, m⟩ := em
    rw [hp] at h
    injection h with h
    subst h
    have hspec : s < 2 ∧ e < 2 ^ 8 ∧ m < 2 ^ 23 ∧
        (if s = 0 then FN.pos (magOf32 e m) else FN.neg (magOf32 e m)) = v := by
      cases v with
      | pos g =>
          obtain ⟨hs, he, hm, hg⟩ :=
            f32Mag_spec 0 g s e m (by simpa [f32Fields] using hp)
          exact ⟨by omega, he, hm, by rw [if_pos (by omega), hg]⟩
      | neg g =>
          obtain ⟨hs, he, hm, hg⟩ :=
            f32Mag_spec 1 g s e m (by simpa [f32Fields] using hp)
          exact ⟨by omega, he, hm, by rw [if_neg (by omega), hg]⟩
    obtain ⟨hs, he, hm, hv⟩ := hspec
    refine ⟨bytesLE 4 (s * 2 ^ 31 + e * 2 ^ 23 + m), ?_, ?_⟩
    · rw [hdiv, ← bytesLE_length 4 (s * 2 ^ 31 + e * 2 ^ 23 + m)]
      exact Rep_Bbyte _
    · rw [invFbytes32_of s e m hs he hm, hv]

/-- **`grammar Bf64 : f64 = p:BfN(64) => p`.** -/
theorem encF64_Bf64 (v : F64) (bs : Bytes) (h : encF64 v = some bs) : Bf64 bs v := by
  have hdiv : (64 : Nat) / 8 = 8 := by decide
  unfold encF64 at h
  cases hp : f64Fields v with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨s, em⟩ := p
    obtain ⟨e, m⟩ := em
    rw [hp] at h
    injection h with h
    subst h
    have hspec : s < 2 ∧ e < 2 ^ 11 ∧ m < 2 ^ 52 ∧
        (if s = 0 then FN.pos (magOf64 e m) else FN.neg (magOf64 e m)) = v := by
      cases v with
      | pos g =>
          obtain ⟨hs, he, hm, hg⟩ :=
            f64Mag_spec 0 g s e m (by simpa [f64Fields] using hp)
          exact ⟨by omega, he, hm, by rw [if_pos (by omega), hg]⟩
      | neg g =>
          obtain ⟨hs, he, hm, hg⟩ :=
            f64Mag_spec 1 g s e m (by simpa [f64Fields] using hp)
          exact ⟨by omega, he, hm, by rw [if_neg (by omega), hg]⟩
    obtain ⟨hs, he, hm, hv⟩ := hspec
    refine ⟨bytesLE 8 (s * 2 ^ 63 + e * 2 ^ 52 + m), ?_, ?_⟩
    · rw [hdiv, ← bytesLE_length 8 (s * 2 ^ 63 + e * 2 ^ 52 + m)]
      exact Rep_Bbyte _
    · rw [invFbytes64_of s e m hs he hm, hv]


/-! ## Types

`5.2-binary.types.spectec`, production by production.  Each `encX` below is the
right inverse of the corresponding `BX` on exactly the values `BX` can produce;
the `/sem` forms `BOT`, `deftype` and `REC n` are outside every `BX` and get
`none`. -/

/-- `grammar Bnumtype : numtype`. -/
def encNumType : NumType → Bytes
  | .f64 => [tb 0x7C]
  | .f32 => [tb 0x7D]
  | .i64 => [tb 0x7E]
  | .i32 => [tb 0x7F]

theorem encNumType_B (nt : NumType) : Bnumtype (encNumType nt) nt := by
  cases nt <;> constructor

/-- `grammar Bvectype : vectype`. -/
def encVecType : VecType → Bytes
  | .v128 => [tb 0x7B]

theorem encVecType_B (vt : VecType) : Bvectype (encVecType vt) vt := by
  cases vt <;> constructor

/-- `grammar Babsheaptype : heaptype`.  `BOT` is a `/sem` form with no
production. -/
def encAbsHeapType : AbsHeapType → Option Bytes
  | .exn => some [tb 0x69]
  | .array => some [tb 0x6A]
  | .struct => some [tb 0x6B]
  | .i31 => some [tb 0x6C]
  | .eq => some [tb 0x6D]
  | .any => some [tb 0x6E]
  | .extern => some [tb 0x6F]
  | .func => some [tb 0x70]
  | .none => some [tb 0x71]
  | .noextern => some [tb 0x72]
  | .nofunc => some [tb 0x73]
  | .noexn => some [tb 0x74]
  | .bot => Option.none

theorem encAbsHeapType_B (a : AbsHeapType) (bs : Bytes)
    (h : encAbsHeapType a = some bs) : Babsheaptype bs (.abs a) := by
  cases a <;> simp only [encAbsHeapType] at h <;>
    first
      | (injection h with h; subst h; constructor)
      | exact absurd h (by simp)

/-- `grammar Bheaptype : heaptype`. -/
def encHeapType : HeapType → Option Bytes
  | .abs a => encAbsHeapType a
  | .use (.idx x) => some (lebS x.val)
  | .use (.defd _) => Option.none
  | .use (.recu _) => Option.none

theorem encHeapType_B (ht : HeapType) (bs : Bytes)
    (h : encHeapType ht = some bs) : Bheaptype bs ht := by
  cases ht with
  | abs a => exact Bheaptype.abs bs (.abs a) (encAbsHeapType_B a bs h)
  | use tu =>
      cases tu with
      | idx x =>
          simp only [encHeapType] at h
          injection h with h; subst h
          exact Bheaptype.idx (lebS x.val) (x.val : Int) x
            (lebS_Bs33For x.val x.property) (Int.ofNat_nonneg _) rfl
      | defd d => exact absurd h (by simp [encHeapType])
      | recu n => exact absurd h (by simp [encHeapType])

/-- `grammar Breftype : reftype`.  A nullable ABSTRACT heap type takes the
one-byte shorthand, which is the shorter of the two derivations. -/
def encRefType : RefType → Option Bytes
  | .ref (some .null) (.abs a) => encAbsHeapType a
  | .ref (some .null) ht => consO (tb 0x63) (encHeapType ht)
  | .ref Option.none ht => consO (tb 0x64) (encHeapType ht)

theorem encRefType_B (rt : RefType) (bs : Bytes)
    (h : encRefType rt = some bs) : Breftype bs rt := by
  cases rt with
  | ref nul ht =>
      cases nul with
      | none =>
          simp only [encRefType] at h
          obtain ⟨a, ha, hbs⟩ := consO_eq h
          subst hbs
          exact Breftype.nonNull a ht (encHeapType_B ht a ha)
      | some nl =>
          cases nl
          cases ht with
          | abs a =>
              simp only [encRefType] at h
              exact Breftype.abs bs (.abs a) (encAbsHeapType_B a bs h)
          | use tu =>
              simp only [encRefType] at h
              obtain ⟨a, ha, hbs⟩ := consO_eq h
              subst hbs
              exact Breftype.null a (.use tu) (encHeapType_B _ a ha)

/-- `grammar Bvaltype : valtype`.  `BOT` is a `/sem` form with no production. -/
def encValType : ValType → Option Bytes
  | .num nt => some (encNumType nt)
  | .vec vt => some (encVecType vt)
  | .ref rt => encRefType rt
  | .bot => Option.none

theorem encValType_B (t : ValType) (bs : Bytes)
    (h : encValType t = some bs) : Bvaltype bs t := by
  cases t with
  | num nt =>
      simp only [encValType] at h; injection h with h; subst h
      exact Bvaltype.num _ nt (encNumType_B nt)
  | vec vt =>
      simp only [encValType] at h; injection h with h; subst h
      exact Bvaltype.vec _ vt (encVecType_B vt)
  | ref rt => exact Bvaltype.ref bs rt (encRefType_B rt bs h)
  | bot => exact absurd h (by simp [encValType])

/-- `grammar Bresulttype : resulttype = | t*:Blist(Bvaltype) => t*`. -/
def encResultType (ts : ValTypes) : Option Bytes := encList encValType ts.toList

theorem encResultType_B (ts : ValTypes) (bs : Bytes)
    (h : encResultType ts = some bs) : Bresulttype bs ts :=
  encList_Blist encValType_B ts.toList bs h

/-- `grammar Bmut : mut?`. -/
def encMut : Option Mut → Bytes
  | Option.none => [tb 0x00]
  | some .mut => [tb 0x01]

theorem encMut_B (mo : Option Mut) : Bmut (encMut mo) mo := by
  cases mo with
  | none => exact Bmut.const
  | some mt => cases mt; exact Bmut.mutable

/-- `grammar Bpacktype : packtype`. -/
def encPackType : PackType → Bytes
  | .i16 => [tb 0x77]
  | .i8 => [tb 0x78]

theorem encPackType_B (pt : PackType) : Bpacktype (encPackType pt) pt := by
  cases pt <;> constructor

/-- `grammar Bstoragetype : storagetype`. -/
def encStorageType : StorageType → Option Bytes
  | .val t => encValType t
  | .pack pt => some (encPackType pt)

theorem encStorageType_B (zt : StorageType) (bs : Bytes)
    (h : encStorageType zt = some bs) : Bstoragetype bs zt := by
  cases zt with
  | val t => exact Bstoragetype.val bs t (encValType_B t bs h)
  | pack pt =>
      simp only [encStorageType] at h; injection h with h; subst h
      exact Bstoragetype.pack _ pt (encPackType_B pt)

/-- `grammar Bfieldtype : fieldtype = | zt:Bstoragetype mut?:Bmut => mut? zt`. -/
def encFieldType : FieldType → Option Bytes
  | .mk mo zt => catO (encStorageType zt) (some (encMut mo))

theorem encFieldType_B (ft : FieldType) (bs : Bytes)
    (h : encFieldType ft = some bs) : Bfieldtype bs ft := by
  cases ft with
  | mk mo zt =>
      simp only [encFieldType] at h
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection hb with hb
      subst hbs; subst hb
      exact Bfieldtype.mk a (encMut mo) zt mo (encStorageType_B zt a ha) (encMut_B mo)

/-- `grammar Bcomptype : comptype`. -/
def encCompType : CompType → Option Bytes
  | .array ft => consO (tb 0x5E) (encFieldType ft)
  | .struct fts => consO (tb 0x5F) (encList encFieldType fts.toList)
  | .func dom cod => consO (tb 0x60) (catO (encResultType dom) (encResultType cod))

theorem encCompType_B (ct : CompType) (bs : Bytes)
    (h : encCompType ct = some bs) : Bcomptype bs ct := by
  cases ct with
  | array ft =>
      simp only [encCompType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      exact Bcomptype.array a ft (encFieldType_B ft a ha)
  | struct fts =>
      simp only [encCompType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      exact Bcomptype.struct a fts (encList_Blist encFieldType_B _ a ha)
  | func dom cod =>
      simp only [encCompType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      obtain ⟨b, c, hb, hc, hab⟩ := catO_eq ha
      subst hab
      exact Bcomptype.func b c dom cod (encResultType_B dom b hb) (encResultType_B cod c hc)

/-- The declared supertypes of a `subtype` as type INDICES; `none` if any of
them is a `/sem` `typeuse`, which the binary format cannot write. -/
def typeIdxsOf : List TypeUse → Option (List TypeIdx)
  | [] => some []
  | .idx x :: rest => (typeIdxsOf rest).map (fun xs => x :: xs)
  | _ :: _ => Option.none

theorem typeIdxsOf_spec : ∀ (tus : List TypeUse) (xs : List TypeIdx),
    typeIdxsOf tus = some xs → tus = xs.map TypeUse.idx
  | [], xs, h => by injection h with h; subst h; rfl
  | .idx x :: rest, xs, h => by
      simp only [typeIdxsOf] at h
      cases hr : typeIdxsOf rest with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some ys =>
          rw [hr] at h
          injection h with h
          subst h
          simp only [List.map_cons, List.cons.injEq, true_and]
          exact typeIdxsOf_spec rest ys hr
  | .defd _ :: _, xs, h => absurd h (by simp [typeIdxsOf])
  | .recu _ :: _, xs, h => absurd h (by simp [typeIdxsOf])

/-- A type index, as a `Bu32`. -/
def encIdx (x : U32) : Option Bytes := some (lebU x.val)

theorem encIdx_B (x : U32) (bs : Bytes) (h : encIdx x = some bs) : Bu32 bs x := by
  injection h with h; subst h; exact encU32_Bu32 x

/-- `grammar Bsubtype : subtype`.  A final subtype with no declared supertype
takes the bare `comptype` shorthand. -/
def encSubType : SubType → Option Bytes
  | .sub (some .final) .nil ct => encCompType ct
  | .sub fin tus ct =>
      match typeIdxsOf tus.toList with
      | some xs =>
          consO (tb (match fin with | some .final => 0x4F | Option.none => 0x50))
            (catO (encList encIdx xs) (encCompType ct))
      | Option.none => Option.none

theorem encSubType_B (st : SubType) (bs : Bytes)
    (h : encSubType st = some bs) : Bsubtype bs st := by
  cases st with
  | sub fin tus ct =>
    match fin, tus with
    | some Final.final, TypeUses.nil =>
        exact Bsubtype.bare bs ct (encCompType_B ct bs h)
    | some Final.final, TypeUses.cons tu tus' =>
        simp only [encSubType] at h
        cases hx : typeIdxsOf (TypeUses.cons tu tus').toList with
        | none => rw [hx] at h; exact absurd h (by simp)
        | some xs =>
            rw [hx] at h
            obtain ⟨a, ha, hbs⟩ := consO_eq h
            subst hbs
            obtain ⟨b, c, hb, hc, hab⟩ := catO_eq ha
            subst hab
            exact Bsubtype.finalSub b c xs _ ct
              (encList_Blist encIdx_B xs b hb) (encCompType_B ct c hc)
              (typeIdxsOf_spec _ xs hx)
    | Option.none, tus' =>
        simp only [encSubType] at h
        cases hx : typeIdxsOf tus'.toList with
        | none => rw [hx] at h; exact absurd h (by simp)
        | some xs =>
            rw [hx] at h
            obtain ⟨a, ha, hbs⟩ := consO_eq h
            subst hbs
            obtain ⟨b, c, hb, hc, hab⟩ := catO_eq ha
            subst hab
            exact Bsubtype.openSub b c xs _ ct
              (encList_Blist encIdx_B xs b hb) (encCompType_B ct c hc)
              (typeIdxsOf_spec _ xs hx)

/-- `grammar Brectype : rectype`.  A singleton recursion group takes the bare
`subtype` shorthand. -/
def encRecType : RecType → Option Bytes
  | .recr (.cons st .nil) => encSubType st
  | .recr sts => consO (tb 0x4E) (encList encSubType sts.toList)

theorem encRecType_B (qt : RecType) (bs : Bytes)
    (h : encRecType qt = some bs) : Brectype bs qt := by
  cases qt with
  | recr sts =>
    match sts with
    | SubTypes.cons st SubTypes.nil =>
        exact Brectype.single bs st (encSubType_B st bs h)
    | SubTypes.nil =>
        simp only [encRecType] at h
        obtain ⟨a, ha, hbs⟩ := consO_eq h
        subst hbs
        exact Brectype.recGroup a SubTypes.nil (encList_Blist encSubType_B _ a ha)
    | SubTypes.cons st (SubTypes.cons st' rest) =>
        simp only [encRecType] at h
        obtain ⟨a, ha, hbs⟩ := consO_eq h
        subst hbs
        exact Brectype.recGroup a _ (encList_Blist encSubType_B _ a ha)

/-! ## External types -/

/-- `grammar Blimits : (addrtype, limits)`. -/
def encLimits (at' : AddrType) (lim : Limits) : Bytes :=
  match at', lim.max with
  | .i32, Option.none => tb 0x00 :: lebU lim.min.val
  | .i32, some m => tb 0x01 :: (lebU lim.min.val ++ lebU m.val)
  | .i64, Option.none => tb 0x04 :: lebU lim.min.val
  | .i64, some m => tb 0x05 :: (lebU lim.min.val ++ lebU m.val)

theorem encLimits_B (at' : AddrType) (lim : Limits) :
    Blimits (encLimits at' lim) (at', lim) := by
  obtain ⟨mn, mx⟩ := lim
  cases at' <;> cases mx
  · exact Blimits.i32Min _ mn (encU64_Bu64 mn)
  · exact Blimits.i32MinMax _ _ mn _ (encU64_Bu64 mn) (encU64_Bu64 _)
  · exact Blimits.i64Min _ mn (encU64_Bu64 mn)
  · exact Blimits.i64MinMax _ _ mn _ (encU64_Bu64 mn) (encU64_Bu64 _)

/-- `grammar Btagtype : tagtype = | 0x00 x:Btypeidx => _IDX x`. -/
def encTagType : TagType → Option Bytes
  | .idx x => some (tb 0x00 :: lebU x.val)
  | _ => Option.none

theorem encTagType_B (jt : TagType) (bs : Bytes)
    (h : encTagType jt = some bs) : Btagtype bs jt := by
  cases jt with
  | idx x =>
      simp only [encTagType] at h; injection h with h; subst h
      exact Btagtype.mk _ x (encU32_Bu32 x)
  | defd d => exact absurd h (by simp [encTagType])
  | recu n => exact absurd h (by simp [encTagType])

/-- `grammar Bglobaltype : globaltype`. -/
def encGlobalType (gt : GlobalType) : Option Bytes :=
  catO (encValType gt.valtype) (some (encMut gt.mutability))

theorem encGlobalType_B (gt : GlobalType) (bs : Bytes)
    (h : encGlobalType gt = some bs) : Bglobaltype bs gt := by
  obtain ⟨mo, t⟩ := gt
  simp only [encGlobalType] at h
  obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
  injection hb with hb
  subst hbs; subst hb
  exact Bglobaltype.mk a (encMut mo) t mo (encValType_B t a ha) (encMut_B mo)

/-- `grammar Bmemtype : memtype = | (at,lim):Blimits => at lim PAGE`. -/
def encMemType (mt : MemType) : Bytes := encLimits mt.addr mt.lim

theorem encMemType_B (mt : MemType) : Bmemtype (encMemType mt) mt := by
  obtain ⟨a, l⟩ := mt
  exact Bmemtype.mk _ a l (encLimits_B a l)

/-- `grammar Btabletype : tabletype`. -/
def encTableType (tt : TableType) : Option Bytes :=
  catO (encRefType tt.elem) (some (encLimits tt.addr tt.lim))

theorem encTableType_B (tt : TableType) (bs : Bytes)
    (h : encTableType tt = some bs) : Btabletype bs tt := by
  obtain ⟨ad, lm, el⟩ := tt
  simp only [encTableType] at h
  obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
  injection hb with hb
  subst hbs; subst hb
  exact Btabletype.mk a _ el ad lm (encRefType_B el a ha) (encLimits_B ad lm)

/-- `grammar Bexterntype : externtype`. -/
def encExternType : ExternType → Option Bytes
  | .func (.idx x) => some (tb 0x00 :: lebU x.val)
  | .func _ => Option.none
  | .table tt => consO (tb 0x01) (encTableType tt)
  | .mem mt => some (tb 0x02 :: encMemType mt)
  | .global gt => consO (tb 0x03) (encGlobalType gt)
  | .tag jt => consO (tb 0x04) (encTagType jt)

theorem encExternType_B (xt : ExternType) (bs : Bytes)
    (h : encExternType xt = some bs) : Bexterntype bs xt := by
  cases xt with
  | func tu =>
      cases tu with
      | idx x =>
          simp only [encExternType] at h; injection h with h; subst h
          exact Bexterntype.func _ x (encU32_Bu32 x)
      | defd d => exact absurd h (by simp [encExternType])
      | recu n => exact absurd h (by simp [encExternType])
  | table tt =>
      simp only [encExternType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      exact Bexterntype.table a tt (encTableType_B tt a ha)
  | mem mt =>
      simp only [encExternType] at h; injection h with h; subst h
      exact Bexterntype.mem _ mt (encMemType_B mt)
  | global gt =>
      simp only [encExternType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      exact Bexterntype.global a gt (encGlobalType_B gt a ha)
  | tag jt =>
      simp only [encExternType] at h
      obtain ⟨a, ha, hbs⟩ := consO_eq h
      subst hbs
      exact Bexterntype.tag a jt (encTagType_B jt a ha)


/-! ## Instruction operands

`5.3-binary.instructions.spectec`: `Bblocktype`, `Bcatch`, `Bmemarg` and
`Bcastop`. -/

/-- Alternation of two optional byte sequences: the instruction encoder is the
union of its fragments, exactly as `Binstr` is.  When both alternatives happen
to accept the same abstract instruction, retain the shorter encoding; this
makes length completeness compositional across the grammar union. -/
def orO : Option Bytes → Option Bytes → Option Bytes
  | Option.none, y => y
  | some a, Option.none => some a
  | some a, some b => if a.length ≤ b.length then some a else some b

theorem orO_eq {x y : Option Bytes} {bs : Bytes} (h : orO x y = some bs) :
    x = some bs ∨ y = some bs := by
  cases x with
  | none => exact Or.inr h
  | some a =>
      cases y with
      | none => exact Or.inl h
      | some b =>
          simp only [orO] at h
          split at h
          · injection h with h; subst h; exact Or.inl rfl
          · injection h with h; subst h; exact Or.inr rfl

/-- `grammar Bblocktype : blocktype`. -/
def encBlockType : BlockType → Option Bytes
  | .result Option.none => some [tb 0x40]
  | .result (some t) => encValType t
  | .idx x => some (lebS x.val)

theorem encBlockType_B (bt : BlockType) (bs : Bytes)
    (h : encBlockType bt = some bs) : Bblocktype bs bt := by
  cases bt with
  | result to =>
      cases to with
      | none =>
          simp only [encBlockType] at h; injection h with h; subst h
          exact Bblocktype.empty
      | some t => exact Bblocktype.val bs t (encValType_B t bs h)
  | idx x =>
      simp only [encBlockType] at h; injection h with h; subst h
      exact Bblocktype.idx _ (x.val : Int) x (lebS_Bs33For x.val x.property)
        (Int.ofNat_nonneg _) rfl

/-- `grammar Bcatch : catch`. -/
def encCatch : Catch → Option Bytes
  | .tag x l => some (tb 0x00 :: (lebU x.val ++ lebU l.val))
  | .tagRef x l => some (tb 0x01 :: (lebU x.val ++ lebU l.val))
  | .all l => some (tb 0x02 :: lebU l.val)
  | .allRef l => some (tb 0x03 :: lebU l.val)

theorem encCatch_B (c : Catch) (bs : Bytes) (h : encCatch c = some bs) :
    Bcatch bs c := by
  cases c <;> simp only [encCatch] at h <;>
    (injection h with h; subst h; constructor <;> exact encU32_Bu32 _)

/-- `grammar Bmemarg : memidxop`.  The alignment doubles as the discriminator
and is stored in six bits, so an alignment `>= 2^6` has no derivation. -/
def encMemArg (x : MemIdx) (ao : MemArg) : Option Bytes :=
  if ao.align.val < 2 ^ 6 then
    if x.val = 0 then some (lebU ao.align.val ++ lebU ao.offset.val)
    else some (lebU (ao.align.val + 2 ^ 6) ++ lebU x.val ++ lebU ao.offset.val)
  else Option.none

theorem encMemArg_B (x : MemIdx) (ao : MemArg) (bs : Bytes)
    (h : encMemArg x ao = some bs) : Bmemarg bs (x, ao) := by
  unfold encMemArg at h
  split at h
  · rename_i hal
    split at h
    · rename_i hx
      injection h with h; subst h
      exact Bmemarg.mem0 _ _ ao.align ao.offset x (encU32_Bu32 _) (encU32_Bu32 _) hal hx
    · rename_i hx
      injection h with h; subst h
      have hb : ao.align.val + 2 ^ 6 < 2 ^ 32 := by
        have h6 : (2 : Nat) ^ 6 = 64 := by decide
        have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
        omega
      exact Bmemarg.memx _ _ _ ⟨ao.align.val + 2 ^ 6, hb⟩ ao.align ao.offset x
        (encU32_Bu32 ⟨ao.align.val + 2 ^ 6, hb⟩) (encU32_Bu32 x) (encU32_Bu32 _)
        (by simp) (by simp; omega) (by simp)
  · exact absurd h (by simp)

/-- `grammar Bcastop : castop`. -/
def encCastOp : Option Null → Option Null → Bytes
  | Option.none, Option.none => [tb 0x00]
  | some .null, Option.none => [tb 0x01]
  | Option.none, some .null => [tb 0x02]
  | some .null, some .null => [tb 0x03]

theorem encCastOp_B (n1 n2 : Option Null) : Bcastop (encCastOp n1 n2) (n1, n2) := by
  cases n1 with
  | none =>
      cases n2 with
      | none => exact Bcastop.nn
      | some b => cases b; exact Bcastop.ny
  | some a =>
      cases a
      cases n2 with
      | none => exact Bcastop.yn
      | some b => cases b; exact Bcastop.yy

/-! ## The instruction fragments that do not recur into `Binstr` -/

/-- `grammar Binstr/parametric : instr`. -/
def encInstrParam : Instr → Option Bytes
  | .unreachable => some [tb 0x00]
  | .nop => some [tb 0x01]
  | .drop => some [tb 0x1A]
  | .select Option.none => some [tb 0x1B]
  | .select (some ts) => consO (tb 0x1C) (encList encValType ts)
  | _ => Option.none

theorem encInstrParam_B (i : Instr) (bs : Bytes)
    (h : encInstrParam i = some bs) : BinstrParametric bs i := by
  unfold encInstrParam at h
  split at h
  · injection h with h; subst h; exact BinstrParametric.unreachable
  · injection h with h; subst h; exact BinstrParametric.nop
  · injection h with h; subst h; exact BinstrParametric.drop
  · injection h with h; subst h; exact BinstrParametric.select
  · rename_i ts
    obtain ⟨a, ha, hbs⟩ := consO_eq h
    subst hbs
    exact BinstrParametric.selectT a ts (encList_Blist encValType_B ts a ha)
  · exact absurd h (by simp)

/-- The authority-independent, non-recursive control alternatives. -/
def encInstrCtlBase : Instr → Option Bytes
  | .throw x => some (tb 0x08 :: lebU x.val)
  | .throwRef => some [tb 0x0A]
  | .br l => some (tb 0x0C :: lebU l.val)
  | .brIf l => some (tb 0x0D :: lebU l.val)
  | .brTable ls l => consO (tb 0x0E) (catO (encList encIdx ls) (some (lebU l.val)))
  | .ret => some [tb 0x0F]
  | .call x => some (tb 0x10 :: lebU x.val)
  | .callIndirect x (.idx y) => some (tb 0x11 :: (lebU y.val ++ lebU x.val))
  | .returnCall x => some (tb 0x12 :: lebU x.val)
  | .returnCallIndirect x (.idx y) => some (tb 0x13 :: (lebU y.val ++ lebU x.val))
  | _ => Option.none

/-- The two typed-reference call alternatives selected only by the amended
binary authority. -/
def encInstrCtlAmended : Instr → Option Bytes
  | .callRef (.idx x) =>
      match authority.revision with
      | .pinned => Option.none
      | .amended => some (tb 0x14 :: lebU x.val)
  | .returnCallRef (.idx x) =>
      match authority.revision with
      | .pinned => Option.none
      | .amended => some (tb 0x15 :: lebU x.val)
  | _ => Option.none

/-- `grammar Binstr/control : instr`, the alternatives that do not recur. -/
def encInstrCtl (i : Instr) : Option Bytes :=
  orO (encInstrCtlBase i) (encInstrCtlAmended i)

theorem encInstrCtlBase_B (i : Instr) (bs : Bytes)
    (h : encInstrCtlBase i = some bs) : BinstrControl bs i := by
  unfold encInstrCtlBase at h
  split at h
  · injection h with h; subst h; exact BinstrControl.throw _ _ (encU32_Bu32 _)
  · injection h with h; subst h; exact BinstrControl.throwRef
  · injection h with h; subst h; exact BinstrControl.br _ _ (encU32_Bu32 _)
  · injection h with h; subst h; exact BinstrControl.brIf _ _ (encU32_Bu32 _)
  · rename_i ls l
    obtain ⟨a, ha, hbs⟩ := consO_eq h
    subst hbs
    obtain ⟨b, c, hb, hc, hab⟩ := catO_eq ha
    injection hc with hc
    subst hab; subst hc
    exact BinstrControl.brTable b _ ls l (encList_Blist encIdx_B ls b hb) (encU32_Bu32 l)
  · injection h with h; subst h; exact BinstrControl.ret
  · injection h with h; subst h; exact BinstrControl.call _ _ (encU32_Bu32 _)
  · injection h with h; subst h
    exact BinstrControl.callIndirect _ _ _ _ (encU32_Bu32 _) (encU32_Bu32 _)
  · injection h with h; subst h; exact BinstrControl.returnCall _ _ (encU32_Bu32 _)
  · injection h with h; subst h
    exact BinstrControl.returnCallIndirect _ _ _ _ (encU32_Bu32 _) (encU32_Bu32 _)
  · exact absurd h (by simp)

theorem encInstrCtlAmended_B (i : Instr) (bs : Bytes)
    (h : encInstrCtlAmended i = some bs) : BinstrControlFor bs i := by
  unfold encInstrCtlAmended at h
  split at h
  · rename_i x
    cases authority with
    | mk revision =>
        cases revision with
        | pinned => exact absurd h (by simp)
        | amended =>
            injection h with h
            subst h
            exact BinstrControlFor.callRef (encU32_Bu32 x)
  · rename_i x
    cases authority with
    | mk revision =>
        cases revision with
        | pinned => exact absurd h (by simp)
        | amended =>
            injection h with h
            subst h
            exact BinstrControlFor.returnCallRef (encU32_Bu32 x)
  · exact absurd h (by simp)

theorem encInstrCtl_B (i : Instr) (bs : Bytes)
    (h : encInstrCtl i = some bs) : BinstrControlFor bs i := by
  rcases orO_eq h with h | h
  · exact BinstrControlFor.ofPinned (encInstrCtlBase_B i bs h)
  · exact encInstrCtlAmended_B i bs h

/-- `grammar Binstr/local : instr`. -/
def encInstrLoc : Instr → Option Bytes
  | .localGet x => some (tb 0x20 :: lebU x.val)
  | .localSet x => some (tb 0x21 :: lebU x.val)
  | .localTee x => some (tb 0x22 :: lebU x.val)
  | _ => Option.none

theorem encInstrLoc_B (i : Instr) (bs : Bytes)
    (h : encInstrLoc i = some bs) : BinstrLocal bs i := by
  unfold encInstrLoc at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor <;> exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/global : instr`. -/
def encInstrGlob : Instr → Option Bytes
  | .globalGet x => some (tb 0x23 :: lebU x.val)
  | .globalSet x => some (tb 0x24 :: lebU x.val)
  | _ => Option.none

theorem encInstrGlob_B (i : Instr) (bs : Bytes)
    (h : encInstrGlob i = some bs) : BinstrGlobal bs i := by
  unfold encInstrGlob at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor <;> exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/table : instr`.  `TABLE.INIT` takes the ELEMENT index
first, as the pinned source writes it. -/
def encInstrTbl : Instr → Option Bytes
  | .tableGet x => some (tb 0x25 :: lebU x.val)
  | .tableSet x => some (tb 0x26 :: lebU x.val)
  | .tableInit x y => some (pre 0xFC 12 ++ lebU y.val ++ lebU x.val)
  | .elemDrop x => some (pre 0xFC 13 ++ lebU x.val)
  | .tableCopy x y => some (pre 0xFC 14 ++ lebU x.val ++ lebU y.val)
  | .tableGrow x => some (pre 0xFC 15 ++ lebU x.val)
  | .tableSize x => some (pre 0xFC 16 ++ lebU x.val)
  | .tableFill x => some (pre 0xFC 17 ++ lebU x.val)
  | _ => Option.none

theorem encInstrTbl_B (i : Instr) (bs : Bytes)
    (h : encInstrTbl i = some bs) : BinstrTable bs i := by
  unfold encInstrTbl at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor <;>
          first
            | exact pre_Bprefixed _ _ (by decide)
            | exact encU32_Bu32 _)
      | exact absurd h (by simp)


/-- `grammar Binstr/memory : instr`. -/
def encInstrMem : Instr → Option Bytes
  | .load .i32 Option.none x ao => consO (tb 0x28) (encMemArg x ao)
  | .load .i64 Option.none x ao => consO (tb 0x29) (encMemArg x ao)
  | .load .f32 Option.none x ao => consO (tb 0x2A) (encMemArg x ao)
  | .load .f64 Option.none x ao => consO (tb 0x2B) (encMemArg x ao)
  | .load .i32 (some { sz := .s8, sx := .s }) x ao => consO (tb 0x2C) (encMemArg x ao)
  | .load .i32 (some { sz := .s8, sx := .u }) x ao => consO (tb 0x2D) (encMemArg x ao)
  | .load .i32 (some { sz := .s16, sx := .s }) x ao => consO (tb 0x2E) (encMemArg x ao)
  | .load .i32 (some { sz := .s16, sx := .u }) x ao => consO (tb 0x2F) (encMemArg x ao)
  | .load .i64 (some { sz := .s8, sx := .s }) x ao => consO (tb 0x30) (encMemArg x ao)
  | .load .i64 (some { sz := .s8, sx := .u }) x ao => consO (tb 0x31) (encMemArg x ao)
  | .load .i64 (some { sz := .s16, sx := .s }) x ao => consO (tb 0x32) (encMemArg x ao)
  | .load .i64 (some { sz := .s16, sx := .u }) x ao => consO (tb 0x33) (encMemArg x ao)
  | .load .i64 (some { sz := .s32, sx := .s }) x ao => consO (tb 0x34) (encMemArg x ao)
  | .load .i64 (some { sz := .s32, sx := .u }) x ao => consO (tb 0x35) (encMemArg x ao)
  | .store .i32 Option.none x ao => consO (tb 0x36) (encMemArg x ao)
  | .store .i64 Option.none x ao => consO (tb 0x37) (encMemArg x ao)
  | .store .f32 Option.none x ao => consO (tb 0x38) (encMemArg x ao)
  | .store .f64 Option.none x ao => consO (tb 0x39) (encMemArg x ao)
  | .store .i32 (some { sz := .s8 }) x ao => consO (tb 0x3A) (encMemArg x ao)
  | .store .i32 (some { sz := .s16 }) x ao => consO (tb 0x3B) (encMemArg x ao)
  | .store .i64 (some { sz := .s8 }) x ao => consO (tb 0x3C) (encMemArg x ao)
  | .store .i64 (some { sz := .s16 }) x ao => consO (tb 0x3D) (encMemArg x ao)
  | .store .i64 (some { sz := .s32 }) x ao => consO (tb 0x3E) (encMemArg x ao)
  | .memorySize x => some (tb 0x3F :: lebU x.val)
  | .memoryGrow x => some (tb 0x40 :: lebU x.val)
  | .memoryInit x y => some (pre 0xFC 8 ++ lebU y.val ++ lebU x.val)
  | .dataDrop x => some (pre 0xFC 9 ++ lebU x.val)
  | .memoryCopy x y => some (pre 0xFC 10 ++ lebU x.val ++ lebU y.val)
  | .memoryFill x => some (pre 0xFC 11 ++ lebU x.val)
  | _ => Option.none

theorem encInstrMem_B (i : Instr) (bs : Bytes)
    (h : encInstrMem i = some bs) : BinstrMemory bs i := by
  unfold encInstrMem at h
  split at h <;>
    first
      | (obtain ⟨a, ha, hbs⟩ := consO_eq h; subst hbs; constructor
         exact encMemArg_B _ _ _ ha)
      | (injection h with h; subst h; constructor <;>
          first
            | exact pre_Bprefixed _ _ (by decide)
            | exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/ref : instr`. -/
def encInstrRef : Instr → Option Bytes
  | .refNull ht => consO (tb 0xD0) (encHeapType ht)
  | .refIsNull => some [tb 0xD1]
  | .refFunc x => some (tb 0xD2 :: lebU x.val)
  | .refEq => some [tb 0xD3]
  | .refAsNonNull => some [tb 0xD4]
  | .brOnNull l => some (tb 0xD5 :: lebU l.val)
  | .brOnNonNull l => some (tb 0xD6 :: lebU l.val)
  | _ => Option.none

theorem encInstrRef_B (i : Instr) (bs : Bytes)
    (h : encInstrRef i = some bs) : BinstrRef bs i := by
  unfold encInstrRef at h
  split at h <;>
    first
      | (obtain ⟨a, ha, hbs⟩ := consO_eq h; subst hbs; constructor
         exact encHeapType_B _ _ ha)
      | (injection h with h; subst h; constructor <;> exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/struct : instr`. -/
def encInstrStr : Instr → Option Bytes
  | .structNew x => some (pre 0xFB 0 ++ lebU x.val)
  | .structNewDefault x => some (pre 0xFB 1 ++ lebU x.val)
  | .structGet Option.none x i => some (pre 0xFB 2 ++ lebU x.val ++ lebU i.val)
  | .structGet (some .s) x i => some (pre 0xFB 3 ++ lebU x.val ++ lebU i.val)
  | .structGet (some .u) x i => some (pre 0xFB 4 ++ lebU x.val ++ lebU i.val)
  | .structSet x i => some (pre 0xFB 5 ++ lebU x.val ++ lebU i.val)
  | _ => Option.none

theorem encInstrStr_B (i : Instr) (bs : Bytes)
    (h : encInstrStr i = some bs) : BinstrStruct bs i := by
  unfold encInstrStr at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor <;>
          first
            | exact pre_Bprefixed _ _ (by decide)
            | exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/array : instr`. -/
def encInstrArr : Instr → Option Bytes
  | .arrayNew x => some (pre 0xFB 6 ++ lebU x.val)
  | .arrayNewDefault x => some (pre 0xFB 7 ++ lebU x.val)
  | .arrayNewFixed x n => some (pre 0xFB 8 ++ lebU x.val ++ lebU n.val)
  | .arrayNewData x y => some (pre 0xFB 9 ++ lebU x.val ++ lebU y.val)
  | .arrayNewElem x y => some (pre 0xFB 10 ++ lebU x.val ++ lebU y.val)
  | .arrayGet Option.none x => some (pre 0xFB 11 ++ lebU x.val)
  | .arrayGet (some .s) x => some (pre 0xFB 12 ++ lebU x.val)
  | .arrayGet (some .u) x => some (pre 0xFB 13 ++ lebU x.val)
  | .arraySet x => some (pre 0xFB 14 ++ lebU x.val)
  | .arrayLen => some (pre 0xFB 15)
  | .arrayFill x => some (pre 0xFB 16 ++ lebU x.val)
  | .arrayCopy x y => some (pre 0xFB 17 ++ lebU x.val ++ lebU y.val)
  | .arrayInitData x y => some (pre 0xFB 18 ++ lebU x.val ++ lebU y.val)
  | .arrayInitElem x y => some (pre 0xFB 19 ++ lebU x.val ++ lebU y.val)
  | _ => Option.none

theorem encInstrArr_B (i : Instr) (bs : Bytes)
    (h : encInstrArr i = some bs) : BinstrArray bs i := by
  unfold encInstrArr at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor <;>
          first
            | exact pre_Bprefixed _ _ (by decide)
            | exact encU32_Bu32 _)
      | exact absurd h (by simp)

/-- `grammar Binstr/cast : instr`. -/
def encInstrCast : Instr → Option Bytes
  | .refTest (.ref Option.none ht) => catO (some (pre 0xFB 20)) (encHeapType ht)
  | .refTest (.ref (some .null) ht) => catO (some (pre 0xFB 21)) (encHeapType ht)
  | .refCast (.ref Option.none ht) => catO (some (pre 0xFB 22)) (encHeapType ht)
  | .refCast (.ref (some .null) ht) => catO (some (pre 0xFB 23)) (encHeapType ht)
  | .brOnCast l (.ref n1 ht1) (.ref n2 ht2) =>
      catO (catO (catO (catO (some (pre 0xFB 24)) (some (encCastOp n1 n2)))
        (some (lebU l.val))) (encHeapType ht1)) (encHeapType ht2)
  | .brOnCastFail l (.ref n1 ht1) (.ref n2 ht2) =>
      catO (catO (catO (catO (some (pre 0xFB 25)) (some (encCastOp n1 n2)))
        (some (lebU l.val))) (encHeapType ht1)) (encHeapType ht2)
  | _ => Option.none

theorem encInstrCast_B (i : Instr) (bs : Bytes)
    (h : encInstrCast i = some bs) : BinstrCast bs i := by
  unfold encInstrCast at h
  split at h
  case _ ht =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection ha with ha; subst hbs; subst ha
      exact BinstrCast.test _ b ht (pre_Bprefixed _ _ (by decide)) (encHeapType_B ht b hb)
  case _ ht =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection ha with ha; subst hbs; subst ha
      exact BinstrCast.testNull _ b ht (pre_Bprefixed _ _ (by decide))
        (encHeapType_B ht b hb)
  case _ ht =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection ha with ha; subst hbs; subst ha
      exact BinstrCast.cast _ b ht (pre_Bprefixed _ _ (by decide)) (encHeapType_B ht b hb)
  case _ ht =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection ha with ha; subst hbs; subst ha
      exact BinstrCast.castNull _ b ht (pre_Bprefixed _ _ (by decide))
        (encHeapType_B ht b hb)
  case _ l n1 ht1 n2 ht2 =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      subst hbs
      obtain ⟨c, d, hc, hd, hcd⟩ := catO_eq ha
      subst hcd
      obtain ⟨e, f, he, hf, hef⟩ := catO_eq hc
      subst hef
      obtain ⟨g, k, hg, hk, hgk⟩ := catO_eq he
      injection hg with hg; injection hk with hk; injection hf with hf
      subst hgk; subst hg; subst hk; subst hf
      exact BinstrCast.brOnCast _ _ _ d b n1 n2 l ht1 ht2
        (pre_Bprefixed _ _ (by decide)) (encCastOp_B n1 n2) (encU32_Bu32 l)
        (encHeapType_B ht1 d hd) (encHeapType_B ht2 b hb)
  case _ l n1 ht1 n2 ht2 =>
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      subst hbs
      obtain ⟨c, d, hc, hd, hcd⟩ := catO_eq ha
      subst hcd
      obtain ⟨e, f, he, hf, hef⟩ := catO_eq hc
      subst hef
      obtain ⟨g, k, hg, hk, hgk⟩ := catO_eq he
      injection hg with hg; injection hk with hk; injection hf with hf
      subst hgk; subst hg; subst hk; subst hf
      exact BinstrCast.brOnCastFail _ _ _ d b n1 n2 l ht1 ht2
        (pre_Bprefixed _ _ (by decide)) (encCastOp_B n1 n2) (encU32_Bu32 l)
        (encHeapType_B ht1 d hd) (encHeapType_B ht2 b hb)
  case _ => exact absurd h (by simp)

/-- `grammar Binstr/extern : instr`. -/
def encInstrExt : Instr → Option Bytes
  | .anyConvertExtern => some (pre 0xFB 26)
  | .externConvertAny => some (pre 0xFB 27)
  | _ => Option.none

theorem encInstrExt_B (i : Instr) (bs : Bytes)
    (h : encInstrExt i = some bs) : BinstrExtern bs i := by
  unfold encInstrExt at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor
         exact pre_Bprefixed _ _ (by decide))
      | exact absurd h (by simp)

/-- `grammar Binstr/i31 : instr`. -/
def encInstrI31 : Instr → Option Bytes
  | .refI31 => some (pre 0xFB 28)
  | .i31Get .s => some (pre 0xFB 29)
  | .i31Get .u => some (pre 0xFB 30)
  | _ => Option.none

theorem encInstrI31_B (i : Instr) (bs : Bytes)
    (h : encInstrI31 i = some bs) : BinstrI31 bs i := by
  unfold encInstrI31 at h
  split at h <;>
    first
      | (injection h with h; subst h; constructor
         exact pre_Bprefixed _ _ (by decide))
      | exact absurd h (by simp)

/-- The numeric fragments, the alternatives that carry an immediate. -/
def encInstrNumC : Instr → Option Bytes
  | .const .i32 n => some (tb 0x41 :: lebU n.val)
  | .const .i64 n => some (tb 0x42 :: lebU n.val)
  | .const .f32 p => consO (tb 0x43) (encF32 p)
  | .const .f64 p => consO (tb 0x44) (encF64 p)
  | .cvtop .i32 .f32 (.fi (.truncSat .s)) => some (pre 0xFC 0)
  | .cvtop .i32 .f32 (.fi (.truncSat .u)) => some (pre 0xFC 1)
  | .cvtop .i32 .f64 (.fi (.truncSat .s)) => some (pre 0xFC 2)
  | .cvtop .i32 .f64 (.fi (.truncSat .u)) => some (pre 0xFC 3)
  | .cvtop .i64 .f32 (.fi (.truncSat .s)) => some (pre 0xFC 4)
  | .cvtop .i64 .f32 (.fi (.truncSat .u)) => some (pre 0xFC 5)
  | .cvtop .i64 .f64 (.fi (.truncSat .s)) => some (pre 0xFC 6)
  | .cvtop .i64 .f64 (.fi (.truncSat .u)) => some (pre 0xFC 7)
  | _ => Option.none

theorem encInstrNumC_B (i : Instr) (bs : Bytes)
    (h : encInstrNumC i = some bs) : BinstrNum bs i := by
  unfold encInstrNumC at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32Const _ _ (encU32_Bu32 _)
  · injection h with h; subst h; exact BinstrNum.i64Const _ _ (encU64_Bu64 _)
  · obtain ⟨a, ha, hbs⟩ := consO_eq h; subst hbs
    exact BinstrNum.f32Const a _ (encF32_Bf32 _ a ha)
  · obtain ⟨a, ha, hbs⟩ := consO_eq h; subst hbs
    exact BinstrNum.f64Const a _ (encF64_Bf64 _ a ha)
  · injection h with h; subst h
    exact BinstrNum.i32TruncSatF32S _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i32TruncSatF32U _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i32TruncSatF64S _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i32TruncSatF64U _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i64TruncSatF32S _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i64TruncSatF32U _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i64TruncSatF64S _ (pre_Bprefixed _ _ (by decide))
  · injection h with h; subst h
    exact BinstrNum.i64TruncSatF64U _ (pre_Bprefixed _ _ (by decide))
  · exact absurd h (by simp)

/-- The `.testop` alternatives of `grammar Binstr/num-*`. -/
def encTestopN : NumType → Testop → Option Bytes
  | .i32, (.int .eqz) => some [tb 0x45]
  | .i64, (.int .eqz) => some [tb 0x50]
  | _, _ => Option.none

theorem encTestopN_B (nt : NumType) (op : Testop) (bs : Bytes)
    (h : encTestopN nt op = some bs) : BinstrNum bs (.testop nt op) := by
  unfold encTestopN at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32Eqz
  · injection h with h; subst h; exact BinstrNum.i64Eqz
  · exact absurd h (by simp)

/-- The `.relop` alternatives of `grammar Binstr/num-*`. -/
def encRelopN : NumType → Relop → Option Bytes
  | .i32, (.int .eq) => some [tb 0x46]
  | .i32, (.int .ne) => some [tb 0x47]
  | .i32, (.int (.lt .s)) => some [tb 0x48]
  | .i32, (.int (.lt .u)) => some [tb 0x49]
  | .i32, (.int (.gt .s)) => some [tb 0x4A]
  | .i32, (.int (.gt .u)) => some [tb 0x4B]
  | .i32, (.int (.le .s)) => some [tb 0x4C]
  | .i32, (.int (.le .u)) => some [tb 0x4D]
  | .i32, (.int (.ge .s)) => some [tb 0x4E]
  | .i32, (.int (.ge .u)) => some [tb 0x4F]
  | .i64, (.int .eq) => some [tb 0x51]
  | .i64, (.int .ne) => some [tb 0x52]
  | .i64, (.int (.lt .s)) => some [tb 0x53]
  | .i64, (.int (.lt .u)) => some [tb 0x54]
  | .i64, (.int (.gt .s)) => some [tb 0x55]
  | .i64, (.int (.gt .u)) => some [tb 0x56]
  | .i64, (.int (.le .s)) => some [tb 0x57]
  | .i64, (.int (.le .u)) => some [tb 0x58]
  | .i64, (.int (.ge .s)) => some [tb 0x59]
  | .i64, (.int (.ge .u)) => some [tb 0x5A]
  | .f32, (.float .eq) => some [tb 0x5B]
  | .f32, (.float .ne) => some [tb 0x5C]
  | .f32, (.float .lt) => some [tb 0x5D]
  | .f32, (.float .gt) => some [tb 0x5E]
  | .f32, (.float .le) => some [tb 0x5F]
  | .f32, (.float .ge) => some [tb 0x60]
  | .f64, (.float .eq) => some [tb 0x61]
  | .f64, (.float .ne) => some [tb 0x62]
  | .f64, (.float .lt) => some [tb 0x63]
  | .f64, (.float .gt) => some [tb 0x64]
  | .f64, (.float .le) => some [tb 0x65]
  | .f64, (.float .ge) => some [tb 0x66]
  | _, _ => Option.none

theorem encRelopN_B (nt : NumType) (op : Relop) (bs : Bytes)
    (h : encRelopN nt op = some bs) : BinstrNum bs (.relop nt op) := by
  unfold encRelopN at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32Eq
  · injection h with h; subst h; exact BinstrNum.i32Ne
  · injection h with h; subst h; exact BinstrNum.i32LtS
  · injection h with h; subst h; exact BinstrNum.i32LtU
  · injection h with h; subst h; exact BinstrNum.i32GtS
  · injection h with h; subst h; exact BinstrNum.i32GtU
  · injection h with h; subst h; exact BinstrNum.i32LeS
  · injection h with h; subst h; exact BinstrNum.i32LeU
  · injection h with h; subst h; exact BinstrNum.i32GeS
  · injection h with h; subst h; exact BinstrNum.i32GeU
  · injection h with h; subst h; exact BinstrNum.i64Eq
  · injection h with h; subst h; exact BinstrNum.i64Ne
  · injection h with h; subst h; exact BinstrNum.i64LtS
  · injection h with h; subst h; exact BinstrNum.i64LtU
  · injection h with h; subst h; exact BinstrNum.i64GtS
  · injection h with h; subst h; exact BinstrNum.i64GtU
  · injection h with h; subst h; exact BinstrNum.i64LeS
  · injection h with h; subst h; exact BinstrNum.i64LeU
  · injection h with h; subst h; exact BinstrNum.i64GeS
  · injection h with h; subst h; exact BinstrNum.i64GeU
  · injection h with h; subst h; exact BinstrNum.f32Eq
  · injection h with h; subst h; exact BinstrNum.f32Ne
  · injection h with h; subst h; exact BinstrNum.f32Lt
  · injection h with h; subst h; exact BinstrNum.f32Gt
  · injection h with h; subst h; exact BinstrNum.f32Le
  · injection h with h; subst h; exact BinstrNum.f32Ge
  · injection h with h; subst h; exact BinstrNum.f64Eq
  · injection h with h; subst h; exact BinstrNum.f64Ne
  · injection h with h; subst h; exact BinstrNum.f64Lt
  · injection h with h; subst h; exact BinstrNum.f64Gt
  · injection h with h; subst h; exact BinstrNum.f64Le
  · injection h with h; subst h; exact BinstrNum.f64Ge
  · exact absurd h (by simp)

/-- The `.unop` alternatives of `grammar Binstr/num-*`. -/
def encUnopN : NumType → Unop → Option Bytes
  | .i32, (.int .clz) => some [tb 0x67]
  | .i32, (.int .ctz) => some [tb 0x68]
  | .i32, (.int .popcnt) => some [tb 0x69]
  | .i64, (.int .clz) => some [tb 0x79]
  | .i64, (.int .ctz) => some [tb 0x7A]
  | .i64, (.int .popcnt) => some [tb 0x7B]
  | .i32, (.int (.extend .s8)) => some [tb 0xC0]
  | .i32, (.int (.extend .s16)) => some [tb 0xC1]
  | .i64, (.int (.extend .s8)) => some [tb 0xC2]
  | .i64, (.int (.extend .s16)) => some [tb 0xC3]
  | .i64, (.int (.extend .s32)) => some [tb 0xC4]
  | .f32, (.float .abs) => some [tb 0x8B]
  | .f32, (.float .neg) => some [tb 0x8C]
  | .f32, (.float .ceil) => some [tb 0x8D]
  | .f32, (.float .floor) => some [tb 0x8E]
  | .f32, (.float .trunc) => some [tb 0x8F]
  | .f32, (.float .nearest) => some [tb 0x90]
  | .f32, (.float .sqrt) => some [tb 0x91]
  | .f64, (.float .abs) => some [tb 0x99]
  | .f64, (.float .neg) => some [tb 0x9A]
  | .f64, (.float .ceil) => some [tb 0x9B]
  | .f64, (.float .floor) => some [tb 0x9C]
  | .f64, (.float .trunc) => some [tb 0x9D]
  | .f64, (.float .nearest) => some [tb 0x9E]
  | .f64, (.float .sqrt) => some [tb 0x9F]
  | _, _ => Option.none

theorem encUnopN_B (nt : NumType) (op : Unop) (bs : Bytes)
    (h : encUnopN nt op = some bs) : BinstrNum bs (.unop nt op) := by
  unfold encUnopN at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32Clz
  · injection h with h; subst h; exact BinstrNum.i32Ctz
  · injection h with h; subst h; exact BinstrNum.i32Popcnt
  · injection h with h; subst h; exact BinstrNum.i64Clz
  · injection h with h; subst h; exact BinstrNum.i64Ctz
  · injection h with h; subst h; exact BinstrNum.i64Popcnt
  · injection h with h; subst h; exact BinstrNum.i32Extend8
  · injection h with h; subst h; exact BinstrNum.i32Extend16
  · injection h with h; subst h; exact BinstrNum.i64Extend8
  · injection h with h; subst h; exact BinstrNum.i64Extend16
  · injection h with h; subst h; exact BinstrNum.i64Extend32
  · injection h with h; subst h; exact BinstrNum.f32Abs
  · injection h with h; subst h; exact BinstrNum.f32Neg
  · injection h with h; subst h; exact BinstrNum.f32Ceil
  · injection h with h; subst h; exact BinstrNum.f32Floor
  · injection h with h; subst h; exact BinstrNum.f32Trunc
  · injection h with h; subst h; exact BinstrNum.f32Nearest
  · injection h with h; subst h; exact BinstrNum.f32Sqrt
  · injection h with h; subst h; exact BinstrNum.f64Abs
  · injection h with h; subst h; exact BinstrNum.f64Neg
  · injection h with h; subst h; exact BinstrNum.f64Ceil
  · injection h with h; subst h; exact BinstrNum.f64Floor
  · injection h with h; subst h; exact BinstrNum.f64Trunc
  · injection h with h; subst h; exact BinstrNum.f64Nearest
  · injection h with h; subst h; exact BinstrNum.f64Sqrt
  · exact absurd h (by simp)

/-- The `.binop` alternatives of `grammar Binstr/num-*`. -/
def encBinopN : NumType → Binop → Option Bytes
  | .i32, (.int .add) => some [tb 0x6A]
  | .i32, (.int .sub) => some [tb 0x6B]
  | .i32, (.int .mul) => some [tb 0x6C]
  | .i32, (.int (.div .s)) => some [tb 0x6D]
  | .i32, (.int (.div .u)) => some [tb 0x6E]
  | .i32, (.int (.rem .s)) => some [tb 0x6F]
  | .i32, (.int (.rem .u)) => some [tb 0x70]
  | .i32, (.int .and) => some [tb 0x71]
  | .i32, (.int .or) => some [tb 0x72]
  | .i32, (.int .xor) => some [tb 0x73]
  | .i32, (.int .shl) => some [tb 0x74]
  | .i32, (.int (.shr .s)) => some [tb 0x75]
  | .i32, (.int (.shr .u)) => some [tb 0x76]
  | .i32, (.int .rotl) => some [tb 0x77]
  | .i32, (.int .rotr) => some [tb 0x78]
  | .i64, (.int .add) => some [tb 0x7C]
  | .i64, (.int .sub) => some [tb 0x7D]
  | .i64, (.int .mul) => some [tb 0x7E]
  | .i64, (.int (.div .s)) => some [tb 0x7F]
  | .i64, (.int (.div .u)) => some [tb 0x80]
  | .i64, (.int (.rem .s)) => some [tb 0x81]
  | .i64, (.int (.rem .u)) => some [tb 0x82]
  | .i64, (.int .and) => some [tb 0x83]
  | .i64, (.int .or) => some [tb 0x84]
  | .i64, (.int .xor) => some [tb 0x85]
  | .i64, (.int .shl) => some [tb 0x86]
  | .i64, (.int (.shr .s)) => some [tb 0x87]
  | .i64, (.int (.shr .u)) => some [tb 0x88]
  | .i64, (.int .rotl) => some [tb 0x89]
  | .i64, (.int .rotr) => some [tb 0x8A]
  | .f32, (.float .add) => some [tb 0x92]
  | .f32, (.float .sub) => some [tb 0x93]
  | .f32, (.float .mul) => some [tb 0x94]
  | .f32, (.float .div) => some [tb 0x95]
  | .f32, (.float .min) => some [tb 0x96]
  | .f32, (.float .max) => some [tb 0x97]
  | .f32, (.float .copysign) => some [tb 0x98]
  | .f64, (.float .add) => some [tb 0xA0]
  | .f64, (.float .sub) => some [tb 0xA1]
  | .f64, (.float .mul) => some [tb 0xA2]
  | .f64, (.float .div) => some [tb 0xA3]
  | .f64, (.float .min) => some [tb 0xA4]
  | .f64, (.float .max) => some [tb 0xA5]
  | .f64, (.float .copysign) => some [tb 0xA6]
  | _, _ => Option.none

theorem encBinopN_B (nt : NumType) (op : Binop) (bs : Bytes)
    (h : encBinopN nt op = some bs) : BinstrNum bs (.binop nt op) := by
  unfold encBinopN at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32Add
  · injection h with h; subst h; exact BinstrNum.i32Sub
  · injection h with h; subst h; exact BinstrNum.i32Mul
  · injection h with h; subst h; exact BinstrNum.i32DivS
  · injection h with h; subst h; exact BinstrNum.i32DivU
  · injection h with h; subst h; exact BinstrNum.i32RemS
  · injection h with h; subst h; exact BinstrNum.i32RemU
  · injection h with h; subst h; exact BinstrNum.i32And
  · injection h with h; subst h; exact BinstrNum.i32Or
  · injection h with h; subst h; exact BinstrNum.i32Xor
  · injection h with h; subst h; exact BinstrNum.i32Shl
  · injection h with h; subst h; exact BinstrNum.i32ShrS
  · injection h with h; subst h; exact BinstrNum.i32ShrU
  · injection h with h; subst h; exact BinstrNum.i32Rotl
  · injection h with h; subst h; exact BinstrNum.i32Rotr
  · injection h with h; subst h; exact BinstrNum.i64Add
  · injection h with h; subst h; exact BinstrNum.i64Sub
  · injection h with h; subst h; exact BinstrNum.i64Mul
  · injection h with h; subst h; exact BinstrNum.i64DivS
  · injection h with h; subst h; exact BinstrNum.i64DivU
  · injection h with h; subst h; exact BinstrNum.i64RemS
  · injection h with h; subst h; exact BinstrNum.i64RemU
  · injection h with h; subst h; exact BinstrNum.i64And
  · injection h with h; subst h; exact BinstrNum.i64Or
  · injection h with h; subst h; exact BinstrNum.i64Xor
  · injection h with h; subst h; exact BinstrNum.i64Shl
  · injection h with h; subst h; exact BinstrNum.i64ShrS
  · injection h with h; subst h; exact BinstrNum.i64ShrU
  · injection h with h; subst h; exact BinstrNum.i64Rotl
  · injection h with h; subst h; exact BinstrNum.i64Rotr
  · injection h with h; subst h; exact BinstrNum.f32Add
  · injection h with h; subst h; exact BinstrNum.f32Sub
  · injection h with h; subst h; exact BinstrNum.f32Mul
  · injection h with h; subst h; exact BinstrNum.f32Div
  · injection h with h; subst h; exact BinstrNum.f32Min
  · injection h with h; subst h; exact BinstrNum.f32Max
  · injection h with h; subst h; exact BinstrNum.f32Copysign
  · injection h with h; subst h; exact BinstrNum.f64Add
  · injection h with h; subst h; exact BinstrNum.f64Sub
  · injection h with h; subst h; exact BinstrNum.f64Mul
  · injection h with h; subst h; exact BinstrNum.f64Div
  · injection h with h; subst h; exact BinstrNum.f64Min
  · injection h with h; subst h; exact BinstrNum.f64Max
  · injection h with h; subst h; exact BinstrNum.f64Copysign
  · exact absurd h (by simp)

/-- The authority-independent `.cvtop` alternatives of
`grammar Binstr/num-*`. -/
def encCvtopNBase : NumType → NumType → Cvtop → Option Bytes
  | .i32, .i64, (.ii .wrap) => some [tb 0xA7]
  | .i32, .f32, (.fi (.trunc .s)) => some [tb 0xA8]
  | .i32, .f32, (.fi (.trunc .u)) => some [tb 0xA9]
  | .i32, .f64, (.fi (.trunc .s)) => some [tb 0xAA]
  | .i32, .f64, (.fi (.trunc .u)) => some [tb 0xAB]
  | .i64, .i32, (.ii (.extend .s)) => some [tb 0xAC]
  | .i64, .i32, (.ii (.extend .u)) => some [tb 0xAD]
  | .i64, .f32, (.fi (.trunc .s)) => some [tb 0xAE]
  | .i64, .f32, (.fi (.trunc .u)) => some [tb 0xAF]
  | .i64, .f64, (.fi (.trunc .s)) => some [tb 0xB0]
  | .i64, .f64, (.fi (.trunc .u)) => some [tb 0xB1]
  | .f32, .i32, (.ifl (.convert .s)) => some [tb 0xB2]
  | .f32, .i32, (.ifl (.convert .u)) => some [tb 0xB3]
  | .f32, .i64, (.ifl (.convert .s)) => some [tb 0xB4]
  | .f32, .i64, (.ifl (.convert .u)) => some [tb 0xB5]
  | .f32, .f64, (.ff .demote) => some [tb 0xB6]
  | .f64, .i32, (.ifl (.convert .s)) => some [tb 0xB7]
  | .f64, .i32, (.ifl (.convert .u)) => some [tb 0xB8]
  | .f64, .i64, (.ifl (.convert .s)) => some [tb 0xB9]
  | .f64, .i64, (.ifl (.convert .u)) => some [tb 0xBA]
  | .i32, .f32, (.fi .reinterpret) => some [tb 0xBC]
  | .i64, .f64, (.fi .reinterpret) => some [tb 0xBD]
  | .f32, .i32, (.ifl .reinterpret) => some [tb 0xBE]
  | .f64, .i64, (.ifl .reinterpret) => some [tb 0xBF]
  | _, _, _ => Option.none

/-- Opcode `0xBB`, selected according to the finite binary authority. -/
def encCvtopNPromote : NumType → NumType → Cvtop → Option Bytes
  | .f32, .f64, (.ff .promote) =>
      match authority.revision with
      | .pinned => some [tb 0xBB]
      | .amended => Option.none
  | .f64, .f32, (.ff .promote) =>
      match authority.revision with
      | .pinned => Option.none
      | .amended => some [tb 0xBB]
  | _, _, _ => Option.none

/-- The `.cvtop` alternatives of `grammar Binstr/num-*`. -/
def encCvtopN (nt1 : NumType) (nt2 : NumType) (op : Cvtop) : Option Bytes :=
  orO (encCvtopNBase nt1 nt2 op) (encCvtopNPromote nt1 nt2 op)

theorem encCvtopNBase_B (nt1 : NumType) (nt2 : NumType) (op : Cvtop) (bs : Bytes)
    (h : encCvtopNBase nt1 nt2 op = some bs) :
    BinstrNum bs (.cvtop nt1 nt2 op) := by
  unfold encCvtopNBase at h
  split at h
  · injection h with h; subst h; exact BinstrNum.i32WrapI64
  · injection h with h; subst h; exact BinstrNum.i32TruncF32S
  · injection h with h; subst h; exact BinstrNum.i32TruncF32U
  · injection h with h; subst h; exact BinstrNum.i32TruncF64S
  · injection h with h; subst h; exact BinstrNum.i32TruncF64U
  · injection h with h; subst h; exact BinstrNum.i64ExtendI32S
  · injection h with h; subst h; exact BinstrNum.i64ExtendI32U
  · injection h with h; subst h; exact BinstrNum.i64TruncF32S
  · injection h with h; subst h; exact BinstrNum.i64TruncF32U
  · injection h with h; subst h; exact BinstrNum.i64TruncF64S
  · injection h with h; subst h; exact BinstrNum.i64TruncF64U
  · injection h with h; subst h; exact BinstrNum.f32ConvertI32S
  · injection h with h; subst h; exact BinstrNum.f32ConvertI32U
  · injection h with h; subst h; exact BinstrNum.f32ConvertI64S
  · injection h with h; subst h; exact BinstrNum.f32ConvertI64U
  · injection h with h; subst h; exact BinstrNum.f32DemoteF64
  · injection h with h; subst h; exact BinstrNum.f64ConvertI32S
  · injection h with h; subst h; exact BinstrNum.f64ConvertI32U
  · injection h with h; subst h; exact BinstrNum.f64ConvertI64S
  · injection h with h; subst h; exact BinstrNum.f64ConvertI64U
  · injection h with h; subst h; exact BinstrNum.i32ReinterpretF32
  · injection h with h; subst h; exact BinstrNum.i64ReinterpretF64
  · injection h with h; subst h; exact BinstrNum.f32ReinterpretI32
  · injection h with h; subst h; exact BinstrNum.f64ReinterpretI64
  · exact absurd h (by simp)

theorem encCvtopNBase_ne_bad (nt1 : NumType) (nt2 : NumType) (op : Cvtop)
    (bs : Bytes) (h : encCvtopNBase nt1 nt2 op = some bs) :
    (.cvtop nt1 nt2 op : Instr) ≠ pinnedBadPromote := by
  intro hbad
  simp [pinnedBadPromote] at hbad
  rcases hbad with ⟨rfl, rfl, rfl⟩
  simp [encCvtopNBase] at h

theorem encCvtopNPromote_B (nt1 : NumType) (nt2 : NumType) (op : Cvtop)
    (bs : Bytes) (h : encCvtopNPromote nt1 nt2 op = some bs) :
    BinstrNumFor bs (.cvtop nt1 nt2 op) := by
  unfold encCvtopNPromote at h
  split at h
  · cases authority with
    | mk revision =>
        cases revision with
        | pinned =>
            injection h with h
            subst h
            exact BinstrNum.f32PromoteF64
        | amended => exact absurd h (by simp)
  · cases authority with
    | mk revision =>
        cases revision with
        | pinned => exact absurd h (by simp)
        | amended =>
            injection h with h
            subst h
            exact BinstrNumFor.correctedPromote
  · exact absurd h (by simp)

theorem encCvtopN_B (nt1 : NumType) (nt2 : NumType) (op : Cvtop) (bs : Bytes)
    (h : encCvtopN nt1 nt2 op = some bs) :
    BinstrNumFor bs (.cvtop nt1 nt2 op) := by
  rcases orO_eq h with h | h
  · exact BinstrNumFor.ofPinned (encCvtopNBase_B nt1 nt2 op bs h)
      (encCvtopNBase_ne_bad nt1 nt2 op bs h)
  · exact encCvtopNPromote_B nt1 nt2 op bs h

/-- The numeric fragments, the alternatives that are a single opcode byte. -/
def encInstrNumOp : Instr → Option Bytes
  | .unop nt op => encUnopN nt op
  | .binop nt op => encBinopN nt op
  | .testop nt op => encTestopN nt op
  | .relop nt op => encRelopN nt op
  | .cvtop nt1 nt2 op => encCvtopN nt1 nt2 op
  | _ => Option.none

theorem encInstrNumOp_B (i : Instr) (bs : Bytes)
    (h : encInstrNumOp i = some bs) : BinstrNumFor bs i := by
  unfold encInstrNumOp at h
  split at h
  · exact BinstrNumFor.ofPinned (encUnopN_B _ _ _ h) (by simp [pinnedBadPromote])
  · exact BinstrNumFor.ofPinned (encBinopN_B _ _ _ h) (by simp [pinnedBadPromote])
  · exact BinstrNumFor.ofPinned (encTestopN_B _ _ _ h) (by simp [pinnedBadPromote])
  · exact BinstrNumFor.ofPinned (encRelopN_B _ _ _ h) (by simp [pinnedBadPromote])
  · exact encCvtopN_B _ _ _ _ h
  · exact absurd h (by simp)

/-- All scalar numeric alternatives, grouped once for the flat instruction
union and its compositional completeness proof. -/
def encInstrNum (i : Instr) : Option Bytes :=
  orO (encInstrNumC i) (encInstrNumOp i)

theorem encInstrNum_B (i : Instr) (bs : Bytes)
    (h : encInstrNum i = some bs) : BinstrNumFor bs i := by
  rcases orO_eq h with h | h
  · exact BinstrNumFor.ofPinned (encInstrNumC_B i bs h) (by
      intro hi
      subst i
      simp [encInstrNumC, pinnedBadPromote] at h)
  · exact encInstrNumOp_B i bs h

/-! ## Vector immediates and the encoder-local `0xFD` table -/

/-- `grammar Blaneidx`: a lane index is exactly one byte. -/
def encLaneIdx (i : LaneIdx) : Bytes := [Byte.ofNat i.val]

theorem encLaneIdx_B (i : LaneIdx) : Blaneidx (encLaneIdx i) i :=
  Blaneidx.mk _ _ (Byte_ofNat_val i.property).symm

/-- The fixed-width, uncounted lane-index sequence used by `VSHUFFLE`. -/
def encLaneIdxs : List LaneIdx → Bytes
  | [] => []
  | i :: is => encLaneIdx i ++ encLaneIdxs is

theorem encLaneIdxs_B : ∀ (is : List LaneIdx),
    Rep Blaneidx is.length (encLaneIdxs is) is
  | [] => Rep.nil
  | i :: is => Rep.cons (encLaneIdx i) i (encLaneIdxs is) is is.length
      (encLaneIdx_B i) (encLaneIdxs_B is)

/-- A prefixed vector-memory instruction with a `Bmemarg` immediate. -/
def encFDMem (k : Nat) (x : MemIdx) (ao : MemArg) : Option Bytes :=
  catO (some (pre 0xFD k)) (encMemArg x ao)

theorem encFDMem_eq {k : Nat} {x : MemIdx} {ao : MemArg} {bs : Bytes}
    (h : encFDMem k x ao = some bs) :
    ∃ bm, encMemArg x ao = some bm ∧ bs = pre 0xFD k ++ bm := by
  obtain ⟨bo, bm, hbo, hbm, rfl⟩ := catO_eq h
  injection hbo with hbo
  subst hbo
  exact ⟨bm, hbm, rfl⟩

/-- A prefixed vector-memory instruction with `Bmemarg` and lane immediates. -/
def encFDMemLane (k : Nat) (x : MemIdx) (ao : MemArg) (i : LaneIdx) :
    Option Bytes :=
  catO (encFDMem k x ao) (some (encLaneIdx i))

theorem encFDMemLane_eq {k : Nat} {x : MemIdx} {ao : MemArg} {i : LaneIdx}
    {bs : Bytes} (h : encFDMemLane k x ao i = some bs) :
    ∃ bm, encMemArg x ao = some bm ∧
      bs = pre 0xFD k ++ bm ++ encLaneIdx i := by
  obtain ⟨b, bi, hb, hbi, rfl⟩ := catO_eq h
  injection hbi with hbi
  subst hbi
  obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq hb
  exact ⟨bm, hbm, rfl⟩

/-- Every vector production carrying an immediate.  Shapes not named by the
pinned grammar and a shuffle not containing exactly sixteen lanes return
`none`, as they have no corresponding `BinstrVecMem` derivation. -/
def encInstrVecImm : Instr → Option Bytes
  | .vload .v128 none x ao => encFDMem 0 x ao
  | .vload .v128 (some (.shape .s8 8 .s)) x ao => encFDMem 1 x ao
  | .vload .v128 (some (.shape .s8 8 .u)) x ao => encFDMem 2 x ao
  | .vload .v128 (some (.shape .s16 4 .s)) x ao => encFDMem 3 x ao
  | .vload .v128 (some (.shape .s16 4 .u)) x ao => encFDMem 4 x ao
  | .vload .v128 (some (.shape .s32 2 .s)) x ao => encFDMem 5 x ao
  | .vload .v128 (some (.shape .s32 2 .u)) x ao => encFDMem 6 x ao
  | .vload .v128 (some (.splat .s8)) x ao => encFDMem 7 x ao
  | .vload .v128 (some (.splat .s16)) x ao => encFDMem 8 x ao
  | .vload .v128 (some (.splat .s32)) x ao => encFDMem 9 x ao
  | .vload .v128 (some (.splat .s64)) x ao => encFDMem 10 x ao
  | .vstore .v128 x ao => encFDMem 11 x ao
  | .vloadLane .v128 .s8 x ao i => encFDMemLane 84 x ao i
  | .vloadLane .v128 .s16 x ao i => encFDMemLane 85 x ao i
  | .vloadLane .v128 .s32 x ao i => encFDMemLane 86 x ao i
  | .vloadLane .v128 .s64 x ao i => encFDMemLane 87 x ao i
  | .vstoreLane .v128 .s8 x ao i => encFDMemLane 88 x ao i
  | .vstoreLane .v128 .s16 x ao i => encFDMemLane 89 x ao i
  | .vstoreLane .v128 .s32 x ao i => encFDMemLane 90 x ao i
  | .vstoreLane .v128 .s64 x ao i => encFDMemLane 91 x ao i
  | .vload .v128 (some (.zero .s32)) x ao => encFDMem 92 x ao
  | .vload .v128 (some (.zero .s64)) x ao => encFDMem 93 x ao
  | .vconst .v128 c => some (pre 0xFD 12 ++ bytesLE 16 c.val)
  | .vshuffle sh ls =>
      if sh = bshI8x16 ∧ ls.length = 16 then
        some (pre 0xFD 13 ++ encLaneIdxs ls)
      else none
  | .vextractLane { lane := .pack .i8, dim := .d16 } (some .s) i =>
      some (pre 0xFD 21 ++ encLaneIdx i)
  | .vextractLane { lane := .pack .i8, dim := .d16 } (some .u) i =>
      some (pre 0xFD 22 ++ encLaneIdx i)
  | .vreplaceLane { lane := .pack .i8, dim := .d16 } i =>
      some (pre 0xFD 23 ++ encLaneIdx i)
  | .vextractLane { lane := .pack .i16, dim := .d8 } (some .s) i =>
      some (pre 0xFD 24 ++ encLaneIdx i)
  | .vextractLane { lane := .pack .i16, dim := .d8 } (some .u) i =>
      some (pre 0xFD 25 ++ encLaneIdx i)
  | .vreplaceLane { lane := .pack .i16, dim := .d8 } i =>
      some (pre 0xFD 26 ++ encLaneIdx i)
  | .vextractLane { lane := .num .i32, dim := .d4 } none i =>
      some (pre 0xFD 27 ++ encLaneIdx i)
  | .vreplaceLane { lane := .num .i32, dim := .d4 } i =>
      some (pre 0xFD 28 ++ encLaneIdx i)
  | .vextractLane { lane := .num .i64, dim := .d2 } none i =>
      some (pre 0xFD 29 ++ encLaneIdx i)
  | .vreplaceLane { lane := .num .i64, dim := .d2 } i =>
      some (pre 0xFD 30 ++ encLaneIdx i)
  | .vextractLane { lane := .num .f32, dim := .d4 } none i =>
      some (pre 0xFD 31 ++ encLaneIdx i)
  | .vreplaceLane { lane := .num .f32, dim := .d4 } i =>
      some (pre 0xFD 32 ++ encLaneIdx i)
  | .vextractLane { lane := .num .f64, dim := .d2 } none i =>
      some (pre 0xFD 33 ++ encLaneIdx i)
  | .vreplaceLane { lane := .num .f64, dim := .d2 } i =>
      some (pre 0xFD 34 ++ encLaneIdx i)
  | _ => none

/-- Soundness of every immediate-carrying `0xFD` production against the
independent declarative grammar. -/
theorem encInstrVecImm_B (i : Instr) (bs : Bytes)
    (h : encInstrVecImm i = some bs) : Binstr bs i := by
  unfold encInstrVecImm at h
  split at h
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8x8S _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8x8U _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16x4S _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16x4U _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32x2S _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32x2U _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8Splat _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16Splat _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Splat _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Splat _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load8Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load16Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store8Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store16Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store32Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMemLane_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Store64Lane _ _ _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm) (encLaneIdx_B _))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load32Zero _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · obtain ⟨bm, hbm, rfl⟩ := encFDMem_eq h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Load64Zero _ _ _ _
      (pre_Bprefixed _ _ (by decide)) (encMemArg_B _ _ _ hbm))
  · rename_i c
    injection h with h
    subst h
    have hc : c.val < 0x100 ^ 16 := by
      have hp : (0x100 : Nat) ^ 16 = 2 ^ 128 := by decide
      rw [hp]
      exact c.property
    exact Binstr.ofVecMem _ _ (BinstrVecMem.v128Const _ _ _ _
      (pre_Bprefixed _ _ (by decide))
      (by simpa [bytesLE_length] using Rep_Bbyte (bytesLE 16 c.val))
      (leNat_bytesLE 16 c.val hc).symm)
  · rename_i sh ls
    split at h
    · rename_i hshape
      injection h with h
      subst h
      rcases hshape with ⟨rfl, hlen⟩
      exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Shuffle _ _ _
        (pre_Bprefixed _ _ (by decide)) (by simpa [hlen] using encLaneIdxs_B ls))
    · exact absurd h (by simp)
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ExtractLaneS _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ExtractLaneU _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ExtractLaneS _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ExtractLaneU _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4ExtractLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2ExtractLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4ExtractLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2ExtractLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · injection h with h; subst h
    exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2ReplaceLane _ _ _
      (pre_Bprefixed _ _ (by decide)) (encLaneIdx_B _))
  · exact absurd h (by simp)

/-- The encoder-local verbatim pinned table of no-immediate `0xFD k`
instructions. -/
def encFD0Instr : Nat → Option Instr
  | 14 => some (Instr.vswizzlop bshI8x16 .swizzle)
  | 256 => some (Instr.vswizzlop bshI8x16 .relaxedSwizzle)
  | 15 => some (Instr.vsplat shI8x16)
  | 16 => some (Instr.vsplat shI16x8)
  | 17 => some (Instr.vsplat shI32x4)
  | 18 => some (Instr.vsplat shI64x2)
  | 19 => some (Instr.vsplat shF32x4)
  | 20 => some (Instr.vsplat shF64x2)
  | 35 => some (Instr.vrelop shI8x16 (.int .eq))
  | 36 => some (Instr.vrelop shI8x16 (.int .ne))
  | 37 => some (Instr.vrelop shI8x16 (.int (.lt .s)))
  | 38 => some (Instr.vrelop shI8x16 (.int (.lt .u)))
  | 39 => some (Instr.vrelop shI8x16 (.int (.gt .s)))
  | 40 => some (Instr.vrelop shI8x16 (.int (.gt .u)))
  | 41 => some (Instr.vrelop shI8x16 (.int (.le .s)))
  | 42 => some (Instr.vrelop shI8x16 (.int (.le .u)))
  | 43 => some (Instr.vrelop shI8x16 (.int (.ge .s)))
  | 44 => some (Instr.vrelop shI8x16 (.int (.ge .u)))
  | 45 => some (Instr.vrelop shI16x8 (.int .eq))
  | 46 => some (Instr.vrelop shI16x8 (.int .ne))
  | 47 => some (Instr.vrelop shI16x8 (.int (.lt .s)))
  | 48 => some (Instr.vrelop shI16x8 (.int (.lt .u)))
  | 49 => some (Instr.vrelop shI16x8 (.int (.gt .s)))
  | 50 => some (Instr.vrelop shI16x8 (.int (.gt .u)))
  | 51 => some (Instr.vrelop shI16x8 (.int (.le .s)))
  | 52 => some (Instr.vrelop shI16x8 (.int (.le .u)))
  | 53 => some (Instr.vrelop shI16x8 (.int (.ge .s)))
  | 54 => some (Instr.vrelop shI16x8 (.int (.ge .u)))
  | 55 => some (Instr.vrelop shI32x4 (.int .eq))
  | 56 => some (Instr.vrelop shI32x4 (.int .ne))
  | 57 => some (Instr.vrelop shI32x4 (.int (.lt .s)))
  | 58 => some (Instr.vrelop shI32x4 (.int (.lt .u)))
  | 59 => some (Instr.vrelop shI32x4 (.int (.gt .s)))
  | 60 => some (Instr.vrelop shI32x4 (.int (.gt .u)))
  | 61 => some (Instr.vrelop shI32x4 (.int (.le .s)))
  | 62 => some (Instr.vrelop shI32x4 (.int (.le .u)))
  | 63 => some (Instr.vrelop shI32x4 (.int (.ge .s)))
  | 64 => some (Instr.vrelop shI32x4 (.int (.ge .u)))
  | 65 => some (Instr.vrelop shF32x4 (.float .eq))
  | 66 => some (Instr.vrelop shF32x4 (.float .ne))
  | 67 => some (Instr.vrelop shF32x4 (.float .lt))
  | 68 => some (Instr.vrelop shF32x4 (.float .gt))
  | 69 => some (Instr.vrelop shF32x4 (.float .le))
  | 70 => some (Instr.vrelop shF32x4 (.float .ge))
  | 71 => some (Instr.vrelop shF64x2 (.float .eq))
  | 72 => some (Instr.vrelop shF64x2 (.float .ne))
  | 73 => some (Instr.vrelop shF64x2 (.float .lt))
  | 74 => some (Instr.vrelop shF64x2 (.float .gt))
  | 75 => some (Instr.vrelop shF64x2 (.float .le))
  | 76 => some (Instr.vrelop shF64x2 (.float .ge))
  | 214 => some (Instr.vrelop shI64x2 (.int .eq))
  | 215 => some (Instr.vrelop shI64x2 (.int .ne))
  | 216 => some (Instr.vrelop shI64x2 (.int (.lt .s)))
  | 217 => some (Instr.vrelop shI64x2 (.int (.gt .s)))
  | 218 => some (Instr.vrelop shI64x2 (.int (.le .s)))
  | 219 => some (Instr.vrelop shI64x2 (.int (.ge .s)))
  | 77 => some (Instr.vvunop .v128 .not)
  | 78 => some (Instr.vvbinop .v128 .and)
  | 79 => some (Instr.vvbinop .v128 .andnot)
  | 80 => some (Instr.vvbinop .v128 .or)
  | 81 => some (Instr.vvbinop .v128 .xor)
  | 82 => some (Instr.vvternop .v128 .bitselect)
  | 83 => some (Instr.vvtestop .v128 .anyTrue)
  | 96 => some (Instr.vunop shI8x16 (.int .abs))
  | 97 => some (Instr.vunop shI8x16 (.int .neg))
  | 98 => some (Instr.vunop shI8x16 (.int .popcnt))
  | 99 => some (Instr.vtestop shI8x16 (.int .allTrue))
  | 100 => some (Instr.vbitmask ishI8x16)
  | 101 => some (Instr.vnarrow ishI8x16 ishI16x8 .s)
  | 102 => some (Instr.vnarrow ishI8x16 ishI16x8 .u)
  | 107 => some (Instr.vshiftop ishI8x16 .shl)
  | 108 => some (Instr.vshiftop ishI8x16 (.shr .s))
  | 109 => some (Instr.vshiftop ishI8x16 (.shr .u))
  | 110 => some (Instr.vbinop shI8x16 (.int .add))
  | 111 => some (Instr.vbinop shI8x16 (.int (.addSat .s)))
  | 112 => some (Instr.vbinop shI8x16 (.int (.addSat .u)))
  | 113 => some (Instr.vbinop shI8x16 (.int .sub))
  | 114 => some (Instr.vbinop shI8x16 (.int (.subSat .s)))
  | 115 => some (Instr.vbinop shI8x16 (.int (.subSat .u)))
  | 118 => some (Instr.vbinop shI8x16 (.int (.min .s)))
  | 119 => some (Instr.vbinop shI8x16 (.int (.min .u)))
  | 120 => some (Instr.vbinop shI8x16 (.int (.max .s)))
  | 121 => some (Instr.vbinop shI8x16 (.int (.max .u)))
  | 123 => some (Instr.vbinop shI8x16 (.int (.avgr .u)))
  | 124 => some (Instr.vextunop ishI16x8 ishI8x16 (.extaddPairwise .s))
  | 125 => some (Instr.vextunop ishI16x8 ishI8x16 (.extaddPairwise .u))
  | 128 => some (Instr.vunop shI16x8 (.int .abs))
  | 129 => some (Instr.vunop shI16x8 (.int .neg))
  | 130 => some (Instr.vbinop shI16x8 (.int (.q15mulrSat .s)))
  | 142 => some (Instr.vbinop shI16x8 (.int .add))
  | 143 => some (Instr.vbinop shI16x8 (.int (.addSat .s)))
  | 144 => some (Instr.vbinop shI16x8 (.int (.addSat .u)))
  | 145 => some (Instr.vbinop shI16x8 (.int .sub))
  | 146 => some (Instr.vbinop shI16x8 (.int (.subSat .s)))
  | 147 => some (Instr.vbinop shI16x8 (.int (.subSat .u)))
  | 149 => some (Instr.vbinop shI16x8 (.int .mul))
  | 150 => some (Instr.vbinop shI16x8 (.int (.min .s)))
  | 151 => some (Instr.vbinop shI16x8 (.int (.min .u)))
  | 152 => some (Instr.vbinop shI16x8 (.int (.max .s)))
  | 153 => some (Instr.vbinop shI16x8 (.int (.max .u)))
  | 155 => some (Instr.vbinop shI16x8 (.int (.avgr .u)))
  | 273 => some (Instr.vbinop shI16x8 (.int (.relaxedQ15mulr .s)))
  | 131 => some (Instr.vtestop shI16x8 (.int .allTrue))
  | 132 => some (Instr.vbitmask ishI16x8)
  | 133 => some (Instr.vnarrow ishI16x8 ishI32x4 .s)
  | 134 => some (Instr.vnarrow ishI16x8 ishI32x4 .u)
  | 135 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .low .s)))
  | 136 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .high .s)))
  | 137 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .low .u)))
  | 138 => some (Instr.vcvtop shI16x8 shI8x16 (.jj (.extend .high .u)))
  | 139 => some (Instr.vshiftop ishI16x8 .shl)
  | 140 => some (Instr.vshiftop ishI16x8 (.shr .s))
  | 141 => some (Instr.vshiftop ishI16x8 (.shr .u))
  | 156 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .low .s))
  | 157 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .high .s))
  | 158 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .low .u))
  | 159 => some (Instr.vextbinop ishI16x8 ishI8x16 (.extmul .high .u))
  | 274 => some (Instr.vextbinop ishI16x8 ishI8x16 (.relaxedDot .s))
  | 126 => some (Instr.vextunop ishI32x4 ishI16x8 (.extaddPairwise .s))
  | 127 => some (Instr.vextunop ishI32x4 ishI16x8 (.extaddPairwise .u))
  | 160 => some (Instr.vunop shI32x4 (.int .abs))
  | 161 => some (Instr.vunop shI32x4 (.int .neg))
  | 163 => some (Instr.vtestop shI32x4 (.int .allTrue))
  | 164 => some (Instr.vbitmask ishI32x4)
  | 167 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .low .s)))
  | 168 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .high .s)))
  | 169 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .low .u)))
  | 170 => some (Instr.vcvtop shI32x4 shI16x8 (.jj (.extend .high .u)))
  | 171 => some (Instr.vshiftop ishI32x4 .shl)
  | 172 => some (Instr.vshiftop ishI32x4 (.shr .s))
  | 173 => some (Instr.vshiftop ishI32x4 (.shr .u))
  | 174 => some (Instr.vbinop shI32x4 (.int .add))
  | 177 => some (Instr.vbinop shI32x4 (.int .sub))
  | 181 => some (Instr.vbinop shI32x4 (.int .mul))
  | 182 => some (Instr.vbinop shI32x4 (.int (.min .s)))
  | 183 => some (Instr.vbinop shI32x4 (.int (.min .u)))
  | 184 => some (Instr.vbinop shI32x4 (.int (.max .s)))
  | 185 => some (Instr.vbinop shI32x4 (.int (.max .u)))
  | 186 => some (Instr.vextbinop ishI32x4 ishI16x8 (.dot .s))
  | 188 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .low .s))
  | 189 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .high .s))
  | 190 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .low .u))
  | 191 => some (Instr.vextbinop ishI32x4 ishI16x8 (.extmul .high .u))
  | 275 => some (Instr.vextternop ishI32x4 ishI16x8 (.relaxedDotAdd .s))
  | 192 => some (Instr.vunop shI64x2 (.int .abs))
  | 193 => some (Instr.vunop shI64x2 (.int .neg))
  | 195 => some (Instr.vtestop shI64x2 (.int .allTrue))
  | 196 => some (Instr.vbitmask ishI64x2)
  | 199 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .low .s)))
  | 200 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .high .s)))
  | 201 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .low .u)))
  | 202 => some (Instr.vcvtop shI64x2 shI32x4 (.jj (.extend .high .u)))
  | 203 => some (Instr.vshiftop ishI64x2 .shl)
  | 204 => some (Instr.vshiftop ishI64x2 (.shr .s))
  | 205 => some (Instr.vshiftop ishI64x2 (.shr .u))
  | 206 => some (Instr.vbinop shI64x2 (.int .add))
  | 209 => some (Instr.vbinop shI64x2 (.int .sub))
  | 213 => some (Instr.vbinop shI64x2 (.int .mul))
  | 220 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .low .s))
  | 221 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .high .s))
  | 222 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .low .u))
  | 223 => some (Instr.vextbinop ishI64x2 ishI32x4 (.extmul .high .u))
  | 103 => some (Instr.vunop shF32x4 (.float .ceil))
  | 104 => some (Instr.vunop shF32x4 (.float .floor))
  | 105 => some (Instr.vunop shF32x4 (.float .trunc))
  | 106 => some (Instr.vunop shF32x4 (.float .nearest))
  | 224 => some (Instr.vunop shF32x4 (.float .abs))
  | 225 => some (Instr.vunop shF32x4 (.float .neg))
  | 227 => some (Instr.vunop shF32x4 (.float .sqrt))
  | 228 => some (Instr.vbinop shF32x4 (.float .add))
  | 229 => some (Instr.vbinop shF32x4 (.float .sub))
  | 230 => some (Instr.vbinop shF32x4 (.float .mul))
  | 231 => some (Instr.vbinop shF32x4 (.float .div))
  | 232 => some (Instr.vbinop shF32x4 (.float .min))
  | 233 => some (Instr.vbinop shF32x4 (.float .max))
  | 234 => some (Instr.vbinop shF32x4 (.float .pmin))
  | 235 => some (Instr.vbinop shF32x4 (.float .pmax))
  | 269 => some (Instr.vbinop shF32x4 (.float .relaxedMin))
  | 270 => some (Instr.vbinop shF32x4 (.float .relaxedMax))
  | 261 => some (Instr.vternop shF32x4 (.float .relaxedMadd))
  | 262 => some (Instr.vternop shF32x4 (.float .relaxedNmadd))
  | 116 => some (Instr.vunop shF64x2 (.float .ceil))
  | 117 => some (Instr.vunop shF64x2 (.float .floor))
  | 122 => some (Instr.vunop shF64x2 (.float .trunc))
  | 148 => some (Instr.vunop shF64x2 (.float .nearest))
  | 236 => some (Instr.vunop shF64x2 (.float .abs))
  | 237 => some (Instr.vunop shF64x2 (.float .neg))
  | 239 => some (Instr.vunop shF64x2 (.float .sqrt))
  | 240 => some (Instr.vbinop shF64x2 (.float .add))
  | 241 => some (Instr.vbinop shF64x2 (.float .sub))
  | 242 => some (Instr.vbinop shF64x2 (.float .mul))
  | 243 => some (Instr.vbinop shF64x2 (.float .div))
  | 244 => some (Instr.vbinop shF64x2 (.float .min))
  | 245 => some (Instr.vbinop shF64x2 (.float .max))
  | 246 => some (Instr.vbinop shF64x2 (.float .pmin))
  | 247 => some (Instr.vbinop shF64x2 (.float .pmax))
  | 271 => some (Instr.vbinop shF64x2 (.float .relaxedMin))
  | 272 => some (Instr.vbinop shF64x2 (.float .relaxedMax))
  | 263 => some (Instr.vternop shF64x2 (.float .relaxedMadd))
  | 264 => some (Instr.vternop shF64x2 (.float .relaxedNmadd))
  | 265 => some (Instr.vternop shI8x16 (.int .relaxedLaneselect))
  | 266 => some (Instr.vternop shI16x8 (.int .relaxedLaneselect))
  | 267 => some (Instr.vternop shI32x4 (.int .relaxedLaneselect))
  | 268 => some (Instr.vternop shI64x2 (.int .relaxedLaneselect))
  | 94 => some (Instr.vcvtop shF32x4 shF64x2 (.ff (.demote .zero)))
  | 95 => some (Instr.vcvtop shF64x2 shF32x4 (.ff (.promote .low)))
  | 248 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.truncSat .s none)))
  | 249 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.truncSat .u none)))
  | 250 => some (Instr.vcvtop shF32x4 shI32x4 (.jf (.convert none .s)))
  | 251 => some (Instr.vcvtop shF32x4 shI32x4 (.jf (.convert none .u)))
  | 252 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.truncSat .s (some .zero))))
  | 253 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.truncSat .u (some .zero))))
  | 254 => some (Instr.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .s)))
  | 255 => some (Instr.vcvtop shF64x2 shI32x4 (.jf (.convert (some .low) .u)))
  | 257 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .s none)))
  | 258 => some (Instr.vcvtop shI32x4 shF32x4 (.fj (.relaxedTrunc .u none)))
  | 259 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .s (some .zero))))
  | 260 => some (Instr.vcvtop shI32x4 shF64x2 (.fj (.relaxedTrunc .u (some .zero))))
  | _ => none

/-- The authority-selected encoder table.  AMD-012 overrides only selector
275; every other selector reuses the one pinned table above. -/
def encFD0InstrFor [authority : BinaryAuthority] : Nat → Option Instr :=
  match authority.revision with
  | .pinned => encFD0Instr
  | .amended => fun k =>
      if k = 275 then
        some (Instr.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s))
      else encFD0Instr k

@[simp] theorem encFD0InstrFor_pinned :
    @encFD0InstrFor pinnedBinaryAuthority = encFD0Instr := rfl

/-- Away from AMD-012 selector 275, the selected table is the pinned table. -/
theorem encFD0InstrFor_of_ne {k : Nat} (hne : k ≠ 275) :
    encFD0InstrFor k = encFD0Instr k := by
  cases hr : authority.revision with
  | pinned => simp [encFD0InstrFor, hr]
  | amended => simp [encFD0InstrFor, hr, hne]

theorem encFD0Instr_ne275_sound {k : Nat} {i : Instr} {bo : Bytes}
    (hk : encFD0Instr k = some i) (hkne : k ≠ 275)
    (hbo : Bprefixed 0xFD k bo) : Binstr bo i := by
  unfold encFD0Instr at hk
  split at hk
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Swizzle bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16RelaxedSwizzle bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i8x16Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i16x8Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i32x4Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.i64x2Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.f32x4Splat bo hbo)
  · cases hk; exact Binstr.ofVecMem _ _ (BinstrVecMem.f64x2Splat bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i8x16GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i16x8GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GtU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4LeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i32x4GeU bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Lt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Gt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Le bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f32x4Ge bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Lt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Gt bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Le bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.f64x2Ge bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2Eq bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2Ne bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2LtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2GtS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2LeS bo hbo)
  · cases hk; exact Binstr.ofVecRel _ _ (BinstrVecRel.i64x2GeS bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.not bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.and bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.andnot bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.or bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.xor bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.bitselect bo hbo)
  · cases hk; exact Binstr.ofVecV128 _ _ (BinstrVecV128.anyTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Abs bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Neg bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Popcnt bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AllTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Bitmask bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16NarrowI16x8S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16NarrowI16x8U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Shl bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16ShrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16ShrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Add bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AddSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AddSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16Sub bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16SubSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16SubSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MinS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MinU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MaxS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16MaxU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i8x16AvgrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtaddPairwiseI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtaddPairwiseI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Abs bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Neg bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Q15mulrSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Add bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AddSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AddSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Sub bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8SubSatS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8SubSatU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Mul bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MinS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MinU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MaxS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8MaxU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AvgrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8RelaxedQ15mulrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8AllTrue bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Bitmask bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8NarrowI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8NarrowI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendLowI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendHighI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendLowI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtendHighI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8Shl bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ShrS bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ShrU bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulLowI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulHighI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulLowI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8ExtmulHighI8x16U bo hbo)
  · cases hk; exact Binstr.ofVecInt8And16 _ _ (BinstrVecInt8And16.i16x8RelaxedDotI8x16S bo hbo)
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtaddPairwiseI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtaddPairwiseI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Abs bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Neg bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4AllTrue bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Bitmask bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendLowI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendHighI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendLowI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtendHighI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Shl bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ShrS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ShrU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Add bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Sub bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4Mul bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MinS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MinU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MaxS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4MaxU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4DotI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulLowI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulHighI16x8S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulLowI16x8U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i32x4ExtmulHighI16x8U bo hbo) (by decide))
  · exact (hkne rfl).elim
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Abs bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Neg bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2AllTrue bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Bitmask bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendLowI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendHighI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendLowI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtendHighI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Shl bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ShrS bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ShrU bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Add bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Sub bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2Mul bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulLowI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulHighI32x4S bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulLowI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecInt32And64 _ _
      (BinstrVecInt32And64For.ofPinned (BinstrVecInt32And64.i64x2ExtmulHighI32x4U bo hbo) (by decide))
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Ceil bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Floor bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Trunc bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Nearest bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Abs bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Neg bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Sqrt bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Add bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Sub bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Mul bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Div bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Min bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Max bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Pmin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4Pmax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedMadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4RelaxedNmadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Ceil bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Floor bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Trunc bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Nearest bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Abs bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Neg bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Sqrt bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Add bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Sub bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Mul bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Div bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Min bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Max bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Pmin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2Pmax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMin bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMax bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedMadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2RelaxedNmadd bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i8x16RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i16x8RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i64x2RelaxedLaneselect bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4DemoteF64x2Zero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2PromoteLowF32x4 bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4ConvertI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f32x4ConvertI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF64x2SZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4TruncSatF64x2UZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2ConvertLowI32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.f64x2ConvertLowI32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF32x4S bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF32x4U bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF64x2SZero bo hbo)
  · cases hk; exact Binstr.ofVecFloat _ _ (BinstrVecFloat.i32x4RelaxedTruncF64x2UZero bo hbo)
  · cases hk

/-- Soundness of the authority-selected encoder table, including AMD-012's
corrected selector 275 and the verbatim pinned default. -/
theorem encFD0InstrFor_sound {k : Nat} {i : Instr} {bo : Bytes}
    (hk : encFD0InstrFor k = some i)
    (hbo : Bprefixed 0xFD k bo) : Binstr bo i := by
  cases hr : authority.revision with
  | pinned =>
      simp [encFD0InstrFor, hr] at hk
      by_cases hk275 : k = 275
      · subst k
        simp [encFD0Instr] at hk
        cases hk
        apply Binstr.ofVecInt32And64
        simp [BinstrVecInt32And64For, hr]
        exact BinstrVecInt32And64.i32x4RelaxedDotAddI16x8S bo hbo
      · exact encFD0Instr_ne275_sound hk hk275 hbo
  | amended =>
      by_cases hk275 : k = 275
      · subst k
        simp [encFD0InstrFor, hr] at hk
        cases hk
        apply Binstr.ofVecInt32And64
        simp [BinstrVecInt32And64For, hr]
        exact BinstrVecInt32And64'.correctedRelaxedDotAdd bo hbo
      · have hk' : encFD0Instr k = some i := by
          simpa [encFD0InstrFor, hr, hk275] using hk
        exact encFD0Instr_ne275_sound hk' hk275 hbo

/-- Search the finite `0xFD` selector interval for a no-immediate instruction.
The decreasing upper bound makes the lookup structurally recursive and keeps
the encoder executable without importing the decoder's opcode dispatch. -/
def findFDOpcode (i : Instr) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
      match encFD0Instr n with
      | none => findFDOpcode i n
      | some j => if j = i then some n else findFDOpcode i n

theorem findFDOpcode_spec (i : Instr) (n k : Nat)
    (h : findFDOpcode i n = some k) :
    encFD0Instr k = some i ∧ k < n := by
  induction n with
  | zero => simp [findFDOpcode] at h
  | succ n ih =>
      simp only [findFDOpcode] at h
      split at h
      · obtain ⟨hs, hk⟩ := ih h
        exact ⟨hs, by omega⟩
      · rename_i j hj
        split at h
        · rename_i hji
          injection h with hkn
          subst k
          subst i
          exact ⟨hj, by omega⟩
        · obtain ⟨hs, hk⟩ := ih h
          exact ⟨hs, by omega⟩

/-- The 218 vector productions with no immediate.  `276` is one past the
largest standard or relaxed-SIMD selector (`275`). -/
def encInstrVec0 (i : Instr) : Option Bytes :=
  if i = (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s) : Instr) then
    match authority.revision with
    | .pinned => none
    | .amended => some (pre 0xFD 275)
  else if i = pinnedBadRelaxedDotAdd then
    match authority.revision with
    | .pinned => some (pre 0xFD 275)
    | .amended => none
  else
    match findFDOpcode i 276 with
    | none => none
    | some k => some (pre 0xFD k)

theorem encInstrVec0_B (i : Instr) (bs : Bytes)
    (h : encInstrVec0 i = some bs) : Binstr bs i := by
  by_cases hc : i = (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s) : Instr)
  · subst i
    cases hr : authority.revision with
    | pinned =>
        simp only [encInstrVec0, if_pos rfl, hr, if_true] at h
        cases h
    | amended =>
        simp only [encInstrVec0, if_pos rfl, hr, if_true] at h
        injection h with hbs
        subst bs
        apply Binstr.ofVecInt32And64
        simp [BinstrVecInt32And64For, hr]
        exact BinstrVecInt32And64'.correctedRelaxedDotAdd _
          (pre_Bprefixed 0xFD 275 (by decide))
  · by_cases hb : i = pinnedBadRelaxedDotAdd
    · subst i
      cases hr : authority.revision with
      | pinned =>
          simp only [encInstrVec0, if_neg hc, if_pos rfl, hr, if_true] at h
          injection h with hbs
          subst bs
          apply Binstr.ofVecInt32And64
          simp [BinstrVecInt32And64For, hr]
          exact BinstrVecInt32And64.i32x4RelaxedDotAddI16x8S _
            (pre_Bprefixed 0xFD 275 (by decide))
      | amended =>
          simp only [encInstrVec0, if_neg hc, if_pos rfl, hr, if_true] at h
          cases h
    · simp only [encInstrVec0, if_neg hc, if_neg hb] at h
      split at h
      · exact absurd h (by simp)
      · rename_i k hk
        injection h with hbs
        subst bs
        obtain ⟨hs, hlt⟩ := findFDOpcode_spec i 276 k hk
        have hkne : k ≠ 275 := by
          intro heq
          subst k
          change some pinnedBadRelaxedDotAdd = some i at hs
          injection hs with hi
          exact hb hi.symm
        have hsFor : encFD0InstrFor k = some i := by
          rw [encFD0InstrFor_of_ne hkne]
          exact hs
        exact encFD0InstrFor_sound hsFor (pre_Bprefixed _ _ (by omega))

/-- The complete non-recursive vector fragment: 38 immediate productions and
218 no-immediate standard or relaxed-SIMD productions. -/
def encInstrVec (i : Instr) : Option Bytes :=
  orO (encInstrVecImm i) (encInstrVec0 i)

theorem encInstrVec_B (i : Instr) (bs : Bytes)
    (h : encInstrVec i = some bs) : Binstr bs i := by
  rcases orO_eq h with h | h
  · exact encInstrVecImm_B i bs h
  · exact encInstrVec0_B i bs h

/-- Every fragment of `Binstr` that does not recur into `Binstr`, as one
encoder.  `Binstr` is the UNION of its fragments, and `orO` is that union. -/
def encInstrFlat (i : Instr) : Option Bytes :=
  orO (encInstrParam i) <|
  orO (encInstrCtl i) <|
  orO (encInstrLoc i) <|
  orO (encInstrGlob i) <|
  orO (encInstrTbl i) <|
  orO (encInstrMem i) <|
  orO (encInstrRef i) <|
  orO (encInstrStr i) <|
  orO (encInstrArr i) <|
  orO (encInstrCast i) <|
  orO (encInstrExt i) <|
  orO (encInstrI31 i) <|
  orO (encInstrNum i) (encInstrVec i)

/-- **The non-recursive alternatives of `grammar Binstr`.** -/
theorem encInstrFlat_B (i : Instr) (bs : Bytes)
    (h : encInstrFlat i = some bs) : Binstr bs i := by
  unfold encInstrFlat at h
  rcases orO_eq h with h | h
  · exact Binstr.ofParametric _ _ (encInstrParam_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofControl _ _ (encInstrCtl_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofLocal _ _ (encInstrLoc_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofGlobal _ _ (encInstrGlob_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofTable _ _ (encInstrTbl_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofMemory _ _ (encInstrMem_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofRef _ _ (encInstrRef_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofStruct _ _ (encInstrStr_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofArray _ _ (encInstrArr_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofCast _ _ (encInstrCast_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofExtern _ _ (encInstrExt_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofI31 _ _ (encInstrI31_B i bs h)
  rcases orO_eq h with h | h
  · exact Binstr.ofNum _ _ (encInstrNum_B i bs h)
  · exact encInstrVec_B i bs h


/-! ## The four alternatives that recur into `Binstr`, and `Bexpr`

`BLOCK`, `LOOP`, the two forms of `IF` and `TRY_TABLE` are the only productions
of `5.3-binary.instructions.spectec` that mention `Binstr` again; they are
`BinaryGrammar/Expressions.lean`, and they are the only recursion here. -/

mutual

/-- The recursive alternatives of `grammar Binstr : instr`. -/
def encInstrRec : Instr → Option Bytes
  | .block bt body =>
      consO (tb 0x02) (catO (catO (encBlockType bt) (encInstrs body)) (some [tb 0x0B]))
  | .loop bt body =>
      consO (tb 0x03) (catO (catO (encBlockType bt) (encInstrs body)) (some [tb 0x0B]))
  | .ifElse bt thn .nil =>
      consO (tb 0x04) (catO (catO (encBlockType bt) (encInstrs thn)) (some [tb 0x0B]))
  | .ifElse bt thn els =>
      consO (tb 0x04) (catO (catO (catO (catO (encBlockType bt) (encInstrs thn))
        (some [tb 0x05])) (encInstrs els)) (some [tb 0x0B]))
  | .tryTable bt cs body =>
      consO (tb 0x1F) (catO (catO (catO (encBlockType bt) (encList encCatch cs.val))
        (encInstrs body)) (some [tb 0x0B]))
  | _ => Option.none

/-- `(in:Binstr)*`, the Kleene star of the instruction grammar. -/
def encInstrs : InstrSeq → Option Bytes
  | .nil => some []
  | .cons i rest => catO (orO (encInstrRec i) (encInstrFlat i)) (encInstrs rest)

end

/-- **`grammar Binstr : instr`**, the union of every fragment. -/
def encInstr (i : Instr) : Option Bytes := orO (encInstrRec i) (encInstrFlat i)

/-! ### A measure for the induction

The two encoders are mutually recursive, so the correctness proof is one
induction over a size measure rather than two separate ones. -/

mutual

/-- The nesting size of an instruction. -/
def instrSize : Instr → Nat
  | .block _ body => instrsSize body + 1
  | .loop _ body => instrsSize body + 1
  | .ifElse _ thn els => instrsSize thn + instrsSize els + 1
  | .tryTable _ _ body => instrsSize body + 1
  | _ => 1

/-- The nesting size of an instruction sequence. -/
def instrsSize : InstrSeq → Nat
  | .nil => 0
  | .cons i rest => instrSize i + instrsSize rest + 1

end

/-- **`grammar Binstr` and `(in:Binstr)*`**, both directions of the recursive
knot at once. -/
theorem enc_B_aux : ∀ (n : Nat),
    (∀ (i : Instr), instrSize i ≤ n → ∀ bs, encInstr i = some bs → Binstr bs i) ∧
    (∀ (s : InstrSeq), instrsSize s ≤ n →
      ∀ bs, encInstrs s = some bs → Binstrs bs s.toList) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    constructor
    · intro i hsz bs h
      unfold encInstr at h
      rcases orO_eq h with h | h
      · revert hsz h
        cases i
        case block bt body =>
            intro hsz h
            simp only [encInstrRec] at h
            simp only [instrSize] at hsz
            obtain ⟨a, ha, hbs⟩ := consO_eq h
            subst hbs
            obtain ⟨b, c, hb, hc, hbc⟩ := catO_eq ha
            injection hc with hc
            subst hbc; subst hc
            obtain ⟨d, e, hd, he, hde⟩ := catO_eq hb
            subst hde
            have hrec := (ih (instrsSize body) (by omega)).2 body (Nat.le_refl _) e he
            simpa using Binstr.block d e bt body.toList (encBlockType_B bt d hd) hrec
        case loop bt body =>
            intro hsz h
            simp only [encInstrRec] at h
            simp only [instrSize] at hsz
            obtain ⟨a, ha, hbs⟩ := consO_eq h
            subst hbs
            obtain ⟨b, c, hb, hc, hbc⟩ := catO_eq ha
            injection hc with hc
            subst hbc; subst hc
            obtain ⟨d, e, hd, he, hde⟩ := catO_eq hb
            subst hde
            have hrec := (ih (instrsSize body) (by omega)).2 body (Nat.le_refl _) e he
            simpa using Binstr.loop d e bt body.toList (encBlockType_B bt d hd) hrec
        case ifElse bt thn els =>
            intro hsz h
            simp only [instrSize] at hsz
            cases els with
            | nil =>
                simp only [encInstrRec] at h
                obtain ⟨a, ha, hbs⟩ := consO_eq h
                subst hbs
                obtain ⟨b, c, hb, hc, hbc⟩ := catO_eq ha
                injection hc with hc
                subst hbc; subst hc
                obtain ⟨d, e, hd, he, hde⟩ := catO_eq hb
                subst hde
                have hrec := (ih (instrsSize thn) (by omega)).2 thn (Nat.le_refl _) e he
                simpa using Binstr.ifThen d e bt thn.toList (encBlockType_B bt d hd) hrec
            | cons i0 r0 =>
                simp only [encInstrRec] at h
                obtain ⟨a, ha, hbs⟩ := consO_eq h
                subst hbs
                obtain ⟨p, q, hp, hq, hpq⟩ := catO_eq ha
                injection hq with hq
                subst hpq; subst hq
                obtain ⟨u, v, hu, hv, huv⟩ := catO_eq hp
                subst huv
                obtain ⟨w, z, hw, hz, hwz⟩ := catO_eq hu
                injection hz with hz
                subst hwz; subst hz
                obtain ⟨d, e, hd, he, hde⟩ := catO_eq hw
                subst hde
                have h1 := (ih (instrsSize thn) (by simp only [instrsSize] at hsz; omega)).2
                  thn (Nat.le_refl _) e he
                have h2 := (ih (instrsSize (InstrSeq.cons i0 r0))
                  (by simp only [instrsSize] at hsz ⊢; omega)).2
                  (InstrSeq.cons i0 r0) (Nat.le_refl _) v hv
                simpa using Binstr.ifElse d e v bt thn.toList
                  (InstrSeq.cons i0 r0).toList (encBlockType_B bt d hd) h1 h2
        case tryTable bt cs body =>
            intro hsz h
            simp only [encInstrRec] at h
            simp only [instrSize] at hsz
            obtain ⟨a, ha, hbs⟩ := consO_eq h
            subst hbs
            obtain ⟨b, c, hb, hc, hbc⟩ := catO_eq ha
            injection hc with hc
            subst hbc; subst hc
            obtain ⟨d, e, hd, he, hde⟩ := catO_eq hb
            subst hde
            obtain ⟨u, v, hu, hv, huv⟩ := catO_eq hd
            subst huv
            have hrec := (ih (instrsSize body) (by omega)).2 body (Nat.le_refl _) e he
            simpa using Binstr.tryTable u v e bt cs body.toList
              (encBlockType_B bt u hu) (encList_Blist encCatch_B _ v hv) hrec
        all_goals (intro hsz h; exact absurd h (by simp [encInstrRec]))
      · exact encInstrFlat_B i bs h
    · intro s hsz bs h
      cases s with
      | nil =>
          simp only [encInstrs] at h
          injection h with h; subst h
          exact Binstrs.nil
      | cons i rest =>
          simp only [encInstrs] at h
          simp only [instrsSize] at hsz
          obtain ⟨a, b, ha, hb, hab⟩ := catO_eq h
          subst hab
          exact Binstrs.cons a b i rest.toList
            ((ih (instrSize i) (by omega)).1 i (Nat.le_refl _) a ha)
            ((ih (instrsSize rest) (by omega)).2 rest (Nat.le_refl _) b hb)

/-- **`grammar Binstr : instr`.** -/
theorem encInstr_B (i : Instr) (bs : Bytes) (h : encInstr i = some bs) : Binstr bs i :=
  (enc_B_aux (instrSize i)).1 i (Nat.le_refl _) bs h

/-- **`(in:Binstr)*`.** -/
theorem encInstrs_B (s : InstrSeq) (bs : Bytes) (h : encInstrs s = some bs) :
    Binstrs bs s.toList :=
  (enc_B_aux (instrsSize s)).2 s (Nat.le_refl _) bs h

/-- `grammar Bexpr : expr = | (in:Binstr)* 0x0B => in*`. -/
def encExpr (e : Expr) : Option Bytes := catO (encInstrs e) (some [tb 0x0B])

/-- **`grammar Bexpr : expr`.** -/
theorem encExpr_B (e : Expr) (bs : Bytes) (h : encExpr e = some bs) : Bexpr bs e := by
  unfold encExpr at h
  obtain ⟨a, b, ha, hb, hab⟩ := catO_eq h
  injection hb with hb
  subst hab; subst hb
  simpa using Bexpr.mk a e.toList (encInstrs_B e a ha)


/-! ## Names -/

/-- `grammar Bbyte`, as an encoder: a byte is its own encoding. -/
def encByte (b : Byte) : Option Bytes := some [b]

theorem encByte_B (b : Byte) (bs : Bytes) (h : encByte b = some bs) : Bbyte bs b := by
  injection h with h; subst h; exact Bbyte.mk b

/-- `b*:Blist(Bbyte)`. -/
def encByteList (bl : List Byte) : Option Bytes := encList encByte bl

theorem encByteList_B (bl : List Byte) (bs : Bytes) (h : encByteList bl = some bs) :
    Blist Bbyte bs bl := encList_Blist encByte_B bl bs h

/-- `grammar Bname : name = | b*:Blist(Bbyte) => name  -- if $utf8(name) = b*`. -/
def encName (nm : Name) : Option Bytes := encByteList (utf8 nm.val)

theorem encName_B (nm : Name) (bs : Bytes) (h : encName nm = some bs) : Bname bs nm :=
  Bname.mk bs (utf8 nm.val) nm (encByteList_B _ bs h) rfl

/-- A total element encoder makes `encRep` total. -/
theorem encRep_isSome {α : Type} {f : α → Option Bytes} (hf : ∀ a, ∃ b, f a = some b) :
    ∀ xs : List α, ∃ bs, encRep f xs = some bs := by
  intro xs
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
      obtain ⟨b, hb⟩ := hf a
      obtain ⟨c, hc⟩ := ih
      exact ⟨b ++ c, by simp [encRep, hb, hc, catO]⟩

/-- A NAME is never a reason to fail: `syntax name` carries the very bound
`Blist` needs, `|$utf8(char*)| < 2^32`. -/
theorem encName_isSome (nm : Name) : ∃ bs, encName nm = some bs := by
  obtain ⟨c, hc⟩ := encRep_isSome (f := encByte) (fun b => ⟨[b], rfl⟩) (utf8 nm.val)
  exact ⟨lebU (utf8 nm.val).length ++ c, by
    simp [encName, encByteList, encList, nm.property, hc, catO]⟩

/-! ## Type section -/

/-- `grammar Btype : type = | qt:Brectype => TYPE qt`. -/
def encTypeDef (td : TypeDef) : Option Bytes := encRecType td.rectype

theorem encTypeDef_B (td : TypeDef) (bs : Bytes) (h : encTypeDef td = some bs) :
    Btype bs td :=
  Btype.mk bs td.rectype (encRecType_B td.rectype bs h)

/-- `grammar Btypesec : type* = | ty*:Bsection_(1, Blist(Btype)) => ty*`. -/
def encTypeSec (ts : List TypeDef) : Option Bytes := encListSection 1 encTypeDef ts

theorem encTypeSec_B (ts : List TypeDef) (bs : Bytes) (h : encTypeSec ts = some bs) :
    Btypesec bs ts :=
  encListSection_Bsection encTypeDef_B 1 ts bs h

/-! ## Import section -/

/-- `grammar Bimport : import`. -/
def encImport (im : Import) : Option Bytes :=
  catO (catO (encName im.moduleName) (encName im.itemName))
    (encExternType im.externtype)

theorem encImport_B (im : Import) (bs : Bytes) (h : encImport im = some bs) :
    Bimport bs im := by
  obtain ⟨nm₁, nm₂, xt⟩ := im
  simp only [encImport] at h
  obtain ⟨a, c, ha, hc, hbs⟩ := catO_eq h
  obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
  subst hbs; subst hac
  exact Bimport.mk p q c nm₁ nm₂ xt (encName_B _ p hp) (encName_B _ q hq)
    (encExternType_B xt c hc)

/-- `grammar Bimportsec : import*`. -/
def encImportSec (ims : List Import) : Option Bytes := encListSection 2 encImport ims

theorem encImportSec_B (ims : List Import) (bs : Bytes) (h : encImportSec ims = some bs) :
    Bimportsec bs ims :=
  encListSection_Bsection encImport_B 2 ims bs h

/-! ## Function section -/

/-- `grammar Bfuncsec : typeidx*`. -/
def encFuncSec (xs : List TypeIdx) : Option Bytes := encListSection 3 encIdx xs

theorem encFuncSec_B (xs : List TypeIdx) (bs : Bytes) (h : encFuncSec xs = some bs) :
    Bfuncsec bs xs :=
  encListSection_Bsection encIdx_B 3 xs bs h

/-! ## Table section -/

/-- `grammar Btable : table`.  The bare `tabletype` shorthand is taken exactly
when the initialiser is `REF.NULL ht` for the element type's own `ht`, which is
the side condition `-- if tt = at lim (REF NULL? ht)`. -/
def encTable (t : Table) : Option Bytes :=
  match t.tabletype.elem with
  | .ref _ ht =>
      if t.init = .cons (.refNull ht) .nil then encTableType t.tabletype
      else
        consO (tb 0x40) (consO (tb 0x00)
          (catO (encTableType t.tabletype) (encExpr t.init)))

theorem encTable_B (t : Table) (bs : Bytes) (h : encTable t = some bs) :
    Btable bs t := by
  obtain ⟨tt, init⟩ := t
  obtain ⟨ad, lm, el⟩ := tt
  cases el with
  | ref nul ht =>
      simp only [encTable] at h
      split at h
      · rename_i hinit
        subst hinit
        exact Btable.shorthand bs _ nul ht (encTableType_B _ bs h) rfl
      · obtain ⟨a, ha, hbs⟩ := consO_eq h
        obtain ⟨c, hc, hac⟩ := consO_eq ha
        subst hbs; subst hac
        obtain ⟨p, q, hp, hq, hcq⟩ := catO_eq hc
        subst hcq
        exact Btable.withInit p q _ init (encTableType_B _ p hp) (encExpr_B init q hq)

/-- `grammar Btablesec : table*`. -/
def encTableSec (tabs : List Table) : Option Bytes := encListSection 4 encTable tabs

theorem encTableSec_B (tabs : List Table) (bs : Bytes) (h : encTableSec tabs = some bs) :
    Btablesec bs tabs :=
  encListSection_Bsection encTable_B 4 tabs bs h

/-! ## Memory section -/

/-- `grammar Bmem : mem = | mt:Bmemtype => MEMORY mt`. -/
def encMem (mm : Mem) : Option Bytes := some (encMemType mm.memtype)

theorem encMem_B (mm : Mem) (bs : Bytes) (h : encMem mm = some bs) : Bmem bs mm := by
  simp only [encMem] at h
  injection h with h; subst h
  exact Bmem.mk _ mm.memtype (encMemType_B mm.memtype)

/-- `grammar Bmemsec : mem*`. -/
def encMemSec (ms : List Mem) : Option Bytes := encListSection 5 encMem ms

theorem encMemSec_B (ms : List Mem) (bs : Bytes) (h : encMemSec ms = some bs) :
    Bmemsec bs ms :=
  encListSection_Bsection encMem_B 5 ms bs h

/-! ## Tag section -/

/-- `grammar Btag : tag = | jt:Btagtype => TAG jt`. -/
def encTag (tg : Tag) : Option Bytes := encTagType tg.tagtype

theorem encTag_B (tg : Tag) (bs : Bytes) (h : encTag tg = some bs) : Btag bs tg :=
  Btag.mk bs tg.tagtype (encTagType_B tg.tagtype bs h)

/-- `grammar Btagsec : tag*`. -/
def encTagSec (ts : List Tag) : Option Bytes := encListSection 13 encTag ts

theorem encTagSec_B (ts : List Tag) (bs : Bytes) (h : encTagSec ts = some bs) :
    Btagsec bs ts :=
  encListSection_Bsection encTag_B 13 ts bs h

/-! ## Global section -/

/-- `grammar Bglobal : global = | gt:Bglobaltype e:Bexpr => GLOBAL gt e`. -/
def encGlobal (g : Global) : Option Bytes :=
  catO (encGlobalType g.globaltype) (encExpr g.init)

theorem encGlobal_B (g : Global) (bs : Bytes) (h : encGlobal g = some bs) :
    Bglobal bs g := by
  obtain ⟨gt, e⟩ := g
  simp only [encGlobal] at h
  obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
  subst hbs
  exact Bglobal.mk a b gt e (encGlobalType_B gt a ha) (encExpr_B e b hb)

/-- `grammar Bglobalsec : global*`. -/
def encGlobalSec (gs : List Global) : Option Bytes := encListSection 6 encGlobal gs

theorem encGlobalSec_B (gs : List Global) (bs : Bytes) (h : encGlobalSec gs = some bs) :
    Bglobalsec bs gs :=
  encListSection_Bsection encGlobal_B 6 gs bs h

/-! ## Export section -/

/-- `grammar Bexternidx : externidx`. -/
def encExternIdx : ExternIdx → Option Bytes
  | .func x => some (tb 0x00 :: lebU x.val)
  | .table x => some (tb 0x01 :: lebU x.val)
  | .mem x => some (tb 0x02 :: lebU x.val)
  | .global x => some (tb 0x03 :: lebU x.val)
  | .tag x => some (tb 0x04 :: lebU x.val)

theorem encExternIdx_B (xx : ExternIdx) (bs : Bytes) (h : encExternIdx xx = some bs) :
    Bexternidx bs xx := by
  cases xx <;> (simp only [encExternIdx] at h; injection h with h; subst h) <;>
    constructor <;> exact encU32_Bu32 _

/-- `grammar Bexport : export = | nm:Bname xx:Bexternidx => EXPORT nm xx`. -/
def encExport (e : Export) : Option Bytes :=
  catO (encName e.name) (encExternIdx e.externidx)

theorem encExport_B (e : Export) (bs : Bytes) (h : encExport e = some bs) :
    Bexport bs e := by
  obtain ⟨nm, xx⟩ := e
  simp only [encExport] at h
  obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
  subst hbs
  exact Bexport.mk a b nm xx (encName_B nm a ha) (encExternIdx_B xx b hb)

/-- `grammar Bexportsec : export*`. -/
def encExportSec (exs : List Export) : Option Bytes := encListSection 7 encExport exs

theorem encExportSec_B (exs : List Export) (bs : Bytes) (h : encExportSec exs = some bs) :
    Bexportsec bs exs :=
  encListSection_Bsection encExport_B 7 exs bs h

/-! ## Start section -/

/-- `grammar Bstartsec : start?`.  Absent when there is no start function, which
is `Bsection_`'s `eps` alternative. -/
def encStartSec : Option Start → Option Bytes
  | Option.none => some []
  | some s => encSectionBody 8 (lebU s.funcidx.val)

theorem encStartSec_B (so : Option Start) (bs : Bytes) (h : encStartSec so = some bs) :
    Bstartsec bs so := by
  cases so with
  | none =>
      simp only [encStartSec] at h
      injection h with h; subst h
      exact Bstartsec.absent [] Bsection.absent
  | some s =>
      simp only [encStartSec] at h
      exact Bstartsec.present bs s
        (encSectionBody_Bsection (Bstart.mk _ s.funcidx (encU32_Bu32 _)) h)

/-! ## Element section -/

/-- A single `REF.FUNC y` initialiser expression, inverted. -/
def refFuncOf : Expr → Option FuncIdx
  | .cons (.refFunc y) .nil => some y
  | _ => Option.none

theorem refFuncOf_spec (e : Expr) (y : FuncIdx) (h : refFuncOf e = some y) :
    e = .cons (.refFunc y) .nil := by
  unfold refFuncOf at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- `(REF.FUNC y)*` inverted: `none` unless every initialiser expression is a
single `REF.FUNC`. -/
def funcIdxsOf : List Expr → Option (List FuncIdx)
  | [] => some []
  | e :: rest =>
      match refFuncOf e, funcIdxsOf rest with
      | some y, some ys => some (y :: ys)
      | _, _ => Option.none

theorem funcIdxsOf_spec : ∀ (es : List Expr) (ys : List FuncIdx),
    funcIdxsOf es = some ys → refFuncExprs ys = es
  | [], ys, h => by injection h with h; subst h; rfl
  | e :: rest, ys, h => by
      simp only [funcIdxsOf] at h
      cases hy : refFuncOf e with
      | none => rw [hy] at h; exact absurd h (by simp)
      | some y =>
        cases hr : funcIdxsOf rest with
        | none => rw [hy, hr] at h; exact absurd h (by simp)
        | some zs =>
            rw [hy, hr] at h
            injection h with h
            subst h
            simp only [refFuncExprs, List.map_cons, List.cons.injEq]
            exact ⟨(refFuncOf_spec e y hy).symm, funcIdxsOf_spec rest zs hr⟩

/-- `grammar Belem : elem`.

FOUR of the eight alternatives are emitted, and they are the four that between
them cover every element segment the grammar can derive at all:

* `5:Bu32 rt e*` for a PASSIVE segment and `7:Bu32 rt e*` for a DECLARE one --
  both take an arbitrary `reftype` and arbitrary initialiser expressions;
* `4:Bu32 e_O e*` and `6:Bu32 x e_O e*` for an ACTIVE segment whose element type
  is `REF NULL FUNC`, the first when the table index is `0`;
* `0:Bu32 e_O y*` for an ACTIVE segment at table `0` whose element type is
  `REF FUNC` and whose initialisers are all `REF.FUNC`.

An ACTIVE segment with any other element type has NO `Belem` derivation:
alternatives 4 and 6 fix it to `REF NULL FUNC`, alternative 0 fixes it to
`REF FUNC` and alternative 2 reaches only `REF NULL FUNC` through `Belemkind`.
`none` there is forced by the pinned grammar. -/
def encElemBase (e : Elem) : Option Bytes :=
  match e.mode with
  | .passive =>
      catO (catO (some (lebU 5)) (encRefType e.reftype)) (encList encExpr e.init)
  | .declare =>
      catO (catO (some (lebU 7)) (encRefType e.reftype)) (encList encExpr e.init)
  | .active x off =>
      if e.reftype = .ref (some .null) (.abs .func) then
        (if x.val = 0 then
          catO (catO (some (lebU 4)) (encExpr off)) (encList encExpr e.init)
         else
          catO (catO (catO (some (lebU 6)) (some (lebU x.val))) (encExpr off))
            (encList encExpr e.init))
      else if e.reftype = .ref Option.none (.abs .func) then
        (if x.val = 0 then
          match funcIdxsOf e.init with
          | some ys => catO (catO (some (lebU 0)) (encExpr off)) (encList encIdx ys)
          | Option.none => Option.none
         else Option.none)
      else Option.none

theorem encElemBase_B (e : Elem) (bs : Bytes) (h : encElemBase e = some bs) :
    Belem bs e := by
  obtain ⟨rt, init, mode⟩ := e
  cases mode with
  | passive =>
      simp only [encElemBase] at h
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
      injection hp with hp
      subst hbs; subst hac; subst hp
      exact Belem.passiveExpr _ q b rt init (lebU_Bu32lit 5 (by decide))
        (encRefType_B rt q hq) (encList_Blist encExpr_B init b hb)
  | declare =>
      simp only [encElemBase] at h
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
      injection hp with hp
      subst hbs; subst hac; subst hp
      exact Belem.declareExpr _ q b rt init (lebU_Bu32lit 7 (by decide))
        (encRefType_B rt q hq) (encList_Blist encExpr_B init b hb)
  | active x off =>
      simp only [encElemBase] at h
      split at h
      · rename_i hrt
        subst hrt
        split at h
        · rename_i hx
          obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
          obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
          injection hp with hp
          subst hbs; subst hac; subst hp
          exact Belem.activeExprZero _ q b off init x (lebU_Bu32lit 4 (by decide))
            (encExpr_B off q hq) (encList_Blist encExpr_B init b hb) hx
        · obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
          obtain ⟨c, q, hc, hq, hac⟩ := catO_eq ha
          obtain ⟨p, u, hp, hu, hcu⟩ := catO_eq hc
          injection hp with hp; injection hu with hu
          subst hbs; subst hac; subst hcu; subst hp; subst hu
          exact Belem.activeExpr _ _ q b x off init (lebU_Bu32lit 6 (by decide))
            (encU32_Bu32 x) (encExpr_B off q hq) (encList_Blist encExpr_B init b hb)
      · split at h
        · rename_i hrt
          subst hrt
          split at h
          · rename_i hx
            split at h
            · rename_i ys hys
              obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
              obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
              injection hp with hp
              subst hbs; subst hac; subst hp
              have hd := Belem.activeFuncrefZero _ q b off ys x
                (lebU_Bu32lit 0 (by decide)) (encExpr_B off q hq)
                (encList_Blist encIdx_B ys b hb) hx
              rw [funcIdxsOf_spec init ys hys] at hd
              exact hd
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)

/-- The four compact function-index element forms.  They are candidates beside
the general expression forms because `orO` retains the shorter successful
encoding. -/
def encElemFunc (e : Elem) : Option Bytes :=
  match funcIdxsOf e.init with
  | Option.none => Option.none
  | some ys =>
      match e.mode with
      | .passive =>
          if e.reftype = .ref (some .null) (.abs .func) then
            catO (some (lebU 1 ++ [tb 0x00])) (encList encIdx ys)
          else Option.none
      | .declare =>
          if e.reftype = .ref (some .null) (.abs .func) then
            catO (some (lebU 3 ++ [tb 0x00])) (encList encIdx ys)
          else Option.none
      | .active x off =>
          if e.reftype = .ref (some .null) (.abs .func) then
            catO
              (catO
                (catO (some (lebU 2)) (some (lebU x.val)))
                (encExpr off))
              (catO (some [tb 0x00]) (encList encIdx ys))
          else Option.none

theorem encElemFunc_B (e : Elem) (bs : Bytes) (h : encElemFunc e = some bs) :
    Belem bs e := by
  obtain ⟨rt, init, mode⟩ := e
  cases mode with
  | passive =>
      cases hys : funcIdxsOf init with
      | none => simp [encElemFunc, hys] at h
      | some ys =>
          simp only [encElemFunc, hys] at h
          split at h
          · rename_i hrt
            subst rt
            obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
            injection ha with ha
            subst hbs; subst ha
            have hd := Belem.passiveFuncref (lebU 1) [tb 0x00] b
              (.ref (some .null) (.abs .func)) ys
              (lebU_Bu32lit 1 (by decide)) Belemkind.funcref
              (encList_Blist encIdx_B ys b hb)
            rw [funcIdxsOf_spec init ys hys] at hd
            exact hd
          · exact absurd h (by simp)
  | declare =>
      cases hys : funcIdxsOf init with
      | none => simp [encElemFunc, hys] at h
      | some ys =>
          simp only [encElemFunc, hys] at h
          split at h
          · rename_i hrt
            subst rt
            obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
            injection ha with ha
            subst hbs; subst ha
            have hd := Belem.declareFuncref (lebU 3) [tb 0x00] b
              (.ref (some .null) (.abs .func)) ys
              (lebU_Bu32lit 3 (by decide)) Belemkind.funcref
              (encList_Blist encIdx_B ys b hb)
            rw [funcIdxsOf_spec init ys hys] at hd
            exact hd
          · exact absurd h (by simp)
  | active x off =>
      cases hys : funcIdxsOf init with
      | none => simp [encElemFunc, hys] at h
      | some ys =>
          simp only [encElemFunc, hys] at h
          split at h
          · rename_i hrt
            subst rt
            obtain ⟨a, z, ha, hz, hbs⟩ := catO_eq h
            obtain ⟨bk, bys, hbk, hbys, hzb⟩ := catO_eq hz
            obtain ⟨c, be, hc, he, hab⟩ := catO_eq ha
            obtain ⟨bt, bx, ht, hx, hcx⟩ := catO_eq hc
            injection ht with ht; injection hx with hx; injection hbk with hbk
            subst hbs; subst hzb; subst hab; subst hcx
            subst ht; subst hx; subst hbk
            have hd := Belem.activeFuncref (lebU 2) (lebU x.val) be [tb 0x00] bys
              x off (.ref (some .null) (.abs .func)) ys
              (lebU_Bu32lit 2 (by decide)) (encU32_Bu32 x) (encExpr_B off be he)
              Belemkind.funcref (encList_Blist encIdx_B ys bys hbys)
            rw [funcIdxsOf_spec init ys hys] at hd
            simpa [List.append_assoc] using hd
          · exact absurd h (by simp)

/-- Canonical element encoding: choose the shorter of the general expression
form and the compact function-index form whenever both apply. -/
def encElem (e : Elem) : Option Bytes := orO (encElemBase e) (encElemFunc e)

theorem encElem_B (e : Elem) (bs : Bytes) (h : encElem e = some bs) : Belem bs e := by
  rcases orO_eq h with hbase | hfunc
  · exact encElemBase_B e bs hbase
  · exact encElemFunc_B e bs hfunc

/-- `grammar Belemsec : elem*`. -/
def encElemSec (es : List Elem) : Option Bytes := encListSection 9 encElem es

theorem encElemSec_B (es : List Elem) (bs : Bytes) (h : encElemSec es = some bs) :
    Belemsec bs es :=
  encListSection_Bsection encElem_B 9 es bs h

/-! ## Data section -/

/-- `grammar Bdata : data`.  The `0:Bu32` shorthand is taken at memory `0`. -/
def encData (d : Data) : Option Bytes :=
  match d.mode with
  | .passive => catO (some (lebU 1)) (encByteList d.bytes)
  | .active x off =>
      if x.val = 0 then
        catO (catO (some (lebU 0)) (encExpr off)) (encByteList d.bytes)
      else
        catO (catO (catO (some (lebU 2)) (some (lebU x.val))) (encExpr off))
          (encByteList d.bytes)

theorem encData_B (d : Data) (bs : Bytes) (h : encData d = some bs) : Bdata bs d := by
  obtain ⟨bl, mode⟩ := d
  cases mode with
  | passive =>
      simp only [encData] at h
      obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
      injection ha with ha
      subst hbs; subst ha
      exact Bdata.passive _ b bl (lebU_Bu32lit 1 (by decide)) (encByteList_B bl b hb)
  | active x off =>
      simp only [encData] at h
      split at h
      · rename_i hx
        obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
        obtain ⟨p, q, hp, hq, hac⟩ := catO_eq ha
        injection hp with hp
        subst hbs; subst hac; subst hp
        exact Bdata.activeZero _ q b off bl x (lebU_Bu32lit 0 (by decide))
          (encExpr_B off q hq) (encByteList_B bl b hb) hx
      · obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
        obtain ⟨c, q, hc, hq, hac⟩ := catO_eq ha
        obtain ⟨p, u, hp, hu, hcu⟩ := catO_eq hc
        injection hp with hp; injection hu with hu
        subst hbs; subst hac; subst hcu; subst hp; subst hu
        exact Bdata.active _ _ q b x off bl (lebU_Bu32lit 2 (by decide))
          (encU32_Bu32 x) (encExpr_B off q hq) (encByteList_B bl b hb)

/-- `grammar Bdatasec : data*`. -/
def encDataSec (ds : List Data) : Option Bytes := encListSection 11 encData ds

theorem encDataSec_B (ds : List Data) (bs : Bytes) (h : encDataSec ds = some bs) :
    Bdatasec bs ds :=
  encListSection_Bsection encData_B 11 ds bs h

/-! ## Code section -/

/-- Whether every local in a tail is the same as the head of its run. -/
def allLocalEq (l : Local) : List Local → Bool
  | [] => true
  | x :: xs => if x = l then allLocalEq l xs else false

theorem allLocalEq_replicate (l : Local) : ∀ (xs : List Local),
    allLocalEq l xs = true → xs = List.replicate xs.length l
  | [], _ => rfl
  | x :: xs, h => by
      simp only [allLocalEq] at h
      split at h
      · rename_i hx
        subst x
        rw [allLocalEq_replicate l xs h]
        rw [List.length_cons, List.length_replicate]
        exact (@List.replicate_succ _ l xs.length).symm
      · exact absurd h (by simp)

/-- `grammar Blocals : local* = | n:Bu32 t:Bvaltype => (LOCAL t)^n`.
The encoder accepts exactly nonempty uniform runs whose count fits `u32`. -/
def encLocalRun : List Local → Option Bytes
  | [] => none
  | l :: ls =>
      if allLocalEq l ls then
        if (l :: ls).length < 2 ^ 32 then
          catO (some (lebU (l :: ls).length)) (encValType l.valtype)
        else none
      else none

theorem encLocalRun_B (ls : List Local) (bs : Bytes) (h : encLocalRun ls = some bs) :
    Blocals bs ls := by
  match ls with
  | [] => exact absurd h (by simp [encLocalRun])
  | l :: rest =>
      simp only [encLocalRun] at h
      split at h
      · rename_i hsame
        split at h
        · rename_i hlen
          obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
          injection ha with ha
          subst hbs; subst ha
          have hrest := allLocalEq_replicate l rest hsame
          have hrun : l :: rest =
              List.replicate (l :: rest).length { valtype := l.valtype } := by
            cases l
            simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
            exact hrest
          have hd := Blocals.mk (lebU (l :: rest).length) b
            ⟨(l :: rest).length, hlen⟩ l.valtype
            (encU32_Bu32 ⟨(l :: rest).length, hlen⟩) (encValType_B _ b hb)
          rw [← hrun] at hd
          exact hd
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Prepend one local to an already grouped suffix.  Equal adjacent types merge
into its first run; otherwise a fresh singleton run is created. -/
def prependLocalRun (l : Local) : List (List Local) → List (List Local)
  | [] => [[l]]
  | [] :: rs => [l] :: [] :: rs
  | (h :: hs) :: rs =>
      if l = h then (l :: h :: hs) :: rs else [l] :: (h :: hs) :: rs

theorem prependLocalRun_flatten (l : Local) (rss : List (List Local)) :
    (prependLocalRun l rss).flatten = l :: rss.flatten := by
  cases rss with
  | nil => rfl
  | cons r rs =>
      cases r with
      | nil => rfl
      | cons h hs =>
          simp only [prependLocalRun]
          split <;> simp

theorem prependLocalRun_length_le (l : Local) (rss : List (List Local)) :
    (prependLocalRun l rss).length ≤ rss.length + 1 := by
  cases rss with
  | nil => simp [prependLocalRun]
  | cons r rs =>
      cases r with
      | nil => simp [prependLocalRun]
      | cons h hs =>
          simp only [prependLocalRun]
          split <;> simp

/-- Canonical maximal adjacent-equal local runs.  The right fold is structural;
`prependLocalRun` performs the sole possible boundary merge. -/
def localRuns : List Local → List (List Local)
  | [] => []
  | l :: ls => prependLocalRun l (localRuns ls)

theorem localRuns_flatten (ls : List Local) : (localRuns ls).flatten = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [localRuns, prependLocalRun_flatten, ih]

theorem localRuns_length_le (ls : List Local) :
    (localRuns ls).length ≤ ls.length := by
  induction ls with
  | nil => simp [localRuns]
  | cons l ls ih =>
      simp only [localRuns, List.length_cons]
      exact Nat.le_trans (prependLocalRun_length_le l (localRuns ls))
        (Nat.add_le_add_right ih 1)

/-- A nonempty run whose tail is equal to its head. -/
def LocalRunOK : List Local → Prop
  | [] => False
  | l :: ls => allLocalEq l ls = true

/-- Every member is a uniform nonempty local run. -/
def LocalRunsOK (rss : List (List Local)) : Prop :=
  ∀ r, r ∈ rss → LocalRunOK r

theorem prependLocalRun_ok (l : Local) (rss : List (List Local))
    (h : LocalRunsOK rss) : LocalRunsOK (prependLocalRun l rss) := by
  intro r hr
  cases rss with
  | nil =>
      simp only [prependLocalRun, List.mem_cons] at hr
      rcases hr with rfl | hnil
      · rfl
      · contradiction
  | cons run rs =>
      cases run with
      | nil =>
          have hf : False := h [] (by simp)
          exact hf.elim
      | cons x xs =>
          have hx : allLocalEq x xs = true := h (x :: xs) (by simp)
          simp only [prependLocalRun] at hr
          split at hr
          · rename_i heq
            subst x
            rcases List.mem_cons.mp hr with rfl | hr
            · simp [LocalRunOK, allLocalEq, hx]
            · exact h r (List.mem_cons_of_mem _ hr)
          · rcases List.mem_cons.mp hr with rfl | hr
            · rfl
            · exact h r hr

theorem localRuns_ok (ls : List Local) : LocalRunsOK (localRuns ls) := by
  induction ls with
  | nil => simp [localRuns, LocalRunsOK]
  | cons l ls ih => exact prependLocalRun_ok l (localRuns ls) ih

theorem localRuns_member_length_le {ls r : List Local}
    (hr : r ∈ localRuns ls) : r.length ≤ ls.length := by
  have member_length_le_flatten : ∀ (rss : List (List Local)) (r : List Local),
      r ∈ rss → r.length ≤ rss.flatten.length := by
    intro rss
    induction rss with
    | nil => simp
    | cons x xs ih =>
        intro r hr
        simp only [List.mem_cons] at hr
        simp only [List.flatten_cons, List.length_append]
        rcases hr with rfl | hr
        · omega
        · have hle := ih r hr
          omega
  have hflat := member_length_le_flatten (localRuns ls) r hr
  rw [localRuns_flatten] at hflat
  exact hflat

/-- `grammar Bfunc : code`, with the source's `-- if |$concat_(local, loc**)| <
2^32` as the guard: a function with `2^32` or more locals has no derivation. -/
def encFuncBody (c : Code) : Option Bytes :=
  if c.1.length < 2 ^ 32 then
    catO (encList encLocalRun (localRuns c.1)) (encExpr c.2)
  else Option.none

theorem encFuncBody_B (c : Code) (bs : Bytes) (h : encFuncBody c = some bs) :
    Bfunc bs c := by
  obtain ⟨ls, e⟩ := c
  simp only [encFuncBody] at h
  split at h
  · rename_i hlen
    obtain ⟨a, b, ha, hb, hbs⟩ := catO_eq h
    subst hbs
    have hd := Bfunc.mk a b (localRuns ls) e (encList_Blist encLocalRun_B _ a ha)
      (encExpr_B e b hb) (by rw [localRuns_flatten]; exact hlen)
    rw [localRuns_flatten] at hd
    exact hd
  · exact absurd h (by simp)

/-- `len:Bu32` followed by the payload -- the shape of `Bcode`. -/
def encSized (payload : Bytes) : Option Bytes :=
  if payload.length < 2 ^ 32 then some (lebU payload.length ++ payload)
  else Option.none

theorem encSized_Bcode {c : Code} {payload bs : Bytes} (hf : Bfunc payload c)
    (h : encSized payload = some bs) : Bcode bs c := by
  simp only [encSized] at h
  split at h
  · rename_i hlen
    injection h with h; subst h
    exact Bcode.mk (lebU payload.length) payload ⟨payload.length, hlen⟩ c
      (lebU_BuN _ 32 hlen) hf rfl
  · exact absurd h (by simp)

/-- `grammar Bcode : code = | len:Bu32 code:Bfunc => code`. -/
def encCode (c : Code) : Option Bytes :=
  match encFuncBody c with
  | some p => encSized p
  | Option.none => Option.none

theorem encCode_B (c : Code) (bs : Bytes) (h : encCode c = some bs) : Bcode bs c := by
  simp only [encCode] at h
  split at h
  · rename_i p hp
    exact encSized_Bcode (encFuncBody_B c p hp) h
  · exact absurd h (by simp)

/-- `grammar Bcodesec : code*`. -/
def encCodeSec (cs : List Code) : Option Bytes := encListSection 10 encCode cs

theorem encCodeSec_B (cs : List Code) (bs : Bytes) (h : encCodeSec cs = some bs) :
    Bcodesec bs cs :=
  encListSection_Bsection encCode_B 10 cs bs h

/-! ## Data count section -/

/-- Whether the data count section has to be emitted.  `Bmodule`'s second side
condition is `-- if (n? =/= eps \/ $dataidx_funcs(func*) = eps)`: the section may
be omitted exactly when no function body mentions a data index.  It is also
emitted whenever there IS a data segment, which is the choice every producer
makes and which keeps the count and the section in step. -/
def needsDataCnt (m : Module) : Bool :=
  match m.datas, dataIdxFuncs m.funcs with
  | [], [] => false
  | _, _ => true

/-- The `u32?` the data count section carries. -/
def dataCnt? (m : Module) : Option U32 :=
  if needsDataCnt m then
    (if h : m.datas.length < 2 ^ 32 then some ⟨m.datas.length, h⟩ else Option.none)
  else Option.none

/-- `grammar Bdatacntsec : u32?`. -/
def encDataCntSec (m : Module) : Option Bytes :=
  if needsDataCnt m then
    (if m.datas.length < 2 ^ 32 then encSectionBody 12 (lebU m.datas.length)
     else Option.none)
  else some []

theorem encDataCntSec_B (m : Module) (bs : Bytes) (h : encDataCntSec m = some bs) :
    Bdatacntsec bs (dataCnt? m) := by
  simp only [encDataCntSec, dataCnt?] at h ⊢
  split at h
  · rename_i hneed
    rw [if_pos hneed]
    split at h
    · rename_i hlen
      rw [dif_pos hlen]
      exact Bdatacntsec.present bs ⟨m.datas.length, hlen⟩
        (encSectionBody_Bsection
          (Bdatacnt.mk _ ⟨m.datas.length, hlen⟩ (lebU_BuN _ 32 hlen)) h)
    · exact absurd h (by simp)
  · rename_i hneed
    rw [if_neg hneed]
    injection h with h; subst h
    exact Bdatacntsec.absent [] Bsection.absent

/-- `Bmodule`'s first side condition, `-- (if n = |data*|)?`. -/
theorem dataCnt?_length (m : Module) :
    ∀ k : U32, dataCnt? m = some k → k.val = m.datas.length := by
  intro k hk
  simp only [dataCnt?] at hk
  split at hk
  · split at hk
    · injection hk with hk; subst hk; rfl
    · exact absurd hk (by simp)
  · exact absurd hk (by simp)

/-- `Bmodule`'s second side condition,
`-- if (n? =/= eps \/ $dataidx_funcs(func*) = eps)`. -/
theorem dataCnt?_present (m : Module) (bs : Bytes) (h : encDataCntSec m = some bs) :
    dataCnt? m ≠ Option.none ∨ dataIdxFuncs m.funcs = [] := by
  simp only [encDataCntSec] at h
  simp only [dataCnt?]
  split at h
  · rename_i hneed
    rw [if_pos hneed]
    split at h
    · rename_i hlen
      rw [dif_pos hlen]
      exact Or.inl (by simp)
    · exact absurd h (by simp)
  · rename_i hneed
    refine Or.inr ?_
    simp only [needsDataCnt] at hneed
    split at hneed
    · assumption
    · exact absurd rfl hneed

/-! ## The module -/

/-- `grammar Bmagic : () = 0x00 0x61 0x73 0x6D => ()`. -/
def magicBytes : Bytes := [tb 0x00, tb 0x61, tb 0x73, tb 0x6D]

/-- `grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()`. -/
def versionBytes : Bytes := [tb 0x01, tb 0x00, tb 0x00, tb 0x00]

/-- NO CUSTOM SECTION IS EMITTED: every one of the fourteen `Bcustomsec*`
positions of `Bmodule` is instantiated with the empty sequence, and this is the
derivation that says so. -/
theorem starNil : Star Bcustomsec [] [] := ⟨0, Rep.nil⟩

/-- The function section's `typeidx*`: the FUNCTION / CODE SPLIT, left half. -/
def funcTypeIdxs (fs : List Func) : List TypeIdx := fs.map (fun f => f.typeidx)

/-- The code section's `code*`: the FUNCTION / CODE SPLIT, right half. -/
def funcCodes (fs : List Func) : List Code := fs.map (fun f => (f.locals, f.body))

/-- `-- (if func = FUNC typeidx local* expr)*`: pairing the two halves back
together returns the functions they were split from. -/
theorem funcs_zip (fs : List Func) :
    List.zipWith (fun (x : TypeIdx) (c : Code) =>
      ({ typeidx := x, locals := c.1, body := c.2 } : Func))
      (funcTypeIdxs fs) (funcCodes fs) = fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp only [funcTypeIdxs, funcCodes, List.map_cons, List.zipWith_cons_cons] at ih ⊢
      rw [ih]

/-- The two halves have the same length, which is what makes the starred side
condition's pointwise reading the intended one. -/
theorem funcTypeIdxs_length (fs : List Func) :
    (funcTypeIdxs fs).length = (funcCodes fs).length := by
  simp [funcTypeIdxs, funcCodes]

/-- `grammar Bmodule : module`, in the source's SECTION ORDER -- which is not the
numeric order of the section ids: the tag section (13) comes between the memory
(5) and global (6) sections, and the data count section (12) between the element
(9) and code (10) sections. -/
def encModule (m : Module) : Option Bytes :=
  catO (catO (catO (catO (catO (catO (catO (catO (catO (catO (catO (catO (catO
    (catO (some magicBytes) (some versionBytes))
      (encTypeSec m.types))
      (encImportSec m.imports))
      (encFuncSec (funcTypeIdxs m.funcs)))
      (encTableSec m.tables))
      (encMemSec m.mems))
      (encTagSec m.tags))
      (encGlobalSec m.globals))
      (encExportSec m.exports))
      (encStartSec m.start))
      (encElemSec m.elems))
      (encDataCntSec m))
      (encCodeSec (funcCodes m.funcs)))
      (encDataSec m.datas)

/-- **`grammar Bmodule : module`.** -/
theorem encModule_Bmodule (m : Module) (bs : Bytes) (h : encModule m = some bs) :
    Bmodule bs m := by
  unfold encModule at h
  obtain ⟨w13, bda, h13, hda, e13⟩ := catO_eq h
  obtain ⟨w12, bco, h12, hco, e12⟩ := catO_eq h13
  obtain ⟨w11, bdc, h11, hdc, e11⟩ := catO_eq h12
  obtain ⟨w10, bel, h10, hel, e10⟩ := catO_eq h11
  obtain ⟨w9, bst, h9, hst, e9⟩ := catO_eq h10
  obtain ⟨w8, bex, h8, hex, e8⟩ := catO_eq h9
  obtain ⟨w7, bgl, h7, hgl, e7⟩ := catO_eq h8
  obtain ⟨w6, btg, h6, htg, e6⟩ := catO_eq h7
  obtain ⟨w5, bme, h5, hme, e5⟩ := catO_eq h6
  obtain ⟨w4, bta, h4, hta, e4⟩ := catO_eq h5
  obtain ⟨w3, bfu, h3, hfu, e3⟩ := catO_eq h4
  obtain ⟨w2, bim, h2, him, e2⟩ := catO_eq h3
  obtain ⟨w1, bty, h1, hty, e1⟩ := catO_eq h2
  obtain ⟨bmag, bver, hmag, hver, e0⟩ := catO_eq h1
  injection hmag with hmag; injection hver with hver
  subst e13; subst e12; subst e11; subst e10; subst e9; subst e8; subst e7
  subst e6; subst e5; subst e4; subst e3; subst e2; subst e1; subst e0
  subst hmag; subst hver
  have hb := Bmodule.mk magicBytes versionBytes
    [] [] [] [] [] [] [] [] [] [] [] [] [] []
    [] [] [] [] [] [] [] [] [] [] [] [] [] []
    bty bim bfu bta bme btg bgl bex bst bel bdc bco bda
    m.types m.imports (funcTypeIdxs m.funcs) m.tables m.mems m.tags m.globals
    m.exports m.start m.elems (dataCnt? m) (funcCodes m.funcs) m.datas m.funcs
    Bmagic.mk Bversion.mk
    starNil (encTypeSec_B _ bty hty)
    starNil (encImportSec_B _ bim him)
    starNil (encFuncSec_B _ bfu hfu)
    starNil (encTableSec_B _ bta hta)
    starNil (encMemSec_B _ bme hme)
    starNil (encTagSec_B _ btg htg)
    starNil (encGlobalSec_B _ bgl hgl)
    starNil (encExportSec_B _ bex hex)
    starNil (encStartSec_B _ bst hst)
    starNil (encElemSec_B _ bel hel)
    starNil (encDataCntSec_B m bdc hdc)
    starNil (encCodeSec_B _ bco hco)
    starNil (encDataSec_B _ bda hda)
    starNil
    (dataCnt?_length m) (dataCnt?_present m bdc hdc)
    (funcTypeIdxs_length m.funcs) (funcs_zip m.funcs).symm
  simpa using hb


/-! ## The public encoder

`encModule` is `Option`-valued so that the failure modes listed at the head of
this file are visible in its type rather than hidden behind a junk value.  The
PUBLIC encoder has to be TOTAL, so it is `encModule` with the empty byte
sequence as that junk value -- and `encodable` is the explicit, DECIDABLE
precondition under which the junk value is not reached.  Nothing below hides a
hypothesis: `encodable m` is a `Bool` computed from `m`. -/

/-- The precondition of the encoder's correctness theorem: `encModule` really
did produce bytes for this module.  It is a `Bool`, hence decidable, and
`Wasm/Core/EncodeSound.lean` composes it with decoder completeness. -/
def encodable (m : Module) : Bool := (encModule m).isSome

/-- The canonical encoding of a module as the grammar's `byte*`.  TOTAL: the
empty sequence on a module the pinned grammar cannot express. -/
def encodeBytes (m : Module) : Bytes := (encModule m).getD []

/-- **The canonical binary encoding of a pinned WebAssembly Core 3.0 module.**
Total, computable, and choice-free: no `Classical.choice` occurs in this
definition or in anything it calls. -/
def encode (m : Module) : ByteArray :=
  WasmGemmGnaf.Foundation.Bytes.pack ((encodeBytes m).map (fun b => UInt8.ofNat b.val))

/-- `encodable` says exactly what it looks like it says. -/
theorem encodeBytes_eq {m : Module} {bs : Bytes} (h : encModule m = some bs) :
    encodeBytes m = bs := by
  simp [encodeBytes, h]

/-- **`grammar Bmodule : module`, at the total encoder.**  Under the explicit
decidable precondition, the bytes `encode` produces are a derivation of the
pinned binary grammar for the module they were produced from. -/
theorem encodeBytes_Bmodule (m : Module) (h : encodable m = true) :
    Bmodule (encodeBytes m) m := by
  unfold encodable at h
  cases hm : encModule m with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some bs => rw [encodeBytes_eq hm]; exact encModule_Bmodule m bs hm

/-! ## Explicit amended-authority API

These definitions never rely on the global pinned instance.  Public wrappers
can therefore call the amended encoder without an ambient instance silently
selecting the pinned format. -/

omit authority in
/-- Option-valued module encoder at the amended binary authority. -/
def encModuleA (m : Module) : Option Bytes :=
  @encModule amendedBinaryAuthority m

omit authority in
/-- Computed success flag for the amended encoder. -/
def encodableA (m : Module) : Bool := (encModuleA m).isSome

omit authority in
/-- Amended canonical bytes, with the ordinary total fallback. -/
def encodeBytesA (m : Module) : Bytes := (encModuleA m).getD []

omit authority in
/-- Total, computational amended module encoder. -/
def encodeA (m : Module) : ByteArray :=
  WasmGemmGnaf.Foundation.Bytes.pack
    ((encodeBytesA m).map (fun b => UInt8.ofNat b.val))

omit authority in
theorem encModuleA_BmoduleA (m : Module) (bs : Bytes)
    (h : encModuleA m = some bs) : BmoduleA bs m :=
  @encModule_Bmodule amendedBinaryAuthority m bs h

omit authority in
theorem encodeBytesA_eq {m : Module} {bs : Bytes} (h : encModuleA m = some bs) :
    encodeBytesA m = bs := by
  simp [encodeBytesA, h]

omit authority in
/-- Soundness of the total amended encoder on its computed success branch. -/
theorem encodeA_BmoduleA (m : Module) (h : encodableA m = true) :
    BmoduleA (encodeBytesA m) m := by
  unfold encodableA at h
  cases hm : encModuleA m with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some bs => rw [encodeBytesA_eq hm]; exact encModuleA_BmoduleA m bs hm

/-! ## Kernel-checked encodings

These are not tests: each is a closed term the kernel checks, pinning down a
canonical choice a reader can compare against `5.4-binary.modules.spectec`
without reading a proof.  They exist at all only because `lebU` is structurally
recursive; a well-founded `lebU` would leave every one of them unavailable. -/

/-- MINIMAL LEB128, at the value where minimality is visible: the encoding of
`0` is ONE byte.  `0x80 0x00` is also a `Bu32` derivation of `0` --- the pinned
`BuN` is permissive --- and this encoder never emits it. -/
example : lebU 0 = [tb 0x00] := by rfl

/-- `128` is the first value that needs two bytes. -/
example : lebU 128 = [tb 0x80, tb 0x01] := by rfl

/-- `624485`, the worked example of the LEB128 literature. -/
example : lebU 624485 = [tb 0xE5, tb 0x8E, tb 0x26] := by rfl

/-- THE EMPTY MODULE encodes to the preamble and NOTHING else: every section is
empty, and an empty section is omitted rather than emitted empty. -/
example :
    encodeBytes { types := [], imports := [], tags := [], globals := [], mems := [],
                  tables := [], funcs := [], datas := [], elems := [], start := none,
                  exports := [] }
      = [tb 0x00, tb 0x61, tb 0x73, tb 0x6D, tb 0x01, tb 0x00, tb 0x00, tb 0x00] := by
  rfl

/-- A START SECTION is `0x08` and a `Bu32` payload, at the pinned position. -/
example :
    encodeBytes { types := [], imports := [], tags := [], globals := [], mems := [],
                  tables := [], funcs := [], datas := [], elems := [],
                  start := some { funcidx := ⟨3, by decide⟩ }, exports := [] }
      = [tb 0x00, tb 0x61, tb 0x73, tb 0x6D, tb 0x01, tb 0x00, tb 0x00, tb 0x00,
         tb 0x08, tb 0x01, tb 0x03] := by
  rfl

/-- A DATA SEGMENT drags the DATA COUNT SECTION in with it, and at the pinned
SECTION ORDER rather than the numeric one: `0x0C` comes BEFORE `0x0B`. -/
example :
    encodeBytes { types := [], imports := [], tags := [], globals := [], mems := [],
                  tables := [], funcs := [],
                  datas := [{ bytes := [], mode := .passive }],
                  elems := [], start := none, exports := [] }
      = [tb 0x00, tb 0x61, tb 0x73, tb 0x6D, tb 0x01, tb 0x00, tb 0x00, tb 0x00,
         tb 0x0C, tb 0x01, tb 0x01,
         tb 0x0B, tb 0x03, tb 0x01, tb 0x01, tb 0x00] := by
  rfl

/-- ANTI-VACUITY: `encodable` is NOT constantly `true`.  `CALL_REF` has no
production in `5.3-binary.instructions.spectec` at the pinned commit, so a
module whose function body contains one has no `Bmodule` derivation at all, and
the encoder says so instead of inventing an opcode. -/
example :
    @encodable pinnedBinaryAuthority
      { types := [], imports := [], tags := [], globals := [], mems := [],
                tables := [],
                funcs := [{ typeidx := ⟨0, by decide⟩, locals := [],
                            body := .cons (.callRef (.idx ⟨0, by decide⟩)) .nil }],
                datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- The `0xFD` vector space is encoded: this concrete `V128.STORE` crosses the
module encoder as an executable coverage check. -/
example :
    @encodable pinnedBinaryAuthority
      { types := [], imports := [], tags := [], globals := [], mems := [],
                tables := [],
                funcs := [{ typeidx := ⟨0, by decide⟩, locals := [],
                            body := .cons (.vstore .v128 ⟨0, by decide⟩
                              { align := ⟨0, by decide⟩, offset := ⟨0, by decide⟩ })
                              .nil }],
                datas := [], elems := [], start := none, exports := [] } = true := by
  decide

end WasmGemmGnaf.Wasm.Core.Binary
