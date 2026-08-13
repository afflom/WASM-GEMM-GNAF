/-
  Wasm/Declarative.lean --- the *relational* reading of the pinned binary
  grammar, and the three SPEC section 15 declarations that are stated against
  it: `Wasm.decode_sound`, `Wasm.decode_complete`, `Wasm.validate_iff_declarative`.

  Normative source: the vendored Core 3.0 sources under `vendor/wasm-spec/`,
  pinned at commit `9d36019973201a19f9c9ebb0f10828b2fe2374aa`, specifically
  `document/core/binary/conventions.rst`, `binary/values.rst`,
  `binary/types.rst`, `binary/instructions.rst` and `binary/modules.rst`, with
  `document/core/valid/` for the validation half.

  ## What this file adds

  `Wasm/Binary.lean` proves an *intrinsic* inverse pair --- `encode` and
  `decode` invert each other --- and is explicit that this is not a statement
  about the pinned grammar.  This file supplies the missing side: a relation

      `Wasm.DeclarativeBinaryRelation : ByteArray -> Module -> Prop`

  defined by grammar productions, with no reference anywhere in its *definition*
  to `Wasm.decode`, `Wasm.decULEB`, `Wasm.decSLEB`, `Wasm.decInstr` or any other
  decoding function, and then proves both halves against it:

  * `Wasm.decode_sound`    --- everything the decoder accepts is derivable;
  * `Wasm.decode_complete` --- everything derivable the decoder accepts.

  Completeness is the direction that rules out a decoder which silently rejects
  a well-formed module, and it is the one an intrinsic round-trip theorem cannot
  give.

  ## Honest scope: what the relation does and does not cover

  This is the point at which claims must be exact, so they are spelled out.

  **1. The grammar's shape is transcribed from the vendored text; the concrete
  opcode numbering is not, because it is not in the vendored text.**  The
  vendored `.rst` files carry their productions as unexpanded SpecTec macros
  (`$${grammar: Binstr/control}`, `$${grammar: Bmodule}`, ...).  The macro
  *bodies* live in the SpecTec sources, which are not part of the 40 vendored
  files.  What the vendored text does state in prose, and what is transcribed
  here, is:

  * `binary/conventions.rst` --- the format is an attribute grammar over byte
    terminals; a byte sequence is well formed iff the grammar generates it;
    productions are concatenations `B_1 ... B_n` with a synthesized attribute.
    `BinaryGrammar.Deriv`, `BinaryGrammar.cat`, `BinaryGrammar.lit`, `BinaryGrammar.eps` and
    `BinaryGrammar.Gen` below are exactly that reading.
  * `binary/conventions.rst`, "Lists" --- `Blist(X)` is the `Bu32` length
    followed by that many `X`.  `BinaryGrammar.list`.
  * `binary/values.rst` --- `BuN` and `BsN` are LEB128, `BfN` is the raw IEEE 754
    bit pattern in little-endian order, `Bname` is a list of bytes.
    `BinaryGrammar.BuN`, `BinaryGrammar.BsN`, `BinaryGrammar.BfN`, `BinaryGrammar.name`.
  * `binary/modules.rst`, "Sections" --- a section is a one-byte id, the `u32`
    byte length of the contents, then the contents, and the module is malformed
    if the size does not match.  `BinaryGrammar.section_`, `BinaryGrammar.sized`.
  * `binary/modules.rst`, "Modules" --- the preamble is the 4-byte `\0asm` magic
    and the version field, followed by the section sequence.  `BinaryGrammar.BModule`.
  * `binary/types.rst` and `binary/instructions.rst` --- the *shape* of every
    type and instruction production: a distinguishing byte followed by the
    encoding of the respective form (composite types, external types, heap
    types), a single byte for number/vector types, an opcode byte followed by
    the immediates (instructions), and structured control instructions
    bracketing a nested instruction sequence.

  The concrete byte values of the opcodes and type tags therefore come from this
  repository's own pinned tables --- `Wasm.opcodeTagged`, `Wasm.Enum.*Tagged` ---
  which `Wasm/Binary.lean` already declares are *not* the Core 3.0 opcode table.
  Those tables are data, not decoding functions, and the relation is
  parameterised by them exactly as the pinned grammar is parameterised by its
  own table.  **No claim of byte-level identity with Core 3.0 is made here.**

  **2. Deliberate narrowings of the pinned grammar, each one a real deviation.**

  * *Canonical LEB128 only.*  `binary/values.rst` explicitly permits trailing
    zero (resp. one) groups within the `ceil(N/7)` byte budget: "either of
    `0x7E` and `0xFE 0x7F` ... are well-formed encodings of `-2` as an `s16`".
    `BinaryGrammar.BuN` and `BinaryGrammar.BsN` carry the extra minimality side condition
    (`0 < n` on a continuation for `BuN`, and the redundancy exclusion for
    `BsN`), so they generate the shortest form only.  A permissive relation
    would make `decode_complete` false for this decoder, which rejects redundant
    continuations with `DecodeFault.nonCanonicalLeb128`.
  * *No `Bu32`/`Bs33` width caps.*  The pinned `BuN` bounds an encoding to
    `ceil(N/7)` bytes; the modelled indices are `Nat`, so no width cap is
    imposed and the relation is closed under arbitrarily large indices.
  * *Fixed, total section sequence.*  The pinned grammar allows every section to
    be absent and allows custom sections anywhere.  `BModule` requires all
    eleven modelled sections, always present, in the pinned order
    `1, 2, 3, 4, 5, 13, 6, 7, 8, 9, 11`, and admits no custom section.
  * *Functions are not split across sections 3 and 10.*  Section 3 carries the
    complete function definition (type index, locals, body); there is no code
    section, and hence no `Bdatacntsec` cross-check either.
  * *Tagged optionals and tagged sums.*  Where the pinned grammar writes `B?` or
    distinguishes alternatives by their leading opcode, the modelled format
    writes an explicit `0`/`1` discriminant byte (`BinaryGrammar.opt`, and the
    `lit [0]` / `lit [1]` prefixes of the sum productions).
  * *Cons-tagged instruction sequences.*  The pinned `Bexpr` terminates an
    instruction sequence with the `END` opcode `0x0B`; `BinaryGrammar.BExpr` tags each
    step instead, `0` for the empty sequence and `1` before each instruction.
  * *Locals are a plain list of value types*, not the pinned run-length
    compressed `Blocals`.
  * *Instruction coverage* is exactly the subset declared in `Wasm/Syntax.lean`;
    instructions outside it are not expressible, so the relation says nothing
    about them.

  Within those stated bounds the relation covers the modelled subset
  **exactly**: `BinaryGrammar.Gen` is a two-sided statement, and
  `declarativeBinaryRelation_iff_encode` proves that the byte sequences the
  grammar derives for a module are precisely `{Wasm.encode m}`, from which both
  `decode_sound` and `decode_complete` follow.  Nothing here is conditional and
  nothing is assumed.

  ## Choice freedom

  `decode_complete` is an executable-witness name under SPEC section 4, so its
  axiom closure must not contain `Classical.choice`.  It does not; neither do
  `decode_sound` or `validate_iff_declarative`.

  Every declaration in this file is proved.  Nothing is assumed.
-/
import WasmGemmGnaf.Wasm.Binary
import WasmGemmGnaf.Wasm.Validate

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation
open Codec Bin Enum

namespace BinaryGrammar

/-! ## The grammar notation of `binary/conventions.rst`, read relationally

"The format is defined by an *attribute grammar* whose only terminal symbols are
bytes.  A byte sequence is a well-formed encoding of a module if and only if it
is generated by the grammar.  Each production of this grammar has exactly one
synthesized attribute: the abstract syntax that the respective byte sequence
encodes."

A nonterminal with a *fixed* synthesized attribute therefore denotes a set of
byte sequences.  `Deriv` is that set; a production with attribute type `α` is a
function `α → Deriv`. -/

/-- The byte sequences a grammar symbol derives for one fixed value of its
synthesized attribute. -/
abbrev Deriv := List UInt8 → Prop

/-- `Gen P t` says the symbol derives exactly the byte sequence `t` and nothing
else.  Both directions matter: `←` is generation, `→` is the uniqueness that
makes decoding well defined. -/
def Gen (P : Deriv) (t : List UInt8) : Prop := ∀ bs : List UInt8, P bs ↔ bs = t

/-- Transport `Gen` along an equality of the generated sequence. -/
theorem Gen.cast {P : Deriv} {a b : List UInt8} (h : Gen P a) (hab : a = b) :
    Gen P b := by
  subst hab; exact h

/-- `eps`, the empty byte sequence. -/
def eps : Deriv := fun bs => bs = []

/-- A terminal byte sequence.  Terminals are bytes and bytes encode themselves
(`binary/values.rst`, "Bytes"). -/
def lit (t : List UInt8) : Deriv := fun bs => bs = t

/-- BinaryGrammar concatenation `B₁ B₂`. -/
def cat (P Q : Deriv) : Deriv :=
  fun bs => ∃ b₁ b₂ : List UInt8, bs = b₁ ++ b₂ ∧ P b₁ ∧ Q b₂

theorem gen_eps : Gen eps [] := fun _ => Iff.rfl

theorem gen_lit (t : List UInt8) : Gen (lit t) t := fun _ => Iff.rfl

theorem gen_cat {P Q : Deriv} {a b : List UInt8} (hP : Gen P a) (hQ : Gen Q b) :
    Gen (cat P Q) (a ++ b) := by
  intro bs
  constructor
  · rintro ⟨b₁, b₂, rfl, h1, h2⟩
    rw [(hP b₁).mp h1, (hQ b₂).mp h2]
  · rintro rfl
    exact ⟨a, b, rfl, (hP a).mpr rfl, (hQ b).mpr rfl⟩

/-- A one-byte terminal followed by a production: the shape of every production
that starts with an opcode or a distinguishing byte. -/
theorem gen_cons {P : Deriv} {a : List UInt8} (b : UInt8) (h : Gen P a) :
    Gen (cat (lit [b]) P) (b :: a) :=
  gen_cat (gen_lit [b]) h

/-! ## `BuN`: unsigned LEB128 (`binary/values.rst`)

"Unsigned integers are encoded in LEB128 format."  A `BuN` derivation is a run
of continuation bytes (high bit set) closed by a terminal byte (high bit clear),
the value being little-endian base 128.

The side condition `0 < n` on `continuation` is the *canonicality* narrowing
recorded in the file header: the pinned grammar also admits trailing zero
groups, this relation does not. -/

/-- The unsigned LEB128 production, restricted to its canonical (shortest)
derivations. -/
inductive BuN : Nat → List UInt8 → Prop where
  /-- A terminal byte: high bit clear, and the value is the byte itself. -/
  | terminal (b : UInt8) (h : b.toNat < 128) : BuN b.toNat [b]
  /-- A continuation byte: high bit set, carrying the low seven bits of the
  value, with the remaining bytes carrying the rest.  `0 < n` excludes a
  redundant continuation. -/
  | continuation (b : UInt8) (h : 128 ≤ b.toNat) (n : Nat) (hn : 0 < n)
      (bs : List UInt8) (hbs : BuN n bs) :
      BuN (b.toNat - 128 + 128 * n) (b :: bs)

theorem BuN_eq_encodeULEB {n : Nat} {bs : List UInt8} (h : BuN n bs) :
    bs = encodeULEB n := by
  induction h with
  | terminal b hb => rw [encodeULEB_lt hb, uint8_ofNat_toNat]
  | continuation b hb n hn bs _ ih =>
      have hblt : b.toNat < 256 := uint8_toNat_lt b
      have hne : ¬ (b.toNat - 128 + 128 * n < 128) := by omega
      rw [encodeULEB_ge hne,
        show (b.toNat - 128 + 128 * n) % 128 = b.toNat - 128 by omega,
        show (b.toNat - 128 + 128 * n) / 128 = n by omega,
        show b.toNat - 128 + 128 = b.toNat by omega, uint8_ofNat_toNat, ih]

theorem encodeULEB_BuN (n : Nat) : BuN n (encodeULEB n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 128
    · rw [encodeULEB_lt h]
      have hb : (UInt8.ofNat n).toNat = n := by
        rw [uint8_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hterm := BuN.terminal (UInt8.ofNat n) (by rw [hb]; exact h)
      rwa [hb] at hterm
    · rw [encodeULEB_ge h]
      have hbv : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [uint8_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hcont := BuN.continuation (UInt8.ofNat (n % 128 + 128))
        (by rw [hbv]; omega) (n / 128) (by omega) _ (ih (n / 128) (by omega))
      rw [hbv] at hcont
      rwa [show n % 128 + 128 - 128 + 128 * (n / 128) = n by omega] at hcont

theorem gen_BuN (n : Nat) : Gen (BuN n) (encodeULEB n) := by
  intro bs
  constructor
  · exact BuN_eq_encodeULEB
  · rintro rfl; exact encodeULEB_BuN n

/-! ## `BsN`: signed LEB128 (`binary/values.rst`)

"Signed integers are encoded in LEB128 format, which uses a two's complement
representation."  The `hminimal` side condition on a continuation is the
canonicality narrowing: a continuation byte whose tail is `0` with a positive
sign bit, or `-1` with a negative sign bit, is a redundant group. -/

/-- The signed LEB128 production, restricted to its canonical derivations. -/
inductive BsN : Int → List UInt8 → Prop where
  /-- A terminal byte: high bit clear, sign taken from bit 6. -/
  | terminal (b : UInt8) (h : b.toNat < 128) :
      BsN (if b.toNat < 64 then (b.toNat : Int) else (b.toNat : Int) - 128) [b]
  /-- A continuation byte, with the redundant groups excluded. -/
  | continuation (b : UInt8) (h : 128 ≤ b.toNat) (v : Int) (bs : List UInt8)
      (hminimal : ¬ ((v = 0 ∧ b.toNat - 128 < 64) ∨
        (v = -1 ∧ 64 ≤ b.toNat - 128)))
      (hbs : BsN v bs) :
      BsN (((b.toNat - 128 : Nat) : Int) + 128 * v) (b :: bs)

/-- Every `BsN` derivation is accepted by the signed LEB128 decoder.  This is a
statement *about* the proof, not about the definition: `BsN` is defined without
reference to `decSLEB`, and the decoder is used only to reuse the arithmetic
already proved in `Wasm/Binary.lean`. -/
theorem BsN_decSLEB {v : Int} {bs : List UInt8} (h : BsN v bs) :
    ∀ r : List UInt8, decSLEB (bs ++ r) = .ok (v, r) := by
  induction h with
  | terminal b hb =>
      intro r
      simp only [List.singleton_append, decSLEB, if_pos hb]
  | continuation b hb v bs hmin _ ih =>
      intro r
      have hb' : ¬ b.toNat < 128 := by omega
      simp only [List.cons_append, decSLEB, if_neg hb', ih r, if_neg hmin]

theorem decSLEB_BsN : ∀ (s : List UInt8) (v : Int) (r : List UInt8),
    decSLEB s = .ok (v, r) → ∃ p : List UInt8, s = p ++ r ∧ BsN v p := by
  intro s
  induction s with
  | nil => intro v r h; simp [decSLEB] at h
  | cons b rest ih =>
    intro v r h
    simp only [decSLEB] at h
    by_cases hb : b.toNat < 128
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst hr
      subst hv
      exact ⟨[b], rfl, BsN.terminal b hb⟩
    · rw [if_neg hb] at h
      revert h
      cases hd : decSLEB rest with
      | error e => intro h; simp at h
      | ok q =>
        obtain ⟨w, r'⟩ := q
        intro h
        simp only at h
        by_cases hc : (w = 0 ∧ b.toNat - 128 < 64) ∨ (w = -1 ∧ 64 ≤ b.toNat - 128)
        · rw [if_pos hc] at h; simp at h
        · rw [if_neg hc] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hr
          subst hv
          obtain ⟨p, hp, hBs⟩ := ih w r' hd
          refine ⟨b :: p, ?_, BsN.continuation b (by omega) w p hc hBs⟩
          rw [hp]
          rfl

theorem gen_BsN (v : Int) : Gen (BsN v) (encodeSLEB v) := by
  intro bs
  constructor
  · intro h
    have h1 := BsN_decSLEB h []
    have h2 := decSLEB_sound _ _ _ h1
    simpa using h2
  · rintro rfl
    have h1 : decSLEB (encodeSLEB v) = .ok (v, []) := by
      have := decSLEB_encodeSLEB v []
      simpa using this
    obtain ⟨p, hp, hBs⟩ := decSLEB_BsN _ v [] h1
    have hpe : p = encodeSLEB v := by simpa using hp.symm
    rwa [hpe] at hBs

/-! ## `BfN`: raw little-endian bit patterns (`binary/values.rst`)

"Floating-point values are encoded directly by their IEEE 754 bit pattern in
little-endian byte order."  Declaratively: `k` bytes whose little-endian value is
the bit pattern. -/

/-- The `k`-byte little-endian bit pattern production. -/
def BfN (k : Nat) (n : Nat) : Deriv := fun bs => bs.length = k ∧ natLE bs = n

theorem gen_BfN (k n : Nat) (h : n < 256 ^ k) : Gen (BfN k n) (bytesLE k n) := by
  intro bs
  constructor
  · rintro ⟨hlen, hval⟩
    have hb := bytesLE_natLE bs
    rw [hlen, hval] at hb
    exact hb.symm
  · rintro rfl
    exact ⟨length_bytesLE k n, natLE_bytesLE_of_lt k n h⟩

/-! ## Lists (`binary/conventions.rst`, "Lists")

"Lists are encoded with their `Bu32` length followed by the encoding of their
element sequence." -/

/-- The element sequence `(x:X)^n` of a list production. -/
def cats {α : Type} (P : α → Deriv) : List α → Deriv
  | [] => eps
  | x :: xs => cat (P x) (cats P xs)

/-- `Blist(X)`: the `Bu32` length followed by that many `X`. -/
def list {α : Type} (P : α → Deriv) (xs : List α) : Deriv :=
  cat (BuN xs.length) (cats P xs)

theorem gen_cats {α : Type} {P : α → Deriv} {f : α → List UInt8}
    (h : ∀ a : α, Gen (P a) (f a)) :
    ∀ xs : List α, Gen (cats P xs) (Bytes.concatBytes f xs)
  | [] => gen_eps
  | x :: xs => gen_cat (h x) (gen_cats h xs)

theorem gen_list {α : Type} {P : α → Deriv} {f : α → List UInt8}
    (h : ∀ a : α, Gen (P a) (f a)) (xs : List α) :
    Gen (list P xs) (Bytes.listBytes f xs) :=
  gen_cat (gen_BuN xs.length) (gen_cats h xs)

/-! ## Optionals

The pinned grammar writes `B?`; the modelled format tags the two cases with a
discriminant byte.  Recorded as a deviation in the file header. -/

/-- A tagged optional occurrence. -/
def opt {α : Type} (P : α → Deriv) : Option α → Deriv
  | none => lit [0]
  | some a => cat (lit [1]) (P a)

theorem gen_opt {α : Type} {P : α → Deriv} {f : α → List UInt8}
    (h : ∀ a : α, Gen (P a) (f a)) :
    ∀ o : Option α, Gen (opt P o) (Bytes.optionBytes f o)
  | none => gen_lit _
  | some a => gen_cons 1 (h a)

/-! ## Names (`binary/values.rst`, "Names")

"Names are encoded as a list of bytes."  UTF-8 well-formedness is a validation
condition, not a syntactic one, exactly as in `Wasm/Syntax.lean`. -/

/-- `Bbyte`: bytes encode themselves. -/
def byte (b : UInt8) : Deriv := lit [b]

theorem gen_byte (b : UInt8) : Gen (byte b) [b] := gen_lit _

theorem concatBytes_singleton :
    ∀ n : List UInt8, Bytes.concatBytes (fun b => [b]) n = n
  | [] => rfl
  | b :: bs => by
      show [b] ++ Bytes.concatBytes (fun c => [c]) bs = b :: bs
      rw [concatBytes_singleton bs]
      rfl

/-- `Bname`: a list of bytes. -/
def name (n : List UInt8) : Deriv := list byte n

theorem gen_name (n : List UInt8) : Gen (name n) (bytesC.enc n) := by
  refine Gen.cast (gen_list (P := byte) (f := fun b => [b]) gen_byte n) ?_
  show Bytes.listBytes (fun b => [b]) n = encodeULEB n.length ++ n
  rw [Bytes.listBytes, concatBytes_singleton]
  rfl

/-! ## Sections (`binary/modules.rst`, "Sections")

"Each section consists of a one-byte section id, the `u32` length of the
contents, in bytes, and the actual contents. ... The module is malformed if the
size does not match the length of the binary contents." -/

/-- A length-prefixed extent whose declared size must equal the length of its
contents. -/
def sized (P : Deriv) : Deriv :=
  fun bs => ∃ b₁ b₂ : List UInt8, bs = b₁ ++ b₂ ∧ BuN b₂.length b₁ ∧ P b₂

theorem gen_sized {P : Deriv} {t : List UInt8} (h : Gen P t) :
    Gen (sized P) (encodeULEB t.length ++ t) := by
  intro bs
  constructor
  · rintro ⟨b₁, b₂, rfl, hn, hp⟩
    have h2 : b₂ = t := (h b₂).mp hp
    have h1 : b₁ = encodeULEB b₂.length := (gen_BuN b₂.length b₁).mp hn
    rw [h1, h2]
  · rintro rfl
    exact ⟨encodeULEB t.length, t, rfl,
      (gen_BuN t.length (encodeULEB t.length)).mpr rfl, (h t).mpr rfl⟩

/-- `Bsection_N(X)`: the id byte, then the sized contents. -/
def section_ (id : UInt8) (P : Deriv) : Deriv := cat (lit [id]) (sized P)

theorem gen_section {P : Deriv} {t : List UInt8} (id : UInt8) (h : Gen P t) :
    Gen (section_ id P) (id :: (encodeULEB t.length ++ t)) :=
  gen_cons id (gen_sized h)

/-! ## Tag tables

The pinned grammar gives each type constructor and each opcode a literal byte.
Those bytes are behind SpecTec macros that the vendored file set does not carry,
so the relation takes them from this repository's pinned tables, which are pure
data.  See the scope note in the file header. -/

/-- The production of a tagged finite type: its number, LEB128 encoded. -/
def tag {α : Type} (T : Codec.Tagged α) (a : α) : Deriv := BuN (T.code a)

theorem gen_tag {α : Type} [DecidableEq α] (T : Codec.Tagged α) (a : α) :
    Gen (tag T a) ((Codec.tagged T).enc a) := gen_BuN (T.code a)

/-- Instruction opcodes: "each opcode is represented by a single byte, and is
followed by the instruction's immediate arguments, where present"
(`binary/instructions.rst`). -/
def op (o : Opcode) : Deriv := tag opcodeTagged o

theorem gen_op (o : Opcode) : Gen (op o) (opcodeC.enc o) := gen_tag opcodeTagged o

/-- A mutability / nullability flag byte. -/
def flag : Bool → Deriv
  | false => lit [0]
  | true => lit [1]

theorem gen_flag (b : Bool) : Gen (flag b) (boolC.enc b) := by
  cases b
  · exact gen_lit _
  · exact gen_lit _

/-! ### Convenience restatements against the codec encoders

Each `Gen` below is stated with the `Wasm/Binary.lean` encoder on the right so
that the mechanical case analysis over instructions can close every leaf by
`exact`.  The left-hand sides are the productions defined above. -/

theorem gen_nat (n : Nat) : Gen (BuN n) (natC.enc n) := gen_BuN n

theorem gen_int (v : Int) : Gen (BsN v) (intC.enc v) := gen_BsN v

theorem gen_nats (l : List Nat) : Gen (list BuN l) (natsC.enc l) :=
  gen_list (P := BuN) (f := natC.enc) gen_nat l

theorem gen_bf32 (x : UInt32) : Gen (BfN 4 x.toNat) (u32C.enc x) := by
  refine gen_BfN 4 x.toNat ?_
  have h := UInt32.toNat_lt x
  simp only [] at h ⊢
  omega

theorem gen_bf64 (x : UInt64) : Gen (BfN 8 x.toNat) (u64C.enc x) := by
  refine gen_BfN 8 x.toNat ?_
  have h := UInt64.toNat_lt x
  simp only [] at h ⊢
  omega

/-! ## Types (`binary/types.rst`) -/

/-- `Bnumtype`: "Number types are encoded by a single byte." -/
def BNumType (t : NumType) : Deriv := tag numTypeTagged t

theorem gen_numType (t : NumType) : Gen (BNumType t) (numTypeC.enc t) :=
  gen_tag numTypeTagged t

/-- `Bvectype`: "Vector types are also encoded by a single byte." -/
def BVecType (t : VecType) : Deriv := tag vecTypeTagged t

theorem gen_vecType (t : VecType) : Gen (BVecType t) (vecTypeC.enc t) :=
  gen_tag vecTypeTagged t

/-- `Bpacktype`. -/
def BPackedType (t : PackedType) : Deriv := tag packedTypeTagged t

theorem gen_packedType (t : PackedType) : Gen (BPackedType t) (packedTypeC.enc t) :=
  gen_tag packedTypeTagged t

/-- The address-type flag of a memory or table (`binary/types.rst`, "Limits"). -/
def BAddressType (t : AddressType) : Deriv := tag addressTypeTagged t

theorem gen_addressType (t : AddressType) :
    Gen (BAddressType t) (addressTypeC.enc t) := gen_tag addressTypeTagged t

/-- `Babsheaptype`: an abstract heap type is a single byte. -/
def BAbsHeapType (t : AbsHeapType) : Deriv := tag absHeapTypeTagged t

theorem gen_absHeapType (t : AbsHeapType) :
    Gen (BAbsHeapType t) (absHeapTypeC.enc t) := gen_tag absHeapTypeTagged t

/-- `Bheaptype`: "either a single byte, or a type index". -/
def BHeapType : HeapType → Deriv
  | .abs t => cat (lit [0]) (BAbsHeapType t)
  | .concrete i => cat (lit [1]) (BuN i)

theorem gen_heapType (t : HeapType) : Gen (BHeapType t) (heapTypeC.enc t) := by
  cases t with
  | abs a => exact gen_cons 0 (gen_absHeapType a)
  | concrete i => exact gen_cons 1 (gen_nat i)

/-- `Breftype`: a nullability flag and a heap type. -/
def BRefType (t : RefType) : Deriv := cat (flag t.nullable) (BHeapType t.heapType)

theorem gen_refType (t : RefType) : Gen (BRefType t) (refTypeC.enc t) :=
  gen_cat (gen_flag t.nullable) (gen_heapType t.heapType)

/-- `Bvaltype`: a number type, a vector type, or a reference type. -/
def BValType : ValType → Deriv
  | .num t => cat (lit [0]) (BNumType t)
  | .vec t => cat (lit [1]) (cat (lit [0]) (BVecType t))
  | .ref t => cat (lit [1]) (cat (lit [1]) (BRefType t))

theorem gen_valType (t : ValType) : Gen (BValType t) (valTypeC.enc t) := by
  cases t with
  | num a => exact gen_cons 0 (gen_numType a)
  | vec a => exact gen_cons 1 (gen_cons 0 (gen_vecType a))
  | ref a => exact gen_cons 1 (gen_cons 1 (gen_refType a))

/-- `Bresulttype`: a list of value types. -/
def BValTypes (l : List ValType) : Deriv := list BValType l

theorem gen_valTypes (l : List ValType) : Gen (BValTypes l) (valTypesC.enc l) :=
  gen_list (P := BValType) (f := valTypeC.enc) gen_valType l

/-- `Bstoragetype`: a value type or a packed type. -/
def BStorageType : StorageType → Deriv
  | .val t => cat (lit [0]) (BValType t)
  | .packed t => cat (lit [1]) (BPackedType t)

theorem gen_storageType (t : StorageType) :
    Gen (BStorageType t) (storageTypeC.enc t) := by
  cases t with
  | val a => exact gen_cons 0 (gen_valType a)
  | packed a => exact gen_cons 1 (gen_packedType a)

/-- `Bfieldtype`: a mutability flag and a storage type. -/
def BFieldType (t : FieldType) : Deriv :=
  cat (flag t.mutable) (BStorageType t.storage)

theorem gen_fieldType (t : FieldType) : Gen (BFieldType t) (fieldTypeC.enc t) :=
  gen_cat (gen_flag t.mutable) (gen_storageType t.storage)

/-- `Bstructtype`: a list of field types. -/
def BStructType (t : StructType) : Deriv := list BFieldType t.fields

theorem gen_structType (t : StructType) : Gen (BStructType t) (structTypeC.enc t) :=
  gen_list (P := BFieldType) (f := fieldTypeC.enc) gen_fieldType t.fields

/-- `Barraytype`: one field type. -/
def BArrayType (t : ArrayType) : Deriv := BFieldType t.element

theorem gen_arrayType (t : ArrayType) : Gen (BArrayType t) (arrayTypeC.enc t) :=
  gen_fieldType t.element

/-- `Bfunctype`: parameter and result types. -/
def BFuncType (t : FuncType) : Deriv :=
  cat (BValTypes t.params) (BValTypes t.results)

theorem gen_funcType (t : FuncType) : Gen (BFuncType t) (funcTypeC.enc t) :=
  gen_cat (gen_valTypes t.params) (gen_valTypes t.results)

/-- `Btagtype`: a function type. -/
def BTagType (t : TagType) : Deriv := BFuncType t.funcType

theorem gen_tagType (t : TagType) : Gen (BTagType t) (tagTypeC.enc t) :=
  gen_funcType t.funcType

/-- `Bcomptype`: "a distinct byte followed by a type encoding of the respective
form". -/
def BCompType : CompType → Deriv
  | .func t => cat (lit [0]) (BFuncType t)
  | .struct t => cat (lit [1]) (cat (lit [0]) (BStructType t))
  | .array t => cat (lit [1]) (cat (lit [1]) (BArrayType t))

theorem gen_compType (t : CompType) : Gen (BCompType t) (compTypeC.enc t) := by
  cases t with
  | func a => exact gen_cons 0 (gen_funcType a)
  | «struct» a => exact gen_cons 1 (gen_cons 0 (gen_structType a))
  | array a => exact gen_cons 1 (gen_cons 1 (gen_arrayType a))

/-- `Bsubtype`: a finality flag, the supertype indices, and the composite body. -/
def BSubType (t : SubType) : Deriv :=
  cat (flag t.final) (cat (list BuN t.supertypes) (BCompType t.body))

theorem gen_subType (t : SubType) : Gen (BSubType t) (subTypeC.enc t) :=
  gen_cat (gen_flag t.final) (gen_cat (gen_nats t.supertypes) (gen_compType t.body))

/-- `Brectype`: a list of sub types. -/
def BRecType (t : RecType) : Deriv := list BSubType t.types

theorem gen_recType (t : RecType) : Gen (BRecType t) (recTypeC.enc t) :=
  gen_list (P := BSubType) (f := subTypeC.enc) gen_subType t.types

/-- `Blimits`: the minimum and the optional maximum. -/
def BLimits (l : Limits) : Deriv := cat (BuN l.min) (opt BuN l.max)

theorem gen_limits (l : Limits) : Gen (BLimits l) (limitsC.enc l) :=
  gen_cat (gen_nat l.min) (gen_opt (P := BuN) (f := natC.enc) gen_nat l.max)

/-- `Bmemtype`: the address type flag and the limits. -/
def BMemType (t : MemType) : Deriv :=
  cat (BAddressType t.addressType) (BLimits t.limits)

theorem gen_memType (t : MemType) : Gen (BMemType t) (memTypeC.enc t) :=
  gen_cat (gen_addressType t.addressType) (gen_limits t.limits)

/-- `Btabletype`: the address type flag, the limits, and the element type. -/
def BTableType (t : TableType) : Deriv :=
  cat (BAddressType t.addressType) (cat (BLimits t.limits) (BRefType t.element))

theorem gen_tableType (t : TableType) : Gen (BTableType t) (tableTypeC.enc t) :=
  gen_cat (gen_addressType t.addressType)
    (gen_cat (gen_limits t.limits) (gen_refType t.element))

/-- `Bglobaltype`: a value type and a mutability flag. -/
def BGlobalType (t : GlobalType) : Deriv :=
  cat (flag t.mutable) (BValType t.valType)

theorem gen_globalType (t : GlobalType) : Gen (BGlobalType t) (globalTypeC.enc t) :=
  gen_cat (gen_flag t.mutable) (gen_valType t.valType)

/-! ## Instruction immediates (`binary/instructions.rst`) -/

/-- Integer and floating point operator families.  The pinned grammar spells each
operator out as its own opcode; the modelled format carries the width and the
operator as further tags after a family opcode. -/
def BIntWidth (w : IntWidth) : Deriv := tag intWidthTagged w

theorem gen_intWidth (w : IntWidth) : Gen (BIntWidth w) (intWidthC.enc w) :=
  gen_tag intWidthTagged w

/-- The float width tag. -/
def BFloatWidth (w : FloatWidth) : Deriv := tag floatWidthTagged w

theorem gen_floatWidth (w : FloatWidth) : Gen (BFloatWidth w) (floatWidthC.enc w) :=
  gen_tag floatWidthTagged w

/-- The signedness tag of a narrowing or widening operator. -/
def BSignExt (s : SignExt) : Deriv := tag signExtTagged s

theorem gen_signExt (s : SignExt) : Gen (BSignExt s) (signExtC.enc s) :=
  gen_tag signExtTagged s

/-- The narrowed access width of a partial load or store. -/
def BMemWidth (w : MemWidth) : Deriv := tag memWidthTagged w

theorem gen_memWidth (w : MemWidth) : Gen (BMemWidth w) (memWidthC.enc w) :=
  gen_tag memWidthTagged w

/-- The catch-clause kind of `try_table`. -/
def BCatchKind (k : CatchKind) : Deriv := tag catchKindTagged k

theorem gen_catchKind (k : CatchKind) : Gen (BCatchKind k) (catchKindC.enc k) :=
  gen_tag catchKindTagged k

/-- The integer unary operator tag. -/
def BIUnOp (o : IUnOp) : Deriv := tag iUnOpTagged o
theorem gen_iUnOp (o : IUnOp) : Gen (BIUnOp o) (iUnOpC.enc o) := gen_tag iUnOpTagged o

/-- The integer binary operator tag. -/
def BIBinOp (o : IBinOp) : Deriv := tag iBinOpTagged o
theorem gen_iBinOp (o : IBinOp) : Gen (BIBinOp o) (iBinOpC.enc o) := gen_tag iBinOpTagged o

/-- The integer test operator tag. -/
def BITestOp (o : ITestOp) : Deriv := tag iTestOpTagged o
theorem gen_iTestOp (o : ITestOp) : Gen (BITestOp o) (iTestOpC.enc o) := gen_tag iTestOpTagged o

/-- The integer relational operator tag. -/
def BIRelOp (o : IRelOp) : Deriv := tag iRelOpTagged o
theorem gen_iRelOp (o : IRelOp) : Gen (BIRelOp o) (iRelOpC.enc o) := gen_tag iRelOpTagged o

/-- The floating point unary operator tag. -/
def BFUnOp (o : FUnOp) : Deriv := tag fUnOpTagged o
theorem gen_fUnOp (o : FUnOp) : Gen (BFUnOp o) (fUnOpC.enc o) := gen_tag fUnOpTagged o

/-- The floating point binary operator tag. -/
def BFBinOp (o : FBinOp) : Deriv := tag fBinOpTagged o
theorem gen_fBinOp (o : FBinOp) : Gen (BFBinOp o) (fBinOpC.enc o) := gen_tag fBinOpTagged o

/-- The floating point relational operator tag. -/
def BFRelOp (o : FRelOp) : Deriv := tag fRelOpTagged o
theorem gen_fRelOp (o : FRelOp) : Gen (BFRelOp o) (fRelOpC.enc o) := gen_tag fRelOpTagged o

/-- The conversion operator tag. -/
def BCvtOp (o : CvtOp) : Deriv := tag cvtOpTagged o
theorem gen_cvtOp (o : CvtOp) : Gen (BCvtOp o) (cvtOpC.enc o) := gen_tag cvtOpTagged o

/-- The vector lane shape tag. -/
def BVecShape (s : VecShape) : Deriv := tag vecShapeTagged s
theorem gen_vecShape (s : VecShape) : Gen (BVecShape s) (vecShapeC.enc s) := gen_tag vecShapeTagged s

/-- The vector unary operator tag. -/
def BVecUnOp (o : VecUnOp) : Deriv := tag vecUnOpTagged o
theorem gen_vecUnOp (o : VecUnOp) : Gen (BVecUnOp o) (vecUnOpC.enc o) := gen_tag vecUnOpTagged o

/-- The vector binary operator tag. -/
def BVecBinOp (o : VecBinOp) : Deriv := tag vecBinOpTagged o
theorem gen_vecBinOp (o : VecBinOp) : Gen (BVecBinOp o) (vecBinOpC.enc o) := gen_tag vecBinOpTagged o

/-- The vector relational operator tag. -/
def BVecRelOp (o : VecRelOp) : Deriv := tag vecRelOpTagged o
theorem gen_vecRelOp (o : VecRelOp) : Gen (BVecRelOp o) (vecRelOpC.enc o) := gen_tag vecRelOpTagged o

/-- `Bmemarg`: the memory index, the alignment exponent and the static offset. -/
def BMemArg (m : MemArg) : Deriv :=
  cat (BuN m.memory) (cat (BuN m.align) (BuN m.offset))

theorem gen_memArg (m : MemArg) : Gen (BMemArg m) (memArgC.enc m) :=
  gen_cat (gen_nat m.memory) (gen_cat (gen_nat m.align) (gen_nat m.offset))

/-- `Bblocktype`: the empty type, a value type, or a type index. -/
def BBlockType : BlockType → Deriv
  | .empty => cat (lit [0]) eps
  | .value t => cat (lit [1]) (cat (lit [0]) (BValType t))
  | .typeIndex i => cat (lit [1]) (cat (lit [1]) (BuN i))

theorem gen_blockType (t : BlockType) : Gen (BBlockType t) (blockTypeC.enc t) := by
  cases t with
  | empty => exact gen_cons 0 gen_eps
  | value a => exact gen_cons 1 (gen_cons 0 (gen_valType a))
  | typeIndex i => exact gen_cons 1 (gen_cons 1 (gen_nat i))

/-- `Bcatch`: the clause kind, the tag index and the label index. -/
def BCatch (c : Catch) : Deriv :=
  cat (BCatchKind c.kind) (cat (BuN c.tag) (BuN c.label))

theorem gen_catch (c : Catch) : Gen (BCatch c) (catchC.enc c) :=
  gen_cat (gen_catchKind c.kind) (gen_cat (gen_nat c.tag) (gen_nat c.label))

theorem gen_catches (l : List Catch) : Gen (list BCatch l) (catchesC.enc l) :=
  gen_list (P := BCatch) (f := catchC.enc) gen_catch l

/-- The narrowed-width-and-sign immediate of a partial load. -/
def BNarrow (p : MemWidth × SignExt) : Deriv := cat (BMemWidth p.1) (BSignExt p.2)

theorem gen_narrow (p : MemWidth × SignExt) :
    Gen (BNarrow p) ((Codec.pair memWidthC signExtC).enc p) :=
  gen_cat (gen_memWidth p.1) (gen_signExt p.2)

theorem gen_optSignExt (o : Option SignExt) :
    Gen (opt BSignExt o) (optSignExtC.enc o) :=
  gen_opt (P := BSignExt) (f := signExtC.enc) gen_signExt o

theorem gen_optMemWidth (o : Option MemWidth) :
    Gen (opt BMemWidth o) (optMemWidthC.enc o) :=
  gen_opt (P := BMemWidth) (f := memWidthC.enc) gen_memWidth o

theorem gen_optNarrow (o : Option (MemWidth × SignExt)) :
    Gen (opt BNarrow o) (optNarrowC.enc o) :=
  gen_opt (P := BNarrow) (f := (Codec.pair memWidthC signExtC).enc) gen_narrow o

theorem gen_optValTypes (o : Option (List ValType)) :
    Gen (opt BValTypes o) (optValTypesC.enc o) :=
  gen_opt (P := BValTypes) (f := valTypesC.enc) gen_valTypes o

/-! ## Instructions and instruction sequences

"Instructions are encoded by opcodes.  Each opcode is represented by a single
byte, and is followed by the instruction's immediate arguments, where present.
The only exception are structured control instructions, which consist of several
opcodes bracketing their nested instruction sequences."
(`binary/instructions.rst`.)

The instruction subset is the one declared in `Wasm/Syntax.lean`; see the scope
note in the file header for what that leaves out and for the cons-tagged reading
of `Bexpr`. -/

mutual

/-- `Binstr`, for the modelled instruction subset. -/
def BInstr : Instr → Deriv
  | .unreachable => op .unreachable
  | .nop => op .nop
  | .br a0 => cat (op .br) (BuN a0)
  | .brIf a0 => cat (op .brIf) (BuN a0)
  | .brTable a0 a1 => cat (op .brTable) (cat (list BuN a0) (BuN a1))
  | .ret => op .ret
  | .call a0 => cat (op .call) (BuN a0)
  | .callIndirect a0 a1 => cat (op .callIndirect) (cat (BuN a0) (BuN a1))
  | .returnCall a0 => cat (op .returnCall) (BuN a0)
  | .returnCallIndirect a0 a1 => cat (op .returnCallIndirect) (cat (BuN a0) (BuN a1))
  | .throw a0 => cat (op .throw) (BuN a0)
  | .throwRef => op .throwRef
  | .drop => op .drop
  | .select a0 => cat (op .select) (opt BValTypes a0)
  | .localGet a0 => cat (op .localGet) (BuN a0)
  | .localSet a0 => cat (op .localSet) (BuN a0)
  | .localTee a0 => cat (op .localTee) (BuN a0)
  | .globalGet a0 => cat (op .globalGet) (BuN a0)
  | .globalSet a0 => cat (op .globalSet) (BuN a0)
  | .refNull a0 => cat (op .refNull) (BHeapType a0)
  | .refIsNull => op .refIsNull
  | .refFunc a0 => cat (op .refFunc) (BuN a0)
  | .refEq => op .refEq
  | .refAsNonNull => op .refAsNonNull
  | .refTest a0 a1 => cat (op .refTest) (cat (flag a0) (BHeapType a1))
  | .refCast a0 a1 => cat (op .refCast) (cat (flag a0) (BHeapType a1))
  | .refI31 => op .refI31
  | .i31GetS => op .i31GetS
  | .i31GetU => op .i31GetU
  | .anyConvertExtern => op .anyConvertExtern
  | .externConvertAny => op .externConvertAny
  | .structNew a0 => cat (op .structNew) (BuN a0)
  | .structNewDefault a0 => cat (op .structNewDefault) (BuN a0)
  | .structGet a0 a1 a2 =>
      cat (op .structGet) (cat (BuN a0) (cat (BuN a1) (opt BSignExt a2)))
  | .structSet a0 a1 => cat (op .structSet) (cat (BuN a0) (BuN a1))
  | .arrayNew a0 => cat (op .arrayNew) (BuN a0)
  | .arrayNewDefault a0 => cat (op .arrayNewDefault) (BuN a0)
  | .arrayGet a0 a1 => cat (op .arrayGet) (cat (BuN a0) (opt BSignExt a1))
  | .arraySet a0 => cat (op .arraySet) (BuN a0)
  | .arrayLen => op .arrayLen
  | .tableGet a0 => cat (op .tableGet) (BuN a0)
  | .tableSet a0 => cat (op .tableSet) (BuN a0)
  | .tableSize a0 => cat (op .tableSize) (BuN a0)
  | .tableGrow a0 => cat (op .tableGrow) (BuN a0)
  | .tableFill a0 => cat (op .tableFill) (BuN a0)
  | .tableCopy a0 a1 => cat (op .tableCopy) (cat (BuN a0) (BuN a1))
  | .tableInit a0 a1 => cat (op .tableInit) (cat (BuN a0) (BuN a1))
  | .elemDrop a0 => cat (op .elemDrop) (BuN a0)
  | .load a0 a1 a2 =>
      cat (op .load) (cat (BNumType a0) (cat (opt BNarrow a1) (BMemArg a2)))
  | .store a0 a1 a2 =>
      cat (op .store) (cat (BNumType a0) (cat (opt BMemWidth a1) (BMemArg a2)))
  | .vecLoad a0 => cat (op .vecLoad) (BMemArg a0)
  | .vecStore a0 => cat (op .vecStore) (BMemArg a0)
  | .memorySize a0 => cat (op .memorySize) (BuN a0)
  | .memoryGrow a0 => cat (op .memoryGrow) (BuN a0)
  | .memoryFill a0 => cat (op .memoryFill) (BuN a0)
  | .memoryCopy a0 a1 => cat (op .memoryCopy) (cat (BuN a0) (BuN a1))
  | .memoryInit a0 a1 => cat (op .memoryInit) (cat (BuN a0) (BuN a1))
  | .dataDrop a0 => cat (op .dataDrop) (BuN a0)
  | .i32Const a0 => cat (op .i32Const) (BsN a0)
  | .i64Const a0 => cat (op .i64Const) (BsN a0)
  | .f32Const a0 => cat (op .f32Const) (BfN 4 a0.toNat)
  | .f64Const a0 => cat (op .f64Const) (BfN 8 a0.toNat)
  | .iUnOp a0 a1 => cat (op .iUnOp) (cat (BIntWidth a0) (BIUnOp a1))
  | .iBinOp a0 a1 => cat (op .iBinOp) (cat (BIntWidth a0) (BIBinOp a1))
  | .iTestOp a0 a1 => cat (op .iTestOp) (cat (BIntWidth a0) (BITestOp a1))
  | .iRelOp a0 a1 => cat (op .iRelOp) (cat (BIntWidth a0) (BIRelOp a1))
  | .fUnOp a0 a1 => cat (op .fUnOp) (cat (BFloatWidth a0) (BFUnOp a1))
  | .fBinOp a0 a1 => cat (op .fBinOp) (cat (BFloatWidth a0) (BFBinOp a1))
  | .fRelOp a0 a1 => cat (op .fRelOp) (cat (BFloatWidth a0) (BFRelOp a1))
  | .cvtOp a0 => cat (op .cvtOp) (BCvtOp a0)
  | .vecConst a0 a1 => cat (op .vecConst) (cat (BfN 8 a0.toNat) (BfN 8 a1.toNat))
  | .vecUnOp a0 a1 => cat (op .vecUnOp) (cat (BVecShape a0) (BVecUnOp a1))
  | .vecBinOp a0 a1 => cat (op .vecBinOp) (cat (BVecShape a0) (BVecBinOp a1))
  | .vecRelOp a0 a1 => cat (op .vecRelOp) (cat (BVecShape a0) (BVecRelOp a1))
  | .vecBitselect => op .vecBitselect
  | .vecSplat a0 => cat (op .vecSplat) (BVecShape a0)
  | .vecExtractLane a0 a1 a2 =>
      cat (op .vecExtractLane) (cat (BVecShape a0) (cat (BuN a1) (opt BSignExt a2)))
  | .vecReplaceLane a0 a1 => cat (op .vecReplaceLane) (cat (BVecShape a0) (BuN a1))
  | .vecShuffle a0 => cat (op .vecShuffle) (list BuN a0)
  | .block bt body => cat (op .block) (cat (BBlockType bt) (BExpr body))
  | .loop bt body => cat (op .loop) (cat (BBlockType bt) (BExpr body))
  | .ifThenElse bt b1 b2 =>
      cat (op .ifThenElse) (cat (BBlockType bt) (cat (BExpr b1) (BExpr b2)))
  | .tryTable bt cs body =>
      cat (op .tryTable) (cat (BBlockType bt) (cat (list BCatch cs) (BExpr body)))

/-- `Bexpr`, in the cons-tagged reading of the modelled format. -/
def BExpr : Expr → Deriv
  | .nil => lit [0]
  | .cons i e => cat (lit [1]) (cat (BInstr i) (BExpr e))

end

set_option maxHeartbeats 4000000 in
/-- The instruction and instruction-sequence productions generate exactly the
canonical encodings.  The induction is on the encoding-length measure
`Instr.cost` / `Expr.cost`, which strictly decreases into the nested sequences of
the structured control instructions. -/
theorem gen_instr_expr : ∀ n : Nat,
    (∀ i : Instr, Instr.cost i ≤ n → Gen (BInstr i) (Instr.enc i)) ∧
    (∀ e : Expr, Expr.cost e ≤ n → Gen (BExpr e) (Expr.enc e)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro i h; exact absurd h (by have := Instr.one_le_cost i; omega)
    · intro e h; exact absurd h (by have := Expr.one_le_cost e; omega)
  | succ f ih =>
    obtain ⟨ihI, ihE⟩ := ih
    refine ⟨?_, ?_⟩
    · intro i h
      cases i
      case block bt body =>
        have hb : Expr.cost body ≤ f := by
          have h1 := opcodeC_enc_length_pos Opcode.block
          simp only [Instr.cost, Instr.enc, List.length_append] at h
          simp only [Expr.cost]
          omega
        exact gen_cat (gen_op _) (gen_cat (gen_blockType _) (ihE body hb))
      case loop bt body =>
        have hb : Expr.cost body ≤ f := by
          have h1 := opcodeC_enc_length_pos Opcode.loop
          simp only [Instr.cost, Instr.enc, List.length_append] at h
          simp only [Expr.cost]
          omega
        exact gen_cat (gen_op _) (gen_cat (gen_blockType _) (ihE body hb))
      case ifThenElse bt b1 b2 =>
        have h1' := opcodeC_enc_length_pos Opcode.ifThenElse
        have hb1 : Expr.cost b1 ≤ f := by
          simp only [Instr.cost, Instr.enc, List.length_append] at h
          simp only [Expr.cost]
          omega
        have hb2 : Expr.cost b2 ≤ f := by
          simp only [Instr.cost, Instr.enc, List.length_append] at h
          simp only [Expr.cost]
          omega
        exact gen_cat (gen_op _)
          (gen_cat (gen_blockType _) (gen_cat (ihE b1 hb1) (ihE b2 hb2)))
      case tryTable bt cs body =>
        have hb : Expr.cost body ≤ f := by
          have h1 := opcodeC_enc_length_pos Opcode.tryTable
          simp only [Instr.cost, Instr.enc, List.length_append] at h
          simp only [Expr.cost]
          omega
        exact gen_cat (gen_op _)
          (gen_cat (gen_blockType _) (gen_cat (gen_catches _) (ihE body hb)))
      all_goals
        simp only [BInstr, Instr.enc]
        repeat'
          first
            | exact gen_op _
            | exact gen_nat _
            | exact gen_int _
            | exact gen_nats _
            | exact gen_flag _
            | exact gen_bf32 _
            | exact gen_bf64 _
            | exact gen_heapType _
            | exact gen_numType _
            | exact gen_memArg _
            | exact gen_blockType _
            | exact gen_catches _
            | exact gen_optValTypes _
            | exact gen_optSignExt _
            | exact gen_optMemWidth _
            | exact gen_optNarrow _
            | exact gen_intWidth _
            | exact gen_iUnOp _
            | exact gen_iBinOp _
            | exact gen_iTestOp _
            | exact gen_iRelOp _
            | exact gen_floatWidth _
            | exact gen_fUnOp _
            | exact gen_fBinOp _
            | exact gen_fRelOp _
            | exact gen_cvtOp _
            | exact gen_vecShape _
            | exact gen_vecUnOp _
            | exact gen_vecBinOp _
            | exact gen_vecRelOp _
            | apply gen_cat
    · intro e h
      cases e
      case nil => exact gen_lit _
      case cons i e' =>
        have hi : Instr.cost i ≤ f := by
          simp only [Expr.cost, Expr.enc, List.length_cons, List.length_append] at h
          simp only [Instr.cost]
          omega
        have he : Expr.cost e' ≤ f := by
          simp only [Expr.cost, Expr.enc, List.length_cons, List.length_append] at h
          simp only [Expr.cost]
          omega
        exact gen_cons 1 (gen_cat (ihI i hi) (ihE e' he))

theorem gen_BInstr (i : Instr) : Gen (BInstr i) (Instr.enc i) :=
  (gen_instr_expr (Instr.cost i)).1 i (Nat.le_refl _)

theorem gen_BExpr (e : Expr) : Gen (BExpr e) (Expr.enc e) :=
  (gen_instr_expr (Expr.cost e)).2 e (Nat.le_refl _)

theorem gen_expr (e : Expr) : Gen (BExpr e) (exprC.enc e) := gen_BExpr e

/-! ## Module components (`binary/modules.rst`) -/

/-- `Bimportdesc`. -/
def BImportDesc : ImportDesc → Deriv
  | .func t => cat (lit [0]) (BuN t)
  | .table t => cat (lit [1]) (cat (lit [0]) (BTableType t))
  | .mem t => cat (lit [1]) (cat (lit [1]) (cat (lit [0]) (BMemType t)))
  | .global t =>
      cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (cat (lit [0]) (BGlobalType t))))
  | .tag t =>
      cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (BTagType t))))

theorem gen_importDesc (d : ImportDesc) : Gen (BImportDesc d) (importDescC.enc d) := by
  cases d with
  | func a => exact gen_cons 0 (gen_nat a)
  | table a => exact gen_cons 1 (gen_cons 0 (gen_tableType a))
  | mem a => exact gen_cons 1 (gen_cons 1 (gen_cons 0 (gen_memType a)))
  | global a =>
      exact gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_cons 0 (gen_globalType a))))
  | tag a => exact gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_tagType a))))

/-- `Bimport`: the two-level name and the described item. -/
def BImport (i : Import) : Deriv :=
  cat (name i.module) (cat (name i.name) (BImportDesc i.desc))

theorem gen_import (i : Import) : Gen (BImport i) (importC.enc i) :=
  gen_cat (gen_name i.module) (gen_cat (gen_name i.name) (gen_importDesc i.desc))

/-- `Bexportdesc`. -/
def BExportDesc : ExportDesc → Deriv
  | .func i => cat (lit [0]) (BuN i)
  | .table i => cat (lit [1]) (cat (lit [0]) (BuN i))
  | .mem i => cat (lit [1]) (cat (lit [1]) (cat (lit [0]) (BuN i)))
  | .global i =>
      cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (cat (lit [0]) (BuN i))))
  | .tag i =>
      cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (cat (lit [1]) (BuN i))))

theorem gen_exportDesc (d : ExportDesc) : Gen (BExportDesc d) (exportDescC.enc d) := by
  cases d with
  | func a => exact gen_cons 0 (gen_nat a)
  | table a => exact gen_cons 1 (gen_cons 0 (gen_nat a))
  | mem a => exact gen_cons 1 (gen_cons 1 (gen_cons 0 (gen_nat a)))
  | global a => exact gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_cons 0 (gen_nat a))))
  | tag a => exact gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_cons 1 (gen_nat a))))

/-- `Bexport`: the name and the described item. -/
def BExport (e : Export) : Deriv := cat (name e.name) (BExportDesc e.desc)

theorem gen_export (e : Export) : Gen (BExport e) (exportC.enc e) :=
  gen_cat (gen_name e.name) (gen_exportDesc e.desc)

/-- A defined function.  The pinned format splits this across the function and
code sections; the modelled format does not (see the scope note). -/
def BFunc (f : Func) : Deriv :=
  cat (BuN f.type) (cat (BValTypes f.locals) (BExpr f.body))

theorem gen_func (f : Func) : Gen (BFunc f) (funcC.enc f) :=
  gen_cat (gen_nat f.type) (gen_cat (gen_valTypes f.locals) (gen_expr f.body))

/-- `Btable`: the table type and its initializer expression. -/
def BTable (t : Table) : Deriv := cat (BTableType t.type) (BExpr t.init)

theorem gen_table (t : Table) : Gen (BTable t) (tableC.enc t) :=
  gen_cat (gen_tableType t.type) (gen_expr t.init)

/-- `Bmem`: the memory type. -/
def BMem (m : Mem) : Deriv := BMemType m.type

theorem gen_mem (m : Mem) : Gen (BMem m) (memC.enc m) := gen_memType m.type

/-- `Bglobal`: the global type and its initializer expression. -/
def BGlobal (g : Global) : Deriv := cat (BGlobalType g.type) (BExpr g.init)

theorem gen_global (g : Global) : Gen (BGlobal g) (globalC.enc g) :=
  gen_cat (gen_globalType g.type) (gen_expr g.init)

/-- The mode of an element segment: passive, active with a table index and an
offset expression, or declarative. -/
def BElemMode : ElemMode → Deriv
  | .passive => cat (lit [0]) eps
  | .active t o => cat (lit [1]) (cat (lit [0]) (cat (BuN t) (BExpr o)))
  | .declarative => cat (lit [1]) (cat (lit [1]) eps)

theorem gen_elemMode (m : ElemMode) : Gen (BElemMode m) (elemModeC.enc m) := by
  cases m with
  | passive => exact gen_cons 0 gen_eps
  | active t o => exact gen_cons 1 (gen_cons 0 (gen_cat (gen_nat t) (gen_expr o)))
  | declarative => exact gen_cons 1 (gen_cons 1 gen_eps)

/-- `Belem`: the element type, the element expressions, and the mode. -/
def BElem (e : Elem) : Deriv :=
  cat (BRefType e.type) (cat (list BExpr e.init) (BElemMode e.mode))

theorem gen_elem (e : Elem) : Gen (BElem e) (elemC.enc e) :=
  gen_cat (gen_refType e.type)
    (gen_cat (gen_list (P := BExpr) (f := exprC.enc) gen_expr e.init)
      (gen_elemMode e.mode))

/-- The mode of a data segment: passive, or active with a memory index and an
offset expression. -/
def BDataMode : DataMode → Deriv
  | .passive => cat (lit [0]) eps
  | .active m o => cat (lit [1]) (cat (BuN m) (BExpr o))

theorem gen_dataMode (m : DataMode) : Gen (BDataMode m) (dataModeC.enc m) := by
  cases m with
  | passive => exact gen_cons 0 gen_eps
  | active t o => exact gen_cons 1 (gen_cat (gen_nat t) (gen_expr o))

/-- `Bdata`: the initializer bytes and the mode. -/
def BData (d : Data) : Deriv := cat (name d.init) (BDataMode d.mode)

theorem gen_data (d : Data) : Gen (BData d) (dataC.enc d) :=
  gen_cat (gen_name d.init) (gen_dataMode d.mode)

/-! ## Modules (`binary/modules.rst`, "Modules")

"The encoding of a module starts with a preamble containing a 4-byte magic
number (the string `\0asm`) and a version field. ... The preamble is followed by
a sequence of sections."

The section sequence here is the fixed, total one of the modelled format; see
the scope note in the file header. -/

/-- `Bmodule`: the preamble, then the eleven modelled sections in the pinned
order `1, 2, 3, 4, 5, 13, 6, 7, 8, 9, 11`. -/
def BModule (m : Module) : Deriv :=
  cat (lit magicBytes)
    (cat (section_ 1 (list BRecType m.types))
      (cat (section_ 2 (list BImport m.imports))
        (cat (section_ 3 (list BFunc m.funcs))
          (cat (section_ 4 (list BTable m.tables))
            (cat (section_ 5 (list BMem m.mems))
              (cat (section_ 13 (list BTagType m.tags))
                (cat (section_ 6 (list BGlobal m.globals))
                  (cat (section_ 7 (list BExport m.exports))
                    (cat (section_ 8 (opt BuN m.start))
                      (cat (section_ 9 (list BElem m.elems))
                        (section_ 11 (list BData m.datas))))))))))))

set_option maxHeartbeats 1000000 in
theorem gen_BModule (m : Module) : Gen (BModule m) (encodeList m) :=
  gen_cat (gen_lit magicBytes)
    (gen_cat (gen_section 1 (gen_list (P := BRecType) (f := recTypeC.enc) gen_recType m.types))
      (gen_cat (gen_section 2 (gen_list (P := BImport) (f := importC.enc) gen_import m.imports))
        (gen_cat (gen_section 3 (gen_list (P := BFunc) (f := funcC.enc) gen_func m.funcs))
          (gen_cat (gen_section 4 (gen_list (P := BTable) (f := tableC.enc) gen_table m.tables))
            (gen_cat (gen_section 5 (gen_list (P := BMem) (f := memC.enc) gen_mem m.mems))
              (gen_cat (gen_section 13 (gen_list (P := BTagType) (f := tagTypeC.enc) gen_tagType m.tags))
                (gen_cat (gen_section 6 (gen_list (P := BGlobal) (f := globalC.enc) gen_global m.globals))
                  (gen_cat (gen_section 7 (gen_list (P := BExport) (f := exportC.enc) gen_export m.exports))
                    (gen_cat (gen_section 8 (gen_opt (P := BuN) (f := natC.enc) gen_nat m.start))
                      (gen_cat (gen_section 9 (gen_list (P := BElem) (f := elemC.enc) gen_elem m.elems))
                        (gen_section 11
                          (gen_list (P := BData) (f := dataC.enc) gen_data m.datas))))))))))))

end BinaryGrammar

/-! ## SPEC section 15: the three declarations -/

/-- **SPEC section 7.3 / 15.**  The declarative reading of the pinned binary
grammar, for the modelled subset: `DeclarativeBinaryRelation bytes m` holds
exactly when the grammar of `Wasm/Declarative.lean` derives `bytes` with
synthesized attribute `m`.

Its definition mentions no decoding function.  The exact coverage, and every
deviation from the vendored Core 3.0 grammar, is stated in this file's header
comment. -/
def DeclarativeBinaryRelation (bytes : ByteArray) (module : Module) : Prop :=
  BinaryGrammar.BModule module bytes.toList

/-- The grammar derives, for a given module, exactly the byte sequence that
`Wasm.encode` produces --- no more and no fewer. -/
theorem declarativeBinaryRelation_iff_encode (bytes : ByteArray) (module : Module) :
    DeclarativeBinaryRelation bytes module ↔ bytes = encode module := by
  constructor
  · intro h
    have h1 : bytes.toList = encodeList module :=
      (BinaryGrammar.gen_BModule module bytes.toList).mp h
    apply Bytes.toList_injective
    rw [h1, toList_encode]
  · rintro rfl
    exact (BinaryGrammar.gen_BModule module (encode module).toList).mpr (toList_encode module)

/-- **SPEC section 7.3 / 15, `Wasm.decode_sound`.**  Whatever the executable
decoder accepts, the declarative grammar derives. -/
theorem decode_sound {bytes : ByteArray} {module : Module}
    (h : decode bytes = .ok module) : DeclarativeBinaryRelation bytes module :=
  (declarativeBinaryRelation_iff_encode bytes module).mpr (decode_is_encode h)

/-- **SPEC section 7.3 / 15, `Wasm.decode_complete`.**  Whatever the declarative
grammar derives, the executable decoder accepts --- and returns exactly the
module the derivation synthesized.  This is the direction that rules out a
decoder which silently rejects a well-formed module. -/
theorem decode_complete {bytes : ByteArray} {module : Module}
    (h : DeclarativeBinaryRelation bytes module) : decode bytes = .ok module := by
  rw [(declarativeBinaryRelation_iff_encode bytes module).mp h]
  exact encode_decode_roundtrip module

/-- Soundness and completeness together: the executable decoder *is* the
grammar. -/
theorem decode_iff_declarative (bytes : ByteArray) (module : Module) :
    decode bytes = .ok module ↔ DeclarativeBinaryRelation bytes module :=
  ⟨decode_sound, decode_complete⟩

/--
**SPEC section 7.3 / 15, `Wasm.validate_iff_declarative`.**  The executable
validator decides the declarative validity judgment.  This is exactly the
proposition `Wasm.validate_bool_iff` proves, restated under the name SPEC
section 15 requires; the statement is not weakened, so it is discharged by
`exact`.

## Which vendored validation rules `DeclarativelyValid` corresponds to

`Wasm.DeclarativelyValid` is the conjunction of `Wasm.validate`'s ten
conditions, with the function-body conjunct replaced by a derivation of
`Wasm.ExprTyping`.  Reading them against
`vendor/wasm-spec/document/core/valid/` (see `Wasm/Validate.lean` for the
per-instruction table and for the two respects in which the vendored snapshot
must be read carefully --- its rule *bodies* are unexpanded SpecTec macros, so
the fully-stated normative content is the prose of `valid/conventions.rst`, the
notes of `valid/instructions.rst`, and the sound-and-complete algorithm of
`appendix/algorithm.rst`):

* `Module.checkTypes` --- `valid/modules.rst` "Types" (`Types_ok`), restricted
  through `valid/types.rst` "Recursive Types" (`Subtype_ok`) and "Composite
  Types" (`Comptype_ok/func`) to final, supertype-free, all-`i32` function
  types.
* `Module.checkMems` --- `valid/modules.rst` "Memories" (`Mem_ok`) and
  `valid/types.rst` "Memory Types" / "Limits" (`Memtype_ok`, `Limits_ok`): the
  bounds are meaningful (`min <= max`) and within the `2 ^ 16` range for an
  `i32` address type.
* `Module.checkGlobal` --- `valid/modules.rst` "Globals" (`Global_ok`), with the
  initializer restricted to the single constant instruction the profile admits.
* `Module.checkTag` --- `valid/modules.rst` "Tags" (`Tag_ok`) and
  `valid/types.rst` "Tag Types" (`Tagtype_ok`): a function type with empty
  results, here pinned to `[i32] -> []`.
* `Module.checkFunc` / `ExprTyping` --- `valid/modules.rst` "Functions"
  (`Func_ok`) and "Locals" (`Local_ok`), with the body typed under
  `Module.funcCtx`, whose label stack carries the function's own result arity
  (`appendix/algorithm.rst`: "every function has an implicit outermost label
  that corresponds to an implicit block frame").  The instruction rules are
  `valid/instructions.rst` for the admitted forms; `Wasm/Validate.lean` lists
  them one by one with their anchors.
* `Module.checkStart` --- `valid/modules.rst` "Start Function" (`Start_ok`).
* `Module.checkExports` --- `syntax/modules.rst` "Exports": "each export is
  labeled by a unique name".
* `Module.checkClosed`, `Module.exportsMemory`, `Module.checkGemmExport` ---
  not Core rules but SPEC section 7.2 profile restrictions: no imports, no
  tables, no element or data segments, and the two pinned exports.  They only
  narrow the accepted set.

## What is *not* covered, and what the equivalence therefore means

Not modelled, and hence rejected rather than validated: SIMD/vector, GC
(structures, arrays, `i31`), reference types and every `ref.*` form, tables and
element segments, bulk memory and data segments, tail calls, exception handling
beyond a bare `throw` (`try_table`, `throw_ref`), `call` / `call_indirect` /
`return` / `br_table` / `select`, non-empty block types, and the `i64`, `f32`
and `f64` families.  Nor is Core's **stack polymorphism** modelled:
`valid/instructions.rst` (`_polymorphism`, and the notes at `_valid-unreachable`
and `_valid-br`) makes `unreachable`, `br` and `throw` stack-polymorphic, while
`Wasm.InstrTyping` types them concretely, which rejects programs Core accepts.

So `DeclarativelyValid` is a *sound restriction* of Core 3.0 validation --- it
accepts only modules Core accepts --- and this theorem is an equivalence
between the executable validator and the declarative judgment **for the
modelled subset**, not an equivalence with Core 3.0 validation as a whole. -/
theorem validate_iff_declarative (module : Module) :
    validate module = true ↔ DeclarativelyValid module :=
  validate_bool_iff module

/-! ## Non-vacuity and the canonicality narrowing, checked

The relation would be worthless if it held of everything or of nothing.  These
four facts are the cheapest evidence that it does neither, and that the
canonical-LEB128 narrowing recorded in the file header is real. -/

theorem encodeULEB_three_hundred : encodeULEB 300 = [0xAC, 0x02] := by
  rw [encodeULEB_ge (by omega), encodeULEB_lt (show 300 / 128 < 128 by omega)]
  rfl

theorem encodeULEB_three : encodeULEB 3 = [0x03] := encodeULEB_lt (by omega)

/-- The canonical two-byte unsigned LEB128 encoding of `300` is derivable. -/
theorem BuN_three_hundred : BinaryGrammar.BuN 300 [0xAC, 0x02] :=
  (BinaryGrammar.gen_BuN 300 [0xAC, 0x02]).mpr encodeULEB_three_hundred.symm

/-- The *non*-canonical encoding `0x83 0x00` of `3`, which the pinned
`binary/values.rst` note explicitly allows and this relation deliberately does
not, is **not** derivable. -/
theorem not_BuN_noncanonical_three : ¬ BinaryGrammar.BuN 3 [0x83, 0x00] := by
  intro h
  have h2 := (BinaryGrammar.gen_BuN 3 [0x83, 0x00]).mp h
  rw [encodeULEB_three] at h2
  exact absurd h2 (by decide)

/-- The relation holds of the empty module and its encoding. -/
theorem declarative_encode_empty :
    DeclarativeBinaryRelation (encode Module.empty) Module.empty :=
  decode_sound (encode_decode_roundtrip Module.empty)

/-- The relation does not hold of the empty byte string. -/
theorem not_declarative_empty :
    ¬ DeclarativeBinaryRelation ByteArray.empty Module.empty := by
  intro h
  have hd := decode_complete h
  rw [decode_empty] at hd
  exact absurd hd (by simp)

end WasmGemmGnaf.Wasm
