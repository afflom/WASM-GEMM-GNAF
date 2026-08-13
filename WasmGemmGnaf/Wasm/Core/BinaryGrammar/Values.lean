/-
  Wasm/Core/BinaryGrammar/Values.lean --- the DECLARATIVE binary grammar of
  values, for the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/5.1-binary.values.spectec

  at the pinned commit, together with the grammar notation of
  `X.4-notation.binary.spectec` that the file uses.

  WHAT A GRAMMAR IS HERE, AND WHY IT IS NOT A DECODER.  SpecTec writes the
  binary format as a grammar: a nonterminal `BX : T` names a RELATION between
  byte sequences and values of the abstract sort `T`.  It is transcribed here as
  exactly that -- `Bytes -> T -> Prop` -- built as an inductive relation with one
  constructor per alternative of the production.  Nothing in this module, or in
  any module of `BinaryGrammar/`, mentions a decoding function, and no module
  here imports one.  That is deliberate and it is the whole point: an external
  audit rejected the repository's earlier `decode_sound` / `decode_complete`
  because the "specification" they were proved against was the decoder itself,
  which makes those theorems `rfl` and makes them say nothing.  A decoder proved
  sound and complete against THIS relation says something, because this relation
  was read off the pinned grammar and cannot see the decoder.

  NOTATION.  The SpecTec combinators are transcribed once, here, and used
  throughout:

  * juxtaposition (concatenation) is `++` on the byte side;
  * a terminal `0xNN` is the one-byte list `[tb 0xNN]`;
  * `eps` is `[]`;
  * `X^n` is `Rep`, `X*` is `Star`, `X?` is `Option` with an explicit pair of
    constructors at each use site;
  * `list(BX)` is `Blist` -- a `Bu32` count followed by exactly that many `BX`;
  * `Bsection_(N, BX)` and `Bcustomsec` are in `BinaryGrammar/Modules.lean`,
    with the rest of `5.4`.

  BOUNDED PERMISSIVE LEB128.  `BuN(N)` and `BsN(N)` are transcribed exactly as
  the pinned source writes them, which means NON-MINIMAL encodings are accepted
  inside the length bound: `0x80 0x00` is a derivation of `Bu32` for the value
  `0`, because the second alternative fires on any byte `>= 2^7` and the
  recursive call is at `N - 7`.  A codec that accepts only the canonical
  encoding is strictly narrower than Core 3.0, and that narrowing was one of the
  grounds on which the audit rejected `decode_complete`.  The bound is the
  descending `N`: `Bu32` admits at most five bytes, of which the last must be
  both `< 2^7` and `< 2^(32-28) = 2^4`.
-/
import WasmGemmGnaf.Wasm.Core.Modules

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

/-! ## Grammar notation

`X.4-notation.binary.spectec` fixes the meaning of a SpecTec grammar; these are
the combinators it uses. -/

/-- A byte sequence, the left-hand side of every grammar relation. -/
abbrev Bytes : Type := List Byte

/-- A terminal byte of the grammar, written `0xNN` in the source.  Every
argument used below is `< 0x100`, so the reduction in `Byte.ofNat` is the
identity. -/
def tb (n : Nat) : Byte := Byte.ofNat n

/-- `(el:BX)^n`: exactly `n` consecutive derivations of `BX`, concatenated. -/
inductive Rep {α : Type} (G : Bytes → α → Prop) : Nat → Bytes → List α → Prop where
  /-- `X^0 = eps`. -/
  | nil : Rep G 0 [] []
  /-- `X^(k+1) = X X^k`. -/
  | cons (b : Bytes) (x : α) (bs : Bytes) (xs : List α) (k : Nat) :
      G b x → Rep G k bs xs → Rep G (k + 1) (b ++ bs) (x :: xs)

/-- `(el:BX)*`: any number of consecutive derivations of `BX`. -/
def Star {α : Type} (G : Bytes → α → Prop) (bs : Bytes) (xs : List α) : Prop :=
  ∃ n : Nat, Rep G n bs xs

theorem Rep.length {α : Type} {G : Bytes → α → Prop} {n : Nat} {bs : Bytes}
    {xs : List α} (h : Rep G n bs xs) : xs.length = n := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

/-! ## Numbers -/

/-- `grammar Bbyte : byte = 0x00 | ... | 0xFF`: any single byte. -/
inductive Bbyte : Bytes → Byte → Prop where
  | mk (b : Byte) : Bbyte [b] b

/-- `grammar BuN(N) : uN(N)`, the bounded permissive unsigned LEB128 of the
pinned source:

    | n:Bbyte                 => n                       -- if n < 2^7 /\ n < 2^N
    | n:Bbyte m:BuN(N-7)      => 2^7 * m + (n - 2^7)     -- if n >= 2^7 /\ N > 7

The relation ranges over `Nat`; `BuN.lt_two_pow` below shows that every
derivable value really does lie in `uN(N)`, so nothing is widened by that
choice, and nothing is narrowed either. -/
inductive BuN : Nat → Bytes → Nat → Prop where
  /-- Terminal byte: `-- if $(n < 2^7 /\ n < 2^N)`. -/
  | last (N : Nat) (n : Byte) :
      n.val < 2 ^ 7 → n.val < 2 ^ N → BuN N [n] n.val
  /-- Continuation byte: `-- if $(n >= 2^7 /\ N > 7)`. -/
  | more (N : Nat) (n : Byte) (bs : Bytes) (m : Nat) :
      2 ^ 7 ≤ n.val → 7 < N → BuN (N - 7) bs m →
      BuN N (n :: bs) (2 ^ 7 * m + (n.val - 2 ^ 7))

/-- Every value `BuN(N)` derives lies in `uN(N)`: the grammar's own length bound
is what enforces the range, and it does. -/
theorem BuN.lt_two_pow :
    ∀ {N : Nat} {bs : Bytes} {v : Nat}, BuN N bs v → v < 2 ^ N := by
  intro N bs v h
  induction h with
  | last _ _ _ hlt => exact hlt
  | more N n bs m _ hN _ ih =>
      have hb : n.val < 0x100 := n.property
      have h128 : (2 : Nat) ^ 7 = 128 := rfl
      have hsplit : (2 : Nat) ^ 7 * 2 ^ (N - 7) = 2 ^ N := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hstep : 2 ^ 7 * m + (n.val - 2 ^ 7) < 2 ^ 7 * 2 ^ (N - 7) := by
        have h1 : 2 ^ 7 * (m + 1) ≤ 2 ^ 7 * 2 ^ (N - 7) :=
          Nat.mul_le_mul_left _ ih
        have h2 : 2 ^ 7 * (m + 1) = 2 ^ 7 * m + 2 ^ 7 := by
          rw [Nat.mul_add, Nat.mul_one]
        omega
      omega

/-- `grammar BsN(N) : sN(N)`, the signed LEB128 of the pinned source.

TRANSCRIBED VERBATIM, INCLUDING AN APPARENT UPSTREAM DEFECT.  The pinned file
writes the continuation alternative as

    | n:Bbyte i:BuN(($(N-7))) => $(2^7 * i + (n - 2^7))  -- if $(n >= 2^7 /\ N > 7)

recursing into `BuN`, the UNSIGNED family, not into `BsN`.  Two consequences
follow and both are visible here rather than papered over:

1. no negative value of more than one byte is derivable, since the only
   alternative that can produce a negative result is the single-byte one;
2. the declared result sort `sN(N)` is not respected -- the continuation
   alternative can reach `2^N - 1`, while `sN(N)` stops at `2^(N-1) - 1` -- which
   is why this relation ranges over `Int` rather than over `SN N`.

Both readings agree on the only two uses the binary format makes of `Bs33`
(`Bheaptype` and `Bblocktype`), in the sense that both guard on `>= 0`; they do
NOT agree on which byte sequences are accepted there, because a multi-byte
sequence that the intended grammar would send to a negative number this one
sends to a positive one.  Transcribing what the pinned source says is the only
choice that keeps this file auditable line-by-line against it; the discrepancy
is recorded here so that a reader comparing against the prose specification is
not misled, and so that a future `decode_complete` has to confront it. -/
inductive BsN : Nat → Bytes → Int → Prop where
  /-- `-- if $(n < 2^6 /\ n < 2^(N-1))`. -/
  | pos (N : Nat) (n : Byte) :
      n.val < 2 ^ 6 → n.val < 2 ^ (N - 1) → BsN N [n] (n.val : Int)
  /-- `-- if $(2^6 <= n < 2^7 /\ n >= 2^7 - 2^(N-1))`. -/
  | neg (N : Nat) (n : Byte) :
      2 ^ 6 ≤ n.val → n.val < 2 ^ 7 →
      (2 : Int) ^ 7 - (2 : Int) ^ (N - 1) ≤ (n.val : Int) →
      BsN N [n] ((n.val : Int) - (2 : Int) ^ 7)
  /-- `-- if $(n >= 2^7 /\ N > 7)`; see the caveat in the doc comment. -/
  | more (N : Nat) (n : Byte) (bs : Bytes) (i : Nat) :
      2 ^ 7 ≤ n.val → 7 < N → BuN (N - 7) bs i →
      BsN N (n :: bs) ((2 : Int) ^ 7 * (i : Int) + ((n.val : Int) - (2 : Int) ^ 7))

/-! ### Floating point

`grammar BfN(N) : fN(N) = b*:Bbyte^(N/8) => $inv_fbytes_(N, b*)`.

`$inv_fbytes_` is declared `hint(builtin)` in `3.1-numerics.scalar.spectec` and
carries no equations there, so it is DEFINED here rather than assumed: an
assumed decoder for it would be an axiom on the proof path, which SPEC 19
forbids.  The definition is the IEEE 754 binary interchange format the prose
specification fixes, read little-endian, which is the only reading consistent
with `$fbytes_` being the inverse of `$ibytes_` on the reinterpretation
operators. -/

/-- A byte sequence read as a natural number, least significant byte first. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.val + 0x100 * leNat bs

/-- `$inv_fbytes_(N, b*)`: the IEEE 754 interchange decoding of `N/8` bytes,
least significant byte first.  `none` at a width the pinned source gives no
`$signif` / `$expon` for, or at the wrong number of bytes. -/
def invFbytes (N : Nat) (bs : List Byte) : Option (FN N) :=
  match signif N, expon N with
  | some M, some E =>
      if bs.length = N / 8 then
        let n := leNat bs
        let m := n % 2 ^ M
        let e := n / 2 ^ M % 2 ^ E
        let s := n / 2 ^ (M + E) % 2
        let mag : FNMag N :=
          if e = 0 then .subnorm m
          else if e = 2 ^ E - 1 then (if m = 0 then .inf else .nan m)
          else .norm m ((e : Int) - ((2 ^ (E - 1) - 1 : Nat) : Int))
        some (if s = 0 then .pos mag else .neg mag)
      else none
  | _, _ => none

/-- `grammar BfN(N) : fN(N) = b*:Bbyte^(N/8) => $inv_fbytes_(N, b*)`. -/
def BfN (N : Nat) (bs : Bytes) (v : FN N) : Prop :=
  ∃ bl : List Byte, Rep Bbyte (N / 8) bs bl ∧ invFbytes N bl = some v

/-! ### The named width instances -/

/-- `grammar Bu32 : u32 = n:BuN(32) => n`. -/
def Bu32 (bs : Bytes) (x : U32) : Prop := BuN 32 bs x.val

/-- `grammar Bu64 : u64 = n:BuN(64) => n`. -/
def Bu64 (bs : Bytes) (x : U64) : Prop := BuN 64 bs x.val

/-- `grammar Bs33 : s33 = i:BsN(33) => i`.

The value is an `Int` rather than an `S33` for the reason given on `BsN`. -/
def Bs33 (bs : Bytes) (i : Int) : Prop := BsN 33 bs i

/-- `grammar Bf32 : f32 = p:BfN(32) => p`. -/
def Bf32 (bs : Bytes) (p : F32) : Prop := BfN 32 bs p

/-- `grammar Bf64 : f64 = p:BfN(64) => p`. -/
def Bf64 (bs : Bytes) (p : F64) : Prop := BfN 64 bs p

/-- A `Bu32` whose value is the given literal.  SpecTec writes this as `k:Bu32`
with `k` a numeral -- the selector of a prefixed opcode (`0xFC 12:Bu32`), or the
tag of an element or data segment (`4:Bu32`).  It is a `Bu32`, so it too admits
a non-minimal encoding. -/
def Bu32lit (k : Nat) (bs : Bytes) : Prop := ∃ x : U32, Bu32 bs x ∧ x.val = k

/-- `0xPP k:Bu32`: a prefix byte followed by a `Bu32` encoding of the selector
`k`.  This is the shape every `0xFB` / `0xFC` / `0xFD` opcode of
`5.3-binary.instructions.spectec` has. -/
def Bprefixed (p k : Nat) (bs : Bytes) : Prop :=
  ∃ bn : Bytes, bs = tb p :: bn ∧ Bu32lit k bn

/-! ## Lists -/

/-- `grammar Blist(grammar BX : el) : el* = | n:Bu32 (el:BX)^n => el^n`. -/
inductive Blist {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop where
  | mk (bn bs : Bytes) (n : U32) (xs : List α) :
      Bu32 bn n → Rep G n.val bs xs → Blist G (bn ++ bs) xs

/-- A `list(BX)` is short enough to be a `list(...)`: its length is the value of
a `u32`, hence below `2^32`.  This is what lets a `Blist` derivation supply the
bounded `List_` the syntax layer asks for. -/
theorem Blist.length_lt {α : Type} {G : Bytes → α → Prop} {bs : Bytes}
    {xs : List α} (h : Blist G bs xs) : xs.length < 2 ^ 32 := by
  cases h with
  | mk _ _ n xs _ hrep =>
      have h1 : xs.length = n.val := hrep.length
      rw [h1]
      exact n.property

/-! ## Names -/

/-- `grammar Bname : name = | b*:Blist(Bbyte) => name  -- if $utf8(name) = b*`.

The side condition is what makes this a UTF-8 grammar: a byte list is a `Bname`
for `name` exactly when it IS the UTF-8 encoding of `name`, so an ill-formed
byte sequence has no derivation at all. -/
inductive Bname : Bytes → Name → Prop where
  | mk (bs : Bytes) (bl : List Byte) (nm : Name) :
      Blist Bbyte bs bl → utf8 nm.val = bl → Bname bs nm

/-! ## Indices -/

/-- `grammar Btypeidx : typeidx = x:Bu32 => x`. -/
def Btypeidx (bs : Bytes) (x : TypeIdx) : Prop := Bu32 bs x

/-- `grammar Btagidx : tagidx = x:Bu32 => x`. -/
def Btagidx (bs : Bytes) (x : TagIdx) : Prop := Bu32 bs x

/-- `grammar Bglobalidx : globalidx = x:Bu32 => x`. -/
def Bglobalidx (bs : Bytes) (x : GlobalIdx) : Prop := Bu32 bs x

/-- `grammar Bmemidx : memidx = x:Bu32 => x`. -/
def Bmemidx (bs : Bytes) (x : MemIdx) : Prop := Bu32 bs x

/-- `grammar Btableidx : tableidx = x:Bu32 => x`. -/
def Btableidx (bs : Bytes) (x : TableIdx) : Prop := Bu32 bs x

/-- `grammar Bfuncidx : funcidx = x:Bu32 => x`. -/
def Bfuncidx (bs : Bytes) (x : FuncIdx) : Prop := Bu32 bs x

/-- `grammar Bdataidx : dataidx = x:Bu32 => x`. -/
def Bdataidx (bs : Bytes) (x : DataIdx) : Prop := Bu32 bs x

/-- `grammar Belemidx : elemidx = x:Bu32 => x`. -/
def Belemidx (bs : Bytes) (x : ElemIdx) : Prop := Bu32 bs x

/-- `grammar Blocalidx : localidx = x:Bu32 => x`. -/
def Blocalidx (bs : Bytes) (x : LocalIdx) : Prop := Bu32 bs x

/-- `grammar Blabelidx : labelidx = l:Bu32 => l`. -/
def Blabelidx (bs : Bytes) (l : LabelIdx) : Prop := Bu32 bs l

/-- `grammar Bexternidx : externidx`. -/
inductive Bexternidx : Bytes → ExternIdx → Prop where
  -- core-opcode: 0x00 FUNC
  | func (bs : Bytes) (x : FuncIdx) : Bfuncidx bs x → Bexternidx (tb 0x00 :: bs) (.func x)
  -- core-opcode: 0x01 TABLE
  | table (bs : Bytes) (x : TableIdx) : Btableidx bs x → Bexternidx (tb 0x01 :: bs) (.table x)
  -- core-opcode: 0x02 MEM
  | mem (bs : Bytes) (x : MemIdx) : Bmemidx bs x → Bexternidx (tb 0x02 :: bs) (.mem x)
  -- core-opcode: 0x03 GLOBAL
  | global (bs : Bytes) (x : GlobalIdx) : Bglobalidx bs x → Bexternidx (tb 0x03 :: bs) (.global x)
  -- core-opcode: 0x04 TAG
  | tag (bs : Bytes) (x : TagIdx) : Btagidx bs x → Bexternidx (tb 0x04 :: bs) (.tag x)

end WasmGemmGnaf.Wasm.Core.Binary
