/-
  Wasm/Core/Values.lean --- the value syntax of the pinned WebAssembly Core 3.0
  front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/1.1-syntax.values.spectec

  at the pinned commit.  The coverage marker comment beside a declaration names
  the SpecTec production it discharges; `xtask core` extracts the checklist from
  the vendored file itself and rejects any marker that names something the
  sources do not define.  (This paragraph deliberately does not spell the marker
  prefix out: prose that did would itself be read as a claim.)

  SCOPE.  This file is SYNTAX ONLY.  It says what a Core 3.0 value *is*; it does
  not decode one, validate one, or execute one.  The binary grammar
  (`5.*-binary.*.spectec`) and the typing rules (`2.*-validation.*.spectec`) are
  built on top of this layer, not in it.  Nothing here is claimed to be
  equivalent to `Wasm/Syntax.lean`'s subset machine; the two are reconciled
  later.

  TRANSCRIPTION CONVENTIONS, stated once and used throughout the Core layer:

  * A SpecTec production `syntax x = A | B` becomes a Lean `inductive`, one
    constructor per alternative, in source order.
  * A production that is an abbreviation (`syntax u8 = uN(`8)`) becomes an
    `abbrev`, so the two really are the same type rather than merely isomorphic.
  * A production carrying a side condition (`-- if ...`) becomes the datatype
    *without* the condition plus a decidable `wf` predicate that states it.  The
    condition is transcribed, never dropped: `wf` is what carries it.  This is
    the only faithful choice available, because several conditions (e.g. the
    `list(...)` length bound inside a recursive type) cannot be expressed as a
    Lean subtype without violating the nested-inductive restriction.
  * `X*` becomes `List X`; `X?` becomes `Option X`.
-/

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## Integers

`1.1-syntax.values.spectec` opens with the bit and byte alphabets and the
bounded integer families `uN(N)`, `sN(N)`, `iN(N)`. -/

/-- `syntax bit = 0 | 1`. -/
-- core-syntax: bit
inductive Bit where
  | b0
  | b1
  deriving DecidableEq, Repr, Inhabited

/-- `syntax byte = 0x00 | ... | 0xFF`. -/
-- core-syntax: byte
abbrev Byte : Type := { n : Nat // n < 0x100 }

instance : Inhabited Byte := ⟨⟨0, by decide⟩⟩
instance : Repr Byte := ⟨fun x _ => repr x.val⟩

/-- `0 < 2 ^ N`, needed to inhabit every bounded integer family. -/
theorem two_pow_pos : ∀ N : Nat, 0 < 2 ^ N
  | 0 => by decide
  | n + 1 => by
      have h := two_pow_pos n
      rw [Nat.pow_succ]
      omega

/-- `syntax uN(N) = 0 | ... | 2^N-1`: the unsigned integers of width `N`. -/
-- core-syntax: uN(N)
abbrev UN (N : Nat) : Type := { n : Nat // n < 2 ^ N }

instance (N : Nat) : Inhabited (UN N) := ⟨⟨0, two_pow_pos N⟩⟩
instance (N : Nat) : Repr (UN N) := ⟨fun x _ => repr x.val⟩

/-- `syntax sN(N) = -2^(N-1) | ... | -1 | 0 | +1 | ... | +2^(N-1)-1`: the signed
integers of width `N`, as a two's-complement range over `Int`. -/
-- core-syntax: sN(N)
abbrev SN (N : Nat) : Type :=
  { i : Int //
      -((2 ^ (N - 1) : Nat) : Int) ≤ i ∧ i ≤ ((2 ^ (N - 1) : Nat) : Int) - 1 }

instance (N : Nat) : Inhabited (SN N) :=
  ⟨⟨0, by have := two_pow_pos (N - 1); omega⟩⟩
instance (N : Nat) : Repr (SN N) := ⟨fun x _ => repr x.val⟩

/-- `syntax iN(N) = uN(N)`: an uninterpreted `N`-bit integer, i.e. the same
carrier as `uN(N)`.  The signed reading is a numeric operation, not a syntactic
one, so the two families are literally the same type here — as in the source. -/
-- core-syntax: iN(N)
abbrev IN (N : Nat) : Type := UN N

/-- `syntax u8 = uN(8)`. -/
-- core-syntax: u8
abbrev U8 : Type := UN 8

/-- `syntax u16 = uN(16)`. -/
-- core-syntax: u16
abbrev U16 : Type := UN 16

/-- `syntax u31 = uN(31)`. -/
-- core-syntax: u31
abbrev U31 : Type := UN 31

/-- `syntax u32 = uN(32)`. -/
-- core-syntax: u32
abbrev U32 : Type := UN 32

/-- `syntax u64 = uN(64)`. -/
-- core-syntax: u64
abbrev U64 : Type := UN 64

/-- `syntax u128 = uN(128)`. -/
-- core-syntax: u128
abbrev U128 : Type := UN 128

/-- `syntax s33 = sN(33)`. -/
-- core-syntax: s33
abbrev S33 : Type := SN 33

/-- A byte from an arbitrary natural, reduced modulo `0x100`.  Used to build the
UTF-8 encoding below; every argument it is applied to is already `< 0x100`. -/
def Byte.ofNat (n : Nat) : Byte := ⟨n % 0x100, Nat.mod_lt _ (by decide)⟩

/-! ## Floating-point

`def $signif(N)` and `def $expon(N)` are given by the source at `N = 32` and
`N = 64` only, so they are transcribed as partial functions rather than as total
functions with a junk value. -/

/-- `def $signif(N)`: `$signif(32) = 23`, `$signif(64) = 52`.  Partial. -/
def signif : Nat → Option Nat
  | 32 => some 23
  | 64 => some 52
  | _ => none

/-- `def $expon(N)`: `$expon(32) = 8`, `$expon(64) = 11`.  Partial. -/
def expon : Nat → Option Nat
  | 32 => some 8
  | 64 => some 11
  | _ => none

/-- `def $M(N) = $signif(N)`. -/
abbrev bigM (N : Nat) : Option Nat := signif N

/-- `def $E(N) = $expon(N)`. -/
abbrev bigE (N : Nat) : Option Nat := expon N

/-- `syntax exp = int`: the unbounded exponent of a floating-point magnitude. -/
-- core-syntax: exp
abbrev Exp : Type := Int

/-- `syntax fNmag(N) = NORM m exp | SUBNORM m | INF | NAN (m)`.

The source's side conditions are carried by `FNMag.wf`, not by the constructors:

    NORM m exp  -- if m < 2^M(N) /\ 2-2^(E(N)-1) <= exp <= 2^(E(N)-1)-1
    SUBNORM m   -- if m < 2^M(N) /\ 2-2^(E(N)-1) = exp
    NAN (m)     -- if 1 <= m < 2^M(N)
-/
-- core-syntax: fNmag(N)
inductive FNMag (N : Nat) where
  | norm (m : Nat) (e : Exp)
  | subnorm (m : Nat)
  | inf
  | nan (m : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace FNMag

/-- The side conditions of `fNmag(N)`, verbatim. -/
def wf {N : Nat} : FNMag N → Bool
  | .norm m e =>
      match bigM N, bigE N with
      | some M, some E =>
          decide (m < 2 ^ M) &&
          decide ((2 : Int) - 2 ^ (E - 1) ≤ e) &&
          decide (e ≤ (2 : Int) ^ (E - 1) - 1)
      | _, _ => false
  | .subnorm m =>
      match bigM N with
      | some M => decide (m < 2 ^ M)
      | none => false
  | .inf => true
  | .nan m =>
      match bigM N with
      | some M => decide (1 ≤ m) && decide (m < 2 ^ M)
      | none => false

end FNMag

/-- `syntax fN(N) = POS fNmag(N) | NEG fNmag(N)`. -/
-- core-syntax: fN(N)
inductive FN (N : Nat) where
  | pos (mag : FNMag N)
  | neg (mag : FNMag N)
  deriving DecidableEq, Repr, Inhabited

/-- The side conditions of `fN(N)`: those of its magnitude. -/
def FN.wf {N : Nat} : FN N → Bool
  | .pos mag => mag.wf
  | .neg mag => mag.wf

/-- `syntax f32 = fN(32)`. -/
-- core-syntax: f32
abbrev F32 : Type := FN 32

/-- `syntax f64 = fN(64)`. -/
-- core-syntax: f64
abbrev F64 : Type := FN 64

/-! ## Vectors -/

/-- `syntax vN(N) = uN(N)`. -/
-- core-syntax: vN(N)
abbrev VN (N : Nat) : Type := UN N

/-- `syntax v128 = vN(128)`. -/
-- core-syntax: v128
abbrev V128 : Type := VN 128

/-! ## Lists -/

/-- `syntax list(syntax X) = X*  -- if |X*| < 2^32`.

The bound is part of the production, so it is part of the type wherever Lean
permits.  Inside a recursive type definition it cannot be (a `Subtype` may not
occur in a nested-inductive position), and there the bound is carried by the
enclosing `wf` predicate instead; each such site says so. -/
-- core-syntax: list(syntax
abbrev List_ (X : Type) : Type := { l : List X // l.length < 2 ^ 32 }

instance (X : Type) : Inhabited (List_ X) := ⟨⟨[], two_pow_pos 32⟩⟩
instance (X : Type) [Repr X] : Repr (List_ X) := ⟨fun x n => reprPrec x.val n⟩

/-! ## Names -/

/-- `syntax char = U+0000 | ... | U+D7FF | U+E000 | ... | U+10FFFF`: a Unicode
scalar value, i.e. a code point that is not a surrogate. -/
-- core-syntax: char
abbrev UChar : Type := { c : Nat // c ≤ 0xD7FF ∨ (0xE000 ≤ c ∧ c ≤ 0x10FFFF) }

instance : Inhabited UChar := ⟨⟨0, Or.inl (by decide)⟩⟩
instance : Repr UChar := ⟨fun x _ => repr x.val⟩

/-- The UTF-8 encoding of one scalar value.  `def $utf8(char*) : byte*` is
declared without equations in the SpecTec source (the prose specification fixes
it), so it is defined here rather than assumed: an assumed encoder would be an
axiom on the proof path. -/
def utf8Char (c : UChar) : List Byte :=
  let n := c.val
  if n < 0x80 then
    [Byte.ofNat n]
  else if n < 0x800 then
    [Byte.ofNat (0xC0 + n / 0x40), Byte.ofNat (0x80 + n % 0x40)]
  else if n < 0x10000 then
    [Byte.ofNat (0xE0 + n / 0x1000),
     Byte.ofNat (0x80 + n / 0x40 % 0x40),
     Byte.ofNat (0x80 + n % 0x40)]
  else
    [Byte.ofNat (0xF0 + n / 0x40000),
     Byte.ofNat (0x80 + n / 0x1000 % 0x40),
     Byte.ofNat (0x80 + n / 0x40 % 0x40),
     Byte.ofNat (0x80 + n % 0x40)]

/-- `def $utf8(char*) : byte*`. -/
def utf8 (cs : List UChar) : List Byte := cs.flatMap utf8Char

/-- `syntax name = char*  -- if |$utf8(char*)| < 2^32`. -/
-- core-syntax: name
abbrev Name : Type := { cs : List UChar // (utf8 cs).length < 2 ^ 32 }

instance : Inhabited Name := ⟨⟨[], two_pow_pos 32⟩⟩
instance : Repr Name := ⟨fun x n => reprPrec x.val n⟩

/-! ## Indices -/

/-- `syntax idx = u32`. -/
-- core-syntax: idx
abbrev Idx : Type := U32

/-- `syntax laneidx = u8`. -/
-- core-syntax: laneidx
abbrev LaneIdx : Type := U8

/-- `syntax typeidx = idx`. -/
-- core-syntax: typeidx
abbrev TypeIdx : Type := Idx

/-- `syntax funcidx = idx`. -/
-- core-syntax: funcidx
abbrev FuncIdx : Type := Idx

/-- `syntax globalidx = idx`. -/
-- core-syntax: globalidx
abbrev GlobalIdx : Type := Idx

/-- `syntax tableidx = idx`. -/
-- core-syntax: tableidx
abbrev TableIdx : Type := Idx

/-- `syntax memidx = idx`. -/
-- core-syntax: memidx
abbrev MemIdx : Type := Idx

/-- `syntax tagidx = idx`. -/
-- core-syntax: tagidx
abbrev TagIdx : Type := Idx

/-- `syntax elemidx = idx`. -/
-- core-syntax: elemidx
abbrev ElemIdx : Type := Idx

/-- `syntax dataidx = idx`. -/
-- core-syntax: dataidx
abbrev DataIdx : Type := Idx

/-- `syntax labelidx = idx`. -/
-- core-syntax: labelidx
abbrev LabelIdx : Type := Idx

/-- `syntax localidx = idx`. -/
-- core-syntax: localidx
abbrev LocalIdx : Type := Idx

/-- `syntax fieldidx = idx`. -/
-- core-syntax: fieldidx
abbrev FieldIdx : Type := Idx

/-- `syntax externidx = FUNC funcidx | GLOBAL globalidx | TABLE tableidx
    | MEM memidx | TAG tagidx`. -/
-- core-syntax: externidx
inductive ExternIdx where
  | func (x : FuncIdx)
  | global (x : GlobalIdx)
  | table (x : TableIdx)
  | mem (x : MemIdx)
  | tag (x : TagIdx)
  deriving DecidableEq, Repr, Inhabited

namespace ExternIdx

/-- `def $funcsxx(externidx*) : typeidx*`. -/
def funcs : List ExternIdx → List FuncIdx
  | [] => []
  | .func x :: xs => x :: funcs xs
  | _ :: xs => funcs xs

/-- `def $globalsxx(externidx*) : globalidx*`. -/
def globals : List ExternIdx → List GlobalIdx
  | [] => []
  | .global x :: xs => x :: globals xs
  | _ :: xs => globals xs

/-- `def $tablesxx(externidx*) : tableidx*`. -/
def tables : List ExternIdx → List TableIdx
  | [] => []
  | .table x :: xs => x :: tables xs
  | _ :: xs => tables xs

/-- `def $memsxx(externidx*) : memidx*`. -/
def mems : List ExternIdx → List MemIdx
  | [] => []
  | .mem x :: xs => x :: mems xs
  | _ :: xs => mems xs

/-- `def $tagsxx(externidx*) : tagidx*`. -/
def tags : List ExternIdx → List TagIdx
  | [] => []
  | .tag x :: xs => x :: tags xs
  | _ :: xs => tags xs

end ExternIdx

/-! ## Free indices -/

/-- `syntax free = { TYPES typeidx*, FUNCS funcidx*, GLOBALS globalidx*,
    TABLES tableidx*, MEMS memidx*, ELEMS elemidx*, DATAS dataidx*,
    LOCALS localidx*, LABELS labelidx* }`. -/
-- core-syntax: free
structure Free where
  types : List TypeIdx := []
  funcs : List FuncIdx := []
  globals : List GlobalIdx := []
  tables : List TableIdx := []
  mems : List MemIdx := []
  elems : List ElemIdx := []
  datas : List DataIdx := []
  locals : List LocalIdx := []
  labels : List LabelIdx := []
  deriving DecidableEq, Repr, Inhabited

namespace Free

/-- The empty free-index record, `{}` in the source. -/
def empty : Free := {}

/-- `free ++ free'`, componentwise. -/
def append (a b : Free) : Free where
  types := a.types ++ b.types
  funcs := a.funcs ++ b.funcs
  globals := a.globals ++ b.globals
  tables := a.tables ++ b.tables
  mems := a.mems ++ b.mems
  elems := a.elems ++ b.elems
  datas := a.datas ++ b.datas
  locals := a.locals ++ b.locals
  labels := a.labels ++ b.labels

instance : Append Free := ⟨append⟩

/-- `def $free_opt(free?) : free`. -/
def ofOption : Option Free → Free
  | none => empty
  | some f => f

/-- `def $free_list(free*) : free`. -/
def join : List Free → Free
  | [] => empty
  | f :: fs => append f (join fs)

/-- `def $free_typeidx(typeidx) = {TYPES typeidx}`. -/
def ofTypeIdx (x : TypeIdx) : Free := { types := [x] }

/-- `def $free_funcidx(funcidx) = {FUNCS funcidx}`. -/
def ofFuncIdx (x : FuncIdx) : Free := { funcs := [x] }

/-- `def $free_globalidx(globalidx) = {GLOBALS globalidx}`. -/
def ofGlobalIdx (x : GlobalIdx) : Free := { globals := [x] }

/-- `def $free_tableidx(tableidx) = {TABLES tableidx}`. -/
def ofTableIdx (x : TableIdx) : Free := { tables := [x] }

/-- `def $free_memidx(memidx) = {MEMS memidx}`. -/
def ofMemIdx (x : MemIdx) : Free := { mems := [x] }

/-- `def $free_elemidx(elemidx) = {ELEMS elemidx}`. -/
def ofElemIdx (x : ElemIdx) : Free := { elems := [x] }

/-- `def $free_dataidx(dataidx) = {DATAS dataidx}`. -/
def ofDataIdx (x : DataIdx) : Free := { datas := [x] }

/-- `def $free_localidx(localidx) = {LOCALS localidx}`. -/
def ofLocalIdx (x : LocalIdx) : Free := { locals := [x] }

/-- `def $free_labelidx(labelidx) = {LABELS labelidx}`. -/
def ofLabelIdx (x : LabelIdx) : Free := { labels := [x] }

/-- `def $free_externidx(externidx) : free`.

The pinned source gives equations for `FUNC`, `GLOBAL`, `TABLE` and `MEM` only.
`free` has no `TAGS` component, so the empty record is the only total completion
available; the gap is in the source, and is recorded here rather than hidden. -/
def ofExternIdx : ExternIdx → Free
  | .func x => ofFuncIdx x
  | .global x => ofGlobalIdx x
  | .table x => ofTableIdx x
  | .mem x => ofMemIdx x
  | .tag _ => empty

end Free

end WasmGemmGnaf.Wasm.Core
