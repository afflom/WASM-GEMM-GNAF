/-
  Wasm/Core/Operators.lean --- the literal, operator, shape and memory-argument
  syntax of the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/1.3-syntax.instructions.spectec

  up to and including `syntax blocktype`.  The instruction sort itself is
  `Core/Instructions.lean`; splitting the file keeps elaboration of the ~120
  constructor instruction type separate from the ~60 operator sorts it uses.

  HOW THE PARAMETERISED FAMILIES ARE TRANSCRIBED.  SpecTec writes a family as a
  declaration with no right-hand side followed by one declaration per instance:

      syntax unop_(numtype)
      syntax unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND sz  -- if sz < $sizenn(Inn)
      syntax unop_(Fnn) = ABS | NEG | SQRT | ...

  Two different shapes of family occur, and they are transcribed differently
  because they mean different things.

  * A LITERAL family (`num_`, `pack_`, `lane_`, `vec_`, `lit_`) has instances
    that are genuinely different CARRIERS -- `iN(32)` and `fN(32)` are not the
    same set.  These become `Type`-valued functions of the index, so that
    `Num_ I32` really is `iN(32)`.  Where the source declares no instance (there
    is no `lit_` at a reference type) the family is `Empty`, which is the honest
    reading of "no instance": there are no such literals.

  * An OPERATOR family (`unop_`, `binop_`, `vbinop_`, `vcvtop__`, `loadop_`,
    ...) has instances that are finite sets of SYMBOLS, and the family is their
    union.  These become one inductive per instance plus a sum type for the
    family, together with a decidable predicate `wf` that says which symbols
    belong to which instance.  `wf` also carries every `-- if` side condition of
    the source, verbatim; that is where `EXTEND sz -- if sz < $sizenn(Inn)`
    lives.  Keeping the family non-dependent is what lets `instr` stay a plain
    inductive with a derived `DecidableEq`, which the decoder and the validator
    both need.

  In both cases `wf` is necessary and not optional: an `Instr` built from a
  symbol outside its index's instance is a term of the Lean type but not a Core
  3.0 instruction, exactly as an `fNmag` outside its bounds is not a Core 3.0
  float.
-/
import WasmGemmGnaf.Wasm.Core.Types

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## Constants -/

/-- `syntax num_(Inn) = iN($sizenn(Inn))`. -/
-- core-syntax: num_(Inn)
abbrev NumI (n : Inn) : Type := IN n.size

/-- `syntax num_(Fnn) = fN($sizenn(Fnn))`. -/
-- core-syntax: num_(Fnn)
abbrev NumF (n : Fnn) : Type := FN n.size

/-- `syntax num_(numtype)`: the family whose instances are `num_(Inn)` and
`num_(Fnn)`.  Every `numtype` is one or the other, so the family is total. -/
-- core-syntax: num_(numtype)
def Num_ : NumType → Type
  | .i32 => NumI .i32
  | .i64 => NumI .i64
  | .f32 => NumF .f32
  | .f64 => NumF .f64

instance (nt : NumType) : DecidableEq (Num_ nt) := by
  cases nt
  · exact (inferInstance : DecidableEq (NumI .i32))
  · exact (inferInstance : DecidableEq (NumI .i64))
  · exact (inferInstance : DecidableEq (NumF .f32))
  · exact (inferInstance : DecidableEq (NumF .f64))

instance (nt : NumType) : Repr (Num_ nt) := by
  cases nt
  · exact (inferInstance : Repr (NumI .i32))
  · exact (inferInstance : Repr (NumI .i64))
  · exact (inferInstance : Repr (NumF .f32))
  · exact (inferInstance : Repr (NumF .f64))

instance (nt : NumType) : Inhabited (Num_ nt) := by
  cases nt
  · exact (inferInstance : Inhabited (NumI .i32))
  · exact (inferInstance : Inhabited (NumI .i64))
  · exact (inferInstance : Inhabited (NumF .f32))
  · exact (inferInstance : Inhabited (NumF .f64))

/-- The side conditions of a `num_(nt)` literal.  Integer literals are bounded
by their carrier; float literals additionally have to satisfy the bounds of
`fNmag(N)`. -/
def Num_.wf : (nt : NumType) → Num_ nt → Bool
  | .i32, _ => true
  | .i64, _ => true
  | .f32, c => FN.wf c
  | .f64, c => FN.wf c

/-- `syntax pack_(Pnn) = iN($psizenn(Pnn))`. -/
-- core-syntax: pack_(Pnn)
abbrev PackLit (p : Pnn) : Type := IN p.size

/-- `syntax lane_(numtype) = num_(numtype)`. -/
-- core-syntax: lane_(numtype)
abbrev LaneNum (nt : NumType) : Type := Num_ nt

/-- `syntax lane_(packtype) = pack_(packtype)`. -/
-- core-syntax: lane_(packtype)
abbrev LanePack (pt : PackType) : Type := PackLit pt

/-- `syntax lane_(Jnn) = iN($lsize(Jnn))`.

The source marks this instance `;; HACK`: it overlaps `lane_(numtype)` and
`lane_(packtype)`, and agrees with both where they overlap, since
`$lsize` is `$size` on a `numtype` and `$psize` on a `packtype`. -/
-- core-syntax: lane_(Jnn)
abbrev LaneJ (j : Jnn) : Type := IN j.size

/-- `syntax lane_(lanetype)`: the family whose instances are `lane_(numtype)`
and `lane_(packtype)`. -/
-- core-syntax: lane_(lanetype)
def Lane_ : LaneType → Type
  | .num nt => LaneNum nt
  | .pack pt => LanePack pt

instance (lt : LaneType) : DecidableEq (Lane_ lt) := by
  cases lt with
  | num nt => exact (inferInstance : DecidableEq (Num_ nt))
  | pack pt => exact (inferInstance : DecidableEq (PackLit pt))

/-- `Vnn` reading of a `vectype`; the two sorts have the same single case. -/
def VecType.toVnn : VecType → Vnn
  | .v128 => .v128

/-- `syntax vec_(Vnn) = vN($vsize(Vnn))`. -/
-- core-syntax: vec_(Vnn)
abbrev VecLit (v : Vnn) : Type := VN v.size

instance (v : Vnn) : DecidableEq (VecLit v) := by
  cases v; exact (inferInstance : DecidableEq (VN 128))

instance (v : Vnn) : Repr (VecLit v) := by
  cases v; exact (inferInstance : Repr (VN 128))

instance (v : Vnn) : Inhabited (VecLit v) := by
  cases v; exact (inferInstance : Inhabited (VN 128))

/-- `syntax lit_(numtype) = num_(numtype)`. -/
-- core-syntax: lit_(numtype)
abbrev LitNum (nt : NumType) : Type := Num_ nt

/-- `syntax lit_(vectype) = vec_(vectype)`. -/
-- core-syntax: lit_(vectype)
abbrev LitVec (vt : VecType) : Type := VecLit vt.toVnn

/-- `syntax lit_(packtype) = pack_(packtype)`. -/
-- core-syntax: lit_(packtype)
abbrev LitPack (pt : PackType) : Type := PackLit pt

/-- `syntax lit_(storagetype)`: the family whose instances are `lit_(numtype)`,
`lit_(vectype)` and `lit_(packtype)`.

A `storagetype` may also be a `reftype` or `BOT`, and the source declares no
`lit_` instance for either; there are no reference or bottom literals, so the
family is `Empty` there. -/
-- core-syntax: lit_(storagetype)
def Lit_ : StorageType → Type
  | .val (.num nt) => LitNum nt
  | .val (.vec vt) => LitVec vt
  | .val (.ref _) => Empty
  | .val .bot => Empty
  | .pack pt => LitPack pt

/-! ## Numeric operators -/

/-- `syntax sz = 8 | 16 | 32 | 64`. -/
-- core-syntax: sz
inductive Sz where
  | s8
  | s16
  | s32
  | s64
  deriving DecidableEq, Repr, Inhabited

/-- The width a pack size denotes. -/
def Sz.toNat : Sz → Nat
  | .s8 => 8
  | .s16 => 16
  | .s32 => 32
  | .s64 => 64

/-- `syntax sx = U | S`. -/
-- core-syntax: sx
inductive Sx where
  | u
  | s
  deriving DecidableEq, Repr, Inhabited

/-- `syntax unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND sz`, the last with
`-- if sz < $sizenn(Inn)` (carried by `Unop.wf`). -/
-- core-syntax: unop_(Inn)
inductive UnopI where
  | clz
  | ctz
  | popcnt
  | extend (n : Sz)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax unop_(Fnn) = ABS | NEG | SQRT | CEIL | FLOOR | TRUNC | NEAREST`. -/
-- core-syntax: unop_(Fnn)
inductive UnopF where
  | abs
  | neg
  | sqrt
  | ceil
  | floor
  | trunc
  | nearest
  deriving DecidableEq, Repr, Inhabited

/-- `syntax unop_(numtype)`: the union of `unop_(Inn)` and `unop_(Fnn)`. -/
-- core-syntax: unop_(numtype)
inductive Unop where
  | int (op : UnopI)
  | float (op : UnopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `unop_(nt)`, side conditions included. -/
def Unop.wf (nt : NumType) : Unop → Bool
  | .int op =>
      match nt.toInn? with
      | some n => match op with
          | .extend sz => decide (sz.toNat < n.size)
          | _ => true
      | none => false
  | .float _ => nt.toFnn?.isSome

/-- `syntax binop_(Inn) = ADD | SUB | MUL | DIV sx | REM sx | AND | OR | XOR
    | SHL | SHR sx | ROTL | ROTR`. -/
-- core-syntax: binop_(Inn)
inductive BinopI where
  | add
  | sub
  | mul
  | div (sx : Sx)
  | rem (sx : Sx)
  | and
  | or
  | xor
  | shl
  | shr (sx : Sx)
  | rotl
  | rotr
  deriving DecidableEq, Repr, Inhabited

/-- `syntax binop_(Fnn) = ADD | SUB | MUL | DIV | MIN | MAX | COPYSIGN`. -/
-- core-syntax: binop_(Fnn)
inductive BinopF where
  | add
  | sub
  | mul
  | div
  | min
  | max
  | copysign
  deriving DecidableEq, Repr, Inhabited

/-- `syntax binop_(numtype)`: the union of `binop_(Inn)` and `binop_(Fnn)`. -/
-- core-syntax: binop_(numtype)
inductive Binop where
  | int (op : BinopI)
  | float (op : BinopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `binop_(nt)`. -/
def Binop.wf (nt : NumType) : Binop → Bool
  | .int _ => nt.toInn?.isSome
  | .float _ => nt.toFnn?.isSome

/-- `syntax testop_(Inn) = EQZ`. -/
-- core-syntax: testop_(Inn)
inductive TestopI where
  | eqz
  deriving DecidableEq, Repr, Inhabited

/-- `syntax testop_(numtype)`: the only instance is `testop_(Inn)`; the source
records `testop_(Fnn)` as uninhabited and leaves it commented out. -/
-- core-syntax: testop_(numtype)
inductive Testop where
  | int (op : TestopI)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `testop_(nt)`. -/
def Testop.wf (nt : NumType) : Testop → Bool
  | .int _ => nt.toInn?.isSome

/-- `syntax relop_(Inn) = EQ | NE | LT sx | GT sx | LE sx | GE sx`. -/
-- core-syntax: relop_(Inn)
inductive RelopI where
  | eq
  | ne
  | lt (sx : Sx)
  | gt (sx : Sx)
  | le (sx : Sx)
  | ge (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax relop_(Fnn) = EQ | NE | LT | GT | LE | GE`. -/
-- core-syntax: relop_(Fnn)
inductive RelopF where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
  deriving DecidableEq, Repr, Inhabited

/-- `syntax relop_(numtype)`: the union of `relop_(Inn)` and `relop_(Fnn)`. -/
-- core-syntax: relop_(numtype)
inductive Relop where
  | int (op : RelopI)
  | float (op : RelopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `relop_(nt)`. -/
def Relop.wf (nt : NumType) : Relop → Bool
  | .int _ => nt.toInn?.isSome
  | .float _ => nt.toFnn?.isSome

/-- `syntax cvtop__(Inn_1, Inn_2) = EXTEND sx | WRAP` and
`syntax cvtop__(Inn_1, Fnn_2) = CONVERT sx | REINTERPRET`; the side conditions
on the widths are carried by `Cvtop.wf`. -/
-- core-syntax: cvtop__(Inn_1,
inductive CvtopII where
  | extend (sx : Sx)
  | wrap
  deriving DecidableEq, Repr, Inhabited

/-- `syntax cvtop__(Inn_1, Fnn_2) = CONVERT sx | REINTERPRET`. -/
inductive CvtopIF where
  | convert (sx : Sx)
  | reinterpret
  deriving DecidableEq, Repr, Inhabited

/-- `syntax cvtop__(Fnn_1, Inn_2) = TRUNC sx | TRUNC_SAT sx | REINTERPRET` and
`syntax cvtop__(Fnn_1, Fnn_2) = PROMOTE | DEMOTE`. -/
-- core-syntax: cvtop__(Fnn_1,
inductive CvtopFI where
  | trunc (sx : Sx)
  | truncSat (sx : Sx)
  | reinterpret
  deriving DecidableEq, Repr, Inhabited

/-- `syntax cvtop__(Fnn_1, Fnn_2) = PROMOTE | DEMOTE`. -/
inductive CvtopFF where
  | promote
  | demote
  deriving DecidableEq, Repr, Inhabited

/-- `syntax cvtop__(numtype_1, numtype_2)`: the union of the four instances.

The index order is (operand type, result type), matching the source's
`cvtop__(numtype_2, numtype_1)` in `CVTOP numtype_1 numtype_2 ...`, where
`numtype_1` is the result. -/
-- core-syntax: cvtop__(numtype_1,
inductive Cvtop where
  | ii (op : CvtopII)
  | ifl (op : CvtopIF)
  | fi (op : CvtopFI)
  | ff (op : CvtopFF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `cvtop__(src, tgt)`, side conditions included. -/
def Cvtop.wf (src tgt : NumType) : Cvtop → Bool
  | .ii op =>
      match src.toInn?, tgt.toInn? with
      | some a, some b => match op with
          | .extend _ => decide (a.size < b.size)
          | .wrap => decide (a.size > b.size)
      | _, _ => false
  | .ifl op =>
      match src.toInn?, tgt.toFnn? with
      | some a, some b => match op with
          | .convert _ => true
          | .reinterpret => decide (a.size = b.size)
      | _, _ => false
  | .fi op =>
      match src.toFnn?, tgt.toInn? with
      | some a, some b => match op with
          | .trunc _ => true
          | .truncSat _ => true
          | .reinterpret => decide (a.size = b.size)
      | _, _ => false
  | .ff op =>
      match src.toFnn?, tgt.toFnn? with
      | some a, some b => match op with
          | .promote => decide (a.size < b.size)
          | .demote => decide (a.size > b.size)
      | _, _ => false

/-! ## Vector shapes -/

/-- `syntax dim = 1 | 2 | 4 | 8 | 16`. -/
-- core-syntax: dim
inductive Dim where
  | d1
  | d2
  | d4
  | d8
  | d16
  deriving DecidableEq, Repr, Inhabited

/-- The number a dimension denotes. -/
def Dim.toNat : Dim → Nat
  | .d1 => 1
  | .d2 => 2
  | .d4 => 4
  | .d8 => 8
  | .d16 => 16

/-- `syntax shape = lanetype X dim  -- if $($lsize(lanetype) * dim = 128)`.

The side condition is `Shape.wf`. -/
-- core-syntax: shape
structure Shape where
  lane : LaneType
  dim : Dim
  deriving DecidableEq, Repr, Inhabited

namespace Shape

/-- `-- if $($lsize(lanetype) * dim = 128)`. -/
def wf (s : Shape) : Bool := decide (s.lane.size * s.dim.toNat = 128)

/-- `def $lanetype(shape) : lanetype`. -/
def lanetype (s : Shape) : LaneType := s.lane

/-- `def $unpackshape(shape) : numtype`. -/
def unpack (s : Shape) : NumType := s.lane.unpack

/-- `-- if $lanetype(shape) = Jnn`, the side condition of `ishape`. -/
def isIShape (s : Shape) : Bool := s.lane.toJnn?.isSome

/-- `-- if $lanetype(shape) = I8`, the side condition of `bshape`. -/
def isBShape (s : Shape) : Bool :=
  match s.lane with
  | .pack .i8 => true
  | _ => false

/-- `$lanetype(shape) <- I32 I64 F32 F64`, i.e. the lane type is a `numtype`
rather than a `packtype`.  This is the right-hand side of `VEXTRACT_LANE`'s
`-- if sx? = eps <=> $lanetype(shape) <- I32 I64 F32 F64`. -/
def laneIsNum (s : Shape) : Bool :=
  match s.lane with
  | .num _ => true
  | .pack _ => false

end Shape

/-- `syntax ishape = shape  -- if $lanetype(shape) = Jnn`. -/
-- core-syntax: ishape
abbrev IShape : Type := { s : Shape // s.isIShape = true }

instance : Inhabited IShape := ⟨⟨{ lane := .num .i32, dim := .d4 }, rfl⟩⟩
instance : Repr IShape := ⟨fun x n => reprPrec x.val n⟩

/-- `syntax bshape = shape  -- if $lanetype(shape) = I8`. -/
-- core-syntax: bshape
abbrev BShape : Type := { s : Shape // s.isBShape = true }

instance : Inhabited BShape := ⟨⟨{ lane := .pack .i8, dim := .d16 }, rfl⟩⟩
instance : Repr BShape := ⟨fun x n => reprPrec x.val n⟩

/-- The lane width of an `ishape`, i.e. `$lsizenn(Jnn)` of its lane type. -/
def IShape.laneSize (s : IShape) : Nat := s.val.lane.size

/-- The lane width of a `shape`, i.e. `$lsize` of its lane type. -/
def Shape.laneSize (s : Shape) : Nat := s.lane.size

/-! ## Vector operators -/

/-- `syntax zero = ZERO`. -/
-- core-syntax: zero
inductive Zero where
  | zero
  deriving DecidableEq, Repr, Inhabited

/-- `syntax half = LOW | HIGH`. -/
-- core-syntax: half
inductive Half where
  | low
  | high
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vvunop = NOT`. -/
-- core-syntax: vvunop
inductive VVUnop where
  | not
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vvbinop = AND | ANDNOT | OR | XOR`. -/
-- core-syntax: vvbinop
inductive VVBinop where
  | and
  | andnot
  | or
  | xor
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vvternop = BITSELECT`. -/
-- core-syntax: vvternop
inductive VVTernop where
  | bitselect
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vvtestop = ANY_TRUE`. -/
-- core-syntax: vvtestop
inductive VVTestop where
  | anyTrue
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vunop_(Jnn X M) = ABS | NEG | POPCNT`, the last with
`-- if $lsizenn(Jnn) = 8`. -/
-- core-syntax: vunop_(Jnn
inductive VUnopJ where
  | abs
  | neg
  | popcnt
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vunop_(Fnn X M) = ABS | NEG | SQRT | CEIL | FLOOR | TRUNC
    | NEAREST`. -/
-- core-syntax: vunop_(Fnn
inductive VUnopF where
  | abs
  | neg
  | sqrt
  | ceil
  | floor
  | trunc
  | nearest
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vunop_(shape)`: the union of the `Jnn` and `Fnn` instances. -/
-- core-syntax: vunop_(shape)
inductive VUnop where
  | int (op : VUnopJ)
  | float (op : VUnopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vunop_(sh)`, side conditions included. -/
def VUnop.wf (sh : Shape) : VUnop → Bool
  | .int op =>
      sh.lane.toJnn?.isSome &&
      (match op with
        | .popcnt => decide (sh.laneSize = 8)
        | _ => true)
  | .float _ => sh.lane.toFnn?.isSome

/-- `syntax vbinop_(Jnn X M) = ADD | SUB | ADD_SAT sx | SUB_SAT sx | MUL
    | AVGR U | Q15MULR_SAT S | RELAXED_Q15MULR S | MIN sx | MAX sx`.

The literal signedness arguments of `AVGR`, `Q15MULR_SAT` and
`RELAXED_Q15MULR`, and every width side condition, are carried by
`VBinop.wf`. -/
-- core-syntax: vbinop_(Jnn
inductive VBinopJ where
  | add
  | sub
  | addSat (sx : Sx)
  | subSat (sx : Sx)
  | mul
  | avgr (sx : Sx)
  | q15mulrSat (sx : Sx)
  | relaxedQ15mulr (sx : Sx)
  | min (sx : Sx)
  | max (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vbinop_(Fnn X M) = ADD | SUB | MUL | DIV | MIN | MAX | PMIN | PMAX
    | RELAXED_MIN | RELAXED_MAX`. -/
-- core-syntax: vbinop_(Fnn
inductive VBinopF where
  | add
  | sub
  | mul
  | div
  | min
  | max
  | pmin
  | pmax
  | relaxedMin
  | relaxedMax
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vbinop_(shape)`: the union of the `Jnn` and `Fnn` instances. -/
-- core-syntax: vbinop_(shape)
inductive VBinop where
  | int (op : VBinopJ)
  | float (op : VBinopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vbinop_(sh)`, side conditions included. -/
def VBinop.wf (sh : Shape) : VBinop → Bool
  | .int op =>
      sh.lane.toJnn?.isSome &&
      (match op with
        | .add => true
        | .sub => true
        | .addSat _ => decide (sh.laneSize ≤ 16)
        | .subSat _ => decide (sh.laneSize ≤ 16)
        | .mul => decide (sh.laneSize ≥ 16)
        | .avgr sx => decide (sh.laneSize ≤ 16) && (sx == .u)
        | .q15mulrSat sx => decide (sh.laneSize = 16) && (sx == .s)
        | .relaxedQ15mulr sx => decide (sh.laneSize = 16) && (sx == .s)
        | .min _ => decide (sh.laneSize ≤ 32)
        | .max _ => decide (sh.laneSize ≤ 32))
  | .float _ => sh.lane.toFnn?.isSome

/-- `syntax vternop_(Jnn X M) = RELAXED_LANESELECT`. -/
-- core-syntax: vternop_(Jnn
inductive VTernopJ where
  | relaxedLaneselect
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vternop_(Fnn X M) = RELAXED_MADD | RELAXED_NMADD`. -/
-- core-syntax: vternop_(Fnn
inductive VTernopF where
  | relaxedMadd
  | relaxedNmadd
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vternop_(shape)`: the union of the `Jnn` and `Fnn` instances. -/
-- core-syntax: vternop_(shape)
inductive VTernop where
  | int (op : VTernopJ)
  | float (op : VTernopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vternop_(sh)`. -/
def VTernop.wf (sh : Shape) : VTernop → Bool
  | .int _ => sh.lane.toJnn?.isSome
  | .float _ => sh.lane.toFnn?.isSome

/-- `syntax vtestop_(Jnn X M) = ALL_TRUE`. -/
-- core-syntax: vtestop_(Jnn
inductive VTestopJ where
  | allTrue
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vtestop_(shape)`: the only instance is the `Jnn` one; the source
records `vtestop_(Fnn X N)` as uninhabited and leaves it commented out. -/
-- core-syntax: vtestop_(shape)
inductive VTestop where
  | int (op : VTestopJ)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vtestop_(sh)`. -/
def VTestop.wf (sh : Shape) : VTestop → Bool
  | .int _ => sh.lane.toJnn?.isSome

/-- `syntax vrelop_(Jnn X M) = EQ | NE | LT sx | GT sx | LE sx | GE sx`, the
ordering cases with `-- if $lsizenn(Jnn) =/= 64 \/ sx = S`. -/
-- core-syntax: vrelop_(Jnn
inductive VRelopJ where
  | eq
  | ne
  | lt (sx : Sx)
  | gt (sx : Sx)
  | le (sx : Sx)
  | ge (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vrelop_(Fnn X M) = EQ | NE | LT | GT | LE | GE`. -/
-- core-syntax: vrelop_(Fnn
inductive VRelopF where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vrelop_(shape)`: the union of the `Jnn` and `Fnn` instances. -/
-- core-syntax: vrelop_(shape)
inductive VRelop where
  | int (op : VRelopJ)
  | float (op : VRelopF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vrelop_(sh)`, side conditions included. -/
def VRelop.wf (sh : Shape) : VRelop → Bool
  | .int op =>
      sh.lane.toJnn?.isSome &&
      (match op with
        | .eq => true
        | .ne => true
        | .lt sx => decide (sh.laneSize ≠ 64) || (sx == .s)
        | .gt sx => decide (sh.laneSize ≠ 64) || (sx == .s)
        | .le sx => decide (sh.laneSize ≠ 64) || (sx == .s)
        | .ge sx => decide (sh.laneSize ≠ 64) || (sx == .s))
  | .float _ => sh.lane.toFnn?.isSome

/-- `syntax vshiftop_(Jnn X M) = SHL | SHR sx`. -/
-- core-syntax: vshiftop_(Jnn
inductive VShiftopJ where
  | shl
  | shr (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vshiftop_(ishape)`: the `Jnn` instance is the only one, and every
`ishape` has a `Jnn` lane type by definition, so the family IS that instance. -/
-- core-syntax: vshiftop_(ishape)
abbrev VShiftop : Type := VShiftopJ

/-- `syntax vswizzlop_(I8 X M) = SWIZZLE | RELAXED_SWIZZLE`. -/
-- core-syntax: vswizzlop_(I8
inductive VSwizzlopI8 where
  | swizzle
  | relaxedSwizzle
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vswizzlop_(bshape)`: the `I8` instance is the only one, and every
`bshape` has lane type `I8` by definition, so the family IS that instance. -/
-- core-syntax: vswizzlop_(bshape)
abbrev VSwizzlop : Type := VSwizzlopI8

/-- `syntax vextunop__(Jnn_1 X M_1, Jnn_2 X M_2) = EXTADD_PAIRWISE sx`
with `-- if 16 <= $(2 * $lsizenn1(Jnn_1)) = $lsizenn2(Jnn_2) <= 32`. -/
-- core-syntax: vextunop__(Jnn_1
inductive VExtUnopJ where
  | extaddPairwise (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vextunop__(ishape_1, ishape_2)`: the `Jnn` instance is the only
one, so the family IS that instance. -/
-- core-syntax: vextunop__(ishape_1,
abbrev VExtUnop : Type := VExtUnopJ

/-- `op` is a case of `vextunop__(sh₁, sh₂)`, side conditions included. -/
def VExtUnop.wf (sh₁ sh₂ : IShape) : VExtUnop → Bool
  | .extaddPairwise _ =>
      decide (16 ≤ 2 * sh₁.laneSize) &&
      decide (2 * sh₁.laneSize = sh₂.laneSize) &&
      decide (sh₂.laneSize ≤ 32)

/-- `syntax vextbinop__(Jnn_1 X M_1, Jnn_2 X M_2) = EXTMUL half sx | DOT S
    | RELAXED_DOT S`, with the width side conditions in `VExtBinop.wf`. -/
-- core-syntax: vextbinop__(Jnn_1
inductive VExtBinopJ where
  | extmul (h : Half) (sx : Sx)
  | dot (sx : Sx)
  | relaxedDot (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vextbinop__(ishape_1, ishape_2)`: the `Jnn` instance is the only
one, so the family IS that instance. -/
-- core-syntax: vextbinop__(ishape_1,
abbrev VExtBinop : Type := VExtBinopJ

/-- `op` is a case of `vextbinop__(sh₁, sh₂)`, side conditions included. -/
def VExtBinop.wf (sh₁ sh₂ : IShape) : VExtBinop → Bool
  | .extmul _ _ =>
      decide (2 * sh₁.laneSize = sh₂.laneSize) && decide (sh₂.laneSize ≥ 16)
  | .dot sx =>
      decide (2 * sh₁.laneSize = sh₂.laneSize) && decide (sh₂.laneSize = 32) &&
      (sx == .s)
  | .relaxedDot sx =>
      decide (2 * sh₁.laneSize = sh₂.laneSize) && decide (sh₂.laneSize = 16) &&
      (sx == .s)

/-- `syntax vextternop__(Jnn_1 X M_1, Jnn_2 X M_2) = RELAXED_DOT_ADD S`
with `-- if $(4 * $lsizenn1(Jnn_1)) = $lsizenn2(Jnn_2) = 32`. -/
-- core-syntax: vextternop__(Jnn_1
inductive VExtTernopJ where
  | relaxedDotAdd (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vextternop__(ishape_1, ishape_2)`: the `Jnn` instance is the only
one, so the family IS that instance. -/
-- core-syntax: vextternop__(ishape_1,
abbrev VExtTernop : Type := VExtTernopJ

/-- `op` is a case of `vextternop__(sh₁, sh₂)`, side conditions included. -/
def VExtTernop.wf (sh₁ sh₂ : IShape) : VExtTernop → Bool
  | .relaxedDotAdd sx =>
      decide (4 * sh₁.laneSize = sh₂.laneSize) && decide (sh₂.laneSize = 32) &&
      (sx == .s)

/-- `syntax vcvtop__(Jnn_1 X M_1, Jnn_2 X M_2) = EXTEND half sx`
with `-- if $lsizenn2(Jnn_2) = $(2 * $lsizenn1(Jnn_1))`. -/
-- core-syntax: vcvtop__(Jnn_1
inductive VCvtopJJ where
  | extend (h : Half) (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vcvtop__(Jnn_1 X M_1, Fnn_2 X M_2) = CONVERT half? sx`. -/
inductive VCvtopJF where
  | convert (h : Option Half) (sx : Sx)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vcvtop__(Fnn_1 X M_1, Jnn_2 X M_2) = TRUNC_SAT sx zero?
    | RELAXED_TRUNC sx zero?`. -/
-- core-syntax: vcvtop__(Fnn_1
inductive VCvtopFJ where
  | truncSat (sx : Sx) (z : Option Zero)
  | relaxedTrunc (sx : Sx) (z : Option Zero)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vcvtop__(Fnn_1 X M_1, Fnn_2 X M_2) = DEMOTE zero | PROMOTE LOW`. -/
inductive VCvtopFF where
  | demote (z : Zero)
  | promote (h : Half)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vcvtop__(shape_1, shape_2)`: the union of the four instances.

As with `cvtop__`, the index order is (operand shape, result shape): the source
writes `VCVTOP shape_1 shape_2 vcvtop__(shape_2, shape_1)` with `shape_1` the
result. -/
-- core-syntax: vcvtop__(shape_1,
inductive VCvtop where
  | jj (op : VCvtopJJ)
  | jf (op : VCvtopJF)
  | fj (op : VCvtopFJ)
  | ff (op : VCvtopFF)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vcvtop__(src, tgt)`, side conditions included. -/
def VCvtop.wf (src tgt : Shape) : VCvtop → Bool
  | .jj op =>
      src.lane.toJnn?.isSome && tgt.lane.toJnn?.isSome &&
      (match op with
        | .extend _ _ => decide (tgt.laneSize = 2 * src.laneSize))
  | .jf op =>
      src.lane.toJnn?.isSome && tgt.lane.toFnn?.isSome &&
      (match op with
        | .convert h _ =>
            (decide (tgt.laneSize = 32) && decide (src.laneSize = 32) &&
              (h == none)) ||
            (decide (tgt.laneSize = 2 * src.laneSize) && (h == some .low)))
  | .fj op =>
      src.lane.toFnn?.isSome && tgt.lane.toJnn?.isSome &&
      (match op with
        | .truncSat _ z =>
            (decide (src.laneSize = 32) && decide (tgt.laneSize = 32) &&
              (z == none)) ||
            (decide (src.laneSize = 2 * tgt.laneSize) && (z == some .zero))
        | .relaxedTrunc _ z =>
            (decide (src.laneSize = 32) && decide (tgt.laneSize = 32) &&
              (z == none)) ||
            (decide (src.laneSize = 2 * tgt.laneSize) && (z == some .zero)))
  | .ff op =>
      src.lane.toFnn?.isSome && tgt.lane.toFnn?.isSome &&
      (match op with
        | .demote _ => decide (src.laneSize = 2 * tgt.laneSize)
        | .promote h => decide (2 * src.laneSize = tgt.laneSize) && (h == .low))

/-! ## Memory operators -/

/-- `syntax memarg = {ALIGN u32, OFFSET u32}`. -/
-- core-syntax: memarg
structure MemArg where
  align : U32
  offset : U32
  deriving DecidableEq, Repr, Inhabited

/-- `def $memarg0 = {ALIGN 0, OFFSET 0}`. -/
def MemArg.zero : MemArg := { align := default, offset := default }

/-- `syntax loadop_(Inn) = sz _ sx  -- if sz < $sizenn(Inn)`. -/
-- core-syntax: loadop_(Inn)
structure LoadOpI where
  sz : Sz
  sx : Sx
  deriving DecidableEq, Repr, Inhabited

/-- `syntax loadop_(numtype)`: the source declares an instance at `Inn` only,
so `LoadOp.wf` is false at every `Fnn`. -/
-- core-syntax: loadop_(numtype)
abbrev LoadOp : Type := LoadOpI

/-- `op` is a case of `loadop_(nt)`, side condition included. -/
def LoadOp.wf (nt : NumType) (op : LoadOp) : Bool :=
  match nt.toInn? with
  | some n => decide (op.sz.toNat < n.size)
  | none => false

/-- `syntax storeop_(Inn) = sz  -- if sz < $sizenn(Inn)`. -/
-- core-syntax: storeop_(Inn)
structure StoreOpI where
  sz : Sz
  deriving DecidableEq, Repr, Inhabited

/-- `syntax storeop_(numtype)`: the source declares an instance at `Inn` only,
so `StoreOp.wf` is false at every `Fnn`. -/
-- core-syntax: storeop_(numtype)
abbrev StoreOp : Type := StoreOpI

/-- `op` is a case of `storeop_(nt)`, side condition included. -/
def StoreOp.wf (nt : NumType) (op : StoreOp) : Bool :=
  match nt.toInn? with
  | some n => decide (op.sz.toNat < n.size)
  | none => false

/-- `syntax vloadop_(vectype) = SHAPE sz X M _ sx | SPLAT sz | ZERO sz`, with
`-- if $(sz * M = $vsize(vectype)/2)` on `SHAPE` and `-- if sz >= 32` on
`ZERO`. -/
-- core-syntax: vloadop_(vectype)
inductive VLoadOp where
  | shape (sz : Sz) (m : Nat) (sx : Sx)
  | splat (sz : Sz)
  | zero (sz : Sz)
  deriving DecidableEq, Repr, Inhabited

/-- `op` is a case of `vloadop_(vt)`, side conditions included. -/
def VLoadOp.wf (vt : VecType) : VLoadOp → Bool
  | .shape sz m _ => decide (sz.toNat * m = vt.size / 2)
  | .splat _ => true
  | .zero sz => decide (sz.toNat ≥ 32)

/-! ## Block types -/

/-- `syntax blocktype = _RESULT valtype? | _IDX typeidx`. -/
-- core-syntax: blocktype
inductive BlockType where
  | result (t : Option ValType)
  | idx (x : TypeIdx)
  deriving DecidableEq, Repr, Inhabited

/-- The `/syn` fragment of `blocktype`: the `valtype?` of a `_RESULT` must be a
`valtype/syn`, i.e. never `BOT` and never a `/sem` `typeuse`.  A `_IDX` carries
no type at all. -/
def BlockType.isSyn : BlockType → Bool
  | .result none => true
  | .result (some t) => t.isSyn
  | .idx _ => true

end WasmGemmGnaf.Wasm.Core
