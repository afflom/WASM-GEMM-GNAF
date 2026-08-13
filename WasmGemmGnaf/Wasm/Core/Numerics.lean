/-
  Wasm/Core/Numerics.lean --- the scalar and vector operator semantics the
  Core 3.0 step relation calls out to.

  NORMATIVE SOURCE.

      vendor/wasm-spec/specification/wasm-3.0/3.1-numerics.scalar.spectec
      vendor/wasm-spec/specification/wasm-3.0/3.2-numerics.vector.spectec

  together with the four auxiliaries those two files call into and do not
  define themselves: `$fzero` (`1.1-syntax.values.spectec`), `$prod`
  (`0.2-aux.num.spectec`), `$concat_` / `$setproduct_` (`0.3-aux.seq.spectec`)
  and `$relaxed2` (`3.0-numerics.relaxed.spectec`).  Those four are transcribed
  here too, without coverage markers: they are not numerics obligations, and a
  marker naming one would be a fabricated claim.

  WHAT IS DEFINED HERE, AND WHAT REMAINS A PARAMETER.

  Every auxiliary function `3.1` and `3.2` define BY EQUATION is defined here:
  all 37 of `3.1` and all 47 of `3.2`, including the seventeen vector operator
  dispatchers `$vvunop_` ... `$vcvtop__` and the lanewise combinators
  `$ivunop_` ... `$ivshufflop_` they are built from.  They are `def`s, so the
  step relation of `Core/Execution.lean` is no longer quantified over an
  arbitrary interpretation of the SIMD operators: it is pinned to the pinned
  source's own equations.

  What is NOT defined here is what the pinned source does not define.  `3.1`
  and `3.2` between them declare 74 functions with `hint(builtin)` -- a
  signature and no equations, the prose specification being the authority.  A
  transcription of these two files cannot define what these two files leave
  abstract, so those are the fields of `Numerics`, and they are the ONLY fields
  of `Numerics`.  The record carries 64 of them:

    * the 61 `hint(builtin)` declarations of `3.1`/`3.2` that this development
      calls -- 18 integer (`$iclz_`, `$ictz_`, `$ipopcnt_`, `$inot_`, `$irev_`,
      `$iand_`, `$iandnot_`, `$ior_`, `$ixor_`, `$ishl_`, `$ishr_`, `$irotl_`,
      `$irotr_`, `$ibitselect_`, `$iavgr_`, `$iq15mulr_sat_`,
      `$irelaxed_q15mulr_`, `$irelaxed_laneselect_`), 26 floating-point
      (`$fabs_` ... `$fge_`, `$frelaxed_madd_`, `$frelaxed_nmadd_`), 10
      conversions (`$wrap__`, `$extend__`, `$trunc__`, `$trunc_sat__`,
      `$relaxed_trunc__`, `$demote__`, `$promote__`, `$convert__`, `$narrow__`,
      `$reinterpret__`), 5 representation (`$ibytes_`, `$nbytes_`, `$vbytes_`,
      `$zbytes_`, `$inv_ibits_`) and the 2 lane primitives of `3.2`
      (`$lanes_`, `$inv_lanes_`);
    * `$ND` (`1.0-syntax.profiles.spectec`) and the relaxed-behaviour selectors
      `$R_swizzle` and `$R_idot` (`3.0-numerics.relaxed.spectec`), all three
      also `hint(builtin)`, which `3.2`'s relaxed equations read.

  The remaining 13 `hint(builtin)` declarations of `3.1`/`3.2` -- `$ibits_`,
  `$fbits_`, `$fbytes_`, `$cbytes_`, the seven remaining `$inv_*` inverses,
  `$truncz` and `$ceilz` -- have no call site in this development and so are
  not carried.  `$truncz` is the one place where a `hint(builtin)` function is
  nevertheless given a meaning below: `$idiv_`/`$irem_` use truncation toward
  zero (`Nat` division, `Int.tdiv`/`Int.tmod`), which is what the source's own
  commented-out equation `$truncz(+-q) = +-n -- if n <- nat /\ (q-1) < n <= q`
  says and what the name means.  That is recorded here rather than hidden.

  These are parameters, not axioms: nothing in this development asserts
  anything about them, no proof depends on a property of them, and
  `xtask axioms` sees no new constant.  A `Numerics` is data a caller supplies.

  TOTALITY.  Where the source gives no equation for an argument combination --
  `$unop_(Inn, ABS, _)`, say, which is ill-formed because `ABS` is an
  `unop_(Fnn)`; or `$vrelop_(Fnn X M, LT sx, ...)`, whose operator belongs to
  the `Jnn` instance -- the transcription returns the empty sequence (for the
  sequence-valued operators) or `none` (for the single-valued ones).  That is
  the source's own reading of a missing equation, and it is why several
  operators whose SpecTec result type is a bare `vec_(V128)` or `u32` are
  `Option`-valued here.  No junk value is ever invented for a case the source
  leaves undefined, and none is invented for a case it defines.

  ONE DELIBERATE WIDENING, STATED SO IT IS NOT MISTAKEN FOR AN OVERSIGHT.
  `$vcvtop__` is declared `: vec_(V128)`, yet each of its three equations binds
  its result with `v <- $inv_lanes_(...)*`, i.e. from a SET -- the float
  conversions `$demote__`/`$promote__` are themselves sequence-valued.  It is
  transcribed as returning that set, so that no result the equations license is
  dropped and none is invented; `Step_pure/vcvtop` reads it with `∈`.
-/
import WasmGemmGnaf.Wasm.Core.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Carriers -/

/-- `vec_(V128)`, the only vector literal carrier in Core 3.0. -/
abbrev V128Lit : Type := VecLit Vnn.v128

/-- `def $zsize(storagetype) : nat`: `$size` on a `numtype`, `$vsize` on a
`vectype`, `$psize` on a `packtype`.  The source marks it `hint(partial)`; it is
undefined on a `reftype` and on `BOT`. -/
def zsize : StorageType → Option Nat
  | .val (.num nt) => some nt.size
  | .val (.vec vt) => some vt.size
  | .val (.ref _) => none
  | .val .bot => none
  | .pack pt => some pt.size

/-- `def $cunpack(storagetype) : consttype`, `hint(partial)`:
`$cunpack(consttype) = consttype`, `$cunpack(packtype) = I32`. -/
def cunpack : StorageType → Option ConstType
  | .val (.num nt) => some (.num nt)
  | .val (.vec vt) => some (.vec vt)
  | .val (.ref _) => none
  | .val .bot => none
  | .pack _ => some (.num .i32)

/-- `lit_($cunpack(storagetype))`, the argument carrier of `$cpacknum_` and the
result carrier of `$cunpacknum_`.  `$cunpack` is `hint(partial)`; where it is
undefined the carrier is `Empty`, which is the honest reading of "no such
literal". -/
def CUnpackLit : StorageType → Type
  | .val (.num nt) => Num_ nt
  | .val (.vec vt) => LitVec vt
  | .val (.ref _) => Empty
  | .val .bot => Empty
  | .pack _ => Num_ .i32

/-- `def $unpack(storagetype) : valtype` restricted to the storage types that
have a `lit_` instance; `Core/Types.lean` carries the general `$unpack`. -/
def constToStorage : ConstType → StorageType
  | .num nt => .val (.num nt)
  | .vec vt => .val (.vec vt)

/-- `def $const(consttype, lit_(consttype)) : instr`: the constant instruction
that carries a literal of the given constant type. -/
def constInstr : (ct : ConstType) → Lit_ (constToStorage ct) → Instr
  | .num nt, c => .const nt c
  | .vec vt, c => .vconst vt c

/-! ## Auxiliaries the numerics sources call into

These four belong to `0.2-aux.num.spectec`, `0.3-aux.seq.spectec`,
`1.1-syntax.values.spectec` and `3.0-numerics.relaxed.spectec`, not to the
numerics files, so they carry no coverage marker.  `3.1`/`3.2` cannot be
transcribed without them. -/

/-- `def $prod(eps) = 1`, `def $prod(n n'*) = $(n * $prod(n'*))`
(`0.2-aux.num.spectec`). -/
def prodNat : List Nat → Nat
  | [] => 1
  | n :: ns => n * prodNat ns

/-- `def $setproduct2_(syntax X, w_1, eps) = eps`,
`def $setproduct2_(syntax X, w_1, (w'*) (w*)*) = (w_1 w'*) ++ $setproduct2_(X, w_1, (w*)*)`
(`0.3-aux.seq.spectec`). -/
def setproduct2 {X : Type} (w : X) : List (List X) → List (List X)
  | [] => []
  | ws :: wss => (w :: ws) :: setproduct2 w wss

/-- `def $setproduct1_(syntax X, eps, (w*)*) = eps`,
`def $setproduct1_(syntax X, w_1 w'*, (w*)*) =
   $setproduct2_(X, w_1, (w*)*) ++ $setproduct1_(X, w'*, (w*)*)`. -/
def setproduct1 {X : Type} : List X → List (List X) → List (List X)
  | [], _ => []
  | w :: ws, wss => setproduct2 w wss ++ setproduct1 ws wss

/-- `def $setproduct_(syntax X, eps) = (eps)`,
`def $setproduct_(syntax X, (w_1*) (w*)*) = $setproduct1_(X, w_1*, $setproduct_(X, (w*)*))`.

Read at the uses in `3.2`: a sequence of per-lane RESULT SETS becomes the set of
possible result sequences. -/
def setproduct {X : Type} : List (List X) → List (List X)
  | [] => [[]]
  | ws :: wss => setproduct1 ws (setproduct wss)

/-- The inverse of `$concat_(X, (w_1 w_2)*)` at two-element blocks: the unique
sequence of pairs whose concatenation is `l`, where there is one.  `3.2` writes
`-- if $concat_(N, (j_1 j_2)*) = i*`, which is exactly this. -/
def pairs {X : Type} : List X → Option (List (X × X))
  | [] => some []
  | [_] => none
  | a :: b :: rest => (pairs rest).map (fun ps => (a, b) :: ps)

/-- `def $relaxed2(i, syntax X, X_1, X_2) = (X_1 X_2)[i]  -- if $ND`,
`def $relaxed2(i, syntax X, X_1, X_2) = (X_1 X_2)[0]  -- otherwise`
(`3.0-numerics.relaxed.spectec`).

`syntax relaxed2 = 0 | 1` is carried as a `Bool`, `false` for `0` and `true`
for `1`; `nd` is `$ND`. -/
def relaxed2 {X : Type} (nd : Bool) (i : Bool) (x₁ x₂ : X) : X :=
  if nd then (if i then x₂ else x₁) else x₁

/-- `def $fzero(N) = POS (SUBNORM 0)` (`1.1-syntax.values.spectec`). -/
def fzero (w : Nat) : FN w := .pos (.subnorm 0)

/-! ## Small carrier utilities

Nothing here is a source obligation; each is one of the coercions SpecTec leaves
implicit, made explicit so that no width or bound is assumed silently. -/

/-- `0 : iN(N)`. -/
def inZero (w : Nat) : IN w := ⟨0, two_pow_pos w⟩

/-- A natural as an `iN(N)`, where it fits.  `none` where it does not: SpecTec's
implicit coercion is defined only on the carrier's own range, and a wrap would
invent a value. -/
def inOfNat? (w : Nat) (n : Nat) : Option (IN w) :=
  if h : n < 2 ^ w then some ⟨n, h⟩ else none

/-- A `u32` that is `0` or `1` as a `bit`; `none` otherwise.  `3.2`'s
`$ivbitmaskop_` writes a `u32`-valued comparison into a `bit*`. -/
def bitOfU32? (u : U32) : Option Bit :=
  if u.val = 0 then some .b0 else if u.val = 1 then some .b1 else none

/-- `x*[i : n]`, SpecTec's slice: `n` elements from index `i`, and undefined
where the sequence is too short. -/
def slice? {X : Type} (l : List X) (i n : Nat) : Option (List X) :=
  if i + n ≤ l.length then some ((l.drop i).take n) else none

/-- The lockstep iteration `$f_(..., c_1, c_2)*` of two equally long sequences;
`none` where they are not equally long, which is where the source's premise is
unsatisfiable. -/
def zipWith? {A B C : Type} (f : A → B → C) (as : List A) (bs : List B) :
    Option (List C) :=
  if as.length = bs.length then some (List.zipWith f as bs) else none

/-- The lockstep iteration of three equally long sequences. -/
def zipWith3? {A B C D : Type} (f : A → B → C → D) (as : List A) (bs : List B)
    (cs : List C) : Option (List D) :=
  match zipWith? (fun a b => (a, b)) as bs with
  | none => none
  | some abs => zipWith? (fun p c => f p.1 p.2 c) abs cs

/-! ## Lane carriers

`syntax lane_(Jnn) = iN($lsize(Jnn))` is the source's own `;; HACK` instance: at
a lane type that is a `Jnn` the lane carrier IS the integer carrier of that
width, and at an `Fnn` lane it is the float carrier.  These four functions are
that fact, made checkable; each is `none` exactly where the source declares no
such instance. -/

/-- The `iN($lsize)` reading of a lane sequence, where the lane type is a
`Jnn`. -/
def lanesJ? : (lt : LaneType) → List (Lane_ lt) → Option (List (IN lt.size))
  | .num .i32, cs => some cs
  | .num .i64, cs => some cs
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, cs => some cs

/-- A sequence of `iN($lsize)` as a lane sequence, where the lane type is a
`Jnn`. -/
def ofLanesJ? : (lt : LaneType) → List (IN lt.size) → Option (List (Lane_ lt))
  | .num .i32, cs => some cs
  | .num .i64, cs => some cs
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, cs => some cs

/-- The `fN($lsize)` reading of a lane sequence, where the lane type is an
`Fnn`. -/
def lanesF? : (lt : LaneType) → List (Lane_ lt) → Option (List (FN lt.size))
  | .num .f32, cs => some cs
  | .num .f64, cs => some cs
  | .num .i32, _ => none
  | .num .i64, _ => none
  | .pack _, _ => none

/-- A sequence of `fN($lsize)` as a lane sequence, where the lane type is an
`Fnn`. -/
def ofLanesF? : (lt : LaneType) → List (FN lt.size) → Option (List (Lane_ lt))
  | .num .f32, cs => some cs
  | .num .f64, cs => some cs
  | .num .i32, _ => none
  | .num .i64, _ => none
  | .pack _, _ => none

/-- The `iN($lsize)` reading of a single lane, where the lane type is a `Jnn`. -/
def laneJ? : (lt : LaneType) → Lane_ lt → Option (IN lt.size)
  | .num .i32, c => some c
  | .num .i64, c => some c
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, c => some c

/-- A single `iN($lsize)` as a lane, where the lane type is a `Jnn`. -/
def ofLaneJ? : (lt : LaneType) → IN lt.size → Option (Lane_ lt)
  | .num .i32, c => some c
  | .num .i64, c => some c
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, c => some c

/-- The `fN($lsize)` reading of a single lane, where the lane type is an
`Fnn`. -/
def laneF? : (lt : LaneType) → Lane_ lt → Option (FN lt.size)
  | .num .f32, c => some c
  | .num .f64, c => some c
  | .num .i32, _ => none
  | .num .i64, _ => none
  | .pack _, _ => none

/-- A single `fN($lsize)` as a lane, where the lane type is an `Fnn`. -/
def ofLaneF? : (lt : LaneType) → FN lt.size → Option (Lane_ lt)
  | .num .f32, c => some c
  | .num .f64, c => some c
  | .num .i32, _ => none
  | .num .i64, _ => none
  | .pack _, _ => none

/-- `-- if $lanetype(shape) = Inn`: `3.2`'s `$lcvtop__` restricts the target of
`TRUNC_SAT` and `RELAXED_TRUNC` to an `Inn` lane, not merely a `Jnn` one. -/
def laneIsInn : LaneType → Bool
  | .num .i32 => true
  | .num .i64 => true
  | _ => false

/-- The `Inn X M` shape with the same lane width and dimension as `Fnn X M`,
i.e. the unique shape satisfying `3.2`'s `-- if $isize(Inn) = $fsize(Fnn)` in
`$fvrelop_`.  `none` at a lane type that is not an `Fnn`. -/
def intShapeOf (sh : Shape) : Option Shape :=
  match sh.lane with
  | .num .f32 => some { sh with lane := .num .i32 }
  | .num .f64 => some { sh with lane := .num .i64 }
  | _ => none

/-- The unique `Jnn` lane type of the given width, where there is one.  `3.2`'s
`$vextternop__` names its intermediate shape only by its lane width, through
`-- if $jsizenn(Jnn) = $(2*$lsizenn1(Jnn_1))`. -/
def jnnLaneOfSize : Nat → Option LaneType
  | 8 => some (.pack .i8)
  | 16 => some (.pack .i16)
  | 32 => some (.num .i32)
  | 64 => some (.num .i64)
  | _ => none

/-- `syntax dim = 1 | 2 | 4 | 8 | 16` from its value. -/
def dimOfNat : Nat → Option Dim
  | 1 => some .d1
  | 2 => some .d2
  | 4 => some .d4
  | 8 => some .d8
  | 16 => some .d16
  | _ => none

/-! ## The primitives the pinned sources leave to the prose

Every field below transcribes one `hint(builtin)` declaration: the signature is
the source's, the meaning is the caller's.  See the file header for the
inventory and for the thirteen `hint(builtin)` declarations that have no call
site here and so are absent. -/

/-- The numeric primitives that the pinned SpecTec sources declare without
equations.  These are the only parameters of the Core 3.0 numeric semantics;
everything `3.1` and `3.2` state by equation is a `def` below. -/
structure Numerics where
  /-- `def $ibytes_(N, iN(N)) : byte*`. -/
  ibytes_ : (N : Nat) → IN N → List Byte
  /-- `def $nbytes_(numtype, num_(numtype)) : byte*`. -/
  nbytes_ : (nt : NumType) → Num_ nt → List Byte
  /-- `def $vbytes_(vectype, vec_(vectype)) : byte*`. -/
  vbytes_ : (vt : VecType) → VecLit vt.toVnn → List Byte
  /-- `def $zbytes_(storagetype, lit_(storagetype)) : byte*`. -/
  zbytes_ : (zt : StorageType) → Lit_ zt → List Byte
  /-- `def $inv_ibits_(N, bit*) : iN(N)`. -/
  inv_ibits_ : (N : Nat) → List Bit → IN N
  /-- `def $iclz_(N, iN(N)) : iN(N)`. -/
  iclz_ : (N : Nat) → IN N → IN N
  /-- `def $ictz_(N, iN(N)) : iN(N)`. -/
  ictz_ : (N : Nat) → IN N → IN N
  /-- `def $ipopcnt_(N, iN(N)) : iN(N)`. -/
  ipopcnt_ : (N : Nat) → IN N → IN N
  /-- `def $inot_(N, iN(N)) : iN(N)`. -/
  inot_ : (N : Nat) → IN N → IN N
  /-- `def $irev_(N, iN(N)) : iN(N)`. -/
  irev_ : (N : Nat) → IN N → IN N
  /-- `def $iand_(N, iN(N), iN(N)) : iN(N)`. -/
  iand_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $iandnot_(N, iN(N), iN(N)) : iN(N)`. -/
  iandnot_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $ior_(N, iN(N), iN(N)) : iN(N)`. -/
  ior_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $ixor_(N, iN(N), iN(N)) : iN(N)`. -/
  ixor_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $ishl_(N, iN(N), u32) : iN(N)`. -/
  ishl_ : (N : Nat) → IN N → U32 → IN N
  /-- `def $ishr_(N, sx, iN(N), u32) : iN(N)`. -/
  ishr_ : (N : Nat) → Sx → IN N → U32 → IN N
  /-- `def $irotl_(N, iN(N), iN(N)) : iN(N)`. -/
  irotl_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $irotr_(N, iN(N), iN(N)) : iN(N)`. -/
  irotr_ : (N : Nat) → IN N → IN N → IN N
  /-- `def $ibitselect_(N, iN(N), iN(N), iN(N)) : iN(N)`. -/
  ibitselect_ : (N : Nat) → IN N → IN N → IN N → IN N
  /-- `def $iavgr_(N, sx, iN(N), iN(N)) : iN(N)`. -/
  iavgr_ : (N : Nat) → Sx → IN N → IN N → IN N
  /-- `def $iq15mulr_sat_(N, sx, iN(N), iN(N)) : iN(N)`. -/
  iq15mulr_sat_ : (N : Nat) → Sx → IN N → IN N → IN N
  /-- `def $irelaxed_q15mulr_(N, sx, iN(N), iN(N)) : iN(N)*`. -/
  irelaxed_q15mulr_ : (N : Nat) → Sx → IN N → IN N → List (IN N)
  /-- `def $irelaxed_laneselect_(N, iN(N), iN(N), iN(N)) : iN(N)*`. -/
  irelaxed_laneselect_ : (N : Nat) → IN N → IN N → IN N → List (IN N)
  /-- `def $fabs_(N, fN(N)) : fN(N)*`. -/
  fabs_ : (N : Nat) → FN N → List (FN N)
  /-- `def $fneg_(N, fN(N)) : fN(N)*`. -/
  fneg_ : (N : Nat) → FN N → List (FN N)
  /-- `def $fsqrt_(N, fN(N)) : fN(N)*`. -/
  fsqrt_ : (N : Nat) → FN N → List (FN N)
  /-- `def $fceil_(N, fN(N)) : fN(N)*`. -/
  fceil_ : (N : Nat) → FN N → List (FN N)
  /-- `def $ffloor_(N, fN(N)) : fN(N)*`. -/
  ffloor_ : (N : Nat) → FN N → List (FN N)
  /-- `def $ftrunc_(N, fN(N)) : fN(N)*`. -/
  ftrunc_ : (N : Nat) → FN N → List (FN N)
  /-- `def $fnearest_(N, fN(N)) : fN(N)*`. -/
  fnearest_ : (N : Nat) → FN N → List (FN N)
  /-- `def $fadd_(N, fN(N), fN(N)) : fN(N)*`. -/
  fadd_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fsub_(N, fN(N), fN(N)) : fN(N)*`. -/
  fsub_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fmul_(N, fN(N), fN(N)) : fN(N)*`. -/
  fmul_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fdiv_(N, fN(N), fN(N)) : fN(N)*`. -/
  fdiv_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fmin_(N, fN(N), fN(N)) : fN(N)*`. -/
  fmin_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fmax_(N, fN(N), fN(N)) : fN(N)*`. -/
  fmax_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fpmin_(N, fN(N), fN(N)) : fN(N)*`. -/
  fpmin_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fpmax_(N, fN(N), fN(N)) : fN(N)*`. -/
  fpmax_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $frelaxed_min_(N, fN(N), fN(N)) : fN(N)*`. -/
  frelaxed_min_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $frelaxed_max_(N, fN(N), fN(N)) : fN(N)*`. -/
  frelaxed_max_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $fcopysign_(N, fN(N), fN(N)) : fN(N)*`. -/
  fcopysign_ : (N : Nat) → FN N → FN N → List (FN N)
  /-- `def $feq_(N, fN(N), fN(N)) : u32`. -/
  feq_ : (N : Nat) → FN N → FN N → U32
  /-- `def $fne_(N, fN(N), fN(N)) : u32`. -/
  fne_ : (N : Nat) → FN N → FN N → U32
  /-- `def $flt_(N, fN(N), fN(N)) : u32`. -/
  flt_ : (N : Nat) → FN N → FN N → U32
  /-- `def $fgt_(N, fN(N), fN(N)) : u32`. -/
  fgt_ : (N : Nat) → FN N → FN N → U32
  /-- `def $fle_(N, fN(N), fN(N)) : u32`. -/
  fle_ : (N : Nat) → FN N → FN N → U32
  /-- `def $fge_(N, fN(N), fN(N)) : u32`. -/
  fge_ : (N : Nat) → FN N → FN N → U32
  /-- `def $frelaxed_madd_(N, fN(N), fN(N), fN(N)) : fN(N)*`. -/
  frelaxed_madd_ : (N : Nat) → FN N → FN N → FN N → List (FN N)
  /-- `def $frelaxed_nmadd_(N, fN(N), fN(N), fN(N)) : fN(N)*`. -/
  frelaxed_nmadd_ : (N : Nat) → FN N → FN N → FN N → List (FN N)
  /-- `def $wrap__(M, N, iN(M)) : iN(N)`. -/
  wrap__ : (M N : Nat) → IN M → IN N
  /-- `def $extend__(M, N, sx, iN(M)) : iN(N)`. -/
  extend__ : (M N : Nat) → Sx → IN M → IN N
  /-- `def $trunc__(M, N, sx, fN(M)) : iN(N)?`. -/
  trunc__ : (M N : Nat) → Sx → FN M → Option (IN N)
  /-- `def $trunc_sat__(M, N, sx, fN(M)) : iN(N)?`. -/
  trunc_sat__ : (M N : Nat) → Sx → FN M → Option (IN N)
  /-- `def $relaxed_trunc__(M, N, sx, fN(M)) : iN(N)?`. -/
  relaxed_trunc__ : (M N : Nat) → Sx → FN M → Option (IN N)
  /-- `def $convert__(M, N, sx, iN(M)) : fN(N)`. -/
  convert__ : (M N : Nat) → Sx → IN M → FN N
  /-- `def $promote__(M, N, fN(M)) : fN(N)*`. -/
  promote__ : (M N : Nat) → FN M → List (FN N)
  /-- `def $demote__(M, N, fN(M)) : fN(N)*`. -/
  demote__ : (M N : Nat) → FN M → List (FN N)
  /-- `def $narrow__(M, N, sx, iN(M)) : iN(N)`. -/
  narrow__ : (M N : Nat) → Sx → IN M → IN N
  /-- `def $reinterpret__(numtype_1, numtype_2, num_(numtype_1)) :
      num_(numtype_2)`. -/
  reinterpret__ : (nt₁ nt₂ : NumType) → Num_ nt₁ → Num_ nt₂
  /-- `def $lanes_(shape, vec_(V128)) : lane_($lanetype(shape))*`. -/
  lanes_ : (sh : Shape) → V128Lit → List (Lane_ sh.lane)
  /-- `def $inv_lanes_(shape, lane_($lanetype(shape))*) : vec_(V128)`. -/
  inv_lanes_ : (sh : Shape) → List (Lane_ sh.lane) → V128Lit
  /-- `def $ND : bool` (`1.0-syntax.profiles.spectec`): whether the profile
  admits non-deterministic relaxed behaviour. -/
  nd : Bool
  /-- `def $R_swizzle : relaxed2` (`3.0-numerics.relaxed.spectec`), as a `Bool`;
  see `relaxed2`. -/
  r_swizzle : Bool
  /-- `def $R_idot : relaxed2` (`3.0-numerics.relaxed.spectec`), as a `Bool`. -/
  r_idot : Bool

namespace Numerics

variable (N : Numerics)

/-! ## Conversions -/

/-- `def $s33_to_u32(s33) : u32  hint(show %)`.

The pinned source declares this coercion, gives it no equations, and does not
mark it `hint(builtin)` either.  `hint(show %)` renders `$s33_to_u32(x)` as `x`:
it is the identity on the value.  Its one use is `5.2-binary.types.spectec`'s
`| x33:Bs33 => _IDX $s33_to_u32(x33)  -- if x33 >= 0`, whose guard puts the
argument in `[0, 2^32)`.  Transcribed as the identity on exactly that domain and
undefined outside it; no value is invented where the guard fails. -/
-- core-def: s33_to_u32
def s33_to_u32 (i : S33) : Option U32 :=
  if h : i.val.toNat < 2 ^ 32 ∧ 0 ≤ i.val then some ⟨i.val.toNat, h.1⟩ else none

/-! ## Signed numbers

`def $signed_(N, nat) : int` and its inverse. -/

/-- `def $signed_(N, i) = i           -- if $(i < 2^(N-1))`,
    `def $signed_(N, i) = $(i - 2^N)  -- if $(2^(N-1) <= i < 2^N)`. -/
-- core-def: signed_
def signed_ (w : Nat) (i : IN w) : Int :=
  if i.val < 2 ^ (w - 1) then (i.val : Int) else (i.val : Int) - ((2 ^ w : Nat) : Int)

/-- `def $inv_signed_(N, i) = i          -- if $(0 <= i < 2^(N-1))`,
    `def $inv_signed_(N, i) = $(i + 2^N) -- if $(-2^(N-1) <= i < 0)`.

Transcribed as the total function `i mod 2^N`, whose value is in `[0, 2^N)` and
therefore coincides with the source's first equation on `0 <= i < 2^(N-1)` and
with its second on `-2^(N-1) <= i < 0`.  A total extension is used rather than an
`Option` because the source's own uses (`table.grow-fail`, `memory.grow-fail`,
`$iextend_`) all lie inside the stated domain. -/
-- core-def: inv_signed_
def inv_signed_ (w : Nat) (i : Int) : IN w :=
  ⟨(i % ((2 ^ w : Nat) : Int)).toNat, by
    have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := by
      have := two_pow_pos w
      omega
    have h0 : (0 : Int) ≤ i % ((2 ^ w : Nat) : Int) := Int.emod_nonneg i (by omega)
    have h1 : i % ((2 ^ w : Nat) : Int) < ((2 ^ w : Nat) : Int) :=
      Int.emod_lt_of_pos i hpos
    omega⟩

/-- `def $sx(consttype) = eps`, `def $sx(packtype) = S`.

The source's result type is `sx?`, so the outer `Option` is the partiality: a
`reftype` and `BOT` are `storagetype`s for which no equation is given. -/
-- core-def: sx
def sx : StorageType → Option (Option Sx)
  | .val (.num _) => some none
  | .val (.vec _) => some none
  | .val (.ref _) => none
  | .val .bot => none
  | .pack _ => some (some .s)

/-! ## Construction -/

/-- `def $zero(Jnn) = 0`, `def $zero(Fnn) = $fzero($size(Fnn))`. -/
-- core-def: zero
def zero_ : (lt : LaneType) → Lane_ lt
  | .num .i32 => inZero 32
  | .num .i64 => inZero 64
  | .num .f32 => fzero 32
  | .num .f64 => fzero 64
  | .pack pt => inZero pt.size

/-- `def $bool(false) = 0`, `def $bool(true) = 1`. -/
-- core-def: bool
def bool_ (b : Bool) : U32 := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- `iN(N)` from a natural, reduced modulo `2^N`.  Every use below is a source
equation whose right-hand side is already written `$(... \ 2^N)`. -/
def ofNatWrap (w : Nat) (n : Nat) : IN w := ⟨n % 2 ^ w, Nat.mod_lt _ (two_pow_pos w)⟩

/-! ## Saturation -/

/-- `def $sat_u_(N, i) = 0  -- if i < 0`, `= $(2^N - 1)  -- if i > $(2^N - 1)`,
`= i  -- otherwise`. -/
-- core-def: sat_u_
def sat_u_ (w : Nat) (i : Int) : Nat :=
  if i < 0 then 0
  else if i > ((2 ^ w : Nat) : Int) - 1 then 2 ^ w - 1
  else i.toNat

/-- `def $sat_s_(N, i) = $(-2^(N-1))  -- if i < $(-2^(N-1))`,
`= $(2^(N-1) - 1)  -- if i > $(2^(N-1) - 1)`, `= i  -- otherwise`. -/
-- core-def: sat_s_
def sat_s_ (w : Nat) (i : Int) : Int :=
  if i < -((2 ^ (w - 1) : Nat) : Int) then -((2 ^ (w - 1) : Nat) : Int)
  else if i > ((2 ^ (w - 1) : Nat) : Int) - 1 then ((2 ^ (w - 1) : Nat) : Int) - 1
  else i

/-! ## Integer operations

The equations `3.1` gives.  The remainder of the integer family is a parameter;
see the file header. -/

/-- `def $ineg_(N, i_1) = $((2^N - i_1) \ 2^N)`. -/
-- core-def: ineg_
def ineg_ (w : Nat) (i : IN w) : IN w := ofNatWrap w (2 ^ w - i.val)

/-- `def $iabs_(N, i_1) = i_1  -- if $signed_(N, i_1) >= 0`,
`= $ineg_(N, i_1)  -- otherwise`. -/
-- core-def: iabs_
def iabs_ (w : Nat) (i : IN w) : IN w :=
  if 0 ≤ signed_ w i then i else ineg_ w i

/-- `def $iextend_(N, M, U, i) = $(i \ 2^M)`,
`def $iextend_(N, M, S, i) = $inv_signed_(N, $signed_(M, $(i \ 2^M)))`. -/
-- core-def: iextend_
def iextend_ (w m : Nat) (sx : Sx) (i : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (i.val % 2 ^ m)
  | .s => inv_signed_ w (signed_ m (ofNatWrap m (i.val % 2 ^ m)))

/-- `def $iadd_(N, i_1, i_2) = $((i_1 + i_2) \ 2^N)`. -/
-- core-def: iadd_
def iadd_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (i₁.val + i₂.val)

/-- `def $isub_(N, i_1, i_2) = $((2^N + i_1 - i_2) \ 2^N)`. -/
-- core-def: isub_
def isub_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (2 ^ w + i₁.val - i₂.val)

/-- `def $imul_(N, i_1, i_2) = $((i_1 * i_2) \ 2^N)`. -/
-- core-def: imul_
def imul_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (i₁.val * i₂.val)

/-- `def $idiv_(N, U, i_1, 0) = eps`,
`def $idiv_(N, U, i_1, i_2) = $truncz($(i_1 / i_2))`,
`def $idiv_(N, S, i_1, 0) = eps`,
`def $idiv_(N, S, i_1, i_2) = eps  -- if $($signed_(N,i_1)/$signed_(N,i_2)) = 2^(N-1)`,
`def $idiv_(N, S, i_1, i_2) = $inv_signed_(N, $truncz($($signed_(N,i_1)/$signed_(N,i_2))))`.

`$truncz` of a rational is truncation toward zero; on naturals that is `Nat`
division and on integers it is `Int.tdiv`, which is how the two equations are
written here.  The fourth equation's side condition is stated on the RATIONAL
quotient; `Int.tdiv j_1 j_2 = 2^(N-1)` is equivalent to it, because `|j_1| <=
2^(N-1)` and `|j_2| >= 1` force `|j_1| = 2^(N-1)` and `|j_2| = 1`. -/
-- core-def: idiv_
def idiv_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : Option (IN w) :=
  match sx with
  | .u => if i₂.val = 0 then none else some (ofNatWrap w (i₁.val / i₂.val))
  | .s =>
      if i₂.val = 0 then none
      else
        let j₁ := signed_ w i₁
        let j₂ := signed_ w i₂
        if Int.tdiv j₁ j₂ = ((2 ^ (w - 1) : Nat) : Int) then none
        else some (inv_signed_ w (Int.tdiv j₁ j₂))

/-- `def $irem_(N, U, i_1, 0) = eps`,
`def $irem_(N, U, i_1, i_2) = $(i_1 - i_2 * $truncz($(i_1 / i_2)))`,
`def $irem_(N, S, i_1, 0) = eps`,
`def $irem_(N, S, i_1, i_2) = $inv_signed_(N, $(j_1 - j_2 * $truncz($(j_1 / j_2))))`.

`i - j * truncz(i/j)` is `Nat` remainder on naturals and `Int.tmod` on integers. -/
-- core-def: irem_
def irem_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : Option (IN w) :=
  match sx with
  | .u => if i₂.val = 0 then none else some (ofNatWrap w (i₁.val % i₂.val))
  | .s =>
      if i₂.val = 0 then none
      else some (inv_signed_ w (Int.tmod (signed_ w i₁) (signed_ w i₂)))

/-- `def $imin_(N, U, i_1, i_2) = i_1  -- if i_1 <= i_2`, `= i_2  -- if i_1 > i_2`;
`def $imin_(N, S, i_1, i_2) = i_1  -- if $signed_ <= $signed_`, `= i_2  -- otherwise`. -/
-- core-def: imin_
def imin_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => if i₁.val ≤ i₂.val then i₁ else i₂
  | .s => if signed_ w i₁ ≤ signed_ w i₂ then i₁ else i₂

/-- `def $imax_(N, U, i_1, i_2) = i_1  -- if i_1 >= i_2`, `= i_2  -- if i_1 < i_2`;
`def $imax_(N, S, i_1, i_2) = i_1  -- if $signed_ >= $signed_`, `= i_2  -- otherwise`. -/
-- core-def: imax_
def imax_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => if i₁.val ≥ i₂.val then i₁ else i₂
  | .s => if signed_ w i₁ ≥ signed_ w i₂ then i₁ else i₂

/-- `def $iadd_sat_(N, U, i_1, i_2) = $sat_u_(N, $(i_1 + i_2))`,
`def $iadd_sat_(N, S, i_1, i_2) = $inv_signed_(N, $sat_s_(N, $($signed_ + $signed_)))`. -/
-- core-def: iadd_sat_
def iadd_sat_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (sat_u_ w ((i₁.val : Int) + (i₂.val : Int)))
  | .s => inv_signed_ w (sat_s_ w (signed_ w i₁ + signed_ w i₂))

/-- `def $isub_sat_(N, U, i_1, i_2) = $sat_u_(N, $(i_1 - i_2))`,
`def $isub_sat_(N, S, i_1, i_2) = $inv_signed_(N, $sat_s_(N, $($signed_ - $signed_)))`. -/
-- core-def: isub_sat_
def isub_sat_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (sat_u_ w ((i₁.val : Int) - (i₂.val : Int)))
  | .s => inv_signed_ w (sat_s_ w (signed_ w i₁ - signed_ w i₂))

/-- `def $ieqz_(N, i_1) = $bool(i_1 = 0)`. -/
-- core-def: ieqz_
def ieqz_ (w : Nat) (i : IN w) : U32 := bool_ (i.val == 0)

/-- `def $inez_(N, i_1) = $bool(i_1 =/= 0)`. -/
-- core-def: inez_
def inez_ (w : Nat) (i : IN w) : U32 := bool_ (i.val != 0)

/-- `def $ieq_(N, i_1, i_2) = $bool(i_1 = i_2)`. -/
-- core-def: ieq_
def ieq_ (w : Nat) (i₁ i₂ : IN w) : U32 := bool_ (i₁.val == i₂.val)

/-- `def $ine_(N, i_1, i_2) = $bool(i_1 =/= i_2)`. -/
-- core-def: ine_
def ine_ (w : Nat) (i₁ i₂ : IN w) : U32 := bool_ (i₁.val != i₂.val)

/-- `def $ilt_(N, U, i_1, i_2) = $bool(i_1 < i_2)`,
`def $ilt_(N, S, i_1, i_2) = $bool($signed_ < $signed_)`. -/
-- core-def: ilt_
def ilt_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val < i₂.val))
  | .s => bool_ (decide (signed_ w i₁ < signed_ w i₂))

/-- `def $igt_(N, U, i_1, i_2) = $bool(i_1 > i_2)`,
`def $igt_(N, S, i_1, i_2) = $bool($signed_ > $signed_)`. -/
-- core-def: igt_
def igt_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val > i₂.val))
  | .s => bool_ (decide (signed_ w i₁ > signed_ w i₂))

/-- `def $ile_(N, U, i_1, i_2) = $bool(i_1 <= i_2)`,
`def $ile_(N, S, i_1, i_2) = $bool($signed_ <= $signed_)`. -/
-- core-def: ile_
def ile_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val ≤ i₂.val))
  | .s => bool_ (decide (signed_ w i₁ ≤ signed_ w i₂))

/-- `def $ige_(N, U, i_1, i_2) = $bool(i_1 >= i_2)`,
`def $ige_(N, S, i_1, i_2) = $bool($signed_ >= $signed_)`. -/
-- core-def: ige_
def ige_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val ≥ i₂.val))
  | .s => bool_ (decide (signed_ w i₁ ≥ signed_ w i₂))

/-! ## Packed numbers -/

/-- `def $lpacknum_(numtype, c) = c`,
`def $lpacknum_(packtype, c) = $wrap__($size($lunpack(packtype)), $psize(packtype), c)`. -/
-- core-def: lpacknum_
def lpacknum_ : (lt : LaneType) → Num_ lt.unpack → Lane_ lt
  | .num _, c => c
  | .pack pt, c => N.wrap__ 32 pt.size c

/-- `def $cpacknum_(consttype, c) = c`,
`def $cpacknum_(packtype, c) = $wrap__($size($lunpack(packtype)), $psize(packtype), c)`. -/
-- core-def: cpacknum_
def cpacknum_ : (zt : StorageType) → CUnpackLit zt → Lit_ zt
  | .val (.num _), c => c
  | .val (.vec _), c => c
  | .val (.ref _), c => c.elim
  | .val .bot, c => c.elim
  | .pack pt, c => N.wrap__ 32 pt.size c

/-- `def $lunpacknum_(numtype, c) = c`,
`def $lunpacknum_(packtype, c) = $extend__($psize(packtype), $size($lunpack(packtype)), U, c)`. -/
-- core-def: lunpacknum_
def lunpacknum_ : (lt : LaneType) → Lane_ lt → Num_ lt.unpack
  | .num _, c => c
  | .pack pt, c => N.extend__ pt.size 32 .u c

/-- `def $cunpacknum_(consttype, c) = c`,
`def $cunpacknum_(packtype, c) = $extend__($psize(packtype), $size($lunpack(packtype)), U, c)`. -/
-- core-def: cunpacknum_
def cunpacknum_ : (zt : StorageType) → Lit_ zt → CUnpackLit zt
  | .val (.num _), c => c
  | .val (.vec _), c => c
  | .val (.ref _), c => c.elim
  | .val .bot, c => c.elim
  | .pack pt, c => N.extend__ pt.size 32 .u c

/-- `$const($cunpack(zt), $cunpacknum_(zt, c))`, the composite the array and
struct step rules of `4.3` use.  `none` exactly where `$cunpack` is. -/
def cunpackConst : (zt : StorageType) → Lit_ zt → Option Instr
  | .val (.num nt), c => some (.const nt c)
  | .val (.vec vt), c => some (.vconst vt c)
  | .val (.ref _), c => c.elim
  | .val .bot, c => c.elim
  | .pack pt, c => some (.const .i32 (N.extend__ pt.size 32 .u c))

/-! ## Operator dispatch

`def $unop_`, `$binop_`, `$testop_`, `$relop_`, `$cvtop__` of `3.1`. -/

/-- The `Inn` equations of `def $unop_`. -/
def unopI (w : Nat) : UnopI → IN w → List (IN w)
  | .clz, i => [N.iclz_ w i]
  | .ctz, i => [N.ictz_ w i]
  | .popcnt, i => [N.ipopcnt_ w i]
  | .extend m, i => [iextend_ w m.toNat .s i]

/-- The `Fnn` equations of `def $unop_`. -/
def unopF (w : Nat) : UnopF → FN w → List (FN w)
  | .abs, f => N.fabs_ w f
  | .neg, f => N.fneg_ w f
  | .sqrt, f => N.fsqrt_ w f
  | .ceil, f => N.fceil_ w f
  | .floor, f => N.ffloor_ w f
  | .trunc, f => N.ftrunc_ w f
  | .nearest, f => N.fnearest_ w f

/-- `def $unop_(numtype, unop_(numtype), num_(numtype)) : num_(numtype)*`. -/
-- core-def: unop_
def unop_ : (nt : NumType) → Unop → Num_ nt → List (Num_ nt)
  | .i32, .int o, c => N.unopI 32 o c
  | .i64, .int o, c => N.unopI 64 o c
  | .f32, .float o, c => N.unopF 32 o c
  | .f64, .float o, c => N.unopF 64 o c
  | .i32, .float _, _ => []
  | .i64, .float _, _ => []
  | .f32, .int _, _ => []
  | .f64, .int _, _ => []

/-- The `Inn` equations of `def $binop_`.

`$binop_(Inn, SHL, i_1, i_2) = $ishl_($sizenn(Inn), i_1, i_2)` passes an
`iN(N)` where `$ishl_` declares a `u32`; the source leaves that coercion
implicit, and it is written out here as reduction modulo `2^32`. -/
def binopI (w : Nat) : BinopI → IN w → IN w → List (IN w)
  | .add, i₁, i₂ => [iadd_ w i₁ i₂]
  | .sub, i₁, i₂ => [isub_ w i₁ i₂]
  | .mul, i₁, i₂ => [imul_ w i₁ i₂]
  | .div sx, i₁, i₂ => (idiv_ w sx i₁ i₂).toList
  | .rem sx, i₁, i₂ => (irem_ w sx i₁ i₂).toList
  | .and, i₁, i₂ => [N.iand_ w i₁ i₂]
  | .or, i₁, i₂ => [N.ior_ w i₁ i₂]
  | .xor, i₁, i₂ => [N.ixor_ w i₁ i₂]
  | .shl, i₁, i₂ => [N.ishl_ w i₁ (ofNatWrap 32 i₂.val)]
  | .shr sx, i₁, i₂ => [N.ishr_ w sx i₁ (ofNatWrap 32 i₂.val)]
  | .rotl, i₁, i₂ => [N.irotl_ w i₁ i₂]
  | .rotr, i₁, i₂ => [N.irotr_ w i₁ i₂]

/-- The `Fnn` equations of `def $binop_`. -/
def binopF (w : Nat) : BinopF → FN w → FN w → List (FN w)
  | .add, f₁, f₂ => N.fadd_ w f₁ f₂
  | .sub, f₁, f₂ => N.fsub_ w f₁ f₂
  | .mul, f₁, f₂ => N.fmul_ w f₁ f₂
  | .div, f₁, f₂ => N.fdiv_ w f₁ f₂
  | .min, f₁, f₂ => N.fmin_ w f₁ f₂
  | .max, f₁, f₂ => N.fmax_ w f₁ f₂
  | .copysign, f₁, f₂ => N.fcopysign_ w f₁ f₂

/-- `def $binop_(numtype, binop_(numtype), num_, num_) : num_(numtype)*`. -/
-- core-def: binop_
def binop_ : (nt : NumType) → Binop → Num_ nt → Num_ nt → List (Num_ nt)
  | .i32, .int o, c₁, c₂ => N.binopI 32 o c₁ c₂
  | .i64, .int o, c₁, c₂ => N.binopI 64 o c₁ c₂
  | .f32, .float o, c₁, c₂ => N.binopF 32 o c₁ c₂
  | .f64, .float o, c₁, c₂ => N.binopF 64 o c₁ c₂
  | .i32, .float _, _, _ => []
  | .i64, .float _, _, _ => []
  | .f32, .int _, _, _ => []
  | .f64, .int _, _, _ => []

/-- `def $testop_(Inn, EQZ, i) = $ieqz_($sizenn(Inn), i)`.  `none` where the
source gives no equation. -/
-- core-def: testop_
def testop_ : (nt : NumType) → Testop → Num_ nt → Option U32
  | .i32, .int .eqz, c => some (ieqz_ 32 c)
  | .i64, .int .eqz, c => some (ieqz_ 64 c)
  | .f32, .int _, _ => none
  | .f64, .int _, _ => none

/-- The `Inn` equations of `def $relop_`. -/
def relopI (w : Nat) : RelopI → IN w → IN w → U32
  | .eq, i₁, i₂ => ieq_ w i₁ i₂
  | .ne, i₁, i₂ => ine_ w i₁ i₂
  | .lt sx, i₁, i₂ => ilt_ w sx i₁ i₂
  | .gt sx, i₁, i₂ => igt_ w sx i₁ i₂
  | .le sx, i₁, i₂ => ile_ w sx i₁ i₂
  | .ge sx, i₁, i₂ => ige_ w sx i₁ i₂

/-- The `Fnn` equations of `def $relop_`. -/
def relopF (w : Nat) : RelopF → FN w → FN w → U32
  | .eq, f₁, f₂ => N.feq_ w f₁ f₂
  | .ne, f₁, f₂ => N.fne_ w f₁ f₂
  | .lt, f₁, f₂ => N.flt_ w f₁ f₂
  | .gt, f₁, f₂ => N.fgt_ w f₁ f₂
  | .le, f₁, f₂ => N.fle_ w f₁ f₂
  | .ge, f₁, f₂ => N.fge_ w f₁ f₂

/-- `def $relop_(numtype, relop_(numtype), num_, num_) : u32`.  `none` where the
source gives no equation. -/
-- core-def: relop_
def relop_ : (nt : NumType) → Relop → Num_ nt → Num_ nt → Option U32
  | .i32, .int o, c₁, c₂ => some (relopI 32 o c₁ c₂)
  | .i64, .int o, c₁, c₂ => some (relopI 64 o c₁ c₂)
  | .f32, .float o, c₁, c₂ => some (N.relopF 32 o c₁ c₂)
  | .f64, .float o, c₁, c₂ => some (N.relopF 64 o c₁ c₂)
  | .i32, .float _, _, _ => none
  | .i64, .float _, _, _ => none
  | .f32, .int _, _, _ => none
  | .f64, .int _, _, _ => none

/-- `def $cvtop__(numtype_1, numtype_2, cvtop__(numtype_1, numtype_2), num_) :
    num_(numtype_2)*`.

`nt₁` is the operand type and `nt₂` the result type, as in the source's
`$cvtop__(numtype_1, numtype_2, ...)`. -/
-- core-def: cvtop__
def cvtop__ : (nt₁ nt₂ : NumType) → Cvtop → Num_ nt₁ → List (Num_ nt₂)
  -- Inn_1 -> Inn_2
  | .i32, .i32, .ii (.extend sx), c => [N.extend__ 32 32 sx c]
  | .i32, .i64, .ii (.extend sx), c => [N.extend__ 32 64 sx c]
  | .i64, .i32, .ii (.extend sx), c => [N.extend__ 64 32 sx c]
  | .i64, .i64, .ii (.extend sx), c => [N.extend__ 64 64 sx c]
  | .i32, .i32, .ii .wrap, c => [N.wrap__ 32 32 c]
  | .i32, .i64, .ii .wrap, c => [N.wrap__ 32 64 c]
  | .i64, .i32, .ii .wrap, c => [N.wrap__ 64 32 c]
  | .i64, .i64, .ii .wrap, c => [N.wrap__ 64 64 c]
  -- Fnn_1 -> Inn_2
  | .f32, .i32, .fi (.trunc sx), c => (N.trunc__ 32 32 sx c).toList
  | .f32, .i64, .fi (.trunc sx), c => (N.trunc__ 32 64 sx c).toList
  | .f64, .i32, .fi (.trunc sx), c => (N.trunc__ 64 32 sx c).toList
  | .f64, .i64, .fi (.trunc sx), c => (N.trunc__ 64 64 sx c).toList
  | .f32, .i32, .fi (.truncSat sx), c => (N.trunc_sat__ 32 32 sx c).toList
  | .f32, .i64, .fi (.truncSat sx), c => (N.trunc_sat__ 32 64 sx c).toList
  | .f64, .i32, .fi (.truncSat sx), c => (N.trunc_sat__ 64 32 sx c).toList
  | .f64, .i64, .fi (.truncSat sx), c => (N.trunc_sat__ 64 64 sx c).toList
  | .f32, .i32, .fi .reinterpret, c => [N.reinterpret__ .f32 .i32 c]
  | .f64, .i64, .fi .reinterpret, c => [N.reinterpret__ .f64 .i64 c]
  -- Inn_1 -> Fnn_2
  | .i32, .f32, .ifl (.convert sx), c => [N.convert__ 32 32 sx c]
  | .i32, .f64, .ifl (.convert sx), c => [N.convert__ 32 64 sx c]
  | .i64, .f32, .ifl (.convert sx), c => [N.convert__ 64 32 sx c]
  | .i64, .f64, .ifl (.convert sx), c => [N.convert__ 64 64 sx c]
  | .i32, .f32, .ifl .reinterpret, c => [N.reinterpret__ .i32 .f32 c]
  | .i64, .f64, .ifl .reinterpret, c => [N.reinterpret__ .i64 .f64 c]
  -- Fnn_1 -> Fnn_2
  | .f32, .f32, .ff .promote, c => N.promote__ 32 32 c
  | .f32, .f64, .ff .promote, c => N.promote__ 32 64 c
  | .f64, .f32, .ff .promote, c => N.promote__ 64 32 c
  | .f64, .f64, .ff .promote, c => N.promote__ 64 64 c
  | .f32, .f32, .ff .demote, c => N.demote__ 32 32 c
  | .f32, .f64, .ff .demote, c => N.demote__ 32 64 c
  | .f64, .f32, .ff .demote, c => N.demote__ 64 32 c
  | .f64, .f64, .ff .demote, c => N.demote__ 64 64 c
  -- No equation: the `REINTERPRET` pairs the source excludes by
  -- `-- if $size(_) = $size(_)`, and every operand/operator family mismatch.
  | _, _, _, _ => []

/-! # `3.2-numerics.vector.spectec`

From here on the source is the vector file.  The shape of every transcription is
the same: read the operand lanes with `$lanes_`, apply the scalar operator of
`3.1` lanewise, and rebuild with `$inv_lanes_`.  `$lanes_` and `$inv_lanes_` are
the only two primitives of `3.2`, and they are the two fields of `Numerics` this
half of the file uses. -/

/-- The lanes of `v` at shape `sh`, read as `iN($lsize)`; `none` at a lane type
that is not a `Jnn`, where the source's `Jnn X M` pattern does not apply. -/
def intLanes (sh : Shape) (v : V128Lit) : Option (List (IN sh.lane.size)) :=
  lanesJ? sh.lane (N.lanes_ sh v)

/-- The lanes of `v` at shape `sh`, read as `fN($lsize)`; `none` at a lane type
that is not an `Fnn`. -/
def floatLanes (sh : Shape) (v : V128Lit) : Option (List (FN sh.lane.size)) :=
  lanesF? sh.lane (N.lanes_ sh v)

/-- `$inv_lanes_(sh, c*)` for integer lanes. -/
def intVec (sh : Shape) (cs : List (IN sh.lane.size)) : Option V128Lit :=
  (ofLanesJ? sh.lane cs).map (N.inv_lanes_ sh)

/-- `$inv_lanes_(sh, c*)` for float lanes. -/
def floatVec (sh : Shape) (cs : List (FN sh.lane.size)) : Option V128Lit :=
  (ofLanesF? sh.lane cs).map (N.inv_lanes_ sh)

/-! ## Conversion selectors -/

/-- `def $zeroop(Jnn_1 X M_1, Jnn_2 X M_2, EXTEND half sx) = eps`,
`def $zeroop(Jnn_1 X M_1, Fnn_2 X M_2, CONVERT half? sx) = eps`,
`def $zeroop(Fnn_1 X M_1, Jnn_2 X M_2, TRUNC_SAT sx zero?) = zero?`,
`def $zeroop(Fnn_1 X M_1, Jnn_2 X M_2, RELAXED_TRUNC sx zero?) = zero?`,
`def $zeroop(Fnn_1 X M_1, Fnn_2 X M_2, DEMOTE zero) = zero`,
`def $zeroop(Fnn_1 X M_1, Fnn_2 X M_2, PROMOTE LOW) = eps`.

The result type is `zero?`; the outer `Option` is the partiality, i.e. the
operand/result lane families the listed equations do not cover. -/
-- core-def: zeroop
def zeroop (sh₁ sh₂ : Shape) : VCvtop → Option (Option Zero)
  | .jj (.extend _ _) =>
      if sh₁.lane.toJnn?.isSome && sh₂.lane.toJnn?.isSome then some none else none
  | .jf (.convert _ _) =>
      if sh₁.lane.toJnn?.isSome && sh₂.lane.toFnn?.isSome then some none else none
  | .fj (.truncSat _ z) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toJnn?.isSome then some z else none
  | .fj (.relaxedTrunc _ z) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toJnn?.isSome then some z else none
  | .ff (.demote z) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toFnn?.isSome then some (some z) else none
  | .ff (.promote h) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toFnn?.isSome && h == .low then some none
      else none

/-- `def $halfop(Jnn_1 X M_1, Jnn_2 X M_2, EXTEND half sx) = half`,
`def $halfop(Jnn_1 X M_1, Fnn_2 X M_2, CONVERT half? sx) = half?`,
`def $halfop(Fnn_1 X M_1, Jnn_2 X M_2, TRUNC_SAT sx zero?) = eps`,
`def $halfop(Fnn_1 X M_1, Jnn_2 X M_2, RELAXED_TRUNC sx zero?) = eps`,
`def $halfop(Fnn_1 X M_1, Fnn_2 X M_2, DEMOTE zero) = eps`,
`def $halfop(Fnn_1 X M_1, Fnn_2 X M_2, PROMOTE LOW) = LOW`. -/
-- core-def: halfop
def halfop (sh₁ sh₂ : Shape) : VCvtop → Option (Option Half)
  | .jj (.extend h _) =>
      if sh₁.lane.toJnn?.isSome && sh₂.lane.toJnn?.isSome then some (some h) else none
  | .jf (.convert h _) =>
      if sh₁.lane.toJnn?.isSome && sh₂.lane.toFnn?.isSome then some h else none
  | .fj (.truncSat _ _) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toJnn?.isSome then some none else none
  | .fj (.relaxedTrunc _ _) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toJnn?.isSome then some none else none
  | .ff (.demote _) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toFnn?.isSome then some none else none
  | .ff (.promote h) =>
      if sh₁.lane.toFnn?.isSome && sh₂.lane.toFnn?.isSome && h == .low then
        some (some .low)
      else none

/-- `def $half(LOW, i, j) = i`, `def $half(HIGH, i, j) = j`. -/
-- core-def: half
def half : Half → Nat → Nat → Nat
  | .low, i, _ => i
  | .high, _, j => j

/-! ## Swizzle lanes -/

/-- `def $iswizzle_lane_(N, c*, i) = c*[i]  -- if i < |c*|`,
`def $iswizzle_lane_(N, c*, i) = 0  -- otherwise`. -/
-- core-def: iswizzle_lane_
def iswizzle_lane_ (w : Nat) (cs : List (IN w)) (i : IN w) : IN w :=
  match cs[i.val]? with
  | some c => c
  | none => inZero w

/-- `def $irelaxed_swizzle_lane_(N, c*, i) = c*[i]  -- if i < |c*|`,
`= 0  -- if $signed_(N, i) < 0`,
`= $relaxed2($R_swizzle, iN(N), 0, c*[i \ |c*|])  -- otherwise`.

`none` only where the third equation's index `i \ |c*|` is undefined, i.e. where
`c*` is empty; `$ivswizzlop_` never calls it there, because it passes the lanes
of a vector. -/
-- core-def: irelaxed_swizzle_lane_
def irelaxed_swizzle_lane_ (w : Nat) (cs : List (IN w)) (i : IN w) :
    Option (IN w) :=
  match cs[i.val]? with
  | some c => some c
  | none =>
      if signed_ w i < 0 then some (inZero w)
      else (cs[i.val % cs.length]?).map (relaxed2 N.nd N.r_swizzle (inZero w))

/-! ## Lanewise operations -/

/-- `def $ivunop_(Jnn X M, def $f_, v_1) = $inv_lanes_(Jnn X M, c*)
    -- if c_1* = $lanes_(Jnn X M, v_1)
    -- if c* = $f_($lsizenn(Jnn), c_1)*`. -/
-- core-def: ivunop_
def ivunop_ (sh : Shape) (f : (w : Nat) → IN w → IN w) (v₁ : V128Lit) :
    List V128Lit :=
  match N.intLanes sh v₁ with
  | none => []
  | some c₁s => (N.intVec sh (c₁s.map (f sh.lane.size))).toList

/-- `def $fvunop_(Fnn X M, def $f_, v_1) = $inv_lanes_(Fnn X M, c*)*
    -- if c_1* = $lanes_(Fnn X M, v_1)
    -- if c** = $setproduct_(lane_(Fnn), $f_($sizenn(Fnn), c_1)*)`. -/
-- core-def: fvunop_
def fvunop_ (sh : Shape) (f : (w : Nat) → FN w → List (FN w)) (v₁ : V128Lit) :
    List V128Lit :=
  match N.floatLanes sh v₁ with
  | none => []
  | some c₁s => (setproduct (c₁s.map (f sh.lane.size))).filterMap (N.floatVec sh)

/-- `def $ivbinop_(Jnn X M, def $f_, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $f_($lsizenn(Jnn), c_1, c_2)*`. -/
-- core-def: ivbinop_
def ivbinop_ (sh : Shape) (f : (w : Nat) → IN w → IN w → IN w)
    (v₁ v₂ : V128Lit) : List V128Lit :=
  match N.intLanes sh v₁, N.intLanes sh v₂ with
  | some c₁s, some c₂s =>
      match zipWith? (f sh.lane.size) c₁s c₂s with
      | none => []
      | some cs => (N.intVec sh cs).toList
  | _, _ => []

/-- `def $ivbinopsx_(Jnn X M, def $f_, sx, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $f_($lsizenn(Jnn), sx, c_1, c_2)*`. -/
-- core-def: ivbinopsx_
def ivbinopsx_ (sh : Shape) (f : (w : Nat) → Sx → IN w → IN w → IN w) (sx : Sx)
    (v₁ v₂ : V128Lit) : List V128Lit :=
  match N.intLanes sh v₁, N.intLanes sh v₂ with
  | some c₁s, some c₂s =>
      match zipWith? (f sh.lane.size sx) c₁s c₂s with
      | none => []
      | some cs => (N.intVec sh cs).toList
  | _, _ => []

/-- `def $ivbinopsxnd_(Jnn X M, def $f_, sx, v_1, v_2) = $inv_lanes_(Jnn X M, c*)*
    -- if c** = $setproduct_(lane_(Jnn), $f_($lsizenn(Jnn), sx, c_1, c_2)*)`. -/
-- core-def: ivbinopsxnd_
def ivbinopsxnd_ (sh : Shape) (f : (w : Nat) → Sx → IN w → IN w → List (IN w))
    (sx : Sx) (v₁ v₂ : V128Lit) : List V128Lit :=
  match N.intLanes sh v₁, N.intLanes sh v₂ with
  | some c₁s, some c₂s =>
      match zipWith? (f sh.lane.size sx) c₁s c₂s with
      | none => []
      | some css => (setproduct css).filterMap (N.intVec sh)
  | _, _ => []

/-- `def $fvbinop_(Fnn X M, def $f_, v_1, v_2) = $inv_lanes_(Fnn X M, c*)*
    -- if c** = $setproduct_(lane_(Fnn), $f_($sizenn(Fnn), c_1, c_2)*)`. -/
-- core-def: fvbinop_
def fvbinop_ (sh : Shape) (f : (w : Nat) → FN w → FN w → List (FN w))
    (v₁ v₂ : V128Lit) : List V128Lit :=
  match N.floatLanes sh v₁, N.floatLanes sh v₂ with
  | some c₁s, some c₂s =>
      match zipWith? (f sh.lane.size) c₁s c₂s with
      | none => []
      | some css => (setproduct css).filterMap (N.floatVec sh)
  | _, _ => []

/-- `def $ivternopnd_(Jnn X M, def $f_, v_1, v_2, v_3) = $inv_lanes_(Jnn X M, c*)*
    -- if c** = $setproduct_(lane_(Jnn), $f_($lsizenn(Jnn), c_1, c_2, c_3)*)`. -/
-- core-def: ivternopnd_
def ivternopnd_ (sh : Shape) (f : (w : Nat) → IN w → IN w → IN w → List (IN w))
    (v₁ v₂ v₃ : V128Lit) : List V128Lit :=
  match N.intLanes sh v₁, N.intLanes sh v₂, N.intLanes sh v₃ with
  | some c₁s, some c₂s, some c₃s =>
      match zipWith3? (f sh.lane.size) c₁s c₂s c₃s with
      | none => []
      | some css => (setproduct css).filterMap (N.intVec sh)
  | _, _, _ => []

/-- `def $fvternop_(Fnn X M, def $f_, v_1, v_2, v_3) = $inv_lanes_(Fnn X M, c*)*
    -- if c** = $setproduct_(lane_(Fnn), $f_($sizenn(Fnn), c_1, c_2, c_3)*)`. -/
-- core-def: fvternop_
def fvternop_ (sh : Shape) (f : (w : Nat) → FN w → FN w → FN w → List (FN w))
    (v₁ v₂ v₃ : V128Lit) : List V128Lit :=
  match N.floatLanes sh v₁, N.floatLanes sh v₂, N.floatLanes sh v₃ with
  | some c₁s, some c₂s, some c₃s =>
      match zipWith3? (f sh.lane.size) c₁s c₂s c₃s with
      | none => []
      | some css => (setproduct css).filterMap (N.floatVec sh)
  | _, _, _ => []

/-- `def $ivtestop_(Jnn X M, def $f_, v_1) = $prod(c*)
    -- if c* = $f_($lsizenn(Jnn), c_1)*`. -/
-- core-def: ivtestop_
def ivtestop_ (sh : Shape) (f : (w : Nat) → IN w → U32) (v₁ : V128Lit) :
    Option U32 :=
  match N.intLanes sh v₁ with
  | none => none
  | some c₁s => inOfNat? 32 (prodNat (c₁s.map (fun c => (f sh.lane.size c).val)))

/-- `def $fvtestop_(Fnn X M, def $f_, v_1) = $prod(c*)
    -- if c* = $f_($sizenn(Fnn), c_1)*`. -/
-- core-def: fvtestop_
def fvtestop_ (sh : Shape) (f : (w : Nat) → FN w → U32) (v₁ : V128Lit) :
    Option U32 :=
  match N.floatLanes sh v₁ with
  | none => none
  | some c₁s => inOfNat? 32 (prodNat (c₁s.map (fun c => (f sh.lane.size c).val)))

/-- `def $ivrelop_(Jnn X M, def $f_, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $extend__(1, $lsizenn(Jnn), S, $f_($lsizenn(Jnn), c_1, c_2))*`. -/
-- core-def: ivrelop_
def ivrelop_ (sh : Shape) (f : (w : Nat) → IN w → IN w → U32) (v₁ v₂ : V128Lit) :
    Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  let c₂s ← N.intLanes sh v₂
  let bs ← zipWith? (f sh.lane.size) c₁s c₂s
  let cs ← bs.mapM fun b => (inOfNat? 1 b.val).map (N.extend__ 1 sh.lane.size .s)
  N.intVec sh cs

/-- `def $ivrelopsx_(Jnn X M, def $f_, sx, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $extend__(1, $lsizenn(Jnn), S, $f_($lsizenn(Jnn), sx, c_1, c_2))*`. -/
-- core-def: ivrelopsx_
def ivrelopsx_ (sh : Shape) (f : (w : Nat) → Sx → IN w → IN w → U32) (sx : Sx)
    (v₁ v₂ : V128Lit) : Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  let c₂s ← N.intLanes sh v₂
  let bs ← zipWith? (f sh.lane.size sx) c₁s c₂s
  let cs ← bs.mapM fun b => (inOfNat? 1 b.val).map (N.extend__ 1 sh.lane.size .s)
  N.intVec sh cs

/-- `def $fvrelop_(Fnn X M, def $f_, v_1, v_2) = $inv_lanes_(Inn X M, c*)
    -- if c* = $extend__(1, $sizenn(Fnn), S, $f_($sizenn(Fnn), c_1, c_2))*
    -- if $isize(Inn) = $fsize(Fnn)`.

`intShapeOf` is that side condition: it returns the one `Inn X M` shape of the
operand's lane width and dimension. -/
-- core-def: fvrelop_
def fvrelop_ (sh : Shape) (f : (w : Nat) → FN w → FN w → U32) (v₁ v₂ : V128Lit) :
    Option V128Lit := do
  let shI ← intShapeOf sh
  let c₁s ← N.floatLanes sh v₁
  let c₂s ← N.floatLanes sh v₂
  let bs ← zipWith? (f sh.lane.size) c₁s c₂s
  let cs ← bs.mapM fun b => (inOfNat? 1 b.val).map (N.extend__ 1 shI.lane.size .s)
  N.intVec shI cs

/-- `def $ivshiftop_(Jnn X M, def $f_, v_1, i) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $f_($lsizenn(Jnn), c_1, i)*`. -/
-- core-def: ivshiftop_
def ivshiftop_ (sh : Shape) (f : (w : Nat) → IN w → U32 → IN w) (v₁ : V128Lit)
    (i : U32) : Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  N.intVec sh (c₁s.map (fun c => f sh.lane.size c i))

/-- `def $ivshiftopsx_(Jnn X M, def $f_, sx, v_1, i) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $f_($lsizenn(Jnn), sx, c_1, i)*`. -/
-- core-def: ivshiftopsx_
def ivshiftopsx_ (sh : Shape) (f : (w : Nat) → Sx → IN w → U32 → IN w) (sx : Sx)
    (v₁ : V128Lit) (i : U32) : Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  N.intVec sh (c₁s.map (fun c => f sh.lane.size sx c i))

/-- `def $ivbitmaskop_(Jnn X M, v_1) = $irev_(32, c)
    -- if c_1* = $lanes_(Jnn X M, v_1)
    -- if $ibits_(32, c) = $ilt_($lsizenn(Jnn), S, c_1, 0)* ++ (0)^(32-M)`.

`c` is determined by the second premise through the inverse the source declares
for `$ibits_`, `hint(inverse $inv_ibits_)`; that inverse is the parameter used
here. -/
-- core-def: ivbitmaskop_
def ivbitmaskop_ (sh : Shape) (v₁ : V128Lit) : Option U32 := do
  let c₁s ← N.intLanes sh v₁
  let zero := inZero sh.lane.size
  let bs ← c₁s.mapM (fun c => bitOfU32? (ilt_ sh.lane.size .s c zero))
  let bits := bs ++ List.replicate (32 - sh.dim.toNat) Bit.b0
  pure (N.irev_ 32 (N.inv_ibits_ 32 bits))

/-- `def $ivswizzlop_(Jnn X M, def $f_, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = $f_($lsizenn(Jnn), c_1*, c_2)*`. -/
-- core-def: ivswizzlop_
def ivswizzlop_ (sh : Shape)
    (f : (w : Nat) → List (IN w) → IN w → Option (IN w)) (v₁ v₂ : V128Lit) :
    Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  let c₂s ← N.intLanes sh v₂
  let cs ← c₂s.mapM (fun c => f sh.lane.size c₁s c)
  N.intVec sh cs

/-- `def $ivshufflop_(Jnn X M, i*, v_1, v_2) = $inv_lanes_(Jnn X M, c*)
    -- if c* = ((c_1* ++ c_2*)[i])*`. -/
-- core-def: ivshufflop_
def ivshufflop_ (sh : Shape) (is : List LaneIdx) (v₁ v₂ : V128Lit) :
    Option V128Lit := do
  let c₁s ← N.intLanes sh v₁
  let c₂s ← N.intLanes sh v₂
  let cs ← is.mapM (fun i => (c₁s ++ c₂s)[i.val]?)
  N.intVec sh cs

/-! ## Vector operator dispatch

The seventeen dispatchers `3.2` defines on top of the combinators above, and the
lane- and pair-level auxiliaries three of them call. -/

/-- `def $vvunop_(Vnn, NOT, v) = $inot_($vsizenn(Vnn), v)`. -/
-- core-def: vvunop_
def vvunop_ : VecType → VVUnop → V128Lit → List V128Lit
  | .v128, .not, v => [N.inot_ 128 v]

/-- `def $vvbinop_(Vnn, AND, v_1, v_2) = $iand_($vsizenn(Vnn), v_1, v_2)`,
`ANDNOT` to `$iandnot_`, `OR` to `$ior_`, `XOR` to `$ixor_`. -/
-- core-def: vvbinop_
def vvbinop_ : VecType → VVBinop → V128Lit → V128Lit → List V128Lit
  | .v128, .and, v₁, v₂ => [N.iand_ 128 v₁ v₂]
  | .v128, .andnot, v₁, v₂ => [N.iandnot_ 128 v₁ v₂]
  | .v128, .or, v₁, v₂ => [N.ior_ 128 v₁ v₂]
  | .v128, .xor, v₁, v₂ => [N.ixor_ 128 v₁ v₂]

/-- `def $vvternop_(Vnn, BITSELECT, v_1, v_2, v_3)
    = $ibitselect_($vsizenn(Vnn), v_1, v_2, v_3)`. -/
-- core-def: vvternop_
def vvternop_ : VecType → VVTernop → V128Lit → V128Lit → V128Lit → List V128Lit
  | .v128, .bitselect, v₁, v₂, v₃ => [N.ibitselect_ 128 v₁ v₂ v₃]

/-- `def $vunop_(Fnn X M, ABS, v) = $fvunop_(Fnn X M, $fabs_, v)` and its six
float siblings; `def $vunop_(Jnn X M, ABS, v) = $ivunop_(Jnn X M, $iabs_, v)`,
`NEG` to `$ineg_`, `POPCNT` to `$ipopcnt_`. -/
-- core-def: vunop_
def vunop_ (sh : Shape) : VUnop → V128Lit → List V128Lit
  | .float .abs, v => N.fvunop_ sh N.fabs_ v
  | .float .neg, v => N.fvunop_ sh N.fneg_ v
  | .float .sqrt, v => N.fvunop_ sh N.fsqrt_ v
  | .float .ceil, v => N.fvunop_ sh N.fceil_ v
  | .float .floor, v => N.fvunop_ sh N.ffloor_ v
  | .float .trunc, v => N.fvunop_ sh N.ftrunc_ v
  | .float .nearest, v => N.fvunop_ sh N.fnearest_ v
  | .int .abs, v => N.ivunop_ sh iabs_ v
  | .int .neg, v => N.ivunop_ sh ineg_ v
  | .int .popcnt, v => N.ivunop_ sh N.ipopcnt_ v

/-- `def $vbinop_(Jnn X M, ADD, ...) = $ivbinop_(Jnn X M, $iadd_, ...)` and its
nine `Jnn` siblings, `def $vbinop_(Fnn X M, ADD, ...) = $fvbinop_(...)` and its
nine `Fnn` siblings.

The source fixes the signedness argument of `AVGR`, `Q15MULR_SAT` and
`RELAXED_Q15MULR` in the equation itself (`AVGR U`, `Q15MULR_SAT S`,
`RELAXED_Q15MULR S`); at the other signedness there is no equation. -/
-- core-def: vbinop_
def vbinop_ (sh : Shape) : VBinop → V128Lit → V128Lit → List V128Lit
  | .int .add, v₁, v₂ => N.ivbinop_ sh iadd_ v₁ v₂
  | .int .sub, v₁, v₂ => N.ivbinop_ sh isub_ v₁ v₂
  | .int .mul, v₁, v₂ => N.ivbinop_ sh imul_ v₁ v₂
  | .int (.addSat sx), v₁, v₂ => N.ivbinopsx_ sh iadd_sat_ sx v₁ v₂
  | .int (.subSat sx), v₁, v₂ => N.ivbinopsx_ sh isub_sat_ sx v₁ v₂
  | .int (.min sx), v₁, v₂ => N.ivbinopsx_ sh imin_ sx v₁ v₂
  | .int (.max sx), v₁, v₂ => N.ivbinopsx_ sh imax_ sx v₁ v₂
  | .int (.avgr sx), v₁, v₂ =>
      match sx with
      | .u => N.ivbinopsx_ sh N.iavgr_ .u v₁ v₂
      | .s => []
  | .int (.q15mulrSat sx), v₁, v₂ =>
      match sx with
      | .s => N.ivbinopsx_ sh N.iq15mulr_sat_ .s v₁ v₂
      | .u => []
  | .int (.relaxedQ15mulr sx), v₁, v₂ =>
      match sx with
      | .s => N.ivbinopsxnd_ sh N.irelaxed_q15mulr_ .s v₁ v₂
      | .u => []
  | .float .add, v₁, v₂ => N.fvbinop_ sh N.fadd_ v₁ v₂
  | .float .sub, v₁, v₂ => N.fvbinop_ sh N.fsub_ v₁ v₂
  | .float .mul, v₁, v₂ => N.fvbinop_ sh N.fmul_ v₁ v₂
  | .float .div, v₁, v₂ => N.fvbinop_ sh N.fdiv_ v₁ v₂
  | .float .min, v₁, v₂ => N.fvbinop_ sh N.fmin_ v₁ v₂
  | .float .max, v₁, v₂ => N.fvbinop_ sh N.fmax_ v₁ v₂
  | .float .pmin, v₁, v₂ => N.fvbinop_ sh N.fpmin_ v₁ v₂
  | .float .pmax, v₁, v₂ => N.fvbinop_ sh N.fpmax_ v₁ v₂
  | .float .relaxedMin, v₁, v₂ => N.fvbinop_ sh N.frelaxed_min_ v₁ v₂
  | .float .relaxedMax, v₁, v₂ => N.fvbinop_ sh N.frelaxed_max_ v₁ v₂

/-- `def $vternop_(Jnn X M, RELAXED_LANESELECT, ...)
    = $ivternopnd_(Jnn X M, $irelaxed_laneselect_, ...)`,
`def $vternop_(Fnn X M, RELAXED_MADD, ...) = $fvternop_(..., $frelaxed_madd_, ...)`,
`RELAXED_NMADD` to `$frelaxed_nmadd_`. -/
-- core-def: vternop_
def vternop_ (sh : Shape) : VTernop → V128Lit → V128Lit → V128Lit → List V128Lit
  | .int .relaxedLaneselect, v₁, v₂, v₃ =>
      N.ivternopnd_ sh N.irelaxed_laneselect_ v₁ v₂ v₃
  | .float .relaxedMadd, v₁, v₂, v₃ => N.fvternop_ sh N.frelaxed_madd_ v₁ v₂ v₃
  | .float .relaxedNmadd, v₁, v₂, v₃ => N.fvternop_ sh N.frelaxed_nmadd_ v₁ v₂ v₃

/-- `def $vtestop_(Jnn X M, ALL_TRUE, v) = $ivtestop_(Jnn X M, $inez_, v)`. -/
-- core-def: vtestop_
def vtestop_ (sh : Shape) : VTestop → V128Lit → Option U32
  | .int .allTrue, v => N.ivtestop_ sh inez_ v

/-- `def $vrelop_(Jnn X M, EQ, ...) = $ivrelop_(Jnn X M, $ieq_, ...)` and its
five `Jnn` siblings; `def $vrelop_(Fnn X M, EQ, ...) = $fvrelop_(..., $feq_, ...)`
and its five `Fnn` siblings. -/
-- core-def: vrelop_
def vrelop_ (sh : Shape) : VRelop → V128Lit → V128Lit → Option V128Lit
  | .int .eq, v₁, v₂ => N.ivrelop_ sh ieq_ v₁ v₂
  | .int .ne, v₁, v₂ => N.ivrelop_ sh ine_ v₁ v₂
  | .int (.lt sx), v₁, v₂ => N.ivrelopsx_ sh ilt_ sx v₁ v₂
  | .int (.gt sx), v₁, v₂ => N.ivrelopsx_ sh igt_ sx v₁ v₂
  | .int (.le sx), v₁, v₂ => N.ivrelopsx_ sh ile_ sx v₁ v₂
  | .int (.ge sx), v₁, v₂ => N.ivrelopsx_ sh ige_ sx v₁ v₂
  | .float .eq, v₁, v₂ => N.fvrelop_ sh N.feq_ v₁ v₂
  | .float .ne, v₁, v₂ => N.fvrelop_ sh N.fne_ v₁ v₂
  | .float .lt, v₁, v₂ => N.fvrelop_ sh N.flt_ v₁ v₂
  | .float .gt, v₁, v₂ => N.fvrelop_ sh N.fgt_ v₁ v₂
  | .float .le, v₁, v₂ => N.fvrelop_ sh N.fle_ v₁ v₂
  | .float .ge, v₁, v₂ => N.fvrelop_ sh N.fge_ v₁ v₂

/-- `def $lcvtop__(Jnn_1 X M_1, Jnn_2 X M_2, EXTEND half sx, c_1)
      = $extend__($lsizenn1(Jnn_1), $lsizenn2(Jnn_2), sx, c_1)`,
`(Jnn_1, Fnn_2, CONVERT half? sx)` to `$convert__`,
`(Fnn_1, Inn_2, TRUNC_SAT sx zero?)` to `$trunc_sat__`,
`(Fnn_1, Inn_2, RELAXED_TRUNC sx zero?)` to `$relaxed_trunc__`,
`(Fnn_1, Fnn_2, DEMOTE ZERO)` to `$demote__`,
`(Fnn_1, Fnn_2, PROMOTE LOW)` to `$promote__`.

The third and fourth equations are written with `Inn_2`, not `Jnn_2`: a packed
target lane has no equation, and `laneIsInn` is that restriction. -/
-- core-def: lcvtop__
def lcvtop__ (sh₁ sh₂ : Shape) : VCvtop → Lane_ sh₁.lane → List (Lane_ sh₂.lane)
  | .jj (.extend _ sx), c₁ =>
      match laneJ? sh₁.lane c₁ with
      | none => []
      | some i₁ =>
          (ofLaneJ? sh₂.lane (N.extend__ sh₁.lane.size sh₂.lane.size sx i₁)).toList
  | .jf (.convert _ sx), c₁ =>
      match laneJ? sh₁.lane c₁ with
      | none => []
      | some i₁ =>
          (ofLaneF? sh₂.lane (N.convert__ sh₁.lane.size sh₂.lane.size sx i₁)).toList
  | .fj (.truncSat sx _), c₁ =>
      if laneIsInn sh₂.lane then
        match laneF? sh₁.lane c₁ with
        | none => []
        | some f₁ =>
            ((N.trunc_sat__ sh₁.lane.size sh₂.lane.size sx f₁).bind
              (ofLaneJ? sh₂.lane)).toList
      else []
  | .fj (.relaxedTrunc sx _), c₁ =>
      if laneIsInn sh₂.lane then
        match laneF? sh₁.lane c₁ with
        | none => []
        | some f₁ =>
            ((N.relaxed_trunc__ sh₁.lane.size sh₂.lane.size sx f₁).bind
              (ofLaneJ? sh₂.lane)).toList
      else []
  | .ff (.demote _), c₁ =>
      match laneF? sh₁.lane c₁ with
      | none => []
      | some f₁ =>
          (N.demote__ sh₁.lane.size sh₂.lane.size f₁).filterMap (ofLaneF? sh₂.lane)
  | .ff (.promote h), c₁ =>
      match h, laneF? sh₁.lane c₁ with
      | .low, some f₁ =>
          (N.promote__ sh₁.lane.size sh₂.lane.size f₁).filterMap (ofLaneF? sh₂.lane)
      | _, _ => []

/-- `def $vcvtop__(Lnn_1 X M, Lnn_2 X M, vcvtop, v_1) = v
      -- if $halfop(...) = eps /\ $zeroop(...) = eps
      -- if c** = $setproduct_(lane_(Lnn_2), $lcvtop__(..., c_1)*)
      -- if v <- $inv_lanes_(Lnn_2 X M, c*)*`,
the `half` equation, which slices `$lanes_(...)[$half(half, 0, M_2) : M_2]`, and
the `ZERO` equation, which appends `[$zero(Lnn_2)]^M_1`.

See the file header: the source declares the result `vec_(V128)` while binding
it with `v <- ...`, and this returns the candidate set. -/
-- core-def: vcvtop__
def vcvtop__ (sh₁ sh₂ : Shape) (op : VCvtop) (v₁ : V128Lit) : List V128Lit :=
  match halfop sh₁ sh₂ op, zeroop sh₁ sh₂ op with
  | some none, some none =>
      if sh₁.dim = sh₂.dim then
        (setproduct ((N.lanes_ sh₁ v₁).map (fun c => N.lcvtop__ sh₁ sh₂ op c))).map
          (N.inv_lanes_ sh₂)
      else []
  | some (some h), _ =>
      match slice? (N.lanes_ sh₁ v₁) (half h 0 sh₂.dim.toNat) sh₂.dim.toNat with
      | none => []
      | some c₁s =>
          (setproduct (c₁s.map (fun c => N.lcvtop__ sh₁ sh₂ op c))).map
            (N.inv_lanes_ sh₂)
  | _, some (some _) =>
      (setproduct
        ((N.lanes_ sh₁ v₁).map (fun c => N.lcvtop__ sh₁ sh₂ op c) ++
          List.replicate sh₁.dim.toNat [zero_ sh₂.lane])).map (N.inv_lanes_ sh₂)
  | _, _ => []

/-- `def $vshiftop_(Jnn X M, SHL, v, i) = $ivshiftop_(Jnn X M, $ishl_, v, i)`,
`def $vshiftop_(Jnn X M, SHR sx, v, i) = $ivshiftopsx_(Jnn X M, $ishr_, sx, v, i)`. -/
-- core-def: vshiftop_
def vshiftop_ (sh : IShape) : VShiftop → V128Lit → U32 → Option V128Lit
  | .shl, v, i => N.ivshiftop_ sh.val N.ishl_ v i
  | .shr sx, v, i => N.ivshiftopsx_ sh.val N.ishr_ sx v i

/-- `def $vbitmaskop_(Jnn X M, v) = $ivbitmaskop_(Jnn X M, v)`. -/
-- core-def: vbitmaskop_
def vbitmaskop_ (sh : IShape) (v : V128Lit) : Option U32 :=
  N.ivbitmaskop_ sh.val v

/-- `def $vswizzlop_(I8 X M, SWIZZLE, v_1, v_2)
      = $ivswizzlop_(I8 X M, $iswizzle_lane_, v_1, v_2)`,
`RELAXED_SWIZZLE` to `$irelaxed_swizzle_lane_`. -/
-- core-def: vswizzlop_
def vswizzlop_ (sh : BShape) : VSwizzlop → V128Lit → V128Lit → Option V128Lit
  | .swizzle, v₁, v₂ =>
      N.ivswizzlop_ sh.val (fun w cs i => some (iswizzle_lane_ w cs i)) v₁ v₂
  | .relaxedSwizzle, v₁, v₂ =>
      N.ivswizzlop_ sh.val N.irelaxed_swizzle_lane_ v₁ v₂

/-- `def $vshufflop_(I8 X M, i*, v_1, v_2) = $ivshufflop_(I8 X M, i*, v_1, v_2)`. -/
-- core-def: vshufflop_
def vshufflop_ (sh : BShape) (is : List LaneIdx) (v₁ v₂ : V128Lit) :
    Option V128Lit :=
  N.ivshufflop_ sh.val is v₁ v₂

/-- `def $vnarrowop__(Jnn_1 X M_1, Jnn_2 X M_2, sx, v_1, v_2) = v
      -- if c_1* = $lanes_(Jnn_1 X M_1, v_1)
      -- if c_2* = $lanes_(Jnn_1 X M_1, v_2)
      -- if c'_1* = $narrow__($lsize(Jnn_1), $lsize(Jnn_2), sx, c_1)*
      -- if c'_2* = $narrow__($lsize(Jnn_1), $lsize(Jnn_2), sx, c_2)*
      -- if v = $inv_lanes_(Jnn_2 X M_2, c'_1* ++ c'_2*)`.

Both operands are read at the OPERAND shape `Jnn_1 X M_1`, as the source
writes. -/
-- core-def: vnarrowop__
def vnarrowop__ (sh₁ sh₂ : IShape) (sx : Sx) (v₁ v₂ : V128Lit) :
    Option V128Lit := do
  let c₁s ← N.intLanes sh₁.val v₁
  let c₂s ← N.intLanes sh₁.val v₂
  let n := N.narrow__ sh₁.val.lane.size sh₂.val.lane.size sx
  N.intVec sh₂.val (c₁s.map n ++ c₂s.map n)

/-! ## Extended lanewise operations -/

/-- `def $ivextunop__(Jnn_1 X M_1, Jnn_2 X M_2, def $f_, sx, v_1)
      = $inv_lanes_(Jnn_2 X M_2, c*)
      -- if c'_1* = $extend__($lsizenn1(Jnn_1), $lsizenn2(Jnn_2), sx, c_1)*
      -- if c* = $f_($lsizenn2(Jnn_2), c'_1*)`. -/
-- core-def: ivextunop__
def ivextunop__ (sh₁ sh₂ : Shape)
    (f : (w : Nat) → List (IN w) → Option (List (IN w))) (sx : Sx)
    (v₁ : V128Lit) : Option V128Lit := do
  let c₁s ← N.intLanes sh₁ v₁
  let cs ← f sh₂.lane.size
    (c₁s.map (N.extend__ sh₁.lane.size sh₂.lane.size sx))
  N.intVec sh₂ cs

/-- `def $ivextbinop__(Jnn_1 X M_1, Jnn_2 X M_2, def $f_, sx_1, sx_2, i, k, v_1, v_2)
      = $inv_lanes_(Jnn_2 X M_2, c*)
      -- if c_1* = $lanes_(Jnn_1 X M_1, v_1)[i : k]
      -- if c_2* = $lanes_(Jnn_1 X M_1, v_2)[i : k]
      -- if c'_1* = $extend__(..., sx_1, c_1)*
      -- if c'_2* = $extend__(..., sx_2, c_2)*
      -- if c* = $f_($lsizenn2(Jnn_2), c'_1*, c'_2*)`.

The source types the slice bounds `i` and `k` as `laneidx`; both call sites in
`$vextbinop__` pass a dimension or a `$half` offset, and they are `Nat` here so
that no `u8` bound has to be discharged at a site the source never approaches. -/
-- core-def: ivextbinop__
def ivextbinop__ (sh₁ sh₂ : Shape)
    (f : (w : Nat) → List (IN w) → List (IN w) → Option (List (IN w)))
    (sx₁ sx₂ : Sx) (i k : Nat) (v₁ v₂ : V128Lit) : Option V128Lit := do
  let l₁ ← N.intLanes sh₁ v₁
  let l₂ ← N.intLanes sh₁ v₂
  let c₁s ← slice? l₁ i k
  let c₂s ← slice? l₂ i k
  let cs ← f sh₂.lane.size
    (c₁s.map (N.extend__ sh₁.lane.size sh₂.lane.size sx₁))
    (c₂s.map (N.extend__ sh₁.lane.size sh₂.lane.size sx₂))
  N.intVec sh₂ cs

/-- `def $ivadd_pairwise_(N, i*) = $iadd_(N, j_1, j_2)*
      -- if $concat_(N, (j_1 j_2)*) = i*`. -/
-- core-def: ivadd_pairwise_
def ivadd_pairwise_ (w : Nat) (is : List (IN w)) : Option (List (IN w)) :=
  (pairs is).map (fun ps => ps.map (fun p => iadd_ w p.1 p.2))

/-- `def $ivmul_(N, i_1*, i_2*) = $imul_(N, i_1, i_2)*`. -/
-- core-def: ivmul_
def ivmul_ (w : Nat) (i₁s i₂s : List (IN w)) : Option (List (IN w)) :=
  zipWith? (imul_ w) i₁s i₂s

/-- `def $ivdot_(N, i_1*, i_2*) = $iadd_(N, j_1, j_2)*
      -- if $concat_(iN(N), (j_1 j_2)*) = $imul_(N, i_1, i_2)*`. -/
-- core-def: ivdot_
def ivdot_ (w : Nat) (i₁s i₂s : List (IN w)) : Option (List (IN w)) := do
  let ms ← zipWith? (imul_ w) i₁s i₂s
  let ps ← pairs ms
  pure (ps.map (fun p => iadd_ w p.1 p.2))

/-- `def $ivdot_sat_(N, i_1*, i_2*) = $iadd_sat_(N, S, j_1, j_2)*
      -- if $concat_(iN(N), (j_1 j_2)*) = $imul_(N, i_1, i_2)*`. -/
-- core-def: ivdot_sat_
def ivdot_sat_ (w : Nat) (i₁s i₂s : List (IN w)) : Option (List (IN w)) := do
  let ms ← zipWith? (imul_ w) i₁s i₂s
  let ps ← pairs ms
  pure (ps.map (fun p => iadd_sat_ w .s p.1 p.2))

/-- `$vextunop__` at plain shapes.  `$vextternop__` calls it at an intermediate
shape that the source names only by its lane width, so it cannot be an `ishape`
subtype without a proof obligation the source does not state. -/
def vextunopShape (sh₁ sh₂ : Shape) : VExtUnop → V128Lit → Option V128Lit
  | .extaddPairwise sx, v₁ => N.ivextunop__ sh₁ sh₂ ivadd_pairwise_ sx v₁

/-- `$vextbinop__` at plain shapes; see `vextunopShape`. -/
def vextbinopShape (sh₁ sh₂ : Shape) :
    VExtBinop → V128Lit → V128Lit → Option V128Lit
  | .extmul h sx, v₁, v₂ =>
      N.ivextbinop__ sh₁ sh₂ ivmul_ sx sx (half h 0 sh₂.dim.toNat)
        sh₂.dim.toNat v₁ v₂
  | .dot sx, v₁, v₂ =>
      match sx with
      | .s => N.ivextbinop__ sh₁ sh₂ ivdot_ .s .s 0 sh₁.dim.toNat v₁ v₂
      | .u => none
  | .relaxedDot sx, v₁, v₂ =>
      match sx with
      | .s =>
          N.ivextbinop__ sh₁ sh₂ ivdot_sat_ .s (relaxed2 N.nd N.r_idot .s .u) 0
            sh₁.dim.toNat v₁ v₂
      | .u => none

/-- `def $vextunop__(Jnn_1 X M_1, Jnn_2 X M_2, EXTADD_PAIRWISE sx, v_1)
      = $ivextunop__(Jnn_1 X M_1, Jnn_2 X M_2, $ivadd_pairwise_, sx, v_1)`. -/
-- core-def: vextunop__
def vextunop__ (sh₁ sh₂ : IShape) (op : VExtUnop) (v₁ : V128Lit) :
    Option V128Lit :=
  N.vextunopShape sh₁.val sh₂.val op v₁

/-- `def $vextbinop__(Jnn_1 X M_1, Jnn_2 X M_2, EXTMUL half sx, v_1, v_2)
      = $ivextbinop__(..., $ivmul_, sx, sx, $half(half, 0, M_2), M_2, v_1, v_2)`,
`DOT S` to `$ivdot_` with `S, S, 0, M_1`,
`RELAXED_DOT S` to `$ivdot_sat_` with `S, $relaxed2($R_idot, sx, S, U), 0, M_1`. -/
-- core-def: vextbinop__
def vextbinop__ (sh₁ sh₂ : IShape) (op : VExtBinop) (v₁ v₂ : V128Lit) :
    Option V128Lit :=
  N.vextbinopShape sh₁.val sh₂.val op v₁ v₂

/-- `def $vextternop__(Jnn_1 X M_1, Jnn_2 X M_2, RELAXED_DOT_ADD S, c_1, c_2, c_3) = c
      -- if $jsizenn(Jnn) = $(2*$lsizenn1(Jnn_1))
      -- if M = $(2*M_2)
      -- if c' = $vextbinop__(Jnn_1 X M_1, Jnn X M, RELAXED_DOT S, c_1, c_2)
      -- if c'' = $vextunop__(Jnn X M, Jnn_2 X M_2, EXTADD_PAIRWISE S, c')
      -- if c <- $vbinop_(Jnn_2 X M_2, ADD, c'', c_3)`.

The first two premises determine the intermediate shape `Jnn X M`; the last
binds `c` from a sequence, and `$vbinop_(Jnn X M, ADD, ...)` is `$ivbinop_`,
whose value is a single vector, so the equation defines `c` exactly when that
sequence is a singleton. -/
-- core-def: vextternop__
def vextternop__ (sh₁ sh₂ : IShape) :
    VExtTernop → V128Lit → V128Lit → V128Lit → Option V128Lit
  | .relaxedDotAdd sx, v₁, v₂, v₃ =>
      match sx with
      | .u => none
      | .s => do
          let lt ← jnnLaneOfSize (2 * sh₁.val.lane.size)
          let m ← dimOfNat (2 * sh₂.val.dim.toNat)
          let shM : Shape := { lane := lt, dim := m }
          let c' ← N.vextbinopShape sh₁.val shM (.relaxedDot .s) v₁ v₂
          let c'' ← N.vextunopShape shM sh₂.val (.extaddPairwise .s) c'
          match N.vbinop_ sh₂.val (.int .add) c'' v₃ with
          | [c] => some c
          | _ => none

end Numerics

/-! ## Sanity checks

Kernel-checked evaluations, not tests.  Every transcription above that does NOT
read a `hint(builtin)` parameter computes, and these pin down what it computes;
each names the source equation it discriminates.  The operators that do read a
parameter cannot be evaluated here, and no attempt is made to fake one. -/

/-- `def $half(LOW, i, j) = i`. -/
example : Numerics.half .low 0 4 = 0 := by decide

/-- `def $half(HIGH, i, j) = j`. -/
example : Numerics.half .high 0 4 = 4 := by decide

/-- `$setproduct_` turns a sequence of per-lane result SETS into the set of
result sequences: `[{1,2}, {3}]` becomes `{[1,3], [2,3]}`. -/
example : setproduct ([[1, 2], [3]] : List (List Nat)) = [[1, 3], [2, 3]] := by
  decide

/-- `$setproduct_(X, eps) = (eps)`: the empty sequence of sets has exactly one
product, the empty sequence -- which is why a zero-lane shape does not silently
produce no result at all. -/
example : setproduct ([] : List (List Nat)) = [[]] := by decide

/-- `-- if $concat_(N, (j_1 j_2)*) = i*` pairs a sequence up ... -/
example : pairs ([1, 2, 3, 4] : List Nat) = some [(1, 2), (3, 4)] := by decide

/-- ... and has no solution at an odd length, which is where `$ivdot_` and
`$ivadd_pairwise_` are undefined. -/
example : pairs ([1, 2, 3] : List Nat) = none := by decide

/-- `$signed_` reads the top bit as a sign: `255 : iN(8)` is `-1`. -/
example : Numerics.signed_ 8 ⟨255, by decide⟩ = -1 := by decide

/-- ... and leaves a value below `2^(N-1)` alone. -/
example : Numerics.signed_ 8 ⟨127, by decide⟩ = 127 := by decide

/-- `def $sat_s_(N, i) = $(2^(N-1) - 1)  -- if i > $(2^(N-1) - 1)`. -/
example : Numerics.sat_s_ 8 200 = 127 := by decide

/-- `def $sat_u_(N, i) = 0  -- if i < 0`. -/
example : Numerics.sat_u_ 8 (-1) = 0 := by decide

/-- `def $iadd_(N, i_1, i_2) = $((i_1 + i_2) \ 2^N)` wraps. -/
example :
    Numerics.iadd_ 8 ⟨255, by decide⟩ ⟨2, by decide⟩ = ⟨1, by decide⟩ := by decide

/-- `def $idiv_(N, S, i_1, i_2) = eps` at the overflowing quotient
`-2^(N-1) / -1`. -/
example : Numerics.idiv_ 8 .s ⟨128, by decide⟩ ⟨255, by decide⟩ = none := by
  decide

/-- ... while every other signed division has a value. -/
example :
    Numerics.idiv_ 8 .s ⟨249, by decide⟩ ⟨2, by decide⟩
      = some ⟨253, by decide⟩ := by decide

/-- `def $iswizzle_lane_(N, c*, i) = c*[i]  -- if i < |c*|`. -/
example :
    Numerics.iswizzle_lane_ 8 [⟨7, by decide⟩, ⟨9, by decide⟩] ⟨1, by decide⟩
      = ⟨9, by decide⟩ := by decide

/-- `def $iswizzle_lane_(N, c*, i) = 0  -- otherwise`. -/
example :
    Numerics.iswizzle_lane_ 8 [⟨7, by decide⟩, ⟨9, by decide⟩] ⟨5, by decide⟩
      = inZero 8 := by decide

/-- `def $zeroop(Fnn_1 X M_1, Jnn_2 X M_2, TRUNC_SAT sx zero?) = zero?`, here
the `F64X2 -> I32X4` form that carries `ZERO`. -/
example :
    Numerics.zeroop { lane := .num .f64, dim := .d2 } { lane := .num .i32, dim := .d4 }
        (.fj (.truncSat .s (some .zero)))
      = some (some .zero) := by decide

/-- `def $halfop(Fnn_1 X M_1, Jnn_2 X M_2, TRUNC_SAT sx zero?) = eps` on the
same operator: a `TRUNC_SAT` selects no half. -/
example :
    Numerics.halfop { lane := .num .f64, dim := .d2 } { lane := .num .i32, dim := .d4 }
        (.fj (.truncSat .s (some .zero)))
      = some none := by decide

/-- `def $halfop(Jnn_1 X M_1, Jnn_2 X M_2, EXTEND half sx) = half`. -/
example :
    Numerics.halfop { lane := .pack .i8, dim := .d16 } { lane := .pack .i16, dim := .d8 }
        (.jj (.extend .high .s))
      = some (some .high) := by decide

/-- `$halfop` has no equation at an operand/result family the listed equations
do not cover, and `$vcvtop__` is undefined there in consequence. -/
example :
    Numerics.halfop { lane := .num .f32, dim := .d4 } { lane := .num .f32, dim := .d4 }
        (.jj (.extend .low .s))
      = none := by decide

/-- `def $ivmul_(N, i_1*, i_2*) = $imul_(N, i_1, i_2)*`, and it is undefined on
sequences of different lengths. -/
example :
    Numerics.ivmul_ 8 [⟨3, by decide⟩] [⟨4, by decide⟩, ⟨5, by decide⟩] = none := by
  decide

/-- `def $ivdot_(N, i_1*, i_2*) = $iadd_(N, j_1, j_2)*
    -- if $concat_(iN(N), (j_1 j_2)*) = $imul_(N, i_1, i_2)*`:
`(1*2) + (3*4) = 14`. -/
example :
    Numerics.ivdot_ 8 [⟨1, by decide⟩, ⟨3, by decide⟩]
        [⟨2, by decide⟩, ⟨4, by decide⟩]
      = some [⟨14, by decide⟩] := by decide

/-- `$s33_to_u32` is the identity where `5.2-binary.types.spectec`'s guard
`x33 >= 0` holds ... -/
example : Numerics.s33_to_u32 ⟨7, by decide⟩ = some ⟨7, by decide⟩ := by decide

/-- ... and has no value where it does not. -/
example : Numerics.s33_to_u32 ⟨-1, by decide⟩ = none := by decide

/-- `def $sx(consttype) = eps`, `def $sx(packtype) = S`. -/
example : Numerics.sx (.pack .i8) = some (some .s) := by decide

/-- ... and no equation at a `reftype`. -/
example : Numerics.sx (.val .bot) = none := by decide

end WasmGemmGnaf.Wasm.Core.Exec
