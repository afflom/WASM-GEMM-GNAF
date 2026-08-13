/-
  Wasm/Core/Numerics.lean --- the operator semantics the Core 3.0 step relation
  calls out to.

  NORMATIVE SOURCE.

      vendor/wasm-spec/specification/wasm-3.0/3.1-numerics.scalar.spectec
      vendor/wasm-spec/specification/wasm-3.0/3.2-numerics.vector.spectec

  SCOPE, STATED PLAINLY, BECAUSE THIS IS THE ONE PLACE WHERE A READER COULD BE
  MISLED.

  The pinned SpecTec sources do NOT define every numeric primitive they declare.
  A large family carries `hint(builtin)` -- the source declares the signature and
  says, in effect, "the prose specification fixes this".  `3.1` marks
  `$ibytes_`, `$fbytes_`, `$nbytes_`, `$vbytes_`, `$zbytes_`, `$iclz_`,
  `$ictz_`, `$ipopcnt_`, `$iand_`, `$ior_`, `$ixor_`, `$ishl_`, `$ishr_`,
  `$irotl_`, `$irotr_`, every `$f...` floating-point operation, and every
  conversion `$wrap__`, `$extend__`, `$trunc__`, `$trunc_sat__`, `$convert__`,
  `$promote__`, `$demote__`, `$reinterpret__` exactly that way; `3.2` marks
  `$lanes_` and `$inv_lanes_` the same way.

  Those primitives are therefore PARAMETERS here, collected in `Numerics`.  They
  are parameters, not axioms: nothing in this development asserts anything about
  them, no proof depends on a property of them, and `xtask axioms` sees no new
  constant.  A `Numerics` is data a caller supplies.

  `Numerics` additionally carries the seventeen VECTOR operator dispatchers of
  `3.2` (`$vvunop_` ... `$vcvtop__`).  Those the pinned source DOES define, in
  terms of higher-order lanewise combinators.  They are NOT transcribed here, and
  carrying them as parameters is how that gap is recorded rather than hidden.
  Anyone reading the step relation should read this paragraph as: the vector
  instruction rules of `4.3` are transcribed, and the lanewise meaning of the
  vector operators they invoke is not.

  Everything `3.1` states by equation IS transcribed below, on top of those
  parameters: `$signed_`, `$inv_signed_`, `$sat_u_`, `$sat_s_`, `$bool`,
  `$ineg_`, `$iabs_`, `$iextend_`, `$iadd_`, `$isub_`, `$imul_`, `$idiv_`,
  `$irem_`, `$imin_`, `$imax_`, `$iadd_sat_`, `$isub_sat_`, `$ieqz_`, `$inez_`,
  `$ieq_`, `$ine_`, `$ilt_`, `$igt_`, `$ile_`, `$ige_`, `$lpacknum_`,
  `$cpacknum_`, `$lunpacknum_`, `$cunpacknum_`, and the operator dispatch
  `$unop_`, `$binop_`, `$testop_`, `$relop_`, `$cvtop__`.

  TOTALITY.  Where the source gives no equation for an argument combination --
  `$unop_(Inn, ABS, _)`, say, which is ill-formed because `ABS` is an
  `unop_(Fnn)` -- the transcription returns the empty sequence (for the
  set-valued operators) or `none` (for the single-valued ones).  That is the
  source's own reading of a missing equation, and `Instr.wf` excludes every such
  instruction anyway.  No junk value is ever invented for a case the source
  defines.
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

/-! ## The primitives the pinned sources leave to the prose

Every field below transcribes one `hint(builtin)` declaration of `3.1` or `3.2`,
or one vector dispatcher of `3.2` that this file does not transcribe.  The
signature is the source's; the meaning is the caller's. -/

/-- The numeric primitives of `3.1`/`3.2` that the pinned SpecTec sources declare
without equations, together with the vector operator dispatchers of `3.2` that
this development has not transcribed.  See the file header. -/
structure Numerics where
  /-- `def $ibytes_(N, iN(N)) : byte*`. -/
  ibytes_ : (N : Nat) → IN N → List Byte
  /-- `def $nbytes_(numtype, num_(numtype)) : byte*`. -/
  nbytes_ : (nt : NumType) → Num_ nt → List Byte
  /-- `def $vbytes_(vectype, vec_(vectype)) : byte*`. -/
  vbytes_ : (vt : VecType) → VecLit vt.toVnn → List Byte
  /-- `def $zbytes_(storagetype, lit_(storagetype)) : byte*`. -/
  zbytes_ : (zt : StorageType) → Lit_ zt → List Byte
  /-- `def $iclz_(N, iN(N)) : iN(N)`. -/
  iclz_ : (N : Nat) → IN N → IN N
  /-- `def $ictz_(N, iN(N)) : iN(N)`. -/
  ictz_ : (N : Nat) → IN N → IN N
  /-- `def $ipopcnt_(N, iN(N)) : iN(N)`. -/
  ipopcnt_ : (N : Nat) → IN N → IN N
  /-- `def $iand_(N, iN(N), iN(N)) : iN(N)`. -/
  iand_ : (N : Nat) → IN N → IN N → IN N
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
  /-- `def $wrap__(M, N, iN(M)) : iN(N)`. -/
  wrap__ : (M N : Nat) → IN M → IN N
  /-- `def $extend__(M, N, sx, iN(M)) : iN(N)`. -/
  extend__ : (M N : Nat) → Sx → IN M → IN N
  /-- `def $trunc__(M, N, sx, fN(M)) : iN(N)?`. -/
  trunc__ : (M N : Nat) → Sx → FN M → Option (IN N)
  /-- `def $trunc_sat__(M, N, sx, fN(M)) : iN(N)?`. -/
  trunc_sat__ : (M N : Nat) → Sx → FN M → Option (IN N)
  /-- `def $convert__(M, N, sx, iN(M)) : fN(N)`. -/
  convert__ : (M N : Nat) → Sx → IN M → FN N
  /-- `def $promote__(M, N, fN(M)) : fN(N)*`. -/
  promote__ : (M N : Nat) → FN M → List (FN N)
  /-- `def $demote__(M, N, fN(M)) : fN(N)*`. -/
  demote__ : (M N : Nat) → FN M → List (FN N)
  /-- `def $reinterpret__(numtype_1, numtype_2, num_(numtype_1)) :
      num_(numtype_2)`. -/
  reinterpret__ : (nt₁ nt₂ : NumType) → Num_ nt₁ → Num_ nt₂
  /-- `def $lanes_(shape, vec_(V128)) : lane_($lanetype(shape))*`. -/
  lanes_ : (sh : Shape) → V128Lit → List (Lane_ sh.lane)
  /-- `def $inv_lanes_(shape, lane_($lanetype(shape))*) : vec_(V128)`. -/
  inv_lanes_ : (sh : Shape) → List (Lane_ sh.lane) → V128Lit
  /-- `def $vvunop_(vectype, vvunop, vec_(vectype)) : vec_(vectype)*`.
  Defined by `3.2`; NOT transcribed. -/
  vvunop_ : VecType → VVUnop → V128Lit → List V128Lit
  /-- `def $vvbinop_(...)`.  Defined by `3.2`; NOT transcribed. -/
  vvbinop_ : VecType → VVBinop → V128Lit → V128Lit → List V128Lit
  /-- `def $vvternop_(...)`.  Defined by `3.2`; NOT transcribed. -/
  vvternop_ : VecType → VVTernop → V128Lit → V128Lit → V128Lit → List V128Lit
  /-- `def $vunop_(shape, vunop_(shape), vec_(V128)) : vec_(V128)*`.
  Defined by `3.2`; NOT transcribed. -/
  vunop_ : Shape → VUnop → V128Lit → List V128Lit
  /-- `def $vbinop_(...)`.  Defined by `3.2`; NOT transcribed. -/
  vbinop_ : Shape → VBinop → V128Lit → V128Lit → List V128Lit
  /-- `def $vternop_(...)`.  Defined by `3.2`; NOT transcribed. -/
  vternop_ : Shape → VTernop → V128Lit → V128Lit → V128Lit → List V128Lit
  /-- `def $vtestop_(shape, vtestop_(shape), vec_(V128)) : u32`.
  Defined by `3.2`; NOT transcribed. -/
  vtestop_ : Shape → VTestop → V128Lit → U32
  /-- `def $vrelop_(...) : vec_(V128)`.  Defined by `3.2`; NOT transcribed. -/
  vrelop_ : Shape → VRelop → V128Lit → V128Lit → V128Lit
  /-- `def $vshiftop_(...) : vec_(V128)`.  Defined by `3.2`; NOT transcribed. -/
  vshiftop_ : IShape → VShiftop → V128Lit → U32 → V128Lit
  /-- `def $vbitmaskop_(shape, vec_(V128)) : u32`.
  Defined by `3.2`; NOT transcribed. -/
  vbitmaskop_ : IShape → V128Lit → U32
  /-- `def $vswizzlop_(...) : vec_(V128)`.  Defined by `3.2`; NOT transcribed. -/
  vswizzlop_ : BShape → VSwizzlop → V128Lit → V128Lit → V128Lit
  /-- `def $vshufflop_(shape, laneidx*, vec_(V128), vec_(V128)) : vec_(V128)`.
  Defined by `3.2`; NOT transcribed. -/
  vshufflop_ : BShape → List LaneIdx → V128Lit → V128Lit → V128Lit
  /-- `def $vextunop__(...)`.  Defined by `3.2`; NOT transcribed.  The argument
  order is the source's: operand shape first, result shape second. -/
  vextunop__ : IShape → IShape → VExtUnop → V128Lit → V128Lit
  /-- `def $vextbinop__(...)`.  Defined by `3.2`; NOT transcribed. -/
  vextbinop__ : IShape → IShape → VExtBinop → V128Lit → V128Lit → V128Lit
  /-- `def $vextternop__(...)`.  Defined by `3.2`; NOT transcribed. -/
  vextternop__ : IShape → IShape → VExtTernop → V128Lit → V128Lit → V128Lit →
    V128Lit
  /-- `def $vnarrowop__(...)`.  Defined by `3.2`; NOT transcribed. -/
  vnarrowop__ : IShape → IShape → Sx → V128Lit → V128Lit → V128Lit
  /-- `def $vcvtop__(...)`.  Defined by `3.2`; NOT transcribed. -/
  vcvtop__ : Shape → Shape → VCvtop → V128Lit → V128Lit

namespace Numerics

variable (N : Numerics)

/-! ## Signed numbers

`def $signed_(N, nat) : int` and its inverse. -/

/-- `def $signed_(N, i) = i           -- if $(i < 2^(N-1))`,
    `def $signed_(N, i) = $(i - 2^N)  -- if $(2^(N-1) <= i < 2^N)`. -/
def signed_ (w : Nat) (i : IN w) : Int :=
  if i.val < 2 ^ (w - 1) then (i.val : Int) else (i.val : Int) - ((2 ^ w : Nat) : Int)

/-- `def $inv_signed_(N, i) = i          -- if $(0 <= i < 2^(N-1))`,
    `def $inv_signed_(N, i) = $(i + 2^N) -- if $(-2^(N-1) <= i < 0)`.

Transcribed as the total function `i mod 2^N`, whose value is in `[0, 2^N)` and
therefore coincides with the source's first equation on `0 <= i < 2^(N-1)` and
with its second on `-2^(N-1) <= i < 0`.  A total extension is used rather than an
`Option` because the source's own uses (`table.grow-fail`, `memory.grow-fail`,
`$iextend_`) all lie inside the stated domain. -/
def inv_signed_ (w : Nat) (i : Int) : IN w :=
  ⟨(i % ((2 ^ w : Nat) : Int)).toNat, by
    have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := by
      have := two_pow_pos w
      omega
    have h0 : (0 : Int) ≤ i % ((2 ^ w : Nat) : Int) := Int.emod_nonneg i (by omega)
    have h1 : i % ((2 ^ w : Nat) : Int) < ((2 ^ w : Nat) : Int) :=
      Int.emod_lt_of_pos i hpos
    omega⟩

/-! ## Saturation -/

/-- `def $sat_u_(N, i) = 0  -- if i < 0`, `= $(2^N - 1)  -- if i > $(2^N - 1)`,
`= i  -- otherwise`. -/
def sat_u_ (w : Nat) (i : Int) : Nat :=
  if i < 0 then 0
  else if i > ((2 ^ w : Nat) : Int) - 1 then 2 ^ w - 1
  else i.toNat

/-- `def $sat_s_(N, i) = $(-2^(N-1))  -- if i < $(-2^(N-1))`,
`= $(2^(N-1) - 1)  -- if i > $(2^(N-1) - 1)`, `= i  -- otherwise`. -/
def sat_s_ (w : Nat) (i : Int) : Int :=
  if i < -((2 ^ (w - 1) : Nat) : Int) then -((2 ^ (w - 1) : Nat) : Int)
  else if i > ((2 ^ (w - 1) : Nat) : Int) - 1 then ((2 ^ (w - 1) : Nat) : Int) - 1
  else i

/-- `def $bool(false) = 0`, `def $bool(true) = 1`. -/
def bool_ (b : Bool) : U32 := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- `iN(N)` from a natural, reduced modulo `2^N`.  Every use below is a source
equation whose right-hand side is already written `$(... \ 2^N)`. -/
def ofNatWrap (w : Nat) (n : Nat) : IN w := ⟨n % 2 ^ w, Nat.mod_lt _ (two_pow_pos w)⟩

/-! ## Integer operations

The equations `3.1` gives.  The remainder of the integer family is a parameter;
see the file header. -/

/-- `def $ineg_(N, i_1) = $((2^N - i_1) \ 2^N)`. -/
def ineg_ (w : Nat) (i : IN w) : IN w := ofNatWrap w (2 ^ w - i.val)

/-- `def $iabs_(N, i_1) = i_1  -- if $signed_(N, i_1) >= 0`,
`= $ineg_(N, i_1)  -- otherwise`. -/
def iabs_ (w : Nat) (i : IN w) : IN w :=
  if 0 ≤ signed_ w i then i else ineg_ w i

/-- `def $iextend_(N, M, U, i) = $(i \ 2^M)`,
`def $iextend_(N, M, S, i) = $inv_signed_(N, $signed_(M, $(i \ 2^M)))`. -/
def iextend_ (w m : Nat) (sx : Sx) (i : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (i.val % 2 ^ m)
  | .s => inv_signed_ w (signed_ m (ofNatWrap m (i.val % 2 ^ m)))

/-- `def $iadd_(N, i_1, i_2) = $((i_1 + i_2) \ 2^N)`. -/
def iadd_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (i₁.val + i₂.val)

/-- `def $isub_(N, i_1, i_2) = $((2^N + i_1 - i_2) \ 2^N)`. -/
def isub_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (2 ^ w + i₁.val - i₂.val)

/-- `def $imul_(N, i_1, i_2) = $((i_1 * i_2) \ 2^N)`. -/
def imul_ (w : Nat) (i₁ i₂ : IN w) : IN w := ofNatWrap w (i₁.val * i₂.val)

/-- `def $idiv_(N, U, i_1, 0) = eps`,
`def $idiv_(N, U, i_1, i_2) = $truncz($(i_1 / i_2))`,
`def $idiv_(N, S, i_1, 0) = eps`,
`def $idiv_(N, S, i_1, i_2) = eps  -- if $($signed_(N,i_1)/$signed_(N,i_2)) = 2^(N-1)`,
`def $idiv_(N, S, i_1, i_2) = $inv_signed_(N, $truncz($($signed_(N,i_1)/$signed_(N,i_2))))`.

`$truncz` of a rational is truncation toward zero; on naturals that is `Nat`
division and on integers it is `Int.tdiv`, which is how the two equations are
written here. -/
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
def irem_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : Option (IN w) :=
  match sx with
  | .u => if i₂.val = 0 then none else some (ofNatWrap w (i₁.val % i₂.val))
  | .s =>
      if i₂.val = 0 then none
      else some (inv_signed_ w (Int.tmod (signed_ w i₁) (signed_ w i₂)))

/-- `def $imin_(N, U, i_1, i_2) = i_1  -- if i_1 <= i_2`, `= i_2  -- if i_1 > i_2`;
`def $imin_(N, S, i_1, i_2) = i_1  -- if $signed_ <= $signed_`, `= i_2  -- otherwise`. -/
def imin_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => if i₁.val ≤ i₂.val then i₁ else i₂
  | .s => if signed_ w i₁ ≤ signed_ w i₂ then i₁ else i₂

/-- `def $imax_(N, U, i_1, i_2) = i_1  -- if i_1 >= i_2`, `= i_2  -- if i_1 < i_2`;
`def $imax_(N, S, i_1, i_2) = i_1  -- if $signed_ >= $signed_`, `= i_2  -- otherwise`. -/
def imax_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => if i₁.val ≥ i₂.val then i₁ else i₂
  | .s => if signed_ w i₁ ≥ signed_ w i₂ then i₁ else i₂

/-- `def $iadd_sat_(N, U, i_1, i_2) = $sat_u_(N, $(i_1 + i_2))`,
`def $iadd_sat_(N, S, i_1, i_2) = $inv_signed_(N, $sat_s_(N, $($signed_ + $signed_)))`. -/
def iadd_sat_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (sat_u_ w ((i₁.val : Int) + (i₂.val : Int)))
  | .s => inv_signed_ w (sat_s_ w (signed_ w i₁ + signed_ w i₂))

/-- `def $isub_sat_(N, U, i_1, i_2) = $sat_u_(N, $(i_1 - i_2))`,
`def $isub_sat_(N, S, i_1, i_2) = $inv_signed_(N, $sat_s_(N, $($signed_ - $signed_)))`. -/
def isub_sat_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : IN w :=
  match sx with
  | .u => ofNatWrap w (sat_u_ w ((i₁.val : Int) - (i₂.val : Int)))
  | .s => inv_signed_ w (sat_s_ w (signed_ w i₁ - signed_ w i₂))

/-- `def $ieqz_(N, i_1) = $bool(i_1 = 0)`. -/
def ieqz_ (w : Nat) (i : IN w) : U32 := bool_ (i.val == 0)

/-- `def $inez_(N, i_1) = $bool(i_1 =/= 0)`. -/
def inez_ (w : Nat) (i : IN w) : U32 := bool_ (i.val != 0)

/-- `def $ieq_(N, i_1, i_2) = $bool(i_1 = i_2)`. -/
def ieq_ (w : Nat) (i₁ i₂ : IN w) : U32 := bool_ (i₁.val == i₂.val)

/-- `def $ine_(N, i_1, i_2) = $bool(i_1 =/= i_2)`. -/
def ine_ (w : Nat) (i₁ i₂ : IN w) : U32 := bool_ (i₁.val != i₂.val)

/-- `def $ilt_(N, U, i_1, i_2) = $bool(i_1 < i_2)`,
`def $ilt_(N, S, i_1, i_2) = $bool($signed_ < $signed_)`. -/
def ilt_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val < i₂.val))
  | .s => bool_ (decide (signed_ w i₁ < signed_ w i₂))

/-- `def $igt_(N, U, i_1, i_2) = $bool(i_1 > i_2)`,
`def $igt_(N, S, i_1, i_2) = $bool($signed_ > $signed_)`. -/
def igt_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val > i₂.val))
  | .s => bool_ (decide (signed_ w i₁ > signed_ w i₂))

/-- `def $ile_(N, U, i_1, i_2) = $bool(i_1 <= i_2)`,
`def $ile_(N, S, i_1, i_2) = $bool($signed_ <= $signed_)`. -/
def ile_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val ≤ i₂.val))
  | .s => bool_ (decide (signed_ w i₁ ≤ signed_ w i₂))

/-- `def $ige_(N, U, i_1, i_2) = $bool(i_1 >= i_2)`,
`def $ige_(N, S, i_1, i_2) = $bool($signed_ >= $signed_)`. -/
def ige_ (w : Nat) (sx : Sx) (i₁ i₂ : IN w) : U32 :=
  match sx with
  | .u => bool_ (decide (i₁.val ≥ i₂.val))
  | .s => bool_ (decide (signed_ w i₁ ≥ signed_ w i₂))

/-! ## Packed numbers -/

/-- `def $lpacknum_(numtype, c) = c`,
`def $lpacknum_(packtype, c) = $wrap__($size($lunpack(packtype)), $psize(packtype), c)`. -/
def lpacknum_ : (lt : LaneType) → Num_ lt.unpack → Lane_ lt
  | .num _, c => c
  | .pack pt, c => N.wrap__ 32 pt.size c

/-- `def $lunpacknum_(numtype, c) = c`,
`def $lunpacknum_(packtype, c) = $extend__($psize(packtype), $size($lunpack(packtype)), U, c)`. -/
def lunpacknum_ : (lt : LaneType) → Lane_ lt → Num_ lt.unpack
  | .num _, c => c
  | .pack pt, c => N.extend__ pt.size 32 .u c

/-- `def $cunpacknum_(consttype, c) = c`,
`def $cunpacknum_(packtype, c) = $extend__($psize(packtype), $size($lunpack(packtype)), U, c)`,
composed with `$const($cunpack(zt), -)` as the step rules of `4.3` use it. -/
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
def unop_ : (nt : NumType) → Unop → Num_ nt → List (Num_ nt)
  | .i32, .int o, c => N.unopI 32 o c
  | .i64, .int o, c => N.unopI 64 o c
  | .f32, .float o, c => N.unopF 32 o c
  | .f64, .float o, c => N.unopF 64 o c
  | .i32, .float _, _ => []
  | .i64, .float _, _ => []
  | .f32, .int _, _ => []
  | .f64, .int _, _ => []

/-- The `Inn` equations of `def $binop_`. -/
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

end Numerics

end WasmGemmGnaf.Wasm.Core.Exec
