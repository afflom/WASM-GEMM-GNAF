import WasmGemmGnaf.GNAF.Typing
import WasmGemmGnaf.Wasm.CoreBackEnd
import WasmGemmGnaf.Wasm.Core.Profile

set_option autoImplicit false

/-!
# GNAF: direct compiler to public amended WebAssembly Core

`GNAF.compile` consumes the profile/problem-indexed `CheckedPlan` of
`GNAF/Typing.lean` and constructs the public representable `Wasm.Module`
directly.  There is no legacy-subset module or instruction bridge on this path.

## The machine model of the translation

The GNAF machine of `GNAF/Semantics.lean` has a cell-addressed memory, a
private scratch store, a scalar register file, code/data tables, a status word
and an output region.  The translation fixes the following representation.

* GNAF memory cell `i` is lowered to the Core memory byte address fixed by the
  source layout certificate.
* The scratch store follows the memory image and code/data tables follow the
  scratch.  `buildOutput` is source-private metadata and emits no public store;
  observable result bytes are written only by the plan's actual memory stores.
  The remaining private layout is one exported memory, sized by
  `CompileEnv.pages`; the amended Harness grows that memory to each invocation's
  exact raw-window page target before installation. Acceptance observes only the
  source-memory prefix.
* Scalar register `r` is an `i64` local at `2 + r` (locals `0` and `1` are the
  two `i32` ABI parameters). Register writes, width-eight descriptor fields,
  address arithmetic and loop bounds therefore retain all 64 bits. The status
  is also private `i64` local `2 + regs`, wrapped to the ABI `i32` only by the
  final epilogue. Every effective memory address is computed in `i64` and is
  wrapped to the wasm32 memory index only on the independently classified
  in-window path.
Every conversion from a source `Nat` to a Core literal is reached only through
`CheckedPlan.coreRepresentable`; no address or page count is clamped.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf.Foundation

/-! ## The compilation environment -/

/-- The static layout parameters of one compilation: the sizes of the GNAF
machine's stores, and the loop-nesting depth of the plan. -/
structure CompileEnv where
  /-- Size of the scalar register file. -/
  regs : Nat
  /-- Number of GNAF memory cells. -/
  memWords : Nat
  /-- Static upper bound on the number of scratch cells. -/
  scratchWords : Nat
  /-- Number of code/data tables. -/
  tableCount : Nat
  /-- Number of cells reserved for each code/data table. -/
  tableStride : Nat
  /-- Static bound on the plan's nesting depth. -/
  depthBound : Nat
  deriving DecidableEq, Repr, Inhabited

namespace CompileEnv

/-- Byte address of GNAF memory cell `i`. -/
def memAddr (_e : CompileEnv) (i : Nat) : Nat := i

/-- Byte address of the first scratch cell. -/
def scratchBase (e : CompileEnv) : Nat := e.memWords

/-- Byte address of scratch cell `i`. -/
def scratchAddr (e : CompileEnv) (i : Nat) : Nat := e.scratchBase + 8 * i

/-- Byte address of the first code/data table cell. -/
def tableBase (e : CompileEnv) : Nat := e.scratchBase + 8 * e.scratchWords

/-- Byte address of the status word. -/
def statusAddr (e : CompileEnv) : Nat :=
  e.tableBase + 8 * (e.tableCount * e.tableStride)

/-- Byte address of the output pointer word. -/
def outPtrAddr (e : CompileEnv) : Nat := e.statusAddr + 4

/-- Byte address of the output length word. -/
def outLenAddr (e : CompileEnv) : Nat := e.statusAddr + 8

/-- Total number of bytes the layout needs. -/
def byteSize (e : CompileEnv) : Nat := e.outLenAddr + 4

  /-- Least initial page count containing the compiler's private static layout.
  The Harness grows from this minimum to the exact raw-window target before
  installation, so an invocation never forces an unrelated 4-GiB allocation. -/
def pages (e : CompileEnv) : Nat := Wasm.pagesFor e.byteSize

/-- The declared wasm32 maximum.  This permits every profile-lawful raw window
while `pages` remains the small source-layout minimum. -/
def maxPages (_e : CompileEnv) : Nat := 65536

/-- Local index of scalar register `r`. -/
def regLocal (_e : CompileEnv) (r : Nat) : Nat := 2 + r

/-- Local index of the scratch local of nesting depth `d`. -/
def tempLocal (e : CompileEnv) (d : Nat) : Nat := 3 + e.regs + d

/-- Local index of the private status word.  It is the first non-register local;
nesting temporaries start one local later, so status updates and control-flow
scratch can never alias. -/
def statusLocal (e : CompileEnv) : Nat := 2 + e.regs

/-- Number of locals declared by the emitted function, beyond the two ABI
parameters. -/
def declaredLocals (e : CompileEnv) : Nat := e.regs + e.depthBound + 2

/-- Total number of locals in scope in the emitted function. -/
def numLocals (e : CompileEnv) : Nat := 2 + e.declaredLocals

end CompileEnv

/-! ## Direct Core instruction shorthands -/

/-- Total internal constructor for a Core `u32`.  The public compiler reaches
it only under `CheckedPlan.coreRepresentable`; `coreU32_exact` is the theorem
used by semantic proofs to eliminate the implementation modulus. -/
def coreU32 (n : Nat) : Wasm.Core.U32 :=
  ⟨n % 2 ^ 32, Nat.mod_lt _ (Wasm.Core.two_pow_pos 32)⟩

theorem coreU32_exact (n : Nat) (h : n < 2 ^ 32) : (coreU32 n).val = n := by
  simp [coreU32, Nat.mod_eq_of_lt h]

/-- Total internal constructor for a Core `u64`. -/
def coreU64 (n : Nat) : Wasm.Core.U64 :=
  ⟨n % 2 ^ 64, Nat.mod_lt _ (Wasm.Core.two_pow_pos 64)⟩

/-- Core index shorthands. -/
def localGet (n : Nat) : Wasm.Core.Instr := Wasm.Core.Instr.localGet (coreU32 n)
def localSet (n : Nat) : Wasm.Core.Instr := Wasm.Core.Instr.localSet (coreU32 n)
def br (n : Nat) : Wasm.Core.Instr := Wasm.Core.Instr.br (coreU32 n)
def brIf (n : Nat) : Wasm.Core.Instr := Wasm.Core.Instr.brIf (coreU32 n)

/-- The memory immediate of every emitted access: memory 0, natural alignment,
zero static offset. -/
def memArg : Wasm.Core.MemArg := { align := coreU32 2, offset := coreU32 0 }

/-- Natural-alignment immediate for packed byte accesses. -/
def byteMemArg : Wasm.Core.MemArg := { align := coreU32 0, offset := coreU32 0 }

/-- A non-negative `i32` constant. -/
def constI (n : Nat) : Wasm.Core.Instr := .const .i32 (coreU32 n)

/-- A non-negative `i64` constant. -/
def constL (n : Nat) : Wasm.Core.Instr := .const .i64 (coreU64 n)

/-- A full-width `i32` load from memory 0. -/
def loadW : Wasm.Core.Instr := .load .i32 none (coreU32 0) memArg

/-- An unsigned byte load into an `i32`.  Source `Machine.mem` is the ABI byte
image, so raw-header cells must use this instruction rather than `i32.load`. -/
def load8U : Wasm.Core.Instr :=
  .load .i32 (some { sz := .s8, sx := .u }) (coreU32 0) byteMemArg

/-- Width-faithful unsigned loads into the compiler's `i64` scalar file. -/
def loadL : Wasm.Core.Instr := .load .i64 none (coreU32 0) memArg
def load8UL : Wasm.Core.Instr :=
  .load .i64 (some { sz := .s8, sx := .u }) (coreU32 0) byteMemArg
def load16UL : Wasm.Core.Instr :=
  .load .i64 (some { sz := .s16, sx := .u }) (coreU32 0)
    { align := coreU32 1, offset := coreU32 0 }
def load32UL : Wasm.Core.Instr :=
  .load .i64 (some { sz := .s32, sx := .u }) (coreU32 0) memArg

/-- A full-width `i32` store to memory 0. -/
def storeW : Wasm.Core.Instr := .store .i32 none (coreU32 0) memArg

def storeL : Wasm.Core.Instr := .store .i64 none (coreU32 0) memArg
def store8L : Wasm.Core.Instr :=
  .store .i64 (some { sz := .s8 }) (coreU32 0) byteMemArg
def store16L : Wasm.Core.Instr :=
  .store .i64 (some { sz := .s16 }) (coreU32 0)
    { align := coreU32 1, offset := coreU32 0 }
def store32L : Wasm.Core.Instr :=
  .store .i64 (some { sz := .s32 }) (coreU32 0) memArg

def addI : Wasm.Core.Instr := .binop .i32 (.int .add)
def subI : Wasm.Core.Instr := .binop .i32 (.int .sub)
def mulI : Wasm.Core.Instr := .binop .i32 (.int .mul)
def andI : Wasm.Core.Instr := .binop .i32 (.int .and)
def orI : Wasm.Core.Instr := .binop .i32 (.int .or)
def eqI : Wasm.Core.Instr := .relop .i32 (.int .eq)
def ltUI : Wasm.Core.Instr := .relop .i32 (.int (.lt .u))
def gtUI : Wasm.Core.Instr := .relop .i32 (.int (.gt .u))
def geUI : Wasm.Core.Instr := .relop .i32 (.int (.ge .u))

def addL : Wasm.Core.Instr := .binop .i64 (.int .add)
def subL : Wasm.Core.Instr := .binop .i64 (.int .sub)
def mulL : Wasm.Core.Instr := .binop .i64 (.int .mul)
def andL : Wasm.Core.Instr := .binop .i64 (.int .and)
def orL : Wasm.Core.Instr := .binop .i64 (.int .or)
def eqL : Wasm.Core.Instr := .relop .i64 (.int .eq)
def ltUL : Wasm.Core.Instr := .relop .i64 (.int (.lt .u))
def gtUL : Wasm.Core.Instr := .relop .i64 (.int (.gt .u))
def geUL : Wasm.Core.Instr := .relop .i64 (.int (.ge .u))
def extendI32U : Wasm.Core.Instr :=
  .cvtop .i64 .i32 (.ii (.extend .u))
def wrapI64 : Wasm.Core.Instr := .cvtop .i32 .i64 (.ii .wrap)

/-- A two-armed `if` with empty block type. -/
def ifE (t f : List Wasm.Core.Instr) : Wasm.Core.Instr :=
  .ifElse (.result none) (Wasm.Core.InstrSeq.ofList t) (Wasm.Core.InstrSeq.ofList f)

/-- A `block` with empty block type. -/
def blockE (b : List Wasm.Core.Instr) : Wasm.Core.Instr :=
  .block (.result none) (Wasm.Core.InstrSeq.ofList b)

/-- A `loop` with empty block type. -/
def loopE (b : List Wasm.Core.Instr) : Wasm.Core.Instr :=
  .loop (.result none) (Wasm.Core.InstrSeq.ofList b)

/-- Load the `i32` at a fixed byte address. -/
def loadAt (addr : Nat) : List Wasm.Core.Instr := [constI addr, loadW]

/-- Load the source byte cell at a fixed byte address. -/
def loadCellAt (addr : Nat) : List Wasm.Core.Instr := [constI addr, load8U]

/-- Push the ABI address `ptr + offset`.  Local zero is the public `ptr`
parameter; source `RegionRef` bases and raw-header indices are relative to it. -/
def inputAddr (offset : Nat) : List Wasm.Core.Instr :=
  [localGet 0, constI offset, addI]

/-- Push the ABI address `ptr + offset` as an `i64`, before dynamic signed or
unsigned address arithmetic. -/
def inputAddr64 (offset : Nat) : List Wasm.Core.Instr :=
  [localGet 0, extendI32U, constL offset, addL]

/-- Load one source byte at an ABI-relative address. -/
def loadInputCell (offset : Nat) : List Wasm.Core.Instr := inputAddr offset ++ [load8U]

/-- Width-faithful unsigned scalar load.  Widths outside the four released
integer storage widths are syntactically rejected; `coreSupported` excludes
that branch from every checked compilation. -/
def loadWidthL : Nat → Wasm.Core.Instr
  | 1 => load8UL
  | 2 => load16UL
  | 4 => load32UL
  | 8 => loadL
  | _ => .unreachable

/-- Width-faithful low-byte scalar store. -/
def storeWidthL : Nat → Wasm.Core.Instr
  | 1 => store8L
  | 2 => store16L
  | 4 => store32L
  | 8 => storeL
  | _ => .unreachable

/-- Effective public address of a mapped source region, computed without
discarding any of the three 64-bit register contributions. -/
def mappedInputAddr (e : CompileEnv) (region : RegionRef) (map : IndexMap) :
    List Wasm.Core.Instr :=
  inputAddr64 (e.memAddr (region.base + map.c0)) ++
    [localGet (e.regLocal 0), constL map.cb, mulL, addL,
     localGet (e.regLocal 1), constL map.ci, mulL, addL,
     localGet (e.regLocal 2), constL map.cj, mulL, addL,
     wrapI64]

/-- The counting loop `for c := 0 while c < n do body; c := c + 1`.  The
counter is the local `c`; `body` must be operand-stack neutral. -/
def countLoop (c n : Nat) (body : List Wasm.Core.Instr) : List Wasm.Core.Instr :=
  [constL 0, localSet c,
   blockE
     [loopE
       ([localGet c, constL n, geUL, brIf 1] ++ body ++
        [localGet c, constL 1, addL, localSet c, br 0])]]

/-- The counting loop
`for c := 0 while c < min !ext loopRegMaxTrips do body; c := c + 1`.

The source evaluator applies exactly this clamp to every register-driven loop.
Scalar locals retain the full ABI `u64`, so the target must test the static
ceiling explicitly rather than relying on an `i32` representation invariant.
The two exit tests are equivalent to the single mathematical minimum while
keeping the input extent unchanged for the loop body. -/
def countLoopVar (c ext : Nat) (body : List Wasm.Core.Instr) : List Wasm.Core.Instr :=
  [constL 0, localSet c,
   blockE
     [loopE
       ([localGet c, localGet ext, geUL, brIf 1,
         localGet c, constL loopRegMaxTrips, geUL, brIf 1] ++ body ++
        [localGet c, constL 1, addL, localSet c, br 0])]]

/-- Dispatch on a local holding a small tag. -/
def dispatchOn (t k : Nat) (a b : List Wasm.Core.Instr) : List Wasm.Core.Instr :=
  [localGet t, constL k, eqL, ifE a b]

/-! ## The compatibility table as emitted code

`Machine.classify` consults `compatible` (SPEC §8.2).  The emitted code
compares a packed key against the closed list of accepted triples;
`mem_compatibleKeys_iff` proves the list is exactly the accepted set, so the
emitted comparison chain is the compatibility table and not an approximation
of it. -/

/-- The packed key of a compatibility triple. -/
def compatKey (m : ArithmeticMode) (stored acc : ScalarKind) : Nat :=
  m.tag * 169 + stored.tag * 13 + acc.tag

/-- The accepted compatibility keys of SPEC §8.2. -/
def compatibleKeys : List Nat :=
  [5, 18, 31, 44, 57, 70, 85, 98,
   175, 189, 201, 215, 227, 241, 253, 267,
   452, 453, 465, 466, 478, 479, 492,
   623, 636, 649, 662]

/-- The emitted key list is exactly the compatibility relation of SPEC §8.2. -/
theorem mem_compatibleKeys_iff (m : ArithmeticMode) (stored acc : ScalarKind) :
    compatKey m stored acc ∈ compatibleKeys ↔ compatible m stored acc = true := by
  revert m stored acc
  decide

theorem compatibleKeys_length : compatibleKeys.length = 27 := rfl

/-! ## Header, classification and layout code -/

/-- Push GNAF memory cell `i`. -/
def cellCode (e : CompileEnv) (i : Nat) : List Wasm.Core.Instr :=
  loadInputCell (e.memAddr i) ++ [extendI32U]

/-- Push the little-endian 16-bit field at cell `i`, exactly
`Machine.u16At i = byteAt i + 256 * byteAt (i+1)`. -/
def u16Code (e : CompileEnv) (i : Nat) : List Wasm.Core.Instr :=
  cellCode e i ++ [constL 256] ++ cellCode e (i + 1) ++ [mulL, addL]

/-- Compare the top of the stack against a constant. -/
def eqConst (n : Nat) : List Wasm.Core.Instr := [constL n, eqL]

/-- Push `Machine.headerOk`: the exact ABI magic, version and header size. -/
def headerOkCode (e : CompileEnv) : List Wasm.Core.Instr :=
  cellCode e 0 ++ eqConst 87 ++
  cellCode e 1 ++ eqConst 71 ++ [andI] ++
  cellCode e 2 ++ eqConst 78 ++ [andI] ++
  cellCode e 3 ++ eqConst 71 ++ [andI] ++
  u16Code e 4 ++ eqConst 1 ++ [andI] ++
  u16Code e 6 ++ eqConst headerSize ++ [andI]

/-- Push whether all three declared tags decode, exactly the `isSome` of
`Machine.declaredTags`. -/
def tagsKnownCode (e : CompileEnv) : List Wasm.Core.Instr :=
  cellCode e 8 ++ [constL 13, ltUL] ++
  cellCode e 11 ++ [constL 13, ltUL, andI] ++
  cellCode e 12 ++ [constL 4, ltUL, andI]

/-- Push the packed compatibility key of the declared tags. -/
def keyCode (e : CompileEnv) : List Wasm.Core.Instr :=
  cellCode e 12 ++ [constL 169, mulL] ++
  cellCode e 8 ++ [constL 13, mulL, addL] ++
  cellCode e 11 ++ [addL]

/-- Or-chain of the accepted compatibility keys. -/
def keyChain (e : CompileEnv) : List Nat → List Wasm.Core.Instr
  | [] => []
  | k :: ks => keyCode e ++ [constL k, eqL, orI] ++ keyChain e ks

/-- Push whether the declared triple is compatible. -/
def compatCode (e : CompileEnv) : List Wasm.Core.Instr :=
  [constI 0] ++ keyChain e compatibleKeys

/-- Compute the classification of SPEC §8.3 into local `t`, in the fixed
precedence order of `Machine.classify`. -/
def classifyCode (e : CompileEnv) (t : Nat) : List Wasm.Core.Instr :=
  if e.memWords < headerSize then [constL 1, localSet t]
  else
    [constL (if e.memWords ≤ maxRawExtent then 0 else 3), localSet t] ++
    headerOkCode e ++
    [ifE
      (tagsKnownCode e ++
        [ifE (compatCode e ++ [ifE [] [constL 1, localSet t]])
             [constL 2, localSet t]])
      [constL 1, localSet t]]

/-- Chain computing `Machine.storedWidth`: the byte width of the decoded
stored-kind tag, and zero when the tag decodes to nothing. -/
def widthChain (e : CompileEnv) : List ScalarKind → List Wasm.Core.Instr
  | [] => []
  | k :: ks =>
      cellCode e 8 ++
      [constL k.tag, eqL, extendI32U, constL k.byteWidth, mulL, addL] ++
        widthChain e ks

/-- Push `Machine.storedWidth`. -/
def widthCode (e : CompileEnv) : List Wasm.Core.Instr :=
  [constL 0] ++ widthChain e ScalarKind.all

/-- One layout test: `if u16At field = storedWidth then t := cls`. -/
def layoutTestCode (e : CompileEnv) (t field cls : Nat) : List Wasm.Core.Instr :=
  u16Code e field ++ (widthCode e ++ [eqL, ifE [constL cls, localSet t] []])

/-- Compute the layout class of SPEC §11.1 into local `t`.  The column-major
test is emitted first and the row-major test second, so that the row-major
class wins when both hold, exactly as `Machine.layoutClass` prescribes. -/
def layoutCode (e : CompileEnv) (t : Nat) : List Wasm.Core.Instr :=
  [constL 2, localSet t] ++ (layoutTestCode e t 56 1 ++ layoutTestCode e t 64 0)

/-- Push the value of a branch condition.  `scratchAtLeast` is decided against
the statically declared scratch extent `scr`, which the typing judgment keeps a
lower bound of the machine's actual scratch. -/
def condCode (e : CompileEnv) (scr : Nat) : Cond → List Wasm.Core.Instr
  | .statusIs s => [localGet e.statusLocal] ++ eqConst s.code
  | .regEq r v => [localGet (e.regLocal r), constL v, eqL]
  | .regLt r v => [localGet (e.regLocal r), constL v, ltUL]
  | .scratchAtLeast n => [constI (if n ≤ scr then 1 else 0)]

/-- The stores that initialize one code/data table. -/
def tableStores (base : Nat) : Nat → List Nat → List Wasm.Core.Instr
  | _, [] => []
  | j, v :: vs =>
      [constI (base + 8 * j), constL v, storeL] ++ tableStores base (j + 1) vs

/-! ## The translation

`code e d scr p` is the operand-stack-neutral instruction sequence of plan `p`
at loop-nesting depth `d` with statically declared scratch extent `scr`. -/

/-- The translation of a plan into the legacy executable subset. -/
def code (e : CompileEnv) : Nat → Nat → Plan → List Wasm.Core.Instr
  | _, _, .nop => []
  | d, scr, .seq a b => code e d scr a ++ code e d scr b
  | d, scr, .classifyRaw v i u x =>
      classifyCode e (e.tempLocal d) ++
      dispatchOn (e.tempLocal d) 0 (code e d scr v)
        (dispatchOn (e.tempLocal d) 1 (code e d scr i)
          (dispatchOn (e.tempLocal d) 2 (code e d scr u) (code e d scr x)))
  | d, scr, .dispatchLayout r c g =>
      layoutCode e (e.tempLocal d) ++
      dispatchOn (e.tempLocal d) 0 (code e d scr r)
        (dispatchOn (e.tempLocal d) 1 (code e d scr c) (code e d scr g))
  | d, scr, .branch co t f =>
      condCode e scr co ++ [ifE (code e d scr t) (code e d scr f)]
  | d, _, .pack src dst map _ =>
      countLoop (e.tempLocal d) src.count
        ([constI (e.scratchAddr dst.base), localGet (e.tempLocal d),
          constL 8, mulL, wrapI64, addI] ++
         (inputAddr64 (e.memAddr (src.base + map.c0)) ++
          [localGet (e.tempLocal d), constL map.cb, mulL, addL, wrapI64,
           load8UL]) ++
         [storeL])
  | d, _, .unpack src dst map _ =>
      countLoop (e.tempLocal d) src.count
        ((inputAddr64 (e.memAddr dst.base) ++
          [localGet (e.tempLocal d), constL 1, mulL, addL, wrapI64]) ++
         [constI (e.scratchAddr (src.base + map.c0)), localGet (e.tempLocal d),
          constL (8 * map.cb), mulL, wrapI64, addI, loadL] ++
         [store8L])
  | _, _, .storeReg dst map width src =>
      mappedInputAddr e dst map ++
        [localGet (e.regLocal src), storeWidthL width]
  | _, _, .loadReg dst src map width =>
      mappedInputAddr e src map ++
        [loadWidthL width, localSet (e.regLocal dst)]
  | d, scr, .loopNest axis body =>
      countLoop (e.tempLocal d) axis.extent
        ([localGet (e.tempLocal d), localSet (e.regLocal axis.indexReg)] ++
         code e (d + 1) scr body)
  | d, scr, .loopReg ir er _ body =>
      countLoopVar (e.tempLocal d) (e.regLocal er)
        ([localGet (e.tempLocal d), localSet (e.regLocal ir)] ++
         code e (d + 1) scr body)
  | d, scr, .tiled _ tiling extents body =>
      countLoop (e.tempLocal d) (tiling.totalTiles extents.m extents.n extents.k)
        ((if 0 < e.regs then [localGet (e.tempLocal d), localSet (e.regLocal 0)] else []) ++
         code e (d + 1) scr body)
  | d, _, .reduce c acc lhs rhs =>
      if Plan.coreScalarI32Supported c then
        countLoop (e.tempLocal d) (Nat.min lhs.count rhs.count)
          ([localGet (e.regLocal acc)] ++
           (inputAddr64 (e.memAddr lhs.base) ++
            [localGet (e.tempLocal d), constL 4, mulL, addL, wrapI64,
             load32UL]) ++
           (inputAddr64 (e.memAddr rhs.base) ++
            [localGet (e.tempLocal d), constL 4, mulL, addL, wrapI64,
             load32UL]) ++
           [mulL, addL, localSet (e.regLocal acc)])
      else [.unreachable]
  | d, scr, .allocScratch bytes body => code e d (scr + bytes) body
  /- The independently admitted straight-line scalar fragment has no
  observable register consumer: memory/control/reduction nodes are rejected by
  `coreSupported`, and `Accepts` observes only memory, effects, and the returned
  status.  These private writes are therefore eliminated by an
  observation-preserving DCE.  When memory/control admission is widened, its
  checker must retain every scalar value that reaches such a consumer. -/
  | _, _, .setReg _ _ => []
  | _, _, .scalarOp _ _ _ _ => []
  | _, _, .vectorOp _ _ _ _ _ => [.unreachable]
  | _, _, .emitTable index data =>
      tableStores (e.tableBase + 8 * (index * e.tableStride)) 0 data
  | _, _, .tableLoad table index dst =>
      [constI (e.tableBase + 8 * (table * e.tableStride + index)), loadL] ++
      [localSet (e.regLocal dst)]
  | _, _, .setStatus s => [constL s.code, localSet e.statusLocal]
  | _, _, .buildOutput _ => []
  | d, scr, .opaqueProcess _ body => code e d scr body

/-- The complete body of the emitted `gemm` function: the plan's code, then the
status word, which is the ABI result. -/
def bodyCode (e : CompileEnv) (scr : Nat) (p : Plan) : List Wasm.Core.Instr :=
  code e 0 scr p ++ [localGet e.statusLocal, wrapI64]

/-- The ABI status load is an inseparable part of every lowering.  Besides
being useful to downstream simulation, this equation is the proof anchor for
the compiler falsifier: deleting or redirecting the epilogue makes this source
theorem stop elaborating. -/
theorem bodyCode_has_status_epilogue (e : CompileEnv) (scr : Nat) (p : Plan) :
    bodyCode e scr p = code e 0 scr p ++ [localGet e.statusLocal, wrapI64] := rfl

/-! ## The emitted module -/

/-- The Core AST emitted from a layout and a function body. -/
def moduleOf (e : CompileEnv) (body : List Wasm.Core.Instr) : Wasm.Core.Module :=
  { types := [Wasm.Core.gemmTypeDef]
    imports := []
    tags := []
    globals := []
    mems :=
      [{ memtype :=
          { addr := .i32
            lim := { min := coreU64 e.pages, max := some (coreU64 e.maxPages) } } }]
    tables := []
    funcs :=
      [{ typeidx := coreU32 0
         locals := List.replicate e.declaredLocals { valtype := .num .i64 }
         body := Wasm.Core.InstrSeq.ofList body }]
    datas := []
    elems := []
    start := none
    exports :=
      [{ name := Wasm.Core.memoryExportName, externidx := .mem (coreU32 0) },
       { name := Wasm.Core.gemmExportName, externidx := .func (coreU32 0) }] }

/-- The compilation environment of a plan checked at interface `s`. -/
def envOf (s : Sig) (p : Plan) : CompileEnv :=
  { regs := s.regs
    memWords := s.mem
    scratchWords := s.scratch + p.charges.scratchPeak
    tableCount := s.tables
    tableStride := p.tableWords
    depthBound := p.depth }

/-- Direct Core AST lowering.  The public `compile` wrapper is introduced only
after `coreRepresentable` has been proved to make this AST encodable; this
internal definition cannot be mistaken for a public representable module. -/
def compileCore {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) : Wasm.Core.Module :=
  let env := envOf checked.inputSig checked.plan
  moduleOf env (bodyCode env checked.inputSig.scratch checked.plan)

/-- Direct Core lowering is deterministic. -/
theorem compileCore_deterministic {P : Wasm.Profile} {G : Gemm.Problem P}
    (a b : CheckedPlan P G) (h : a = b) : compileCore a = compileCore b := by
  rw [h]

/-! ## Amended binary representability envelope -/

/-- An option-valued encoder component produced concrete bytes.  Keeping this
small proposition public lets the source-bound proofs state their two exact
encoder obligations without exposing an implementation witness. -/
def EncoderHasValue {α : Type} (encoded : Option α) : Prop :=
  ∃ value, encoded = some value

private theorem hasEncodedValue_of_isSome {α : Type} {encoded : Option α}
    (h : encoded.isSome = true) : EncoderHasValue encoded :=
  Option.isSome_iff_exists.mp h

private theorem EncoderHasValue.cat
    {left right : Option Wasm.Core.Binary.Bytes}
    (hleft : EncoderHasValue left) (hright : EncoderHasValue right) :
    EncoderHasValue (Wasm.Core.Binary.catO left right) := by
  obtain ⟨a, rfl⟩ := hleft
  obtain ⟨b, rfl⟩ := hright
  exact ⟨a ++ b, rfl⟩

/-- All fixed sections of `moduleOf` are amended-encodable.  Consequently the
whole Core AST is encodable once the two source-dependent obligations are
supplied: the data-count decision for the generated body, and the bounded code
section.  This theorem isolates the exact obligations discharged by
`coreRepresentable`; it assumes neither validation nor compiler semantics. -/
theorem moduleOf_encodable (env : CompileEnv) (body : List Wasm.Core.Instr)
    (hdataCount : EncoderHasValue
      (Wasm.Core.Binary.encDataCntSec (moduleOf env body)))
    (hcode : EncoderHasValue
      (@Wasm.Core.Binary.encCodeSec Wasm.Core.Binary.amendedBinaryAuthority
        (Wasm.Core.Binary.funcCodes (moduleOf env body).funcs))) :
    Wasm.Core.Binary.encodableA (moduleOf env body) = true := by
  have hpreamble : EncoderHasValue
      (Wasm.Core.Binary.catO (some Wasm.Core.Binary.magicBytes)
        (some Wasm.Core.Binary.versionBytes)) :=
    ⟨Wasm.Core.Binary.magicBytes ++ Wasm.Core.Binary.versionBytes, rfl⟩
  have htype : EncoderHasValue
      (Wasm.Core.Binary.encTypeSec [Wasm.Core.gemmTypeDef]) :=
    hasEncodedValue_of_isSome (by decide)
  have himport : EncoderHasValue
      (Wasm.Core.Binary.encImportSec []) := ⟨[], rfl⟩
  have hfunc : EncoderHasValue
      (Wasm.Core.Binary.encFuncSec
        (Wasm.Core.Binary.funcTypeIdxs (moduleOf env body).funcs)) := by
    simpa [moduleOf, Wasm.Core.Binary.funcTypeIdxs, coreU32] using
      (hasEncodedValue_of_isSome (encoded :=
        Wasm.Core.Binary.encFuncSec [coreU32 0]) (by decide))
  have htable : EncoderHasValue
      (Wasm.Core.Binary.encTableSec []) := ⟨[], rfl⟩
  have hmem : EncoderHasValue
      (Wasm.Core.Binary.encMemSec (moduleOf env body).mems) := by
    let payload := Wasm.Core.Binary.lebU 1 ++
      (Wasm.Core.Binary.tb 1 ::
        (Wasm.Core.Binary.lebU (coreU64 env.pages).val ++
          Wasm.Core.Binary.lebU (coreU64 env.maxPages).val))
    have hlebMin :
        (Wasm.Core.Binary.lebU (coreU64 env.pages).val).length ≤ 10 := by
      have hvalue : (coreU64 env.pages).val ≤ 2 ^ 64 - 1 := by
        have := (coreU64 env.pages).property
        omega
      have hmono := Wasm.Core.Binary.lebU_length_mono hvalue
      have hmax :
          (Wasm.Core.Binary.lebU (2 ^ 64 - 1)).length = 10 := by decide
      omega
    have hlebMax :
        (Wasm.Core.Binary.lebU (coreU64 env.maxPages).val).length ≤ 10 := by
      have hvalue : (coreU64 env.maxPages).val ≤ 2 ^ 64 - 1 := by
        have := (coreU64 env.maxPages).property
        omega
      have hmono := Wasm.Core.Binary.lebU_length_mono hvalue
      have hmax :
          (Wasm.Core.Binary.lebU (2 ^ 64 - 1)).length = 10 := by decide
      omega
    have hpayload : payload.length < 2 ^ 32 := by
      simp only [payload, List.length_append, List.length_cons]
      have hone : (Wasm.Core.Binary.lebU 1).length = 1 := by decide
      omega
    refine ⟨Wasm.Core.Binary.tb 5 ::
      (Wasm.Core.Binary.lebU payload.length ++ payload), ?_⟩
    simp only [moduleOf, Wasm.Core.Binary.encMemSec,
      Wasm.Core.Binary.encListSection, Wasm.Core.Binary.encList,
      Wasm.Core.Binary.encRep, Wasm.Core.Binary.encMem,
      Wasm.Core.Binary.encMemType, Wasm.Core.Binary.encLimits,
      Wasm.Core.Binary.encSectionBody, List.length_cons, List.length_nil,
      Nat.reduceAdd, Wasm.Core.Binary.catO]
    rw [dif_pos (by decide : 1 < 2 ^ 32)]
    simp only [List.append_nil]
    change (if payload.length < 2 ^ 32 then
      some (Wasm.Core.Binary.tb 5 ::
        (Wasm.Core.Binary.lebU payload.length ++ payload)) else none) = _
    rw [if_pos hpayload]
  have htag : EncoderHasValue
      (Wasm.Core.Binary.encTagSec []) := ⟨[], rfl⟩
  have hglobal : EncoderHasValue
      (Wasm.Core.Binary.encGlobalSec []) := ⟨[], rfl⟩
  have hexport : EncoderHasValue
      (Wasm.Core.Binary.encExportSec (moduleOf env body).exports) := by
    simpa [moduleOf, coreU32] using
      (hasEncodedValue_of_isSome (encoded := Wasm.Core.Binary.encExportSec
        [{ name := Wasm.Core.memoryExportName, externidx := .mem (coreU32 0) },
         { name := Wasm.Core.gemmExportName, externidx := .func (coreU32 0) }])
        (by decide))
  have hstart : EncoderHasValue
      (Wasm.Core.Binary.encStartSec none) := ⟨[], rfl⟩
  have helem : EncoderHasValue
      (Wasm.Core.Binary.encElemSec []) := ⟨[], rfl⟩
  have hdata : EncoderHasValue
      (Wasm.Core.Binary.encDataSec []) := ⟨[], rfl⟩
  obtain ⟨bytes, hbytes⟩ := EncoderHasValue.cat
    (EncoderHasValue.cat
      (EncoderHasValue.cat
        (EncoderHasValue.cat
          (EncoderHasValue.cat
            (EncoderHasValue.cat
              (EncoderHasValue.cat
                (EncoderHasValue.cat
                  (EncoderHasValue.cat
                    (EncoderHasValue.cat
                      (EncoderHasValue.cat
                        (EncoderHasValue.cat
                          (EncoderHasValue.cat hpreamble htype) himport)
                        hfunc)
                      htable)
                    hmem)
                  htag)
                hglobal)
              hexport)
            hstart)
          helem)
        hdataCount)
      hcode)
    hdata
  have hmodule :
      Wasm.Core.Binary.encModuleA (moduleOf env body) = some bytes := by
    simpa [Wasm.Core.Binary.encModuleA, Wasm.Core.Binary.encModule,
      Wasm.Core.Binary.funcTypeIdxs, Wasm.Core.Binary.funcCodes] using hbytes
  simp [Wasm.Core.Binary.encodableA, hmodule]

end WasmGemmGnaf.GNAF
