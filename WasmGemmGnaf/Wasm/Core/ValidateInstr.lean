/-
  Wasm/Core/ValidateInstr.lean --- the opcode dispatch of the validation
  ALGORITHM of `vendor/wasm-spec/document/core/appendix/algorithm.rst`, and its
  equivalence with the declarative judgment `Instrs_ok` of
  `Core/Validation/Instructions.lean`.

  WHAT IS DECIDED HERE, EXACTLY.  `checkSeq` is the appendix's single pass:
  `push_val`/`pop_val` on the operand stack of the current frame, `push_ctrl`
  and `pop_ctrl` at every structured instruction, `unreachable()` at every
  stack-polymorphic one, and the `Bot` type wherever a polymorphic frame has to
  invent an operand.  The declarative side is the transcribed judgment, WITH its
  `Instrs_ok/sub` and `Instrs_ok/frame` rules --- so the equivalence really is
  between an algorithm and a non-syntax-directed relation, which is the whole
  difficulty and the reason the appendix exists.

  THE FRAGMENT.  The equivalence is NOT proved for all of Core 3.0.  It is
  proved for the instructions and value types listed by `Instr.frag` and
  `ValType.nv` below:

    * value types: `numtype` and `vectype` (`I32 I64 F32 F64 V128`), plus the
      `BOT` the algorithm itself generates.  NOT reference types.
    * instructions: `NOP`, `UNREACHABLE`, `DROP`, `SELECT` (both forms),
      `BLOCK`, `LOOP`, `IF`, `BR`, `BR_IF`, `BR_TABLE`, `RETURN`, `CALL`,
      `RETURN_CALL`, `LOCAL.*`, `GLOBAL.*`, `LOAD`, `STORE`, `VLOAD`,
      `VLOAD_LANE`, `VSTORE`, `VSTORE_LANE`, `MEMORY.SIZE`, `MEMORY.GROW`,
      `MEMORY.FILL`, `MEMORY.COPY`, `MEMORY.INIT`, `DATA.DROP`, every numeric
      instruction (`CONST UNOP BINOP TESTOP RELOP CVTOP`) and every SIMD
      instruction of `1.3-syntax.instructions.spectec` (`VCONST`, `VVUNOP` ...
      `VCVTOP`, `VSPLAT`, `VEXTRACT_LANE`, `VREPLACE_LANE`).
    * NOT: the reference and GC instructions, the table and element
      instructions, `CALL_REF`/`CALL_INDIRECT`, `RETURN_CALL_REF` /
      `RETURN_CALL_INDIRECT`, and exception handling.  Every one of those
      mentions a REFERENCE type in its rule, so deciding it needs
      `Heaptype_sub`, whose decidability is a separate obligation this file
      does not discharge.

  WHAT `BR_TABLE` AND `RETURN_CALL` NEEDED, AND WHY THEY DID NOT NEED THAT.
  Both rules are stated with subtyping --- `Instr_ok/br_table` requires
  `Resulttype_sub: C |- t* <: C.LABELS[l]` at every label and
  `Instr_ok/return_call` requires `Resulttype_sub: C |- t_2* <: C.RETURN` --- but
  on the decided fragment every type on the RIGHT of those premises is a
  `numtype` or a `vectype`, and `Valtype_sub` at such a type is exactly `BOT` or
  equality (`ValidateStack.subOf_of_valtype_sub`).  So the two rules are decided
  by the operand stack alone.

  `BR_TABLE` in particular leaves `t*` FREE and bounds it only from ABOVE, once
  per label, so the algorithm cannot pop against a fixed expectation.  It pops
  with NO expectation --- `St.popN`, the appendix's `pop_val()` iterated --- and
  compares the answer with every label afterwards.  That answer is PRINCIPAL
  (`ValidateSeq.popN_principal`), which is why one pass decides the
  existential: in unreachable code it returns `BOT`, so a `br_table` whose
  labels DISAGREE is still accepted, exactly as Core 3.0 requires.

  Multi-value blocks, block types given by a type index, and full stack
  polymorphism ARE inside the fragment; they are what the appendix algorithm is
  for.  `checkInstr` returns `none` on everything outside the fragment, so
  SOUNDNESS (`checkSeq_sound`) holds for EVERY context and every instruction,
  with no fragment hypothesis; only COMPLETENESS (`checkSeq_complete`) is
  fragment-scoped.

  The corrected declarative target is the sole combined hierarchy
  `Instr_okA`/`Instrs_okA` in
  `Core/Validation/InstructionsCombinedAmended.lean`.  The unrestricted pass
  below is `checkInstrA`/`checkSeqA`; the older fragment pass remains only while
  its existing proof is used as a migration lemma.  It is not the release
  validity endpoint.
-/
import WasmGemmGnaf.Wasm.Core.ValidateStack
import WasmGemmGnaf.Wasm.Core.ValidateTypes
import WasmGemmGnaf.Wasm.Core.Validation.InstructionsCombinedAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

open St

/-! ## The decided fragment, as a decision -/

/-- `resulttype`s of the decided fragment. -/
def nvs (ts : List ValType) : Bool := ts.all ValType.nv

/-- A `deftype` that expands to a function type over the decided fragment,
together with that function type: `expand_def(t)` with `is_func(t)`. -/
def funcTypeOf (dt : DefType) : Option (List ValType × List ValType) :=
  match expandDt dt with
  | some (.func dom cod) =>
      if nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod) then
        some (ValTypes.toList dom, ValTypes.toList cod)
      else none
  | _ => none

/-- The `[t_1*] -> [t_2*]` of a `blocktype`, `Blocktype_ok` decided. -/
def blockType (C : Context) : BlockType → Option (List ValType × List ValType)
  | .result none => some ([], [])
  | .result (some t) => if ValType.nv t then some ([], [t]) else none
  | .idx x =>
      match C.types[x.val]? with
      | some dt => funcTypeOf dt
      | none => none

/-! ## Full amended-Core type expansion

The original dispatcher below was developed first for numeric/vector value
types.  These two helpers are the same two partial semantic operations without
that historical restriction.  Validity of an inline result type is checked
through the corrected hierarchy; an indexed function type is determined by
`Expand`, exactly as in `Blocktype_okA/typeidx`. -/

def funcTypeOfA (dt : DefType) : Option (List ValType × List ValType) :=
  match expandDt dt with
  | some (.func dom cod) => some (ValTypes.toList dom, ValTypes.toList cod)
  | _ => none

def blockTypeA (C : Context) : BlockType → Option (List ValType × List ValType)
  | .result none => some ([], [])
  | .result (some t) =>
      if checkValtypeOkA C t then some ([], [t]) else none
  | .idx x =>
      match C.types[x.val]? with
      | some dt => funcTypeOfA dt
      | none => none

/-- The `blocktype`s of the decided fragment. -/
def BlockType.frag : BlockType → Bool
  | .result none => true
  | .result (some t) => ValType.nv t
  | .idx _ => true

/-! The instructions of the decided fragment; see the file header. -/

mutual
/-- The instructions of the decided fragment. -/
def Instr.frag : Instr → Bool
  | .nop => true
  | .unreachable => true
  | .drop => true
  | .select none => true
  | .select (some [t]) => ValType.nv t
  | .select (some _) => false
  | .block bt body => BlockType.frag bt && InstrSeq.frag body
  | .loop bt body => BlockType.frag bt && InstrSeq.frag body
  | .ifElse bt thn els => BlockType.frag bt && InstrSeq.frag thn && InstrSeq.frag els
  | .br _ => true
  | .brIf _ => true
  | .brTable _ _ => true
  | .ret => true
  | .call _ => true
  | .returnCall _ => true
  | .localGet _ => true
  | .localSet _ => true
  | .localTee _ => true
  | .globalGet _ => true
  | .globalSet _ => true
  | .load _ _ _ _ => true
  | .store _ _ _ _ => true
  | .vload _ _ _ _ => true
  | .vloadLane _ _ _ _ _ => true
  | .vstore _ _ _ => true
  | .vstoreLane _ _ _ _ _ => true
  | .memorySize _ => true
  | .memoryGrow _ => true
  | .memoryFill _ => true
  | .memoryCopy _ _ => true
  | .memoryInit _ _ => true
  | .dataDrop _ => true
  | .const _ _ => true
  | .unop _ _ => true
  | .binop _ _ => true
  | .testop _ _ => true
  | .relop _ _ => true
  | .cvtop _ _ _ => true
  | .vconst _ _ => true
  | .vvunop _ _ => true
  | .vvbinop _ _ => true
  | .vvternop _ _ => true
  | .vvtestop _ _ => true
  | .vunop _ _ => true
  | .vbinop _ _ => true
  | .vternop _ _ => true
  | .vtestop _ _ => true
  | .vrelop _ _ => true
  | .vshiftop _ _ => true
  | .vbitmask _ => true
  | .vswizzlop _ _ => true
  | .vshuffle _ _ => true
  | .vextunop _ _ _ => true
  | .vextbinop _ _ _ => true
  | .vextternop _ _ _ => true
  | .vnarrow _ _ _ => true
  | .vcvtop _ _ _ => true
  | .vsplat _ => true
  | .vextractLane _ _ _ => true
  | .vreplaceLane _ _ => true
  | _ => false

/-- Every instruction of the sequence is in the decided fragment. -/
def InstrSeq.frag : InstrSeq → Bool
  | .nil => true
  | .cons i rest => Instr.frag i && InstrSeq.frag rest
end

/-- The contexts the completeness direction is proved for: every value type
reachable from the context is in the decided fragment, and every local is
already initialised (which is automatic here, because every type of the
fragment is defaultable --- `Local_ok/set` is the only rule that applies). -/
def Context.frag (C : Context) : Bool :=
  C.locals.all (fun lt => (lt.init == Init.set) && ValType.nv lt.valtype) &&
  C.labels.all nvs &&
  (match C.ret with | none => true | some ts => nvs ts) &&
  C.globals.all (fun gt => ValType.nv gt.valtype) &&
  C.funcs.all (fun dt => (funcTypeOf dt).isSome) &&
  C.types.all (fun dt => (funcTypeOf dt).isSome)

/-! ## The instruction types the algorithm computes

`instrType` is the type of an instruction whose declarative type is UNIQUE ---
which is every instruction of the fragment except the nine whose rule leaves
something free: `UNREACHABLE`, `DROP`, `SELECT` without annotation, `BR`,
`RETURN`, and the four structured ones.  Those are handled by `checkInstr`
directly, in the appendix's own terms. -/

/-- The unique declarative type of a fragment instruction, before the
instruction's own `-- if` side conditions are checked. -/
def instrTypeRaw (C : Context) : Instr → Option InstrType
  | .nop => some ⟨[], [], []⟩
  | .select (some [t]) => if ValType.nv t then some ⟨[t, t, ValType.i32], [], [t]⟩ else none
  | .brIf l =>
      match C.labels[l.val]? with
      | some ts => if nvs ts then some ⟨ts ++ [ValType.i32], [], ts⟩ else none
      | none => none
  | .call x =>
      match C.funcs[x.val]? with
      | some dt =>
          match funcTypeOf dt with
          | some (dom, cod) => some ⟨dom, [], cod⟩
          | none => none
      | none => none
  | .localGet x =>
      match C.locals[x.val]? with
      | some ⟨.set, t⟩ => if ValType.nv t then some ⟨[], [], [t]⟩ else none
      | _ => none
  | .localSet x =>
      match C.locals[x.val]? with
      | some ⟨.set, t⟩ => if ValType.nv t then some ⟨[t], [x], []⟩ else none
      | _ => none
  | .localTee x =>
      match C.locals[x.val]? with
      | some ⟨.set, t⟩ => if ValType.nv t then some ⟨[t], [x], [t]⟩ else none
      | _ => none
  | .globalGet x =>
      match C.globals[x.val]? with
      | some gt => if ValType.nv gt.valtype then some ⟨[], [], [gt.valtype]⟩ else none
      | none => none
  | .globalSet x =>
      match C.globals[x.val]? with
      | some ⟨some .mut, t⟩ => if ValType.nv t then some ⟨[t], [], []⟩ else none
      | _ => none
  | .load nt none x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ nt.size / 8 then
            some ⟨[mt.addr.toValType], [], [ValType.num nt]⟩
          else none
      | none => none
  | .load nt (some o) x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ o.sz.toNat / 8 then
            some ⟨[mt.addr.toValType], [], [ValType.num nt]⟩
          else none
      | none => none
  | .store nt none x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ nt.size / 8 then
            some ⟨[mt.addr.toValType, ValType.num nt], [], []⟩
          else none
      | none => none
  | .store nt (some o) x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ o.sz.toNat / 8 then
            some ⟨[mt.addr.toValType, ValType.num nt], [], []⟩
          else none
      | none => none
  | .vload _ none x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ 16 then some ⟨[mt.addr.toValType], [], [ValType.v128]⟩
          else none
      | none => none
  | .vload _ (some (.shape sz n _)) x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ sz.toNat / 8 * n then
            some ⟨[mt.addr.toValType], [], [ValType.v128]⟩
          else none
      | none => none
  | .vload _ (some (.splat sz)) x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ sz.toNat / 8 then
            some ⟨[mt.addr.toValType], [], [ValType.v128]⟩
          else none
      | none => none
  | .vload _ (some (.zero sz)) x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ sz.toNat / 8 then
            some ⟨[mt.addr.toValType], [], [ValType.v128]⟩
          else none
      | none => none
  | .vloadLane _ sz x ao i =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ sz.toNat / 8 ∧ i.val < 128 / sz.toNat then
            some ⟨[mt.addr.toValType, ValType.v128], [], [ValType.v128]⟩
          else none
      | none => none
  | .vstore _ x ao =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ 16 then
            some ⟨[mt.addr.toValType, ValType.v128], [], []⟩
          else none
      | none => none
  | .vstoreLane _ sz x ao i =>
      match C.mems[x.val]? with
      | some mt =>
          if 2 ^ ao.align.val ≤ sz.toNat / 8 ∧ i.val < 128 / sz.toNat then
            some ⟨[mt.addr.toValType, ValType.v128], [], []⟩
          else none
      | none => none
  | .memorySize x =>
      match C.mems[x.val]? with
      | some mt => some ⟨[], [], [mt.addr.toValType]⟩
      | none => none
  | .memoryGrow x =>
      match C.mems[x.val]? with
      | some mt => some ⟨[mt.addr.toValType], [], [mt.addr.toValType]⟩
      | none => none
  | .memoryFill x =>
      match C.mems[x.val]? with
      | some mt =>
          some ⟨[mt.addr.toValType, ValType.i32, mt.addr.toValType], [], []⟩
      | none => none
  | .memoryCopy x y =>
      match C.mems[x.val]?, C.mems[y.val]? with
      | some mt₁, some mt₂ =>
          some ⟨[mt₁.addr.toValType, mt₂.addr.toValType,
                 (AddrType.min mt₁.addr mt₂.addr).toValType], [], []⟩
      | _, _ => none
  | .memoryInit x y =>
      match C.mems[x.val]?, C.datas[y.val]? with
      | some mt, some .ok =>
          some ⟨[mt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
      | _, _ => none
  | .dataDrop x =>
      match C.datas[x.val]? with
      | some .ok => some ⟨[], [], []⟩
      | none => none
  | .const nt _ => some ⟨[], [], [ValType.num nt]⟩
  | .unop nt _ => some ⟨[ValType.num nt], [], [ValType.num nt]⟩
  | .binop nt _ => some ⟨[ValType.num nt, ValType.num nt], [], [ValType.num nt]⟩
  | .testop nt _ => some ⟨[ValType.num nt], [], [ValType.i32]⟩
  | .relop nt _ => some ⟨[ValType.num nt, ValType.num nt], [], [ValType.i32]⟩
  | .cvtop nt₁ nt₂ _ => some ⟨[ValType.num nt₂], [], [ValType.num nt₁]⟩
  | .vconst _ _ => some ⟨[], [], [ValType.v128]⟩
  | .vvunop _ _ => some ⟨[ValType.v128], [], [ValType.v128]⟩
  | .vvbinop _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vvternop _ _ =>
      some ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vvtestop _ _ => some ⟨[ValType.v128], [], [ValType.i32]⟩
  | .vunop _ _ => some ⟨[ValType.v128], [], [ValType.v128]⟩
  | .vbinop _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vternop _ _ =>
      some ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vtestop _ _ => some ⟨[ValType.v128], [], [ValType.i32]⟩
  | .vrelop _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vshiftop _ _ => some ⟨[ValType.v128, ValType.i32], [], [ValType.v128]⟩
  | .vbitmask _ => some ⟨[ValType.v128], [], [ValType.i32]⟩
  | .vswizzlop _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vshuffle sh is =>
      if is.all (fun i => decide (i.val < 2 * sh.val.dim.toNat)) then
        some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
      else none
  | .vextunop _ _ _ => some ⟨[ValType.v128], [], [ValType.v128]⟩
  | .vextbinop _ _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vextternop _ _ _ =>
      some ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vnarrow _ _ _ => some ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  | .vcvtop _ _ _ => some ⟨[ValType.v128], [], [ValType.v128]⟩
  | .vsplat sh => some ⟨[ValType.num sh.unpack], [], [ValType.v128]⟩
  | .vextractLane sh _ i =>
      if i.val < sh.dim.toNat then some ⟨[ValType.v128], [], [ValType.num sh.unpack]⟩
      else none
  | .vreplaceLane sh i =>
      if i.val < sh.dim.toNat then
        some ⟨[ValType.v128, ValType.num sh.unpack], [], [ValType.v128]⟩
      else none
  | _ => none

/-- The unique declarative type of a fragment instruction, when it has one. -/
def instrType (C : Context) (i : Instr) : Option InstrType :=
  if Instr.wf i = true then instrTypeRaw C i else none

/-! ## The unrestricted fixed-type opcode dispatcher

Most Core instructions have a type determined by their immediate operands and
the context.  `instrTypeRawA` extends the earlier numeric/vector dispatcher at
exactly those arms; instructions whose rule leaves a heap type, nullability,
stack prefix, or local-initialization effect existential are handled directly
by the full stack pass below. -/

def instrTypeRawA (C : Context) : Instr → Option InstrType
  | .select (some [t]) =>
      if checkValtypeOkA C t then some ⟨[t, t, ValType.i32], [], [t]⟩ else none
  | .select (some _) => none
  | .brIf l =>
      match C.labels[l.val]? with
      | some ts => some ⟨ts ++ [ValType.i32], [], ts⟩
      | none => none
  | .call x =>
      match C.funcs[x.val]? with
      | some dt => (funcTypeOfA dt).map fun p => ⟨p.1, [], p.2⟩
      | none => none
  | .callRef (.idx x) =>
      match C.types[x.val]? with
      | some dt => (funcTypeOfA dt).map fun p =>
          ⟨p.1 ++ [.ref (.ref (some .null) (.use (.idx x)))], [], p.2⟩
      | none => none
  | .callRef _ => none
  | .callIndirect x (.idx y) =>
      match C.tables[x.val]?, C.types[y.val]? with
      | some tt, some dt =>
          if decReftypeSubN C C.subtypeFuel tt.elem RefType.funcref then
            (funcTypeOfA dt).map fun p => ⟨p.1 ++ [tt.addr.toValType], [], p.2⟩
          else none
      | _, _ => none
  | .callIndirect _ _ => none
  | .localGet x =>
      match C.locals[x.val]? with
      | some ⟨.set, t⟩ => some ⟨[], [], [t]⟩
      | _ => none
  | .localSet x =>
      match C.locals[x.val]? with
      | some ⟨_, t⟩ => some ⟨[t], [x], []⟩
      | none => none
  | .localTee x =>
      match C.locals[x.val]? with
      | some ⟨_, t⟩ => some ⟨[t], [x], [t]⟩
      | none => none
  | .globalGet x =>
      match C.globals[x.val]? with
      | some gt => some ⟨[], [], [gt.valtype]⟩
      | none => none
  | .globalSet x =>
      match C.globals[x.val]? with
      | some ⟨some .mut, t⟩ => some ⟨[t], [], []⟩
      | _ => none
  | .refNull ht =>
      if checkHeaptypeOkA C ht then
        some ⟨[], [], [.ref (.ref (some .null) ht)]⟩
      else none
  | .refFunc x =>
      match C.funcs[x.val]? with
      | some dt =>
          if decide (x ∈ C.refs) then
            some ⟨[], [], [.ref (.ref none (.use (.defd dt)))]⟩
          else none
      | none => none
  | .refI31 => some ⟨[ValType.i32], [], [.ref (.ref none (.abs .i31))]⟩
  | .refEq => some ⟨[.ref RefType.eqref, .ref RefType.eqref], [], [ValType.i32]⟩
  | .i31Get _ => some ⟨[.ref RefType.i31ref], [], [ValType.i32]⟩
  | .structNew x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.struct fts) =>
              some ⟨fts.unpacked, [], [.ref (.ref none (.use (.idx x)))]⟩
          | _ => none
      | none => none
  | .structNewDefault x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.struct fts) =>
              if fts.unpacked.all ValType.hasDefault then
                some ⟨[], [], [.ref (.ref none (.use (.idx x)))]⟩
              else none
          | _ => none
      | none => none
  | .structGet sx x i =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.struct fts) => match (FieldTypes.toList fts)[i.val]? with
              | some (.mk _ zt) =>
                  if decide ((sx = none) ↔ StorageType.isUnpacked zt = true) then
                    some ⟨[.ref (.ref (some .null) (.use (.idx x)))], [],
                      [StorageType.unpack zt]⟩
                  else none
              | none => none
          | _ => none
      | none => none
  | .structSet x i =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.struct fts) => match (FieldTypes.toList fts)[i.val]? with
              | some (.mk (some .mut) zt) =>
                  some ⟨[.ref (.ref (some .null) (.use (.idx x))),
                    StorageType.unpack zt], [], []⟩
              | _ => none
          | _ => none
      | none => none
  | .arrayNew x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array ft) =>
              some ⟨[StorageType.unpack ft.storage, ValType.i32], [],
                [.ref (.ref none (.use (.idx x)))]⟩
          | _ => none
      | none => none
  | .arrayNewDefault x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array ft) =>
              if (StorageType.unpack ft.storage).hasDefault then
                some ⟨[ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
              else none
          | _ => none
      | none => none
  | .arrayNewFixed x n =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array ft) =>
              some ⟨List.replicate n.val (StorageType.unpack ft.storage), [],
                [.ref (.ref none (.use (.idx x)))]⟩
          | _ => none
      | none => none
  | .arrayNewElem x y =>
      match C.types[x.val]?, C.elems[y.val]? with
      | some dt, some rt' => match expandDt dt with
          | some (.array (.mk _ (.val (.ref rt)))) =>
              if decReftypeSubN C C.subtypeFuel rt' rt then
                some ⟨[ValType.i32, ValType.i32], [],
                  [.ref (.ref none (.use (.idx x)))]⟩
              else none
          | _ => none
      | _, _ => none
  | .arrayNewData x y =>
      match C.types[x.val]?, C.datas[y.val]? with
      | some dt, some .ok => match expandDt dt with
          | some (.array ft) =>
              if (StorageType.unpack ft.storage).isNumOrVec then
                some ⟨[ValType.i32, ValType.i32], [],
                  [.ref (.ref none (.use (.idx x)))]⟩
              else none
          | _ => none
      | _, _ => none
  | .arrayGet sx x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array ft) =>
              if decide ((sx = none) ↔ StorageType.isUnpacked ft.storage = true) then
                some ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32], [],
                  [StorageType.unpack ft.storage]⟩
              else none
          | _ => none
      | none => none
  | .arraySet x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array (.mk (some .mut) zt)) =>
              some ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
                StorageType.unpack zt], [], []⟩
          | _ => none
      | none => none
  | .arrayLen => some ⟨[.ref RefType.arrayref], [], [ValType.i32]⟩
  | .arrayFill x =>
      match C.types[x.val]? with
      | some dt => match expandDt dt with
          | some (.array (.mk (some .mut) zt)) =>
              some ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
                StorageType.unpack zt, ValType.i32], [], []⟩
          | _ => none
      | none => none
  | .arrayCopy x₁ x₂ =>
      match C.types[x₁.val]?, C.types[x₂.val]? with
      | some dt₁, some dt₂ => match expandDt dt₁, expandDt dt₂ with
          | some (.array (.mk (some .mut) zt₁)), some (.array (.mk _ zt₂)) =>
              if decStoragetypeSubN C C.subtypeFuel zt₂ zt₁ then
                some ⟨[.ref (.ref (some .null) (.use (.idx x₁))), ValType.i32,
                  .ref (.ref (some .null) (.use (.idx x₂))), ValType.i32,
                  ValType.i32], [], []⟩
              else none
          | _, _ => none
      | _, _ => none
  | .arrayInitElem x y =>
      match C.types[x.val]?, C.elems[y.val]? with
      | some dt, some rt => match expandDt dt with
          | some (.array (.mk (some .mut) zt)) =>
              if decStoragetypeSubN C C.subtypeFuel (.val (.ref rt)) zt then
                some ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
                  ValType.i32, ValType.i32], [], []⟩
              else none
          | _ => none
      | _, _ => none
  | .arrayInitData x y =>
      match C.types[x.val]?, C.datas[y.val]? with
      | some dt, some .ok => match expandDt dt with
          | some (.array (.mk (some .mut) zt)) =>
              if (StorageType.unpack zt).isNumOrVec then
                some ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
                  ValType.i32, ValType.i32], [], []⟩
              else none
          | _ => none
      | _, _ => none
  | .tableGet x =>
      match C.tables[x.val]? with
      | some tt => some ⟨[tt.addr.toValType], [], [.ref tt.elem]⟩
      | none => none
  | .tableSet x =>
      match C.tables[x.val]? with
      | some tt => some ⟨[tt.addr.toValType, .ref tt.elem], [], []⟩
      | none => none
  | .tableSize x =>
      match C.tables[x.val]? with
      | some tt => some ⟨[], [], [tt.addr.toValType]⟩
      | none => none
  | .tableGrow x =>
      match C.tables[x.val]? with
      | some tt => some ⟨[.ref tt.elem, tt.addr.toValType], [], [ValType.i32]⟩
      | none => none
  | .tableFill x =>
      match C.tables[x.val]? with
      | some tt =>
          some ⟨[tt.addr.toValType, .ref tt.elem, tt.addr.toValType], [], []⟩
      | none => none
  | .tableCopy x₁ x₂ =>
      match C.tables[x₁.val]?, C.tables[x₂.val]? with
      | some tt₁, some tt₂ =>
          if decReftypeSubN C C.subtypeFuel tt₂.elem tt₁.elem then
            some ⟨[tt₁.addr.toValType, tt₂.addr.toValType,
              (AddrType.min tt₁.addr tt₂.addr).toValType], [], []⟩
          else none
      | _, _ => none
  | .tableInit x y =>
      match C.tables[x.val]?, C.elems[y.val]? with
      | some tt, some rt =>
          if decReftypeSubN C C.subtypeFuel rt tt.elem then
            some ⟨[tt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
          else none
      | _, _ => none
  | .elemDrop x =>
      match C.elems[x.val]? with
      | some _ => some ⟨[], [], []⟩
      | none => none
  | _ => none

def instrTypeA (C : Context) (i : Instr) : Option InstrType :=
  if Instr.wf i = true then instrTypeRawA C i else none

theorem instrTypeA_sound {C : Context} {i : Instr} {it : InstrType}
    (h : instrTypeA C i = some it) : Instr_okA C i it := by
  rw [instrTypeA] at h
  by_cases hwf : Instr.wf i = true
  · rw [if_pos hwf] at h
    unfold instrTypeRawA at h
    split at h
    · -- SELECT t
      rename_i t
      split at h
      · rename_i ht
        injection h with h; subst h
        exact .select_expl (checkValtypeOkA_sound ht)
      · contradiction
    · contradiction
    · -- BR_IF
      rename_i l
      split at h
      · rename_i ts hl
        injection h with h; subst h
        exact .br_if hl
      · contradiction
    · -- CALL
      rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact .call hx (.mk he)
        · contradiction
      · contradiction
    · -- CALL_REF
      rename_i x
      split at h
      · rename_i dt hx
        unfold funcTypeOfA at h
        split at h
        · rename_i dom cod he
          injection h with h; subst h
          exact .call_ref hx (.mk he)
        · contradiction
      · contradiction
    · contradiction
    · -- CALL_INDIRECT
      rename_i x y
      split at h
      · rename_i tt dt hx hy
        split at h
        · rename_i hsub
          unfold funcTypeOfA at h
          split at h
          · rename_i dom cod he
            injection h with h; subst h
            exact .call_indirect hx (decReftypeSubN_sound hsub) hy (.mk he)
          · contradiction
        · contradiction
      · contradiction
    · contradiction
    · -- LOCAL.GET
      rename_i x
      split at h
      · rename_i t hx
        injection h with h; subst h
        exact .local_get hx
      · contradiction
    · -- LOCAL.SET
      rename_i x
      split at h
      · rename_i ini t hx
        injection h with h; subst h
        exact .local_set hx
      · contradiction
    · -- LOCAL.TEE
      rename_i x
      split at h
      · rename_i ini t hx
        injection h with h; subst h
        exact .local_tee hx
      · contradiction
    · -- GLOBAL.GET
      rename_i x
      split at h
      · rename_i gt hx
        injection h with h; subst h
        exact .global_get hx
      · contradiction
    · -- GLOBAL.SET
      rename_i x
      split at h
      · rename_i t hx
        injection h with h; subst h
        exact .global_set hx
      · contradiction
    · -- REF.NULL
      rename_i ht
      split at h
      · rename_i hok
        injection h with h; subst h
        exact .ref_null (checkHeaptypeOkA_sound hok)
      · contradiction
    · -- REF.FUNC
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i href
          injection h with h; subst h
          exact .ref_func hx (of_decide_eq_true href)
        · contradiction
      · contradiction
    · injection h with h; subst h; exact .ref_i31
    · injection h with h; subst h; exact .ref_eq
    · rename_i sx
      injection h with h; subst h; exact .i31_get
    · -- STRUCT.NEW
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          injection h with h; subst h
          exact .struct_new hx (.mk he)
        · contradiction
      · contradiction
    · -- STRUCT.NEW_DEFAULT
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          split at h
          · rename_i hd
            injection h with h; subst h
            exact .struct_new_default hx (.mk he)
              (fun t ht => Defaultable.mk (List.all_eq_true.mp hd t ht))
          · contradiction
        · contradiction
      · contradiction
    · -- STRUCT.GET
      rename_i sx x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          split at h
          · rename_i m zt hft
            split at h
            · rename_i hs
              injection h with h; subst h
              exact .struct_get hx (.mk he) hft (of_decide_eq_true hs)
            · contradiction
          · contradiction
        · contradiction
      · contradiction
    · -- STRUCT.SET
      rename_i x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i fts he
          split at h
          · rename_i zt hft
            injection h with h; subst h
            exact .struct_set hx (.mk he) hft
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.NEW
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          injection h with h; subst h
          exact .array_new hx (.mk he)
        · contradiction
      · contradiction
    · -- ARRAY.NEW_DEFAULT
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          split at h
          · rename_i hd
            injection h with h; subst h
            exact .array_new_default hx (.mk he) (Defaultable.mk hd)
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.NEW_FIXED
      rename_i x n
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          injection h with h; subst h
          exact .array_new_fixed hx (.mk he)
        · contradiction
      · contradiction
    · -- ARRAY.NEW_ELEM
      rename_i x y
      split at h
      · rename_i dt rt' hx hy
        split at h
        · rename_i m rt he
          split at h
          · rename_i hs
            injection h with h; subst h
            exact .array_new_elem hx (.mk he) hy (decReftypeSubN_sound hs)
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.NEW_DATA
      rename_i x y
      split at h
      · rename_i dt hx hy
        split at h
        · rename_i ft he
          split at h
          · rename_i hn
            injection h with h; subst h
            exact .array_new_data hx (.mk he) hn hy
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.GET
      rename_i sx x
      split at h
      · rename_i dt hx
        split at h
        · rename_i ft he
          split at h
          · rename_i hs
            injection h with h; subst h
            exact .array_get hx (.mk he) (of_decide_eq_true hs)
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.SET
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i zt he
          injection h with h; subst h
          exact .array_set hx (.mk he)
        · contradiction
      · contradiction
    · injection h with h; subst h; exact .array_len
    · -- ARRAY.FILL
      rename_i x
      split at h
      · rename_i dt hx
        split at h
        · rename_i zt he
          injection h with h; subst h
          exact .array_fill hx (.mk he)
        · contradiction
      · contradiction
    · -- ARRAY.COPY
      rename_i x₁ x₂
      split at h
      · rename_i dt₁ dt₂ hx₁ hx₂
        split at h
        · rename_i zt₁ m zt₂ he₁ he₂
          split at h
          · rename_i hs
            injection h with h; subst h
            exact .array_copy hx₁ (.mk he₁) hx₂ (.mk he₂)
              (decStoragetypeSubN_sound hs)
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.INIT_ELEM
      rename_i x y
      split at h
      · rename_i dt rt hx hy
        split at h
        · rename_i zt he
          split at h
          · rename_i hs
            injection h with h; subst h
            exact .array_init_elem hx (.mk he) hy (decStoragetypeSubN_sound hs)
          · contradiction
        · contradiction
      · contradiction
    · -- ARRAY.INIT_DATA
      rename_i x y
      split at h
      · rename_i dt hx hy
        split at h
        · rename_i zt he
          split at h
          · rename_i hn
            injection h with h; subst h
            exact .array_init_data hx (.mk he) hn hy
          · contradiction
        · contradiction
      · contradiction
    · -- TABLE.GET
      rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact .table_get hx
      · contradiction
    · -- TABLE.SET
      rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact .table_set hx
      · contradiction
    · -- TABLE.SIZE
      rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact .table_size hx
      · contradiction
    · -- TABLE.GROW
      rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact .table_grow hx
      · contradiction
    · -- TABLE.FILL
      rename_i x
      split at h
      · rename_i tt hx
        injection h with h; subst h
        exact .table_fill hx
      · contradiction
    · -- TABLE.COPY
      rename_i x₁ x₂
      split at h
      · rename_i tt₁ tt₂ hx₁ hx₂
        split at h
        · rename_i hs
          injection h with h; subst h
          exact .table_copy hx₁ hx₂ (decReftypeSubN_sound hs)
        · contradiction
      · contradiction
    · -- TABLE.INIT
      rename_i x y
      split at h
      · rename_i tt rt hx hy
        split at h
        · rename_i hs
          injection h with h; subst h
          exact .table_init hx hy (decReftypeSubN_sound hs)
        · contradiction
      · contradiction
    · -- ELEM.DROP
      rename_i x
      split at h
      · rename_i rt hx
        injection h with h; subst h
        exact .elem_drop hx
      · contradiction
    · contradiction
  · rw [if_neg hwf] at h
    contradiction


/-! ## The single pass -/

/-! `validate(opcode)` of the appendix, as a total function on the frame state.
Everything outside the decided fragment is rejected. -/

mutual
/-- The appendix's `validate(opcode)` on one instruction. -/
def checkInstr (C : Context) : St → Instr → Option St
  | st, .unreachable => some st.unreach
  | st, .drop =>
      match st.pop with
      | some (_, st') => some st'
      | none => none
  | st, .select none =>
      match st.popE ValType.i32 with
      | some st₁ =>
          match st₁.pop with
          | some (t₁, st₂) =>
              match st₂.pop with
              | some (t₂, st₃) =>
                  if (ValType.nvb t₁ && ValType.nvb t₂) &&
                      (subOf t₁ t₂ || subOf t₂ t₁) then
                    some (st₃.push (if t₁ == ValType.bot then t₂ else t₁))
                  else none
              | none => none
          | none => none
      | none => none
  | st, .br l =>
      match C.labels[l.val]? with
      | some ts =>
          if nvs ts then
            match st.pops ts with
            | some _ => some st.unreach
            | none => none
          else none
      | none => none
  | st, .brTable ls l =>
      match st.popE ValType.i32 with
      | some st₁ =>
          match C.labels[l.val]? with
          | some ts =>
              match st₁.popN ts.length with
              | some (us, _) =>
                  if subs us ts &&
                      ls.all (fun l' =>
                        match C.labels[l'.val]? with
                        | some ts' => subs us ts'
                        | none => false) then
                    some st.unreach
                  else none
              | none => none
          | none => none
      | none => none
  | st, .ret =>
      match C.ret with
      | some ts =>
          if nvs ts then
            match st.pops ts with
            | some _ => some st.unreach
            | none => none
          else none
      | none => none
  | st, .returnCall x =>
      match C.funcs[x.val]? with
      | some dt =>
          match funcTypeOf dt with
          | some (dom, cod) =>
              match C.ret with
              | some ts =>
                  if cod == ts then
                    match st.pops dom with
                    | some _ => some st.unreach
                    | none => none
                  else none
              | none => none
          | none => none
      | none => none
  | st, .block bt body =>
      match blockType C bt with
      | some (ts₁, ts₂) =>
          match st.pops ts₁ with
          | some st₀ =>
              match checkSeq (Context.pushLabel ts₂ C) (St.mk false [] |>.pushs ts₁) body with
              | some stB => if stB.finish ts₂ then some (st₀.pushs ts₂) else none
              | none => none
          | none => none
      | none => none
  | st, .loop bt body =>
      match blockType C bt with
      | some (ts₁, ts₂) =>
          match st.pops ts₁ with
          | some st₀ =>
              match checkSeq (Context.pushLabel ts₁ C) (St.mk false [] |>.pushs ts₁) body with
              | some stB => if stB.finish ts₂ then some (st₀.pushs ts₂) else none
              | none => none
          | none => none
      | none => none
  | st, .ifElse bt thn els =>
      match blockType C bt with
      | some (ts₁, ts₂) =>
          match st.popE ValType.i32 with
          | some st' =>
              match st'.pops ts₁ with
              | some st₀ =>
                  match checkSeq (Context.pushLabel ts₂ C) (St.mk false [] |>.pushs ts₁) thn,
                        checkSeq (Context.pushLabel ts₂ C) (St.mk false [] |>.pushs ts₁) els with
                  | some stT, some stE =>
                      if stT.finish ts₂ && stE.finish ts₂ then some (st₀.pushs ts₂) else none
                  | _, _ => none
              | none => none
          | none => none
      | none => none
  | st, i =>
      match instrType C i with
      | some it =>
          match st.pops it.dom with
          | some st₀ => some (st₀.pushs it.cod)
          | none => none
      | none => none

/-- The appendix's single pass over a sequence of opcodes. -/
def checkSeq (C : Context) : St → InstrSeq → Option St
  | st, .nil => some st
  | st, .cons i rest =>
      match checkInstr C st i with
      | some st' => checkSeq C st' rest
      | none => none
end

/-- The appendix's outermost frame: an expression is checked from an empty,
reachable frame and must end with exactly the declared results. -/
def checkExpr (C : Context) (e : Expr) (ts : List ValType) : Bool :=
  match checkSeq C (St.mk false []) e with
  | some st => st.finish ts
  | none => false

/-! ## Full amended-Core stack pass

The full pass carries the definite-initialization effects of `local.set` and
`local.tee`.  The operand stack remains `St`; only its matching operation is
changed to `popsA`, which includes corrected reference subtyping. -/

def St.finishA (C : Context) (st : St) (ts : List ValType) : Bool :=
  match st.popsA C ts with
  | some st' => st'.vals.isEmpty
  | none => false

def Context.setEffects : Context → List LocalIdx → Option Context
  | C, [] => some C
  | C, x :: xs =>
      match C.locals[x.val]? with
      | some lt => Context.setEffects (C.setLocal x ⟨.set, lt.valtype⟩) xs
      | none => none

def splitLast? {α : Type} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: as => (splitLast? as).map fun p => (a :: p.1, p.2)

def checkCatchA (C : Context) : Catch → Bool
  | .tag x l =>
      match C.tags[x.val]?, C.labels[l.val]? with
      | some jt, some ts => match asDefType jt with
          | some dt => match expandDt dt with
              | some (.func dom .nil) =>
                  subsA C (ValTypes.toList dom) ts
              | _ => false
          | none => false
      | _, _ => false
  | .tagRef x l =>
      match C.tags[x.val]?, C.labels[l.val]? with
      | some jt, some ts => match asDefType jt with
          | some dt => match expandDt dt with
              | some (.func dom .nil) =>
                  subsA C (ValTypes.toList dom ++
                    [.ref (.ref none (.abs .exn))]) ts
              | _ => false
          | none => false
      | _, _ => false
  | .all l =>
      match C.labels[l.val]? with
      | some ts => subsA C [] ts
      | none => false
  | .allRef l =>
      match C.labels[l.val]? with
      | some ts => subsA C [.ref (.ref none (.abs .exn))] ts
      | none => false

/-- Infer the reference witness needed by a syntax rule from an untyped pop.
`BOT` (including the empty polymorphic stack) uses semantic heap bottom, which
is well formed and is below every value type. -/
def St.popRef (st : St) : Option (Option RefType × St) :=
  match st.pop with
  | some (.ref rt, st') => some (some rt, st')
  | some (.bot, st') => some (none, st')
  | _ => none

def applyTypeA (C : Context) (st : St) (it : InstrType) : Option St :=
  match st.popsA C it.dom with
  | some st' => some (st'.pushs it.cod)
  | none => none

mutual

def checkInstrA (C : Context) (st : St) : Instr → Option (List LocalIdx × St)
  | .unreachable => some ([], st.unreach)
  | .drop =>
      match st.pop with
      | some (_, st') => some ([], st')
      | none => none
  | .select none =>
      match st.popEA C ValType.i32 with
      | some st₁ => match st₁.pop with
          | some (t₁, st₂) => match st₂.pop with
              | some (t₂, st₃) =>
                  if (t₁.isNumOrVec && t₂.isNumOrVec) &&
                      (subOfA C t₁ t₂ || subOfA C t₂ t₁) then
                    some ([], st₃.push (if t₁ == ValType.bot then t₂ else t₁))
                  else none
              | none => none
          | none => none
      | none => none
  | .br l =>
      match C.labels[l.val]? with
      | some ts => match st.popsA C ts with
          | some _ => some ([], st.unreach)
          | none => none
      | none => none
  | .brTable ls l =>
      match st.popEA C ValType.i32 with
      | some st₁ => match C.labels[l.val]? with
          | some ts => match st₁.popN ts.length with
              | some (us, _) =>
                  if subsA C us ts && ls.all (fun l' =>
                      match C.labels[l'.val]? with
                      | some ts' => subsA C us ts'
                      | none => false) then
                    some ([], st.unreach)
                  else none
              | none => none
          | none => none
      | none => none
  | .brOnNull l =>
      match C.labels[l.val]?, st.popRef with
      | some ts, some (rt?, st₁) =>
          let ht := match rt? with
            | some (.ref _ ht) => ht
            | none => .abs .bot
          match st₁.popsA C ts with
          | some st₀ =>
              some ([], st₀.pushs (ts ++ [.ref (.ref none ht)]))
          | none => none
      | _, _ => none
  | .brOnNonNull l =>
      match C.labels[l.val]? with
      | some label => match splitLast? label with
          | some (ts, .ref (.ref _ ht)) =>
              applyTypeA C st
                ⟨ts ++ [.ref (.ref (some .null) ht)], [], ts⟩ |>.map ([], ·)
          | _ => none
      | none => none
  | .brOnCast l rt₁ rt₂ =>
      match C.labels[l.val]? with
      | some label => match splitLast? label with
          | some (ts, .ref rt) =>
              if checkReftypeOkA C rt₁ && checkReftypeOkA C rt₂ &&
                  decReftypeSubN C C.subtypeFuel rt₂ rt₁ &&
                  decReftypeSubN C C.subtypeFuel rt₂ rt then
                applyTypeA C st ⟨ts ++ [.ref rt₁], [],
                  ts ++ [.ref (RefType.diff rt₁ rt₂)]⟩ |>.map ([], ·)
              else none
          | _ => none
      | none => none
  | .brOnCastFail l rt₁ rt₂ =>
      match C.labels[l.val]? with
      | some label => match splitLast? label with
          | some (ts, .ref rt) =>
              if checkReftypeOkA C rt₁ && checkReftypeOkA C rt₂ &&
                  decReftypeSubN C C.subtypeFuel rt₂ rt₁ &&
                  decReftypeSubN C C.subtypeFuel (RefType.diff rt₁ rt₂) rt then
                applyTypeA C st ⟨ts ++ [.ref rt₁], [], ts ++ [.ref rt₂]⟩ |>.map ([], ·)
              else none
          | _ => none
      | none => none
  | .ret =>
      match C.ret with
      | some ts => match st.popsA C ts with
          | some _ => some ([], st.unreach)
          | none => none
      | none => none
  | .returnCall x =>
      match C.funcs[x.val]?, C.ret with
      | some dt, some ret => match funcTypeOfA dt with
          | some (dom, cod) =>
              if subsA C cod ret then match st.popsA C dom with
                | some _ => some ([], st.unreach)
                | none => none
              else none
          | none => none
      | _, _ => none
  | .returnCallRef (.idx x) =>
      match C.types[x.val]?, C.ret with
      | some dt, some ret => match funcTypeOfA dt with
          | some (dom, cod) =>
              if subsA C cod ret then
                match st.popsA C (dom ++
                    [.ref (.ref (some .null) (.use (.idx x)))]) with
                | some _ => some ([], st.unreach)
                | none => none
              else none
          | none => none
      | _, _ => none
  | .returnCallRef _ => none
  | .returnCallIndirect x (.idx y) =>
      match C.tables[x.val]?, C.types[y.val]?, C.ret with
      | some tt, some dt, some ret => match funcTypeOfA dt with
          | some (dom, cod) =>
              if decReftypeSubN C C.subtypeFuel tt.elem RefType.funcref &&
                  subsA C cod ret then
                match st.popsA C (dom ++ [tt.addr.toValType]) with
                | some _ => some ([], st.unreach)
                | none => none
              else none
          | none => none
      | _, _, _ => none
  | .returnCallIndirect _ _ => none
  | .throw x =>
      match C.tags[x.val]? with
      | some jt => match asDefType jt with
          | some dt => match expandDt dt with
              | some (.func dom .nil) =>
                  match st.popsA C (ValTypes.toList dom) with
                  | some _ => some ([], st.unreach)
                  | none => none
              | _ => none
          | none => none
      | none => none
  | .throwRef =>
      match st.popEA C (.ref (.ref (some .null) (.abs .exn))) with
      | some _ => some ([], st.unreach)
      | none => none
  | .refIsNull =>
      match st.popRef with
      | some (_, st') => some ([], st'.push ValType.i32)
      | none => none
  | .refAsNonNull =>
      match st.popRef with
      | some (rt?, st') =>
          let ht := match rt? with
            | some (.ref _ ht) => ht
            | none => .abs .bot
          some ([], st'.push (.ref (.ref none ht)))
      | none => none
  | .refTest rt =>
      if checkReftypeOkA C rt then match st.popRef with
        | some (rt'?, st') =>
            let rt' := rt'?.getD rt
            if decReftypeSubN C C.subtypeFuel rt rt' then
              some ([], st'.push ValType.i32)
            else none
        | none => none
      else none
  | .refCast rt =>
      if checkReftypeOkA C rt then match st.popRef with
        | some (rt'?, st') =>
            let rt' := rt'?.getD rt
            if decReftypeSubN C C.subtypeFuel rt rt' then
              some ([], st'.push (.ref rt))
            else none
        | none => none
      else none
  | .externConvertAny =>
      match st.popRef with
      | some (some (.ref nul ht), st') =>
          if decHeaptypeSubN C C.subtypeFuel ht (.abs .any) then
            some ([], st'.push (.ref (.ref nul (.abs .extern))))
          else none
      | some (none, st') =>
          some ([], st'.push (.ref (.ref none (.abs .extern))))
      | _ => none
  | .anyConvertExtern =>
      match st.popRef with
      | some (some (.ref nul ht), st') =>
          if decHeaptypeSubN C C.subtypeFuel ht (.abs .extern) then
            some ([], st'.push (.ref (.ref nul (.abs .any))))
          else none
      | some (none, st') =>
          some ([], st'.push (.ref (.ref none (.abs .any))))
      | _ => none
  | .block bt body =>
      match blockTypeA C bt with
      | some (ts₁, ts₂) => match st.popsA C ts₁ with
          | some st₀ =>
              match checkSeqA (Context.pushLabel ts₂ C)
                  (St.mk false [] |>.pushs ts₁) body with
              | some (_, stB) =>
                  if stB.finishA (Context.pushLabel ts₂ C) ts₂ then
                    some ([], st₀.pushs ts₂)
                  else none
              | none => none
          | none => none
      | none => none
  | .loop bt body =>
      match blockTypeA C bt with
      | some (ts₁, ts₂) => match st.popsA C ts₁ with
          | some st₀ =>
              match checkSeqA (Context.pushLabel ts₁ C)
                  (St.mk false [] |>.pushs ts₁) body with
              | some (_, stB) =>
                  if stB.finishA (Context.pushLabel ts₁ C) ts₂ then
                    some ([], st₀.pushs ts₂)
                  else none
              | none => none
          | none => none
      | none => none
  | .ifElse bt thn els =>
      match blockTypeA C bt with
      | some (ts₁, ts₂) => match st.popEA C ValType.i32 with
          | some st' => match st'.popsA C ts₁ with
              | some st₀ =>
                  match checkSeqA (Context.pushLabel ts₂ C)
                      (St.mk false [] |>.pushs ts₁) thn,
                    checkSeqA (Context.pushLabel ts₂ C)
                      (St.mk false [] |>.pushs ts₁) els with
                  | some (_, stT), some (_, stE) =>
                      if stT.finishA (Context.pushLabel ts₂ C) ts₂ &&
                          stE.finishA (Context.pushLabel ts₂ C) ts₂ then
                        some ([], st₀.pushs ts₂)
                      else none
                  | _, _ => none
              | none => none
          | none => none
      | none => none
  | .tryTable bt cs body =>
      match blockTypeA C bt with
      | some (ts₁, ts₂) =>
          if cs.val.all (checkCatchA C) then match st.popsA C ts₁ with
            | some st₀ =>
                match checkSeqA (Context.pushLabel ts₂ C)
                    (St.mk false [] |>.pushs ts₁) body with
                | some (_, stB) =>
                    if stB.finishA (Context.pushLabel ts₂ C) ts₂ then
                      some ([], st₀.pushs ts₂)
                    else none
                | none => none
            | none => none
          else none
      | none => none
  | i =>
      match instrTypeA C i with
      | some it => (applyTypeA C st it).map (it.locals, ·)
      | none => match instrType C i with
          | some it => (applyTypeA C st it).map (it.locals, ·)
          | none => none

def checkSeqA (C : Context) (st : St) : InstrSeq → Option (List LocalIdx × St)
  | .nil => some ([], st)
  | .cons i rest =>
      match checkInstrA C st i with
      | some (xs₁, st') => match Context.setEffects C xs₁ with
          | some C' => match checkSeqA C' st' rest with
              | some (xs₂, st'') => some (xs₁ ++ xs₂, st'')
              | none => none
          | none => none
      | none => none

end

def checkExprA (C : Context) (e : Expr) (ts : List ValType) : Bool :=
  match checkSeqA C (St.mk false []) e with
  | some (_, st) => st.finishA C ts
  | none => false

/-! ## Soundness of the computed instruction types

Everything `instrType` accepts, the declarative judgment derives.  One case per
arm of `instrType`, and the arms are exactly the rules of
`2.3-validation.instructions.spectec` that the fragment covers. -/

/-- `$sizenn` reading of `nt.toInn?`. -/
theorem toInn_toNumType {nt : NumType} {n : Inn} (h : nt.toInn? = some n) :
    n.toNumType = nt := by
  cases nt <;> simp [NumType.toInn?] at h <;> (try subst h) <;> rfl

theorem instrType_sound {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) : Instr_okA C i it := by
  rw [instrType] at h
  by_cases hwf : Instr.wf i = true
  · rw [if_pos hwf] at h
    unfold instrTypeRaw at h
    split at h
    · -- NOP
      injection h with h; subst h; exact .nop
    · -- SELECT t
      rename_i t
      split at h
      · rename_i hnv
        injection h with h; subst h
        exact .select_expl (valtype_okA_of_nvb (ValType.nvb_of_nv hnv))
      · exact absurd h (by simp)
    · -- BR_IF
      rename_i l
      split at h
      · rename_i ts hlab
        split at h
        · injection h with h; subst h; exact .br_if hlab
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- CALL
      rename_i x
      split at h
      · rename_i dt hfun
        split at h
        · rename_i dom cod hft
          injection h with h; subst h
          rw [funcTypeOf] at hft
          split at hft
          · rename_i dom' cod' hexp
            split at hft
            · injection hft with hft
              obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hft
              exact h1 ▸ h2 ▸ .call hfun (.mk hexp)
            · exact absurd hft (by simp)
          · exact absurd hft (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- LOCAL.GET
      rename_i x
      split at h
      · rename_i t hloc
        split at h
        · injection h with h; subst h; exact .local_get hloc
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- LOCAL.SET
      rename_i x
      split at h
      · rename_i t hloc
        split at h
        · injection h with h; subst h; exact .local_set hloc
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- LOCAL.TEE
      rename_i x
      split at h
      · rename_i t hloc
        split at h
        · injection h with h; subst h; exact .local_tee hloc
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- GLOBAL.GET
      rename_i x
      split at h
      · rename_i gt hglob
        split at h
        · injection h with h; subst h
          obtain ⟨m, t⟩ := gt
          exact .global_get hglob
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- GLOBAL.SET
      rename_i x
      split at h
      · rename_i t hglob
        split at h
        · injection h with h; subst h; exact .global_set hglob
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- LOAD, unpacked
      rename_i nt x ao
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          exact .load_val hmem halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- LOAD, packed
      rename_i nt o x ao
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          simp only [Instr.wf] at hwf
          have hi : (nt.toInn?).isSome = true := by
            rw [LoadOp.wf] at hwf
            cases hn : nt.toInn? with
            | none => rw [hn] at hwf; exact absurd hwf (by simp)
            | some n => rfl
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hi
          have hnt : n.toNumType = nt := toInn_toNumType hn
          subst hnt
          exact .load_pack hmem hwf halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- STORE, unpacked
      rename_i nt x ao
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          exact .store_val hmem halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- STORE, packed
      rename_i nt o x ao
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          simp only [Instr.wf] at hwf
          have hi : (nt.toInn?).isSome = true := by
            rw [StoreOp.wf] at hwf
            cases hn : nt.toInn? with
            | none => rw [hn] at hwf; exact absurd hwf (by simp)
            | some n => rfl
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hi
          have hnt : n.toNumType = nt := toInn_toNumType hn
          subst hnt
          exact .store_pack hmem hwf halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VLOAD, full width
      rename_i vt x ao
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          exact .vload_val hmem halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VLOAD, SHAPE
      rename_i vt sz n sx x ao
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          simp only [Instr.wf] at hwf
          exact .vload_pack hmem hwf halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VLOAD, SPLAT
      rename_i vt sz x ao
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          exact .vload_splat hmem halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VLOAD, ZERO
      rename_i vt sz x ao
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          simp only [Instr.wf] at hwf
          exact .vload_zero hmem hwf halign
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VLOAD_LANE
      rename_i vt sz x ao lane
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i hcond
          injection h with h; subst h
          exact .vload_lane hmem hcond.1 hcond.2
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VSTORE
      rename_i vt x ao
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i halign
          injection h with h; subst h
          exact .vstore hmem (by simpa using halign)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- VSTORE_LANE
      rename_i vt sz x ao lane
      cases vt
      split at h
      · rename_i mt hmem
        split at h
        · rename_i hcond
          injection h with h; subst h
          exact .vstore_lane hmem hcond.1 hcond.2
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- MEMORY.SIZE
      rename_i x
      split at h
      · rename_i mt hmem
        injection h with h; subst h; exact .memory_size hmem
      · exact absurd h (by simp)
    · -- MEMORY.GROW
      rename_i x
      split at h
      · rename_i mt hmem
        injection h with h; subst h; exact .memory_grow hmem
      · exact absurd h (by simp)
    · -- MEMORY.FILL
      rename_i x
      split at h
      · rename_i mt hmem
        injection h with h; subst h; exact .memory_fill hmem
      · exact absurd h (by simp)
    · -- MEMORY.COPY
      rename_i x y
      split at h
      · rename_i mt₁ mt₂ hmem₁ hmem₂
        injection h with h; subst h; exact .memory_copy hmem₁ hmem₂
      · exact absurd h (by simp)
    · -- MEMORY.INIT
      rename_i x y
      split at h
      · rename_i mt hmem hdata
        injection h with h; subst h; exact .memory_init hmem hdata
      · exact absurd h (by simp)
    · -- DATA.DROP
      rename_i x
      split at h
      · rename_i hdata
        injection h with h; subst h; exact .data_drop hdata
      · exact absurd h (by simp)
    · -- CONST
      rename_i nt c
      injection h with h; subst h; exact .const hwf
    · -- UNOP
      rename_i nt op
      injection h with h; subst h; exact .unop hwf
    · -- BINOP
      rename_i nt op
      injection h with h; subst h; exact .binop hwf
    · -- TESTOP
      rename_i nt op
      injection h with h; subst h; exact .testop hwf
    · -- RELOP
      rename_i nt op
      injection h with h; subst h; exact .relop hwf
    · -- CVTOP
      rename_i nt₁ nt₂ op
      injection h with h; subst h; exact .cvtop hwf
    · -- VCONST
      rename_i vt c
      cases vt
      injection h with h; subst h; exact .vconst
    · -- VVUNOP
      rename_i vt op
      cases vt
      injection h with h; subst h; exact .vvunop
    · -- VVBINOP
      rename_i vt op
      cases vt
      injection h with h; subst h; exact .vvbinop
    · -- VVTERNOP
      rename_i vt op
      cases vt
      injection h with h; subst h; exact .vvternop
    · -- VVTESTOP
      rename_i vt op
      cases vt
      injection h with h; subst h; exact .vvtestop
    · -- VUNOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vunop hwf.1 hwf.2
    · -- VBINOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vbinop hwf.1 hwf.2
    · -- VTERNOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vternop hwf.1 hwf.2
    · -- VTESTOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vtestop hwf.1 hwf.2
    · -- VRELOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vrelop hwf.1 hwf.2
    · -- VSHIFTOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf] at hwf
      exact .vshiftop hwf
    · -- VBITMASK
      rename_i sh
      injection h with h; subst h
      simp only [Instr.wf] at hwf
      exact .vbitmask hwf
    · -- VSWIZZLOP
      rename_i sh op
      injection h with h; subst h
      simp only [Instr.wf] at hwf
      exact .vswizzlop hwf
    · -- VSHUFFLE
      rename_i sh is
      split at h
      · rename_i hlanes
        injection h with h; subst h
        simp only [Instr.wf, Bool.and_eq_true] at hwf
        refine .vshuffle hwf.1 (by simpa using hwf.2) ?_
        intro j hj
        have := List.all_eq_true.mp hlanes j hj
        simpa using this
      · exact absurd h (by simp)
    · -- VEXTUNOP
      rename_i sh₁ sh₂ op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vextunop hwf.1.1 hwf.1.2 hwf.2
    · -- VEXTBINOP
      rename_i sh₁ sh₂ op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vextbinop hwf.1.1 hwf.1.2 hwf.2
    · -- VEXTTERNOP
      rename_i sh₁ sh₂ op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vextternop hwf.1.1 hwf.1.2 hwf.2
    · -- VNARROW
      rename_i sh₁ sh₂ sx
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      exact .vnarrow hwf.1.1.1 hwf.1.1.2 hwf.1.2 hwf.2
    · -- VCVTOP
      rename_i sh₁ sh₂ op
      injection h with h; subst h
      simp only [Instr.wf, Bool.and_eq_true] at hwf
      exact .vcvtop hwf.1.1 hwf.1.2 hwf.2
    · -- VSPLAT
      rename_i sh
      injection h with h; subst h
      simp only [Instr.wf] at hwf
      exact .vsplat hwf
    · -- VEXTRACT_LANE
      rename_i sh sx lane
      split at h
      · rename_i hlane
        injection h with h; subst h
        simp only [Instr.wf, Bool.and_eq_true] at hwf
        exact .vextract_lane hwf.1 (by simpa using hwf.2) hlane
      · exact absurd h (by simp)
    · -- VREPLACE_LANE
      rename_i sh lane
      split at h
      · rename_i hlane
        injection h with h; subst h
        simp only [Instr.wf] at hwf
        exact .vreplace_lane hwf hlane
      · exact absurd h (by simp)
    · -- everything outside the fragment
      exact absurd h (by simp)
  · rw [if_neg hwf] at h; exact absurd h (by simp)


/-! ## Completeness of the computed instruction types

The nine instructions whose declarative rule leaves something free are handled
by `checkInstr` itself; for every other instruction of the fragment the rule
determines the type, and `instrType` computes it. -/

/-- The instructions whose declarative type is not determined by the
instruction and the context alone: the stack-polymorphic ones, `DROP` and the
unannotated `SELECT`, whose rules quantify over the operand type, and the four
structured ones, whose rule types a body. -/
def Instr.special : Instr → Bool
  | .unreachable => true
  | .drop => true
  | .select none => true
  | .br _ => true
  | .brTable _ _ => true
  | .ret => true
  | .returnCall _ => true
  | .block _ _ => true
  | .loop _ _ => true
  | .ifElse _ _ _ => true
  | _ => false

theorem frag_local {C : Context} (hC : Context.frag C = true) {x : LocalIdx}
    {lt : LocalType} (h : C.locals[x.val]? = some lt) :
    lt.init = Init.set ∧ ValType.nv lt.valtype = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  have := List.all_eq_true.mp hC.1.1.1.1.1 lt (List.mem_of_getElem? h)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem frag_label {C : Context} (hC : Context.frag C = true) {l : LabelIdx}
    {ts : List ValType} (h : C.labels[l.val]? = some ts) : nvs ts = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  exact List.all_eq_true.mp hC.1.1.1.1.2 ts (List.mem_of_getElem? h)

theorem frag_ret {C : Context} (hC : Context.frag C = true) {ts : List ValType}
    (h : C.ret = some ts) : nvs ts = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  have := hC.1.1.1.2
  rw [h] at this
  exact this

theorem frag_global {C : Context} (hC : Context.frag C = true) {x : GlobalIdx}
    {gt : GlobalType} (h : C.globals[x.val]? = some gt) : ValType.nv gt.valtype = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  exact List.all_eq_true.mp hC.1.1.2 gt (List.mem_of_getElem? h)

theorem frag_func {C : Context} (hC : Context.frag C = true) {x : FuncIdx}
    {dt : DefType} (h : C.funcs[x.val]? = some dt) : (funcTypeOf dt).isSome = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  exact List.all_eq_true.mp hC.1.2 dt (List.mem_of_getElem? h)

theorem frag_type {C : Context} (hC : Context.frag C = true) {x : TypeIdx}
    {dt : DefType} (h : C.types[x.val]? = some dt) : (funcTypeOf dt).isSome = true := by
  simp only [Context.frag, Bool.and_eq_true] at hC
  exact List.all_eq_true.mp hC.2 dt (List.mem_of_getElem? h)

/-- `Expand` is the graph of `$expanddt`, so a `deftype` known to expand to a
function type of the fragment expands to exactly that one. -/
theorem funcTypeOf_of_expand {dt : DefType} {dom cod : ValTypes}
    (hexp : Expand dt (.func dom cod)) (hs : (funcTypeOf dt).isSome = true) :
    funcTypeOf dt = some (ValTypes.toList dom, ValTypes.toList cod) := by
  cases hexp with
  | mk he =>
      have hred : funcTypeOf dt =
          (if (nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)) = true then
            some (ValTypes.toList dom, ValTypes.toList cod) else none) := by
        rw [funcTypeOf, he]
      rw [hred] at hs ⊢
      by_cases hif : (nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)) = true
      · rw [if_pos hif]
      · rw [if_neg hif] at hs; exact absurd hs (by simp)

theorem instrType_complete {C : Context} {i : Instr} {it : InstrType}
    (hC : Context.frag C = true) (hfrag : Instr.frag i = true)
    (hsp : Instr.special i = false) (h : Instr_okA C i it) : instrType C i = some it := by
  have hwf : Instr.wf i = true := Instr_okA.wf_of h
  rw [instrType, if_pos hwf]
  cases h
  case nop => rfl
  case select_expl t _ =>
      simp only [Instr.frag] at hfrag
      simp [instrTypeRaw, hfrag]
  case br_if l ts _ =>
      have hlab : C.labels[l.val]? = some ts := by assumption
      simp [instrTypeRaw, hlab, frag_label hC hlab]
  case call x dt dom cod _ _ =>
      have hfun : C.funcs[x.val]? = some dt := by assumption
      have hexp : Expand dt (.func dom cod) := by assumption
      simp [instrTypeRaw, hfun, funcTypeOf_of_expand hexp (frag_func hC hfun)]
  case local_get x t _ =>
      have hloc : C.locals[x.val]? = some ⟨.set, t⟩ := by assumption
      have hnv := (frag_local hC hloc).2
      simp only at hnv
      simp only [instrTypeRaw, hloc]
      simp [hnv]
  case local_set x ini t _ =>
      have hloc : C.locals[x.val]? = some ⟨ini, t⟩ := by assumption
      have h1 := (frag_local hC hloc).1
      have h2 := (frag_local hC hloc).2
      simp only at h1 h2
      subst h1
      simp only [instrTypeRaw, hloc]
      simp [h2]
  case local_tee x ini t _ =>
      have hloc : C.locals[x.val]? = some ⟨ini, t⟩ := by assumption
      have h1 := (frag_local hC hloc).1
      have h2 := (frag_local hC hloc).2
      simp only at h1 h2
      subst h1
      simp only [instrTypeRaw, hloc]
      simp [h2]
  case global_get x m t _ =>
      have hglob : C.globals[x.val]? = some ⟨m, t⟩ := by assumption
      have hnv := frag_global hC hglob
      simp only at hnv
      simp only [instrTypeRaw, hglob]
      simp [hnv]
  case global_set x t _ =>
      have hglob : C.globals[x.val]? = some ⟨some .mut, t⟩ := by assumption
      have hnv := frag_global hC hglob
      simp only at hnv
      simp only [instrTypeRaw, hglob]
      simp [hnv]
  case load nt op x ao mt _ _ _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ nt.size / 8 := by assumption
      have hpk : OptAll (fun (o : LoadOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op := by assumption
      cases op with
      | none => simp [instrTypeRaw, hmem, halign]
      | some o => simp [instrTypeRaw, hmem, (hpk o rfl).1]
  case load_val nt x ao mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ nt.size / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case load_pack n o x ao mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ o.sz.toNat / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case store nt op x ao mt _ _ _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ nt.size / 8 := by assumption
      have hpk : OptAll (fun (o : StoreOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op := by assumption
      cases op with
      | none => simp [instrTypeRaw, hmem, halign]
      | some o => simp [instrTypeRaw, hmem, (hpk o rfl).1]
  case store_val nt x ao mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ nt.size / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case store_pack n o x ao mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ o.sz.toNat / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case vload_val x ao mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ VecType.size .v128 / 8 := by assumption
      simp only [VecType.size] at halign
      simp [instrTypeRaw, hmem, halign]
  case vload_pack sz n sx x ao mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ sz.toNat / 8 * n := by assumption
      simp [instrTypeRaw, hmem, halign]
  case vload_splat sz x ao mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ sz.toNat / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case vload_zero sz x ao mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ sz.toNat / 8 := by assumption
      simp [instrTypeRaw, hmem, halign]
  case vload_lane sz x ao lane mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ sz.toNat / 8 := by assumption
      have hl : lane.val < 128 / sz.toNat := by assumption
      simp [instrTypeRaw, hmem, halign, hl]
  case vstore x ao mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ VecType.size .v128 / 8 := by assumption
      simp only [VecType.size] at halign
      simp [instrTypeRaw, hmem, halign]
  case vstore_lane sz x ao lane mt _ _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have halign : 2 ^ ao.align.val ≤ sz.toNat / 8 := by assumption
      have hl : lane.val < 128 / sz.toNat := by assumption
      simp [instrTypeRaw, hmem, halign, hl]
  case memory_size x mt _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      simp [instrTypeRaw, hmem]
  case memory_grow x mt _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      simp [instrTypeRaw, hmem]
  case memory_fill x mt _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      simp [instrTypeRaw, hmem]
  case memory_copy x₁ x₂ mt₁ mt₂ _ _ =>
      have hmem₁ : C.mems[x₁.val]? = some mt₁ := by assumption
      have hmem₂ : C.mems[x₂.val]? = some mt₂ := by assumption
      simp [instrTypeRaw, hmem₁, hmem₂]
  case memory_init x y mt _ _ =>
      have hmem : C.mems[x.val]? = some mt := by assumption
      have hdat : C.datas[y.val]? = some .ok := by assumption
      simp [instrTypeRaw, hmem, hdat]
  case data_drop x _ =>
      have hdat : C.datas[x.val]? = some .ok := by assumption
      simp [instrTypeRaw, hdat]
  case const nt c _ => rfl
  case unop nt op _ => rfl
  case binop nt op _ => rfl
  case testop nt op _ => rfl
  case relop nt op _ => rfl
  case cvtop nt₁ nt₂ op _ => rfl
  case vconst c => rfl
  case vvunop op => rfl
  case vvbinop op => rfl
  case vvternop op => rfl
  case vvtestop op => rfl
  case vunop sh op _ _ => rfl
  case vbinop sh op _ _ => rfl
  case vternop sh op _ _ => rfl
  case vtestop sh op _ _ => rfl
  case vrelop sh op _ _ => rfl
  case vshiftop sh op _ => rfl
  case vbitmask sh _ => rfl
  case vswizzlop sh op _ => rfl
  case vshuffle sh is _ _ _ =>
      have hlanes : SeqAll (fun (j : LaneIdx) => j.val < 2 * sh.val.dim.toNat) is := by
        assumption
      simp only [instrTypeRaw]
      rw [if_pos (List.all_eq_true.mpr (fun j hj => by simpa using hlanes j hj))]
  case vextunop sh₁ sh₂ op _ _ _ => rfl
  case vextbinop sh₁ sh₂ op _ _ _ => rfl
  case vextternop sh₁ sh₂ op _ _ _ => rfl
  case vnarrow sh₁ sh₂ sx _ _ _ _ => rfl
  case vcvtop sh₁ sh₂ op _ _ _ => rfl
  case vsplat sh _ => rfl
  case vextract_lane sh sx lane _ _ _ =>
      have hl : lane.val < sh.dim.toNat := by assumption
      simp [instrTypeRaw, hl]
  case vreplace_lane sh lane _ _ =>
      have hl : lane.val < sh.dim.toNat := by assumption
      simp [instrTypeRaw, hl]
  all_goals first
    | (exfalso; revert hfrag; simp [Instr.frag]; done)
    | (exfalso; revert hsp; simp [Instr.special]; done)


/-- Every operand type the computed instruction types mention is in the decided
fragment, so every operand the algorithm pushes is. -/
theorem funcTypeOf_nv {dt : DefType} {dom cod : List ValType}
    (h : funcTypeOf dt = some (dom, cod)) : nvs dom = true ∧ nvs cod = true := by
  rw [funcTypeOf] at h
  split at h
  · rename_i dom' cod' _
    split at h
    · rename_i hif
      simp only [Bool.and_eq_true] at hif
      injection h with h
      rw [Prod.mk.injEq] at h
      exact ⟨h.1 ▸ hif.1, h.2 ▸ hif.2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `funcTypeOf` is `Expand` at a function type of the fragment, read as a
function. -/
theorem funcTypeOf_expand {dt : DefType} {dom cod : List ValType}
    (h : funcTypeOf dt = some (dom, cod)) :
    ∃ d c : ValTypes, Expand dt (.func d c) ∧
      ValTypes.toList d = dom ∧ ValTypes.toList c = cod := by
  rw [funcTypeOf] at h
  cases hexp : expandDt dt with
  | none => simp only [hexp] at h; exact absurd h (by simp)
  | some ct =>
      cases ct with
      | func d c =>
          simp only [hexp] at h
          by_cases hif : (nvs (ValTypes.toList d) && nvs (ValTypes.toList c)) = true
          · rw [if_pos hif] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨d, c, .mk hexp, h.1.symm ▸ rfl, h.2.symm ▸ rfl⟩
          · rw [if_neg hif] at h; exact absurd h (by simp)
      | _ => simp only [hexp] at h; exact absurd h (by simp)

theorem instrType_nv {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) : nvs it.dom = true ∧ nvs it.cod = true := by
  rw [instrType] at h
  split at h
  · unfold instrTypeRaw at h
    split at h
    all_goals (try (split at h))
    all_goals (try (split at h))
    all_goals first
      | (simp at h; done)
      | (injection h with h
         subst h
         refine ⟨?_, ?_⟩ <;>
           simp_all [nvs, ValType.nv, ValType.i32, ValType.v128, AddrType.toValType]
         done)
      | (injection h with h
         subst h
         rename_i hft
         exact ⟨(funcTypeOf_nv hft).1, (funcTypeOf_nv hft).2⟩)
      | (injection h with h
         subst h
         simp_all [nvs, ValType.nv, ValType.i32, ValType.v128, AddrType.toValType]
         done)
  · exact absurd h (by simp)


/-! ## A GAP IN THE PINNED SEQUENCING RULE

The two theorems below are NEGATIVE results about the pinned declarative
judgment, and they are the reason this file does not carry an equivalence in
both directions.

`Instrs_ok/seq` of `2.3-validation.instructions.spectec` composes the HEAD
instruction, typed by `Instr_ok`, with the TAIL sequence:

    C |- instr_1 instr_2* : t_1* ->_(x_1* x_2*) t_3*
    -- Instr_ok:  C |- instr_1  : t_1* ->_(x_1*) t_2*
    -- Instrs_ok: ...          |- instr_2* : t_2* ->_(x_2*) t_3*

so the tail's DOMAIN must be exactly the head's CODOMAIN.  The only rules that
can adjust a type are `Instrs_ok/sub` and `Instrs_ok/frame`, and both apply to
SEQUENCES, never to the head instruction: `sub` preserves the length of the
domain (`Resulttype_sub` iterates over both sequences, so they agree in length),
and `frame` only makes a domain LONGER.  A head whose codomain is shorter than
what the tail consumes can therefore never be composed --- and an instruction
that consumes an operand pushed before the sequence began is exactly that case.

`(I32.CONST c) (BINOP I32 ADD)` is the smallest instance, and it is the example
the spec's own note under `Instrs_ok/frame` says subsumption handles:

    "the direct type of (CONST I32 2) is eps -> I32, not matching the two
     inputs expected by (BINOP I32 ADD).  The subsumption rule allows to weaken
     the type of (CONST I32 2) to the supertype I32 -> I32 I32 ..."

That weakening is `Instrs_ok/frame` applied to the SINGLETON SEQUENCE
`(CONST I32 2)`, which the head-first `seq` rule cannot use, because its head
premise is `Instr_ok`, not `Instrs_ok`.  The classic prose rule for a non-empty
instruction sequence carries the frame INSIDE the composition instead --- "there
is a sequence of value types t_0* such that t_2* = t_0* t*" --- and does not
have this gap.

CONSEQUENCE FOR THIS FILE.  `checkSeq` implements Core's algorithm, so it
accepts `(i32.const 1) (i32.add)`; the pinned judgment gives that sequence NO
type in ANY context.  An `Instrs_ok`-SOUNDNESS theorem for the algorithm is
therefore FALSE, and is not stated here.  Completeness --- everything the
pinned judgment accepts, the algorithm accepts --- is not affected.

WHOSE DEFECT THIS IS.  It is the PINNED SPECTEC SOURCE's, not this
transcription's, and not WebAssembly's.  Three independent checks:

  * the vendored file is byte-identical to upstream blob
    `bfd71e57ff457c61f546e0a308b99740fda02158` at the pinned commit
    `9d36019973201a19f9c9ebb0f10828b2fe2374aa` (2025-09-26), and the four rules
    above are the complete set --- there is no `Instr_ok/sub` and no
    `Instr_ok/frame` anywhere in the vendored tree;
  * the argument is about LENGTHS only (`|codomain of the head| = 1` versus
    `|domain of any tail type| >= 2`), so no operand-order or list-orientation
    convention in this repository can create or remove it;
  * upstream reached the same conclusion AFTER the pin.  WebAssembly/spec issue
    #2194, "instrs_ok/seq's principality requirement is slightly
    over-restrictive" (2026-06-22), reports it in the same terms, and PR #2197,
    "[spec] Fix instr sequence typing rules to actually be composable", merged
    it as `bd4633aced30b720ff62b44cf00c03ece792f008` on 2026-06-23 --- nine
    months after the pinned commit.

The pinned document contradicts the pinned rules on exactly this point:
`document/core/valid/instructions.rst:1357-1366`, at the SAME commit, says the
derivation exists and attributes the weakening `eps -> I32` to `I32 -> I32 I32`
to subsumption.  That is not an `Instrtype_sub` supertype --- the lengths differ
and `Resulttype_sub` is a synchronised iteration --- it is `Instrs_ok/frame` on
the singleton SEQUENCE, a step `seq` cannot consume.  Rendered prose cannot
distinguish `Instr_ok` from `Instrs_ok` (both print as `C |- ... : it`), which
is why the gap is invisible in the published document and only bites a
mechanisation.

WHAT THE REPOSITORY DOES ABOUT IT.  The pin is NOT advanced --- that would
change the vendored blob set and the rule inventory.  The deviation is recorded
as DEV-006 in `model/spec-deviations.json`, and
`Core/Validation/InstructionsCombinedAmended.lean` states the sole amended
judgment the repository uses (`Instrs_okA`), composes the sequence repair with
the corrected type/subtyping hierarchy, derives the compositions the pinned
rules cannot express, and proves that the repair does not widen the arity
discipline. -/

/-! ### The defect, stated in general

`const_binop_untypable` below is one instance.  The general statement is
`cons_inv`: in EVERY pinned derivation of a non-empty sequence, the head is
typed by the PRINCIPAL relation `Instr_ok` and its codomain is EXACTLY a domain
of the tail.  `Instrs_ok/sub` and `Instrs_ok/frame` do not change the subject of
a derivation, so they cannot intervene between the head and the tail; and there
is no `Instr_ok/sub` or `Instr_ok/frame` to adjust the head in place.  Every
instance of the defect --- `const; binop`, `local.get; local.get; i32.add`,
`nop; drop`, and every function body performing binary arithmetic --- is an
application of `cons_untypable_of_arity` to this fact. -/

/-- **THE DEFECT, IN FULL GENERALITY.**  For every context, every head
instruction, every tail, and every instruction type: a pinned derivation of
`i₁ :: is` contains an `Instr_ok` typing of `i₁` whose codomain is EXACTLY the
domain of a pinned typing of `is`.  The head is never framed and never
subsumed. -/
theorem Instrs_ok.cons_inv {C : Context} {i₁ : Instr} {is : List Instr} :
    ∀ {js : List Instr} {it : InstrType}, Instrs_ok C js it → js = i₁ :: is →
      ∃ (C' : Context) (ts₁ ts₂ ts₃ : List ValType) (xs₁ xs₂ : List LocalIdx),
        Instr_ok C i₁ ⟨ts₁, xs₁, ts₂⟩ ∧ Instrs_ok C' is ⟨ts₂, xs₂, ts₃⟩ := by
  intro js it h
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ hd _ _ htail _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, he₂⟩ := he
      subst he₁; subst he₂
      exact ⟨_, _, _, _, _, _, hd, htail⟩
  case sub _ _ _ _ _ _ _ ih => exact ih
  case frame _ _ _ _ _ _ _ _ ih => exact ih
  all_goals trivial

/-- **THE DEFECT AS A REJECTION SCHEMA.**  For every context and every
instruction type: if the head instruction can never produce `n` operands and the
tail always consumes at least `n`, the pinned rules give the composition NO
type.  `const_binop_untypable` is the instance `n = 2`. -/
theorem Instrs_ok.cons_untypable_of_arity {C : Context} {i₁ : Instr}
    {is : List Instr} {n : Nat}
    (hhead : ∀ {C' : Context} {it : InstrType}, Instr_ok C' i₁ it → it.cod.length < n)
    (htail : ∀ {C' : Context} {it : InstrType}, Instrs_ok C' is it → n ≤ it.dom.length) :
    ∀ {js : List Instr} {it : InstrType}, Instrs_ok C js it → js = i₁ :: is → False := by
  intro js it h he
  obtain ⟨_, _, _, _, _, _, hd, ht⟩ := Instrs_ok.cons_inv h he
  have h1 := hhead hd
  have h2 := htail ht
  simp only [] at h1 h2
  omega

/-- Every type the pinned rules give to the one-instruction sequence
`(BINOP nt op)` has a domain of at least two operands: `sub` cannot shorten a
domain and `frame` only lengthens one. -/
theorem Instrs_ok.binop_dom_length {C : Context} {nt : NumType} {op : Binop} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok C is it →
      is = [Instr.binop nt op] → 2 ≤ it.dom.length := by
  intro is it h
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ hi _ _ _ _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, _⟩ := he
      subst he₁
      cases hi
      simp
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, _, _⟩ := hsub
      obtain ⟨hlen, _⟩ := hdom
      have hih := ih he
      simp only [] at hlen hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-- THE GAP, stated as a falsifiable proposition: the pinned rules give
`(I32.CONST c) (I32.ADD)` --- a sequence every WebAssembly engine validates ---
NO instruction type, in NO context.  Hence no module whose function body
contains it is `Module_ok`, and no algorithm that agrees with Core's can be
SOUND for `Instrs_ok`. -/
theorem Instrs_ok.const_binop_untypable {C : Context} {nt : NumType} {c : Num_ nt}
    {op : Binop} : ∀ {is : List Instr} {it : InstrType}, Instrs_ok C is it →
      is = [Instr.const nt c, Instr.binop nt op] → False :=
  Instrs_ok.cons_untypable_of_arity (n := 2)
    (fun hd => by cases hd; simp)
    (fun ht => Instrs_ok.binop_dom_length ht rfl)

/-- ... and therefore the algorithm of the appendix, which accepts that
sequence, cannot be proved sound against the pinned judgment.  This is the
statement that is NOT provable, recorded here as the shape of the obligation
rather than as a claim. -/
example {C : Context} {nt : NumType} {c : Num_ nt} {op : Binop} {it : InstrType} :
    ¬ Instrs_ok C [Instr.const nt c, Instr.binop nt op] it :=
  fun h => Instrs_ok.const_binop_untypable h rfl


/-- The gap theorem is not vacuous: the ONE-instruction sequence is typable, at
exactly the type the algorithm computes for it.  It is the composition of two
instructions that the pinned rules cannot express. -/
example :
    Instrs_ok Context.empty [Instr.binop .i32 (.int .add)]
      ⟨[ValType.i32, ValType.i32], [], [ValType.i32]⟩ :=
  Instrs_ok.seq (ts := []) (Instr_ok.binop rfl) rfl (fun _ _ _ ha _ => by simp at ha)
    (Instrs_ok.frame (ts := [ValType.i32]) Instrs_ok.empty
      (resulttype_ok_of_nvb (ts := [ValType.i32]) (by decide)))


/-- The same gap one instruction further out: `(CONST) (CONST) (BINOP)` is
untypable too, because its tail is. -/
theorem Instrs_ok.const_const_binop_untypable {C : Context} {nt : NumType}
    {c : Num_ nt} {op : Binop} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_ok C is it →
      is = [Instr.const nt c, Instr.const nt c, Instr.binop nt op] → False := by
  intro is it h
  induction h using Instrs_ok.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ _ _ _ htail _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨_, he₂⟩ := he
      exact Instrs_ok.const_binop_untypable htail he₂
  case sub _ _ _ _ _ _ _ ih => exact ih
  case frame _ _ _ _ _ _ _ _ ih => exact ih
  all_goals trivial

/-- ... and hence no context gives that expression a result type. -/
theorem Expr_ok.const_const_binop_untypable {C : Context} {nt : NumType}
    {c : Num_ nt} {op : Binop} {ts : List ValType} :
    ¬ Expr_ok C (InstrSeq.ofList
        [Instr.const nt c, Instr.const nt c, Instr.binop nt op]) ts := by
  intro h
  cases h with
  | mk hseq =>
      rw [InstrSeq.toList_ofList] at hseq
      exact Instrs_ok.const_const_binop_untypable hseq rfl

/-! ## Soundness helpers for the full amended pass -/

theorem funcTypeOfA_sound {dt : DefType} {dom cod : List ValType}
    (h : funcTypeOfA dt = some (dom, cod)) :
    ∃ ds cs : ValTypes, dom = ValTypes.toList ds ∧ cod = ValTypes.toList cs ∧
      Expand dt (.func ds cs) := by
  unfold funcTypeOfA at h
  split at h
  · rename_i ds cs he
    injection h with h
    obtain ⟨hdom, hcod⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨ds, cs, hdom.symm, hcod.symm, .mk he⟩
  · contradiction

theorem blockTypeA_sound {C : Context} {bt : BlockType}
    {dom cod : List ValType} (h : blockTypeA C bt = some (dom, cod)) :
    Blocktype_okA C bt ⟨dom, [], cod⟩ := by
  cases bt with
  | result t =>
      cases t with
      | none =>
          simp only [blockTypeA, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .valtype (fun _ hm => nomatch hm)
      | some t =>
          simp only [blockTypeA] at h
          split at h
          · rename_i ht
            injection h with h
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact .valtype (fun _ hm => by
              simp only [Option.some.injEq] at hm
              subst hm
              exact checkValtypeOkA_sound ht)
          · contradiction
  | idx x =>
      simp only [blockTypeA] at h
      split at h
      · rename_i dt hx
        obtain ⟨ds, cs, rfl, rfl, he⟩ := funcTypeOfA_sound h
        exact .typeidx hx he
      · contradiction

theorem checkCatchA_sound {C : Context} {c : Catch}
    (h : checkCatchA C c = true) : Catch_okA C c := by
  cases c with
  | tag x l =>
      simp only [checkCatchA] at h
      split at h
      · rename_i jt ts hx hl
        split at h
        · rename_i dt hj
          split at h
          · rename_i dom he
            exact .catch hx hj (.mk he) hl (resulttype_subA_of_subsA h)
          · contradiction
        · contradiction
      · contradiction
  | tagRef x l =>
      simp only [checkCatchA] at h
      split at h
      · rename_i jt ts hx hl
        split at h
        · rename_i dt hj
          split at h
          · rename_i dom he
            exact .catch_ref hx hj (.mk he) hl (resulttype_subA_of_subsA h)
          · contradiction
        · contradiction
      · contradiction
  | all l =>
      simp only [checkCatchA] at h
      split at h
      · rename_i ts hl
        exact .catch_all hl (resulttype_subA_of_subsA h)
      · contradiction
  | allRef l =>
      simp only [checkCatchA] at h
      split at h
      · rename_i ts hl
        exact .catch_all_ref hl (resulttype_subA_of_subsA h)
      · contradiction

end Validate
end WasmGemmGnaf.Wasm.Core
