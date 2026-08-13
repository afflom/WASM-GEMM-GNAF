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
      `BLOCK`, `LOOP`, `IF`, `BR`, `BR_IF`, `RETURN`, `CALL`, `LOCAL.*`,
      `GLOBAL.*`, `LOAD`, `STORE`, `VLOAD`, `VLOAD_LANE`, `VSTORE`,
      `VSTORE_LANE`, `MEMORY.SIZE`, `MEMORY.GROW`, `MEMORY.FILL`,
      `MEMORY.COPY`, `MEMORY.INIT`, `DATA.DROP`, every numeric instruction
      (`CONST UNOP BINOP TESTOP RELOP CVTOP`) and every SIMD instruction of
      `1.3-syntax.instructions.spectec` (`VCONST`, `VVUNOP` ... `VCVTOP`,
      `VSPLAT`, `VEXTRACT_LANE`, `VREPLACE_LANE`).
    * NOT: `BR_TABLE`, the reference and GC instructions, the table and element
      instructions, `CALL_REF`/`CALL_INDIRECT`, the tail calls, and exception
      handling.  Every one of those needs `Heaptype_sub`, whose decidability is
      a separate obligation this file does not discharge.

  Multi-value blocks, block types given by a type index, and full stack
  polymorphism ARE inside the fragment; they are what the appendix algorithm is
  for.  `checkInstr` returns `none` on everything outside the fragment, so
  SOUNDNESS (`checkSeq_sound`) holds for EVERY context and every instruction,
  with no fragment hypothesis; only COMPLETENESS (`checkSeq_complete`) is
  fragment-scoped.
-/
import WasmGemmGnaf.Wasm.Core.ValidateStack
import WasmGemmGnaf.Wasm.Core.Validation.Instructions

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
  | .ret => true
  | .call _ => true
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
  | st, .ret =>
      match C.ret with
      | some ts =>
          if nvs ts then
            match st.pops ts with
            | some _ => some st.unreach
            | none => none
          else none
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

/-! ## Soundness of the computed instruction types

Everything `instrType` accepts, the declarative judgment derives.  One case per
arm of `instrType`, and the arms are exactly the rules of
`2.3-validation.instructions.spectec` that the fragment covers. -/

/-- `$sizenn` reading of `nt.toInn?`. -/
theorem toInn_toNumType {nt : NumType} {n : Inn} (h : nt.toInn? = some n) :
    n.toNumType = nt := by
  cases nt <;> simp [NumType.toInn?] at h <;> (try subst h) <;> rfl

theorem instrType_sound {C : Context} {i : Instr} {it : InstrType}
    (h : instrType C i = some it) : Instr_ok C i it := by
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
        exact .select_expl (valtype_ok_of_nvb (ValType.nvb_of_nv hnv))
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
  | .ret => true
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
    (hsp : Instr.special i = false) (h : Instr_ok C i it) : instrType C i = some it := by
  have hwf : Instr.wf i = true := Instr_ok.wf_of h
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
`Core/Validation/InstructionsAmended.lean` states the amended judgment the
repository uses (`Instrs_ok'`), proves it CONTAINS the pinned one
(`Instrs_ok.to_amended`), derives the compositions the pinned rules cannot
express, and proves the amendment did not widen the arity discipline. -/

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

end Validate
end WasmGemmGnaf.Wasm.Core
