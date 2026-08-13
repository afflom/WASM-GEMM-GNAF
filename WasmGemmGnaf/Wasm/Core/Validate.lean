/-
  Wasm/Core/Validate.lean --- the executable module validator: the validation
  ALGORITHM of `vendor/wasm-spec/document/core/appendix/algorithm.rst` wrapped in
  the module-level checks of `2.4-validation.modules.spectec`.

  WHAT THIS FILE IS.  `Wasm.Core.validate : Module -> Bool` is a total,
  computable function.  Its instruction-level core is `Core/ValidateInstr.lean`'s
  `checkSeq`, which is the appendix's single pass --- operand stack, control
  frames through `Context.pushLabel`, `unreachable()` and the `Bot` type --- and
  its module level follows `Module_ok` premise by premise: the staged contexts
  `C'` and `C`, `$rolldt` on the type section, the `REFS` component from
  `$funcidx_nonfuncs`, `Limits_ok` on memories, `Expr_ok_const` on the
  initialisers and offsets, `Externidx_ok` on the exports and `$disjoint_` on
  their names.

  WHAT THIS FILE DOES NOT CLAIM, AND WHY.  There is no
  `validate_iff_declarative` here, and no soundness theorem AGAINST THE PINNED
  `Module_ok`.  (Soundness against the AMENDED `Module_ok'` is a theorem, but it
  is `validate_sound` in `Core/ValidateModule.lean`, a later file; see the last
  paragraph of this header.)  The reason no theorem here mentions the pinned
  relation is a DEFECT IN THE PINNED DECLARATIVE RULES, proved in
  `Core/ValidateInstr.lean` as `Instrs_ok.const_binop_untypable`:

      the pinned `Instrs_ok/seq` composes the head instruction, typed by
      `Instr_ok`, with the tail sequence, so the tail's domain must be exactly
      the head's codomain; `Instrs_ok/sub` preserves domain length and
      `Instrs_ok/frame` only lengthens a domain, and neither applies to the head
      instruction.  Hence `(I32.CONST c) (BINOP I32 ADD)` --- an operand pushed
      before the sequence began, consumed inside it --- has NO instruction type
      in ANY context.

  That is a kernel-checked negative result about the transcription of the pinned
  source, not a guess.  Its consequence for this file is exact: no module whose
  function body composes two instructions in that way is `Module_ok`, so a
  SOUNDNESS theorem `validate m = true -> Module_ok m mt` is FALSE, and stating
  one would be stating a falsehood.  The COMPLETENESS direction
  (`Module_ok m mt -> validate m = true`) is not affected by the defect and is
  not proved here either --- it is an open obligation, and it is recorded as
  one rather than asserted.

  WHOSE DEFECT, AND WHAT THE REPOSITORY USES INSTEAD.  The defect is the PINNED
  SPECTEC SOURCE's.  It is not this transcription's --- the vendored file is
  byte-identical to the upstream blob at the pin, and the argument turns on
  LENGTHS alone, so no operand-order convention here could cause it --- and it
  is not WebAssembly's: upstream filed the same finding as issue #2194 and fixed
  it in PR #2197 (commit `bd4633ac...`, 2026-06-23), nine months after the
  pinned commit.  It is recorded as DEV-006 in `model/spec-deviations.json`.

  The general form of the defect is `Instrs_ok.cons_inv`: in EVERY pinned
  derivation of a non-empty sequence the head is typed by the principal relation
  `Instr_ok`, un-framed and un-subsumed.  `Instrs_ok.cons_untypable_of_arity` is
  the rejection schema; `const_binop_untypable` is its `n = 2` instance.

  `Core/Validation/InstructionsAmended.lean` states the amended judgment the
  repository uses, `Instrs_ok'`: one modified premise --- the frame carried
  INSIDE the composition rule --- and no new rule, propagated through
  `Instr_ok/block`, `Instr_ok/loop` and `Instr_ok/if` so the vacuity does not
  survive one nesting level down.  It is proved to CONTAIN the pinned judgment
  (`Instrs_ok.to_amended`), to derive what the pinned rules cannot
  (`Instrs_ok'.const_binop` and the block, br and stack-polymorphic witnesses
  beside it), and NOT to have widened the arity discipline in doing so
  (`Instrs_ok'.binop_dom_length` is the pinned negative lemma re-proved against
  the amendment).  A soundness or `validate_iff_declarative` theorem may be
  attempted over `Instrs_ok'` with DEV-006 cited; it may NOT be stated over the
  pinned relation, where it is false.

  WHAT HAS SINCE BEEN CLOSED, AND WHERE.  `Core/ValidateSeq.lean` proves the
  instruction-level equivalence of `checkSeq` with `Instrs_ok'` in both
  directions --- `checkSeq_sound` (every context, no fragment hypothesis) and
  `checkSeq_complete` (over `Context.frag` / `Instr.frag`) --- together with
  `checkExpr_sound` and `checkExpr_complete`.  `Core/ValidateModule.lean` then
  proves `validate_sound : validate m = true -> exists mt, Module_ok' m mt`, at
  the whole-module level, for every module and with no side hypothesis.
  `Core/ValidateComplete.lean` proves the CONVERSE, `validate_complete`, and
  the equivalence `validate_iff_declarative`:

      `validate m = true <-> Module.frag m = true /\ exists mt, Module_ok' m mt`

  with no hypothesis --- the fragment condition is a conjunct, because
  `validate` decides it.  What is still outside that fragment is imports, tags,
  tables and element segments, and what they cost is a decision procedure for
  `Heaptype_sub`.

  SPEC 15's `Wasm.validate_iff_declarative` is a different declaration, in
  `Wasm/Declarative.lean`, over the i32-subset model; it stays OUTSTANDING
  until the release path is migrated onto `Wasm.Core`.

  So what this file delivers is the ALGORITHM, executable and checked on
  concrete modules, plus the exact statement of what stands between it and the
  equivalence the repository wants.  The `example`s at the end are
  kernel-checked evaluations, not tests: they pin down what the algorithm
  accepts and rejects, including the stack-polymorphic cases the previous
  i32-only validator could not express.
-/
import WasmGemmGnaf.Wasm.Core.ValidateInstr
import WasmGemmGnaf.Wasm.Core.Validation.Modules

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## The module fragment

The instruction fragment of `Core/ValidateInstr.lean` fixes which instructions
the algorithm decides; these are the module-level consequences.  Imports, tags,
tables and element segments are outside it, because every one of them needs
`Heaptype_sub`. -/

/-- A type section entry of the fragment: one final, supertype-free function
type over `numtype`s and `vectype`s. -/
def TypeDef.frag (td : TypeDef) : Bool :=
  match td.rectype with
  | .recr (.cons (.sub (some .final) .nil (.func dom cod)) .nil) =>
      nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)
  | _ => false

/-- The modules the algorithm decides. -/
def Module.frag (m : Module) : Bool :=
  m.imports.isEmpty && m.tags.isEmpty && m.tables.isEmpty && m.elems.isEmpty &&
  m.types.all TypeDef.frag &&
  m.globals.all (fun g => ValType.nv g.globaltype.valtype && InstrSeq.frag g.init) &&
  m.funcs.all (fun f =>
    f.locals.all (fun l => ValType.nv l.valtype) && InstrSeq.frag f.body) &&
  m.datas.all (fun d =>
    match d.mode with
    | .passive => true
    | .active _ e => InstrSeq.frag e)

/-! ## The type section

`Type_ok` fixes `dt* = $rolldt(x, rectype)` with `x = |C.TYPES|`, and
`Types_ok/cons` extends the context by the entry just rolled; the fold below is
that pair of rules read as a function. -/

/-- `Types_ok` as a computation: the `deftype*` a type section denotes. -/
def rollTypes : List DefType → List TypeDef → List DefType
  | acc, [] => acc
  | acc, td :: tds => rollTypes (acc ++ rollDt (TypeIdx.ofNat acc.length) td.rectype) tds

/-! ## Constant expressions

`Expr_ok_const: C |- expr : t CONST` is `Expr_ok` and `Expr_const` together, so
the check is the algorithm's plus the syntactic `Instr_const` test. -/

/-- `Instr_const`, restricted to the instruction fragment. -/
def Instr.isConst (C : Context) : Instr → Bool
  | .const nt c => Num_.wf nt c
  | .vconst _ _ => true
  | .globalGet x =>
      match C.globals[x.val]? with
      | some ⟨none, _⟩ => true
      | _ => false
  | .binop nt (.int op) =>
      ((nt == NumType.i32) || (nt == NumType.i64)) &&
      (match op with
       | .add => true
       | .sub => true
       | .mul => true
       | _ => false)
  | _ => false

/-- `Expr_ok_const: C |- expr : t CONST`, decided. -/
def checkConstExpr (C : Context) (e : Expr) (t : ValType) : Bool :=
  checkExpr C e [t] && (InstrSeq.toList e).all (Instr.isConst C)

/-! ## The remaining module-level judgments -/

/-- `Limits_ok: C |- limits : k`. -/
def checkLimits (lim : Limits) (k : Nat) : Bool :=
  decide (lim.min.val ≤ k) &&
  (match lim.max with
   | none => true
   | some mx => decide (lim.min.val ≤ mx.val) && decide (mx.val ≤ k))

/-- `Externidx_ok: C |- externidx : externtype`, as a validity test on the
index; the external type it produces is determined by the context. -/
def checkExternIdx (C : Context) : ExternIdx → Bool
  | .func x => (C.funcs[x.val]?).isSome
  | .global x => (C.globals[x.val]?).isSome
  | .mem x => (C.mems[x.val]?).isSome
  | .table x => (C.tables[x.val]?).isSome
  | .tag x => (C.tags[x.val]?).isSome

/-- `Globals_ok`: each initialiser is checked in the context extended by the
globals BEFORE it, which is what stops a global from reading a later one. -/
def checkGlobals (C : Context) : List Global → Option (List GlobalType)
  | [] => some []
  | g :: gs =>
      if ValType.nv g.globaltype.valtype &&
          checkConstExpr C g.init g.globaltype.valtype then
        match checkGlobals (Context.append C { globals := [g.globaltype] }) gs with
        | some gts => some (g.globaltype :: gts)
        | none => none
      else none

/-- `Func_ok`: the body is checked against the declared result type, in the
context that carries the parameters and locals (all of the fragment's types are
defaultable, so `Local_ok/set` applies and every local starts `SET`), the
implicit outermost label and `RETURN`. -/
def checkFunc (C : Context) (f : Func) : Bool :=
  match C.types[f.typeidx.val]? with
  | some dt =>
      match funcTypeOf dt with
      | some (dom, cod) =>
          f.locals.all (fun l => ValType.nv l.valtype) &&
          checkExpr (Context.append C
              { locals := dom.map (fun t => ⟨Init.set, t⟩) ++
                          f.locals.map (fun l => ⟨Init.set, l.valtype⟩),
                labels := [cod],
                ret := some cod })
            f.body cod
      | none => false
  | none => false

/-- `Data_ok` with `Datamode_ok`. -/
def checkData (C : Context) (d : Data) : Bool :=
  match d.mode with
  | .passive => true
  | .active x e =>
      match C.mems[x.val]? with
      | some mt => checkConstExpr C e mt.addr.toValType
      | none => false

/-- `Start_ok: C |- START x : OK`. -/
def checkStart (C : Context) (s : Start) : Bool :=
  match C.funcs[s.funcidx.val]? with
  | some dt =>
      match expandDt dt with
      | some (.func .nil .nil) => true
      | _ => false
  | none => false

/-! ## The module validator -/

/-- The two staged contexts of `Module_ok`: `C'` types the globals and
memories, `C` types the functions, data segments, start function and exports.
`none` when a function names a type index the type section does not define. -/
def Module.contexts (m : Module) : Option (Context × Context) :=
  let dts := rollTypes [] m.types
  match m.funcs.mapM (fun f => dts[f.typeidx.val]?) with
  | none => none
  | some fdts =>
      let C' : Context :=
        { types := dts, funcs := fdts,
          refs := funcidxNonfuncs m.globals m.mems m.tables m.elems }
      match checkGlobals C' m.globals with
      | none => none
      | some gts =>
          some (C',
            Context.append C'
              { globals := gts,
                mems := m.mems.map Mem.memtype,
                datas := m.datas.map (fun _ => DataType.ok) })

/-- **The validator.**  `validate m = true` means the algorithm of
`appendix/algorithm.rst` accepts `m` under the module-level checks of
`2.4-validation.modules.spectec`.  Everything outside the decided fragment is
rejected, so the function is total and computable with no fuel and no
assumption. -/
def validate (m : Module) : Bool :=
  Module.frag m &&
  (match Module.contexts m with
   | none => false
   | some (_, C) =>
       m.mems.all (fun mem => checkLimits mem.memtype.lim (2 ^ 16)) &&
       m.funcs.all (checkFunc C) &&
       m.datas.all (checkData C) &&
       (match m.start with
        | none => true
        | some s => checkStart C s) &&
       m.exports.all (fun e => checkExternIdx C e.externidx) &&
       disjoint (m.exports.map Export.name))

end Validate

/-- `Wasm.Core.validate`, the executable validator of this development. -/
def validate (m : Module) : Bool := Validate.validate m

/-- Every function of a validated module has a `Func_ok` derivation in the
module's own context.  `Module_ok`'s two staged contexts are existential, so
this is the form the negative result below can use. -/
theorem Module_ok.func_ok {m : Module} {mt : ModuleType} (h : Module_ok m mt) :
    ∀ f ∈ m.funcs, ∃ (C : Context) (dt : DefType), Func_ok C f dt := by
  cases h with
  | mk _ _ _ _ _ _ _ _ _ _ hlf hf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro f hfm
      rcases List.mem_iff_getElem.mp hfm with ⟨i, hi, rfl⟩
      have hi' := hlf ▸ hi
      exact ⟨_, _, hf i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hi')⟩



/-! ## Module builders for the checked evaluations below -/

def modOf (tds : List TypeDef) (fs : List Func) : Module :=
  { types := tds, imports := [], tags := [], globals := [], mems := [],
    tables := [], funcs := fs, datas := [], elems := [], start := none,
    exports := [] }

def fn (i : Nat) (locals : List ValType) (body : List Instr) : Func :=
  { typeidx := TypeIdx.ofNat i, locals := locals.map (fun t => { valtype := t }),
    body := InstrSeq.ofList body }

/-! ## The gap, at the module level

`validate` accepts a module that `Module_ok` cannot type.  Both halves are
kernel-checked: the acceptance by evaluation, the rejection by the negative
result of `Core/ValidateInstr.lean`.  This pair is the precise obstruction to
`validate_iff_declarative`, and it is a statement about the PINNED RULES, not
about the algorithm. -/

/-- `(func (result i32) i32.const 0  i32.const 0  i32.add)`. -/
def gapModule : Module :=
  modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
      (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
    [fn 0 [] [.const .i32 default, .const .i32 default, .binop .i32 (.int .add)]]

/-- The algorithm accepts it, as every engine does. -/
example : validate gapModule = true := by decide

/-- The pinned declarative rules give it NO module type: its body is the
sequence `Instrs_ok` cannot compose. -/
theorem gapModule_not_ok (mt : ModuleType) : ¬ Module_ok gapModule mt := by
  intro h
  obtain ⟨C, dt, hok⟩ :=
    Module_ok.func_ok h (fn 0 [] [.const .i32 default, .const .i32 default,
      .binop .i32 (.int .add)]) (by decide)
  cases hok with
  | mk _ _ _ _ hexpr =>
      exact _root_.WasmGemmGnaf.Wasm.Core.Validate.Expr_ok.const_const_binop_untypable hexpr

/-! ## Kernel-checked evaluations

Not tests: each of these is checked by the kernel when the file is elaborated.
They pin down the behaviour of the algorithm on the cases the previous
i32-only validator could not express --- stack polymorphism, multi-value
blocks, SIMD --- and on the ill-formed instructions the tightened syntax
rejects. -/

namespace Validate

/-- The type section entry `(func (param i32 i32) (result i32))`. -/
private def ty2i32 : TypeDef :=
  { rectype := .recr (.cons (.sub (some .final) .nil
      (.func (ValTypes.ofList [ValType.i32, ValType.i32])
             (ValTypes.ofList [ValType.i32]))) .nil) }

/-- The type section entry `(func)`. -/
private def ty0 : TypeDef :=
  { rectype := .recr (.cons (.sub (some .final) .nil
      (.func .nil .nil)) .nil) }

/-- `(func (param i32 i32) (result i32) local.get 0  local.get 1  i32.add)`
validates.  This is the composition the pinned declarative rules cannot type
(`Instrs_ok.const_binop_untypable`) and every engine accepts. -/
example :
    validate (modOf [ty2i32]
      [fn 0 [] [.localGet default, .localGet ⟨1, by decide⟩,
               .binop .i32 (.int .add)]]) = true := by
  decide

/-- ... and the same body with the operands swapped for a `f32.add` is
rejected: the operand types do not match. -/
example :
    validate (modOf [ty2i32]
      [fn 0 [] [.localGet default, .localGet ⟨1, by decide⟩,
               .binop .f32 (.int .add)]]) = false := by
  decide

/-- STACK POLYMORPHISM.  `unreachable` makes the rest of the block accept any
operands: `(func (result i32) unreachable)` validates although the body pushes
nothing.  A validator that typed `UNREACHABLE` concretely would reject it. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [fn 0 [] [.unreachable]]) = true := by
  decide

/-- ... and the polymorphism is not unsound: `unreachable  i32.const  i64.add`
is still rejected, which is the appendix's own example of why operands must
still be pushed and popped inside unreachable code. -/
example :
    validate (modOf [ty0]
      [fn 0 [] [.unreachable, .const .i32 default, .binop .i64 (.int .add)]]) = false := by
  decide

/-- MULTI-VALUE BLOCKS.  A `BLOCK` whose type is a type index consumes and
produces several operands; `(block (param i32 i32) (result i32) i32.add)` in a
two-parameter function validates. -/
example :
    validate (modOf [ty2i32]
      [fn 0 [] [.localGet default, .localGet ⟨1, by decide⟩,
               .block (.idx default) (InstrSeq.ofList [.binop .i32 (.int .add)])]]) = true := by
  decide

/-- BRANCHES.  `(block (result i32) i32.const 0  br 0)` validates: `BR 0`
consumes the label's operands and makes the rest of the block unreachable. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [fn 0 [] [.block (.result (some ValType.i32))
                  (InstrSeq.ofList [.const .i32 default, .br default])]]) = true := by
  decide

/-- SIMD.  `(func (result v128) v128.const  i8x16.add)` --- with the shape
`I8 X 16` --- validates. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.v128]))) .nil) }]
      [fn 0 [] [.vconst .v128 default, .vconst .v128 default,
               .vbinop { lane := .pack .i8, dim := .d16 } (.int (.addSat .s))]]) = true := by
  decide

/-- ... and an operator outside its shape's family is rejected, exactly as
`Instr.wf` requires: `I32X4.POPCNT` fails `$lsizenn(Jnn) = 8`. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.v128]))) .nil) }]
      [fn 0 [] [.vconst .v128 default,
               .vunop { lane := .num .i32, dim := .d4 } (.int .popcnt)]]) = false := by
  decide

/-- LOCALS.  Reading a local that the type section does not give the function
is rejected. -/
example :
    validate (modOf [ty0] [fn 0 [] [.localGet default, .drop]]) = false := by
  decide

/-- The empty module validates. -/
example : validate (modOf [] []) = true := by decide

/-- A module whose function names a type index the type section does not
define is rejected before any body is checked. -/
example : validate (modOf [] [fn 0 [] []]) = false := by decide

end Validate
end WasmGemmGnaf.Wasm.Core
