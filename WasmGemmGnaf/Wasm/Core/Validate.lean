/-
  Wasm/Core/Validate.lean --- the executable module validator for the amended
  declarative Core hierarchy.

  WHAT THIS FILE IS.  `Wasm.Core.validate : Module -> Bool` is a total,
  computable function.  It combines the module-level checks of
  `2.4-validation.modules.spectec` with the corrected amended type
  hierarchy, and it checks every module section, including tables and element
  segments.  Its accepted instruction language remains conservative where the
  module checker calls the older stack pass.  Unconditional soundness against
  `Module_okA` is proved in `Core/ValidateModule.lean`.

  WHAT THIS FILE DOES NOT CLAIM, AND WHY.  There is no
  `validate_iff_declarative` here, and no soundness theorem AGAINST THE PINNED
  `Module_ok`.  (Soundness against the combined AMENDED `Module_okA` is a theorem, but it
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

  `Core/Validation/InstructionsCombinedAmended.lean` states the corrected
  hierarchy used by the proof path: `Instr_okA`/`Instrs_okA`.  The module
  checker below is proved sound against that hierarchy for every module it
  accepts.  The older `checkSeq` pass and the broader
  `checkInstrA`/`checkSeqA` pass coexist in
  `Core/ValidateInstr.lean`; their presence does not by itself establish
  completeness of this module validator.

  COMPLETENESS STATUS.  `Module.frag` is retained below only as the
  historical sufficient condition used by the reverse-direction proof in
  `Core/ValidateComplete.lean`.  The validator does not compute or require
  that Boolean; in particular it checks tables and element segments.  The
  repository also contains an executable amended `Heaptype_sub` decision
  procedure.  What remains open is a proof that every amended declaratively
  valid module is accepted, not the existence of that decision procedure.

  The exact current endpoint is therefore:

  * `Wasm.Core.validate_sound` is unconditional for every accepted module;
  * `Wasm.Core.validate_complete` requires explicit `Module.wf` and
    legacy `Validate.Module.frag` hypotheses;
  * `Wasm.Core.validate_iff_declarative_fragment` is the corresponding
    explicitly restricted equivalence.

  There is no hypothesis-free `Wasm.Core.validate_iff_declarative`.  The
  similarly named declaration in `Wasm/Declarative.lean` is over the
  non-release subset model and remains outstanding.  The examples at the end
  are kernel-checked evaluations of this validator, not completeness evidence.
-/
import WasmGemmGnaf.Wasm.Core.ValidateInstr
import WasmGemmGnaf.Wasm.Core.ValidateTypes
import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## The legacy completeness fragment

`Module.frag` and its component predicates record the syntactic fragment for
which the existing reverse-direction lemmas were proved.  They are retained as
explicit hypotheses of `validate_complete` and
`validate_iff_declarative_fragment`.  They are not called by `validate`
and do not characterize its accepted modules: failure of a `frag` predicate
does not imply validator rejection. -/

/-- A type section entry of the fragment: one supertype-free function type over
`numtype`s and `vectype`s.  FINAL OR NOT: `Subtype_ok` reads the `FINAL?` flag
nowhere --- its premises are the supertype list, `Comptype_ok` and one
`Comptype_sub` per declared supertype --- and `$rollrt` / `$unrollrt` /
`$subst_all_deftype` carry the flag through untouched, so a NON-final function
type is decided by exactly the same argument as a final one.  What is still
excluded is a DECLARED SUPERTYPE, because `Subtype_ok` then has a `Comptype_sub`
premise, hence `Heaptype_sub`. -/
def TypeDef.frag (td : TypeDef) : Bool :=
  match td.rectype with
  | .recr (.cons (.sub _ .nil (.func dom cod)) .nil) =>
      nvs (ValTypes.toList dom) && nvs (ValTypes.toList cod)
  | _ => false

/-- A tag section entry of the fragment: the tag type is written as a type
index.  A tag type written as an explicit `deftype` needs `Deftype_ok`, hence
`Comptype_sub`, hence `Heaptype_sub`; a tag type written as a `REC` variable
cannot occur in a module's tag section at all, because `C.RECS` is empty
outside `Rectype_ok/_rec2`. -/
def Tag.frag (tg : Tag) : Bool :=
  match tg.tagtype with
  | .idx _ => true
  | _ => false

/-- A heap type of the fragment: abstract, or a type index.  A heap type
written as an explicit `deftype` needs `Deftype_ok`. -/
def HeapType.frag : HeapType → Bool
  | .abs _ => true
  | .use (.idx _) => true
  | .use _ => false

/-- An external type of the fragment.  The restriction is on the CONTEXT an
import of it contributes, not on the external type itself:

* a `FUNC` or `TAG` names its function type by a type index, and a `TABLE` its
  element type by an abstract heap type or a type index, for the reason
  `Tag.frag` gives;
* a `GLOBAL` is read by `GLOBAL.GET` in the module's own expressions, so its
  value type must be one the instruction fragment decides;
* a `MEM` is unrestricted --- a `memtype` carries no type at all. -/
def ExternType.frag : ExternType → Bool
  | .func (.idx _) => true
  | .tag (.idx _) => true
  | .global gt => ValType.nv gt.valtype
  | .mem _ => true
  | .table tt => match tt.elem with | .ref _ ht => HeapType.frag ht
  | _ => false

/-- An import of the fragment. -/
def Import.frag (i : Import) : Bool := ExternType.frag i.externtype

/-- The legacy syntactic fragment used as a sufficient hypothesis by the
current completeness proof.  The validator itself does not compute it. -/
def Module.frag (m : Module) : Bool :=
  m.imports.all Import.frag && m.tags.all Tag.frag &&
  m.tables.isEmpty && m.elems.isEmpty &&
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

/-- The legacy accumulator presentation and the proof-oriented staged fold in
`ValidateTypes` compute the same type sequence. -/
theorem rollTypes_eq_append_checkedTypes (C : Context) (tds : List TypeDef) :
    rollTypes C.types tds = C.types ++ checkedTypes C tds := by
  induction tds generalizing C with
  | nil => simp [rollTypes, checkedTypes]
  | cons td tds ih =>
      let dts := rollDt (TypeIdx.ofNat C.types.length) td.rectype
      rw [rollTypes]
      have hC : (Context.append C { types := dts }).types = C.types ++ dts := rfl
      rw [← hC, ih]
      rw [checkedTypes]
      exact List.append_assoc _ _ _

/-! ## Constant expressions

`Expr_ok_const: C |- expr : t CONST` is `Expr_ok` and `Expr_const` together, so
the check is the algorithm's plus the syntactic `Instr_const` test. -/

/-- `Instr_const`, restricted to the instruction fragment. -/
def Instr.isConst (C : Context) : Instr → Bool
  | .const nt c => Num_.wf nt c
  | .vconst _ _ => true
  | .refNull _ => true
  | .refI31 => true
  | .refFunc _ => true
  | .structNew _ => true
  | .structNewDefault _ => true
  | .arrayNew _ => true
  | .arrayNewDefault _ => true
  | .arrayNewFixed _ _ => true
  | .anyConvertExtern => true
  | .externConvertAny => true
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

/-- Reference-valued singleton constant expressions whose source type is
well-formed without consulting a module type certificate.  This is folded into
the table/element checks while the general reference stack dispatcher is being
completed. -/
def checkRefConstExprA (C : Context) (e : Expr) (t : ValType) : Bool :=
  checkValtypeOkA C t &&
  match e with
  | .cons (.refNull ht) .nil =>
      checkHeaptypeOkA C ht &&
        subOfA C (.ref (.ref (some .null) ht)) t
  | _ => false

/-- Constant-expression validation including the reference singleton cases
already supported by the combined amended type hierarchy. -/
def checkConstExprA (C : Context) (e : Expr) (t : ValType) : Bool :=
  (ValType.nv t && checkConstExpr C e t) || checkRefConstExprA C e t

/-! ## The remaining module-level judgments -/

/-- `Limits_ok: C |- limits : k`. -/
def checkLimits (lim : Limits) (k : Nat) : Bool :=
  decide (lim.min.val ≤ k) &&
  (match lim.max with
   | none => true
   | some mx => decide (lim.min.val ≤ mx.val) && decide (mx.val ≤ k))

/-! ## Type uses, heap types and external types

None of these judgments mentions an expression and none of them mentions
subtyping, so each is decided outright on the `typeuse`s the fragment admits: a
type index in range.  `Deftype_ok`, which an explicitly written `deftype` would
need, is the one that would require `Comptype_sub`. -/

/-- A `deftype` whose expansion is a function type: the `Expand` premise of
`Tagtype_ok` and of `Externtype_ok/func`, decided.  Weaker than `funcTypeOf`,
which also constrains the value types --- neither rule does. -/
def isFuncDt (dt : DefType) : Bool :=
  match expandDt dt with
  | some (.func _ _) => true
  | _ => false

/-- `Typeuse_ok: C |- typeuse : OK` together with
`Expand_use: typeuse ~~_C FUNC t_1* -> t_2*`, decided on the `typeuse`s of the
fragment.  This is exactly the premise pair of `Tagtype_ok` and of
`Externtype_ok/func`. -/
def checkFuncTypeUse (C : Context) : TypeUse → Bool
  | .idx x =>
      match C.types[x.val]? with
      | some dt => isFuncDt dt
      | none => false
  | _ => false

/-- `Heaptype_ok: C |- heaptype : OK`, decided on the heap types of the
fragment: `Heaptype_ok/abs` has no premise at all, and a type index needs only
to be in range. -/
def checkHeapType (C : Context) : HeapType → Bool
  | .abs _ => true
  | .use (.idx x) => (C.types[x.val]?).isSome
  | .use _ => false

/-- `Reftype_ok: C |- reftype : OK`, decided. -/
def checkRefType (C : Context) : RefType → Bool
  | .ref _ ht => checkHeapType C ht

/-- `Externtype_ok: C |- externtype : OK`, decided on the external types of the
fragment.  The `GLOBAL` case is `Valtype_ok` restricted to the value types the
instruction fragment decides, because an imported global is a `C.GLOBALS` entry
the module's own expressions read. -/
def checkExternType (C : Context) : ExternType → Bool
  | .tag jt => checkFuncTypeUse C jt
  | .global gt => ValType.nv gt.valtype
  | .mem mt => checkLimits mt.lim (2 ^ 16)
  | .table tt => checkLimits tt.lim (2 ^ 32 - 1) && checkRefType C tt.elem
  | .func tu => checkFuncTypeUse C tu

/-- `Tag_ok: C |- tag : $clos_tagtype(C, tagtype)`, decided.  The tag type it
assigns is determined by the context, so the check is on the premise alone. -/
def checkTag (C : Context) (tg : Tag) : Bool := checkFuncTypeUse C tg.tagtype

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

/-- `Table_okA`: the table type and its reference-typed constant initializer. -/
def checkTable (C : Context) (t : Table) : Bool :=
  checkLimits t.tabletype.lim (2 ^ 32 - 1) &&
  checkRefType C t.tabletype.elem &&
  checkConstExprA C t.init (.ref t.tabletype.elem)

/-- `Elemmode_okA`, including the active segment's element-type inclusion. -/
def checkElemMode (C : Context) (rt : RefType) : ElemMode → Bool
  | .passive => true
  | .declare => true
  | .active x e =>
      match C.tables[x.val]? with
      | some tt =>
          decReftypeSubN C C.subtypeFuel rt tt.elem &&
          checkConstExpr C e tt.addr.toValType
      | none => false

/-- `Elem_okA`: element type validity, constant initializers, and mode. -/
def checkElem (C : Context) (e : Elem) : Bool :=
  checkRefType C e.reftype &&
  e.init.all (fun ex => checkConstExprA C ex (.ref e.reftype)) &&
  checkElemMode C e.reftype e.mode

/-! ## The module validator -/

/-- `{TYPES dt'*}`: the context `Module_ok` types the import section in --- the
type section and nothing else.  It is the ONLY context of the rule that does not
depend on what the imports themselves contribute, which is why the imports can
be typed before either staged context exists. -/
def Module.typeContext (m : Module) : Context := { types := rollTypes [] m.types }

/-- `xt_I*`: the external types the import section denotes.  `Import_ok` assigns
each import `$clos_externtype(C, xt)` in `Module.typeContext`, so the sequence
is determined by the module alone. -/
def Module.importTypes (m : Module) : List ExternType :=
  m.imports.map (fun i => (Module.typeContext m).closExternType i.externtype)

/-- The two staged contexts of `Module_ok`: `C'` types the tags, globals,
memories and tables, `C` types the functions, data segments, start function and
exports.  The imported components come first in every one of `C`'s sequences,
exactly as `jt_I* jt*`, `mt_I* mt*` and `tt_I* tt*` say.

`none` when a function names a type index the type section does not define, or
when a `FUNC` import's `typeuse` does not close to a `deftype` --- which is
`$funcsxt`'s partiality, and is why the rule writes `$funcsxt(xt_I*) = dt_I*`
as a premise rather than as an abbreviation. -/
def Module.contexts (m : Module) : Option (Context × Context) :=
  match funcsXt (Module.importTypes m) with
  | none => none
  | some dtsI =>
      match m.funcs.mapM (fun f => (rollTypes [] m.types)[f.typeidx.val]?) with
      | none => none
      | some fdts =>
          let C' : Context :=
            { types := rollTypes [] m.types,
              globals := ExternType.globals (Module.importTypes m),
              funcs := dtsI ++ fdts,
              refs := funcidxNonfuncs' m.globals m.mems m.tables m.elems }
          match checkGlobals C' m.globals with
          | none => none
          | some gts =>
              some (C',
                Context.append C'
                  { tags := ExternType.tags (Module.importTypes m) ++
                            m.tags.map (fun tg => C'.closTagType tg.tagtype),
                    globals := gts,
                    mems := ExternType.mems (Module.importTypes m) ++
                            m.mems.map Mem.memtype,
                    tables := ExternType.tables (Module.importTypes m) ++
                              m.tables.map Table.tabletype,
                    datas := m.datas.map (fun _ => DataType.ok),
                    elems := m.elems.map Elem.reftype })

/-- **The validator.**  This total computable checker uses the amended type
hierarchy and performs the module-level checks, including tables and element
segments.  It does not consult `Module.frag`.  Its unconditional
soundness is `Wasm.Core.validate_sound`; the currently proved reverse
direction remains explicitly fragment-scoped. -/
def validate (m : Module) : Bool :=
  Module.wf m &&
  checkTypesOkA Context.empty m.types &&
  (match Module.contexts m with
   | none => false
   | some (C', C) =>
       m.imports.all (fun i => checkExternType (Module.typeContext m) i.externtype) &&
       m.tags.all (checkTag C') &&
       m.mems.all (fun mem => checkLimits mem.memtype.lim (2 ^ 16)) &&
       m.tables.all (checkTable C') &&
       m.funcs.all (checkFunc C) &&
       m.datas.all (checkData C) &&
       m.elems.all (checkElem C) &&
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

/-! ## The pinned-rule gap, at the module level

`validate` accepts a module that `Module_ok` cannot type.  Both halves are
kernel-checked: the acceptance by evaluation, the rejection by the negative
result of `Core/ValidateInstr.lean`.  This pair rules out soundness against
the unamended pinned `Module_ok`.  It does not obstruct soundness against
`Module_okA`, which is proved downstream. -/

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

/-! ### Branch tables, tail calls and non-final type definitions

The three families the decided fragment gained.  Every module below is rejected
outright by the previous `Instr.frag` / `TypeDef.frag`. -/

/-- BR_TABLE.  `(func (result i32) (block (result i32) i32.const 0  i32.const 0
br_table 0 0))`: the table's operand is the block's result type, the index is
consumed, and the rest of the block is unreachable. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [fn 0 [] [.block (.result (some ValType.i32))
                  (InstrSeq.ofList [.const .i32 default, .const .i32 default,
                                    .brTable [default] default])]]) = true := by
  decide

/-- ... and the operand type is the PRINCIPAL one, not any single label's.  In
UNREACHABLE code the frame supplies `BOT`, so a `br_table` may name two labels
whose types DISAGREE: `Instr_ok/br_table` derives it with `t* = BOT`, which is
below both.  A checker that compared the labels with each other rather than with
the frame would reject this module, and Core 3.0 accepts it. -/
example :
    validate (modOf [ty0]
      [fn 0 [] [.block (.result (some ValType.i32))
                  (InstrSeq.ofList
                    [.block (.result (some (ValType.num .f32)))
                      (InstrSeq.ofList [.unreachable,
                                        .brTable [default] ⟨1, by decide⟩]),
                     .drop, .const .i32 default]),
                .drop]]) = true := by
  decide

/-- ... and the polymorphism is not unsound: in REACHABLE code the two labels
must both accept the operands the frame really has, and an ARITY disagreement is
rejected outright --- `Resulttype_sub` fixes `|t*|`, so no `t*` is below both a
one-operand and a zero-operand label. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [fn 0 [] [.block (.result none)
                  (InstrSeq.ofList [.const .i32 default, .const .i32 default,
                                    .brTable [default] ⟨1, by decide⟩]),
                .const .i32 default]]) = false := by
  decide

/-- RETURN_CALL.  A function tail-calls itself: `Instr_ok/return_call` requires
the callee's results to be below `C.RETURN`, and here they are equal. -/
example :
    validate (modOf [ty2i32]
      [fn 0 [] [.localGet default, .localGet ⟨1, by decide⟩, .returnCall default]]) = true := by
  decide

/-- ... and a tail call whose callee returns nothing, from a function that
returns `i32`, is rejected: `Resulttype_sub: C |- eps <: (I32)` fails on
length. -/
example :
    validate (modOf [ty2i32, ty0]
      [fn 0 [] [.returnCall ⟨1, by decide⟩], fn 1 [] []]) = false := by
  decide

/-- A NON-FINAL type definition is inside the fragment.  `Subtype_ok` reads the
`FINAL?` flag nowhere, and `$rollrt` / `$unrollrt` / `$subst_all_deftype` carry
it through untouched, so `(type (sub (func)))` is decided by exactly the
argument that decides `(type (sub final (func)))`. -/
example :
    validate (modOf [{ rectype := .recr (.cons (.sub none .nil
        (.func .nil .nil)) .nil) }] [fn 0 [] []]) = true := by
  decide

/-- What the type section still excludes is a DECLARED SUPERTYPE, because
`Subtype_ok` then carries a `Comptype_sub` premise, hence `Heaptype_sub`. -/
example :
    Module.frag (modOf [{ rectype := .recr (.cons (.sub none .nil
        (.func .nil .nil)) .nil) },
      { rectype := .recr (.cons (.sub (some .final)
          (TypeUses.ofList [TypeUse.idx default]) (.func .nil .nil)) .nil) }] []) = false := by
  decide

/-! ### Imports and tags

These are the sections the fragment gained.  Every module below is rejected
outright by the previous `Module.frag`, which required `imports` and `tags` to
be EMPTY; each of them is now decided, and the imported components appear in the
staged contexts where `Module_ok` puts them --- `jt_I* jt*`, `gt_I*`,
`dt_I* dt*`, `mt_I* mt*`, `tt_I* tt*`. -/

/-- A module with an import and a tag section. -/
private def modImp (tds : List TypeDef) (is : List Import) (tgs : List Tag)
    (fs : List Func) (exs : List Export) : Module :=
  { types := tds, imports := is, tags := tgs, globals := [], mems := [],
    tables := [], funcs := fs, datas := [], elems := [], start := none,
    exports := exs }

/-- An import, named `"" ""`; the names matter only to `$disjoint_`, which is a
condition on EXPORT names. -/
private def imp (xt : ExternType) : Import :=
  { moduleName := default, itemName := default, externtype := xt }

/-- AN IMPORTED FUNCTION IS CALLABLE.  `(import (func (type 0)))` puts the
closed `deftype` at `C.FUNCS[0]`, so `CALL 0` in the module's own function ---
which is `C.FUNCS[1]` --- reaches it. -/
example :
    validate (modImp [ty2i32] [imp (.func (.idx default))] []
      [fn 0 [] [.localGet default, .localGet ⟨1, by decide⟩, .call default]] []) = true := by
  decide

/-- ... at the imported function's own type: calling it with one operand where
it takes two is rejected. -/
example :
    validate (modImp [ty2i32] [imp (.func (.idx default))] []
      [fn 0 [] [.localGet default, .call default]] []) = false := by
  decide

/-- AN IMPORTED GLOBAL IS READABLE.  `Module_ok` puts `$globalsxt(xt_I*)` at the
front of `C'.GLOBALS`, before the module's own globals. -/
example :
    validate (modImp [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [imp (.global { mutability := none, valtype := ValType.i32 })] []
      [fn 0 [] [.globalGet default]] []) = true := by
  decide

/-- AN IMPORTED MEMORY IS ADDRESSABLE: `$memsxt(xt_I*)` lands in `C.MEMS`, so
`I32.LOAD` finds a memory in a module that declares none. -/
example :
    validate (modImp [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.func .nil (ValTypes.ofList [ValType.i32]))) .nil) }]
      [imp (.mem { addr := .i32, lim := ⟨⟨1, by decide⟩, none⟩ })] []
      [fn 0 [] [.const .i32 default, .load .i32 none default default]] []) = true := by
  decide

/-- A TAG SECTION VALIDATES, and the tag it declares is exportable: with an
empty `C.TAGS` --- which is what every module of the previous fragment had ---
`Externidx_ok/tag` could never apply. -/
example :
    validate (modImp [ty0] [] [{ tagtype := .idx default }] []
      [{ name := default, externidx := .tag default }]) = true := by
  decide

/-- ... and a tag whose type index the type section does not define is
rejected. -/
example : validate (modImp [] [] [{ tagtype := .idx default }] [] []) = false := by
  decide

/-- A tag whose type index names a NON-function type is rejected: `Tagtype_ok`
requires `Expand_use: typeuse ~~ FUNC t_1* -> t_2*`. -/
example :
    validate (modImp [{ rectype := .recr (.cons (.sub (some .final) .nil
        (.array (.mk none (.val ValType.i32)))) .nil) }] []
      [{ tagtype := .idx default }] [] []) = false := by
  decide

/-- OUTSIDE THE FRAGMENT, STILL.  A `FUNC` import whose `typeuse` is written as
an explicit `deftype` rather than as a type index needs `Deftype_ok`, hence
`Comptype_sub`, hence `Heaptype_sub`; `Module.frag` says so. -/
example :
    Module.frag (modImp [ty0]
      [imp (.func (.defd (.defd (.recr .nil) 0)))] [] [] []) = false := by
  decide

/-- ... as does an imported global of reference type, which the instruction
fragment cannot read. -/
example :
    Module.frag (modImp [ty0]
      [imp (.global { mutability := none, valtype := .ref (.ref none (.abs .func)) })]
      [] [] []) = false := by
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
