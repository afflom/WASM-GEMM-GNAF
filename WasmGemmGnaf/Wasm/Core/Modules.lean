/-
  Wasm/Core/Modules.lean --- the module syntax of the pinned WebAssembly Core
  3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/1.4-syntax.modules.spectec

  at the pinned commit, in source order.  Conventions are those fixed in
  `Core/Values.lean`.

  One naming note: the source's section sort is `syntax type = TYPE rectype`.
  `Type` is Lean's own sort, so the Lean declaration is `TypeDef`; the marker
  still names the production `type`, which is what `xtask core` checks.
-/
import WasmGemmGnaf.Wasm.Core.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- `syntax elemmode = ACTIVE tableidx expr | PASSIVE | DECLARE`. -/
-- core-syntax: elemmode
inductive ElemMode where
  /-- `ACTIVE tableidx expr`. -/
  | active (x : TableIdx) (offset : Expr)
  /-- `PASSIVE`. -/
  | passive
  /-- `DECLARE`. -/
  | declare
  deriving DecidableEq, Repr, Inhabited

/-- `syntax datamode = ACTIVE memidx expr | PASSIVE`. -/
-- core-syntax: datamode
inductive DataMode where
  /-- `ACTIVE memidx expr`. -/
  | active (x : MemIdx) (offset : Expr)
  /-- `PASSIVE`. -/
  | passive
  deriving DecidableEq, Repr, Inhabited

/-- `syntax type = TYPE rectype`. -/
-- core-syntax: type
structure TypeDef where
  rectype : RecType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax tag = TAG tagtype`. -/
-- core-syntax: tag
structure Tag where
  tagtype : TagType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax global = GLOBAL globaltype expr`. -/
-- core-syntax: global
structure Global where
  globaltype : GlobalType
  init : Expr
  deriving DecidableEq, Repr, Inhabited

/-- `syntax mem = MEMORY memtype`. -/
-- core-syntax: mem
structure Mem where
  memtype : MemType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax table = TABLE tabletype expr`. -/
-- core-syntax: table
structure Table where
  tabletype : TableType
  init : Expr
  deriving DecidableEq, Repr, Inhabited

/-- `syntax data = DATA byte* datamode`. -/
-- core-syntax: data
structure Data where
  bytes : List Byte
  mode : DataMode
  deriving DecidableEq, Repr, Inhabited

/-- `syntax local = LOCAL valtype`. -/
-- core-syntax: local
structure Local where
  valtype : ValType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax func = FUNC typeidx local* expr`. -/
-- core-syntax: func
structure Func where
  typeidx : TypeIdx
  locals : List Local
  body : Expr
  deriving DecidableEq, Repr, Inhabited

/-- `syntax elem = ELEM reftype expr* elemmode`. -/
-- core-syntax: elem
structure Elem where
  reftype : RefType
  init : List Expr
  mode : ElemMode
  deriving DecidableEq, Repr, Inhabited

/-- `syntax start = START funcidx`. -/
-- core-syntax: start
structure Start where
  funcidx : FuncIdx
  deriving DecidableEq, Repr, Inhabited

/-- `syntax import = IMPORT name name externtype`. -/
-- core-syntax: import
structure Import where
  moduleName : Name
  itemName : Name
  externtype : ExternType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax export = EXPORT name externidx`. -/
-- core-syntax: export
structure Export where
  name : Name
  externidx : ExternIdx
  deriving DecidableEq, Repr, Inhabited

/-- `syntax module = MODULE type* import* tag* global* mem* table* func* data*
    elem* start? export*`.

The field order is the source's, which is also the order the module-level
validation rule `Module_ok` of `2.4-validation.modules.spectec` traverses.  It
is NOT the binary section order; the binary grammar's ordering obligation
belongs to `5.4-binary.modules.spectec` and is discharged there. -/
-- core-syntax: module
structure Module where
  types : List TypeDef
  imports : List Import
  tags : List Tag
  globals : List Global
  mems : List Mem
  tables : List Table
  funcs : List Func
  datas : List Data
  elems : List Elem
  start : Option Start
  exports : List Export
  deriving DecidableEq, Repr, Inhabited

/-! ## Well-formedness of a module

A Lean `Module` is a term of the module SORT.  Being a Core 3.0 module is more
than that, and the surplus has two independent parts.

* THE SIDE CONDITIONS.  Every `-- if` the instruction and type fragments carry:
  `Instr.wf` on each instruction of each expression, and the `list(X)` bound
  `|X*| < 2^32` at each `list(...)` occurrence inside a `rectype`.

* THE `/syn` PHASE INVARIANT.  `Core/Types.lean` explains why `typeuse`,
  `heaptype` and `valtype` are one Lean sort each rather than two; the price is
  that the sort admits `BOT`, a `deftype` and a `REC n`, none of which the
  syntax phase can produce.  A module obtained by decoding a byte sequence
  therefore satisfies `Module.isSyn`, and a module that does not satisfy it is
  not something `5.4-binary.modules.spectec` can yield.  This is the invariant
  the split into `/syn` and `/sem` states, recovered here as a predicate.

`Module.wf` is their conjunction.  Both are decidable and neither is assumed
anywhere: they are computed from the module. -/

/-- The instruction side conditions of an `elemmode`'s offset expression. -/
def ElemMode.wf : ElemMode → Bool
  | .active _ e => InstrSeq.wf e
  | .passive => true
  | .declare => true

/-- The `/syn` phase invariant of an `elemmode`. -/
def ElemMode.isSyn : ElemMode → Bool
  | .active _ e => InstrSeq.isSyn e
  | .passive => true
  | .declare => true

/-- The instruction side conditions of a `datamode`'s offset expression. -/
def DataMode.wf : DataMode → Bool
  | .active _ e => InstrSeq.wf e
  | .passive => true

/-- The `/syn` phase invariant of a `datamode`. -/
def DataMode.isSyn : DataMode → Bool
  | .active _ e => InstrSeq.isSyn e
  | .passive => true

/-- The `list(...)` bounds of a type section entry. -/
def TypeDef.wf (td : TypeDef) : Bool := td.rectype.wfList

/-- The `/syn` phase invariant of a type section entry. -/
def TypeDef.isSyn (td : TypeDef) : Bool := td.rectype.isSyn

/-- The `/syn` phase invariant of a tag. -/
def Tag.isSyn (tg : Tag) : Bool := tg.tagtype.isSyn

/-- The instruction side conditions of a global's initialiser. -/
def Global.wf (g : Global) : Bool := InstrSeq.wf g.init

/-- The `/syn` phase invariant of a global. -/
def Global.isSyn (g : Global) : Bool := g.globaltype.isSyn && InstrSeq.isSyn g.init

/-- The instruction side conditions of a table's initialiser. -/
def Table.wf (t : Table) : Bool := InstrSeq.wf t.init

/-- The `/syn` phase invariant of a table. -/
def Table.isSyn (t : Table) : Bool := t.tabletype.isSyn && InstrSeq.isSyn t.init

/-- The instruction side conditions of a function body. -/
def Func.wf (f : Func) : Bool := InstrSeq.wf f.body

/-- The `/syn` phase invariant of a function: its declared locals and its
body. -/
def Func.isSyn (f : Func) : Bool :=
  f.locals.all (fun l => l.valtype.isSyn) && InstrSeq.isSyn f.body

/-- The instruction side conditions of a data segment. -/
def Data.wf (d : Data) : Bool := d.mode.wf

/-- The `/syn` phase invariant of a data segment. -/
def Data.isSyn (d : Data) : Bool := d.mode.isSyn

/-- The instruction side conditions of an element segment. -/
def Elem.wf (e : Elem) : Bool := e.init.all InstrSeq.wf && e.mode.wf

/-- The `/syn` phase invariant of an element segment. -/
def Elem.isSyn (e : Elem) : Bool :=
  e.reftype.isSyn && e.init.all InstrSeq.isSyn && e.mode.isSyn

/-- The `/syn` phase invariant of an import. -/
def Import.isSyn (i : Import) : Bool := i.externtype.isSyn

/-- The `/syn` phase invariant of a whole module: no `BOT`, no `deftype` and no
`REC n` occurs anywhere in it, at any depth. -/
def Module.isSyn (m : Module) : Bool :=
  m.types.all TypeDef.isSyn &&
  m.imports.all Import.isSyn &&
  m.tags.all Tag.isSyn &&
  m.globals.all Global.isSyn &&
  m.tables.all Table.isSyn &&
  m.funcs.all Func.isSyn &&
  m.datas.all Data.isSyn &&
  m.elems.all Elem.isSyn

/-- Every side condition of the module's types and instructions, `/syn` phase
invariant included. -/
def Module.wf (m : Module) : Bool :=
  m.types.all TypeDef.wf &&
  m.globals.all Global.wf &&
  m.tables.all Table.wf &&
  m.funcs.all Func.wf &&
  m.datas.all Data.wf &&
  m.elems.all Elem.wf &&
  m.isSyn

/-! ## Sanity checks

Kernel-checked evaluations.  `Module.wf` earns its place only by rejecting
something. -/

/-- The empty module is well-formed. -/
example :
    Module.wf
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [], funcs := [], datas := [], elems := [], start := none,
        exports := [] } = true := by decide

/-- A function whose body is `REF.NULL BOT` satisfies every `-- if` side
condition ... -/
example :
    Module.wf
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [],
        funcs := [{ typeidx := default, locals := [],
                    body := .cons (.refNull (.abs .bot)) .nil }],
        datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- ... and is rejected by the phase invariant alone: a `BOT` heap type is a
`/sem` form that no decoder can produce. -/
example :
    Module.isSyn
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [],
        funcs := [{ typeidx := default, locals := [],
                    body := .cons (.refNull (.abs .bot)) .nil }],
        datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- A local declared at `BOT` is rejected too, and by the same predicate. -/
example :
    Module.isSyn
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [],
        funcs := [{ typeidx := default, locals := [{ valtype := .bot }],
                    body := .nil }],
        datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- An import whose function type is written as a `/sem` `deftype` rather than
a type index is not a `/syn` module either. -/
example :
    Module.isSyn
      { types := [], imports := [{ moduleName := default, itemName := default,
                                   externtype := .func (.defd default) }],
        tags := [], globals := [], mems := [], tables := [], funcs := [],
        datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- A function body with a `UNOP` outside its numeric type's operator family
fails `Module.wf` while satisfying the phase invariant: the two conditions are
independent. -/
example :
    Module.wf
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [],
        funcs := [{ typeidx := default, locals := [],
                    body := .cons (.unop .f32 (.int .clz)) .nil }],
        datas := [], elems := [], start := none, exports := [] } = false := by
  decide

/-- ... and the same module IS `/syn`. -/
example :
    Module.isSyn
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [],
        funcs := [{ typeidx := default, locals := [],
                    body := .cons (.unop .f32 (.int .clz)) .nil }],
        datas := [], elems := [], start := none, exports := [] } = true := by
  decide

end WasmGemmGnaf.Wasm.Core
