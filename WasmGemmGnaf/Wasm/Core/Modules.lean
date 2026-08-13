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

end WasmGemmGnaf.Wasm.Core
