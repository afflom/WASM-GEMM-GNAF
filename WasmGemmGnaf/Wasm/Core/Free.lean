/-
  Wasm/Core/Free.lean --- the free-index functions of the pinned WebAssembly
  Core 3.0 front end.

  NORMATIVE SOURCE.  Every definition below transcribes a `def` of

      vendor/wasm-spec/specification/wasm-3.0/1.2-syntax.types.spectec  (section "Free indices")
      vendor/wasm-spec/specification/wasm-3.0/1.3-syntax.instructions.spectec  (section "Free indices")
      vendor/wasm-spec/specification/wasm-3.0/1.4-syntax.modules.spectec  (section "Free indices")

  at the pinned commit.

  WHY IT IS NEEDED HERE.  `Module_ok` of `2.4-validation.modules.spectec`
  constrains the `REFS` component of the module context by

      -- if x* = $funcidx_nonfuncs(global* mem* table* elem*)

  and `$funcidx_nonfuncs` is `$free_module(...).FUNCS`.  `REFS` is what
  `Instr_ok/ref.func`'s `x <- C.REFS` premise reads, so without these functions
  the module rule could not be stated at all --- it would have to quantify over
  an arbitrary `REFS`, which is a strictly weaker rule.

  ONE ANOMALY IN THE PINNED SOURCE, TRANSCRIBED AS WRITTEN:

      def $free_instr(STRUCT.NEW typeidx) = {}

  Every neighbouring equation (`STRUCT.NEW_DEFAULT`, `STRUCT.GET`, `STRUCT.SET`,
  all of `ARRAY.*`) returns `$free_typeidx(typeidx)`, so the empty record looks
  like an oversight in the source; `REF.I31` and `I31.GET` are likewise `{}` but
  those carry no index at all.  It is transcribed verbatim.  It cannot affect
  `$funcidx_module`, which projects `FUNCS`, and a `typeidx` never contributes
  to `FUNCS`.
-/
import WasmGemmGnaf.Wasm.Core.Modules

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- `$(labelidx - 1)` of `$shift_labelidxs`, saturating at zero as natural
subtraction does. -/
def LabelIdx.pred (l : LabelIdx) : LabelIdx :=
  ⟨l.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.property⟩

/-! ## Free indices of types

`1.2-syntax.types.spectec`.  Only `$free_typevar`'s `_IDX` case ever produces
anything; every other leaf is `{}`. -/

mutual

/-- `def $free_typevar(_IDX typeidx) = $free_typeidx(typeidx)` and
`def $free_typevar(REC n) = {}`, lifted to `typeuse` by
`def $free_typeuse(typevar) = $free_typevar(typevar)` and
`def $free_typeuse(deftype) = $free_deftype(deftype)`. -/
def freeTypeUse : TypeUse → Free
  | .idx x => Free.ofTypeIdx x
  | .recu _ => Free.empty
  | .defd dt => freeDefType dt

/-- `def $free_deftype(_DEF rectype n) = $free_rectype(rectype)`. -/
def freeDefType : DefType → Free
  | .defd qt _ => freeRecType qt

/-- `def $free_rectype(REC subtype*) = $free_list($free_subtype(subtype)*)`. -/
def freeRecType : RecType → Free
  | .recr sts => freeSubTypes sts

/-- `$free_subtype` joined over a `subtype*`. -/
def freeSubTypes : SubTypes → Free
  | .nil => Free.empty
  | .cons st rest => Free.append (freeSubType st) (freeSubTypes rest)

/-- `def $free_subtype(SUB final? typeuse* comptype)
    = $free_list($free_typeuse(typeuse)*) ++ $free_comptype(comptype)`. -/
def freeSubType : SubType → Free
  | .sub _ sups ct => Free.append (freeTypeUses sups) (freeCompType ct)

/-- `$free_typeuse` joined over a `typeuse*`. -/
def freeTypeUses : TypeUses → Free
  | .nil => Free.empty
  | .cons tu rest => Free.append (freeTypeUse tu) (freeTypeUses rest)

/-- `def $free_comptype`, all three equations. -/
def freeCompType : CompType → Free
  | .struct fts => freeFieldTypes fts
  | .array ft => freeFieldType ft
  | .func dom cod => Free.append (freeValTypes dom) (freeValTypes cod)

/-- `$free_fieldtype` joined over a `fieldtype*`. -/
def freeFieldTypes : FieldTypes → Free
  | .nil => Free.empty
  | .cons ft rest => Free.append (freeFieldType ft) (freeFieldTypes rest)

/-- `def $free_fieldtype(mut? storagetype) = $free_storagetype(storagetype)`. -/
def freeFieldType : FieldType → Free
  | .mk _ zt => freeStorageType zt

/-- `def $free_storagetype`, both equations. -/
def freeStorageType : StorageType → Free
  | .val t => freeValType t
  | .pack _ => Free.empty

/-- `def $free_resulttype(valtype*) = $free_list($free_valtype(valtype)*)`. -/
def freeValTypes : ValTypes → Free
  | .nil => Free.empty
  | .cons t rest => Free.append (freeValType t) (freeValTypes rest)

/-- `def $free_valtype`, all four equations. -/
def freeValType : ValType → Free
  | .num _ => Free.empty
  | .vec _ => Free.empty
  | .ref rt => freeRefType rt
  | .bot => Free.empty

/-- `def $free_reftype(REF null? heaptype) = $free_heaptype(heaptype)`. -/
def freeRefType : RefType → Free
  | .ref _ ht => freeHeapType ht

/-- `def $free_heaptype`, both equations; `$free_absheaptype(absheaptype) = {}`. -/
def freeHeapType : HeapType → Free
  | .abs _ => Free.empty
  | .use tu => freeTypeUse tu

end

/-- `def $free_resulttype(valtype*)`, on an ordinary list. -/
def freeResultType (ts : List ValType) : Free := Free.join (ts.map freeValType)

/-- `def $free_tagtype(deftype) = $free_deftype(deftype)`, on the `typeuse` the
syntax layer actually stores. -/
def freeTagType (jt : TagType) : Free := freeTypeUse jt

/-- `def $free_globaltype(mut? valtype) = $free_valtype(valtype)`. -/
def freeGlobalType (gt : GlobalType) : Free := freeValType gt.valtype

/-- `def $free_memtype(addrtype limits PAGE) = $free_addrtype(addrtype)`, and
`$free_addrtype` is `{}`. -/
def freeMemType (_mt : MemType) : Free := Free.empty

/-- `def $free_tabletype(addrtype limits reftype)
    = $free_addrtype(addrtype) ++ $free_reftype(reftype)`. -/
def freeTableType (tt : TableType) : Free := freeRefType tt.elem

/-- `def $free_datatype(OK) = {}`. -/
def freeDataType (_dt : DataType) : Free := Free.empty

/-- `def $free_elemtype(reftype) = $free_reftype(reftype)`. -/
def freeElemType (et : ElemType) : Free := freeRefType et

/-- `def $free_externtype`, all five equations. -/
def freeExternType : ExternType → Free
  | .tag jt => freeTagType jt
  | .global gt => freeGlobalType gt
  | .mem mt => freeMemType mt
  | .table tt => freeTableType tt
  | .func tu => freeTypeUse tu

/-- `def $free_moduletype(externtype_1* -> externtype_2*)`. -/
def freeModuleType (mmt : ModuleType) : Free :=
  Free.append (Free.join (mmt.imports.map freeExternType))
    (Free.join (mmt.exports.map freeExternType))

/-! ## Free indices of instructions

`1.3-syntax.instructions.spectec`. -/

/-- `def $free_shape(lanetype X dim) = $free_lanetype(lanetype)`, which is `{}`. -/
def freeShape (_sh : Shape) : Free := Free.empty

/-- `def $free_blocktype`, both equations. -/
def freeBlockType : BlockType → Free
  | .result t => Free.ofOption (t.map freeValType)
  | .idx x => Free.ofTypeIdx x

/-- `def $shift_labelidxs(labelidx*) : labelidx*`:

    $shift_labelidxs(eps) = eps
    $shift_labelidxs(0 labelidx'*) = $shift_labelidxs(labelidx'*)
    $shift_labelidxs(labelidx labelidx'*) = ($(labelidx - 1)) $shift_labelidxs(labelidx'*)

A label index of `0` refers to the block itself and is discharged by it; every
other index is decremented as it crosses the block boundary. -/
def shiftLabelIdxs : List LabelIdx → List LabelIdx
  | [] => []
  | l :: ls => if l.val = 0 then shiftLabelIdxs ls else l.pred :: shiftLabelIdxs ls

mutual

/-- `def $free_instr(instr) : free`, all equations of the pinned source. -/
def freeInstr : Instr → Free
  | .nop => Free.empty
  | .unreachable => Free.empty
  | .drop => Free.empty
  | .select ts => Free.ofOption (ts.map (fun l => Free.join (l.map freeValType)))
  | .block bt body => Free.append (freeBlockType bt) (freeBlock body)
  | .loop bt body => Free.append (freeBlockType bt) (freeBlock body)
  | .ifElse bt thn els =>
      Free.append (freeBlockType bt) (Free.append (freeBlock thn) (freeBlock els))
  | .br l => Free.ofLabelIdx l
  | .brIf l => Free.ofLabelIdx l
  | .brTable ls l' => Free.append (Free.join (ls.map Free.ofLabelIdx)) (Free.ofLabelIdx l')
  | .brOnNull l => Free.ofLabelIdx l
  | .brOnNonNull l => Free.ofLabelIdx l
  | .brOnCast l rt₁ rt₂ =>
      Free.append (Free.ofLabelIdx l) (Free.append (freeRefType rt₁) (freeRefType rt₂))
  | .brOnCastFail l rt₁ rt₂ =>
      Free.append (Free.ofLabelIdx l) (Free.append (freeRefType rt₁) (freeRefType rt₂))
  | .call x => Free.ofFuncIdx x
  | .callRef tu => freeTypeUse tu
  | .callIndirect x tu => Free.append (Free.ofTableIdx x) (freeTypeUse tu)
  | .ret => Free.empty
  | .returnCall x => Free.ofFuncIdx x
  | .returnCallRef tu => freeTypeUse tu
  | .returnCallIndirect x tu => Free.append (Free.ofTableIdx x) (freeTypeUse tu)
  -- The pinned source gives no `$free_instr` equation for `THROW`, `THROW_REF`
  -- or `TRY_TABLE`; the empty record is the only total completion available,
  -- and it is recorded here rather than hidden.  A `TRY_TABLE` body's free
  -- indices are therefore not reported by this function.
  | .throw _ => Free.empty
  | .throwRef => Free.empty
  | .tryTable _ _ _ => Free.empty
  | .localGet x => Free.ofLocalIdx x
  | .localSet x => Free.ofLocalIdx x
  | .localTee x => Free.ofLocalIdx x
  | .globalGet x => Free.ofGlobalIdx x
  | .globalSet x => Free.ofGlobalIdx x
  | .tableGet x => Free.ofTableIdx x
  | .tableSet x => Free.ofTableIdx x
  | .tableSize x => Free.ofTableIdx x
  | .tableGrow x => Free.ofTableIdx x
  | .tableFill x => Free.ofTableIdx x
  | .tableCopy x y => Free.append (Free.ofTableIdx x) (Free.ofTableIdx y)
  | .tableInit x y => Free.append (Free.ofTableIdx x) (Free.ofElemIdx y)
  | .elemDrop x => Free.ofElemIdx x
  | .load _ _ x _ => Free.ofMemIdx x
  | .store _ _ x _ => Free.ofMemIdx x
  | .vload _ _ x _ => Free.ofMemIdx x
  | .vloadLane _ _ x _ _ => Free.ofMemIdx x
  | .vstore _ x _ => Free.ofMemIdx x
  | .vstoreLane _ _ x _ _ => Free.ofMemIdx x
  | .memorySize x => Free.ofMemIdx x
  | .memoryGrow x => Free.ofMemIdx x
  | .memoryFill x => Free.ofMemIdx x
  | .memoryCopy x y => Free.append (Free.ofMemIdx x) (Free.ofMemIdx y)
  | .memoryInit x y => Free.append (Free.ofMemIdx x) (Free.ofDataIdx y)
  | .dataDrop x => Free.ofDataIdx x
  | .refNull ht => freeHeapType ht
  | .refIsNull => Free.empty
  | .refAsNonNull => Free.empty
  | .refEq => Free.empty
  | .refTest rt => freeRefType rt
  | .refCast rt => freeRefType rt
  | .refFunc x => Free.ofFuncIdx x
  | .refI31 => Free.empty
  | .i31Get _ => Free.empty
  -- `def $free_instr(STRUCT.NEW typeidx) = {}` -- verbatim; see the header.
  | .structNew _ => Free.empty
  | .structNewDefault x => Free.ofTypeIdx x
  | .structGet _ x _ => Free.ofTypeIdx x
  | .structSet x _ => Free.ofTypeIdx x
  | .arrayNew x => Free.ofTypeIdx x
  | .arrayNewDefault x => Free.ofTypeIdx x
  | .arrayNewFixed x _ => Free.ofTypeIdx x
  | .arrayNewData x y => Free.append (Free.ofTypeIdx x) (Free.ofDataIdx y)
  | .arrayNewElem x y => Free.append (Free.ofTypeIdx x) (Free.ofElemIdx y)
  | .arrayGet _ x => Free.ofTypeIdx x
  | .arraySet x => Free.ofTypeIdx x
  | .arrayLen => Free.empty
  | .arrayFill x => Free.ofTypeIdx x
  | .arrayCopy x y => Free.append (Free.ofTypeIdx x) (Free.ofTypeIdx y)
  | .arrayInitData x y => Free.append (Free.ofTypeIdx x) (Free.ofDataIdx y)
  | .arrayInitElem x y => Free.append (Free.ofTypeIdx x) (Free.ofElemIdx y)
  | .externConvertAny => Free.empty
  | .anyConvertExtern => Free.empty
  | .const _ _ => Free.empty
  | .unop _ _ => Free.empty
  | .binop _ _ => Free.empty
  | .testop _ _ => Free.empty
  | .relop _ _ => Free.empty
  | .cvtop _ _ _ => Free.empty
  | .vconst _ _ => Free.empty
  | .vvunop _ _ => Free.empty
  | .vvbinop _ _ => Free.empty
  | .vvternop _ _ => Free.empty
  | .vvtestop _ _ => Free.empty
  | .vunop sh _ => freeShape sh
  | .vbinop sh _ => freeShape sh
  | .vternop sh _ => freeShape sh
  | .vtestop sh _ => freeShape sh
  | .vrelop sh _ => freeShape sh
  | .vshiftop sh _ => freeShape sh.val
  | .vbitmask sh => freeShape sh.val
  | .vswizzlop sh _ => freeShape sh.val
  | .vshuffle sh _ => freeShape sh.val
  | .vextunop sh₁ sh₂ _ => Free.append (freeShape sh₁.val) (freeShape sh₂.val)
  | .vextbinop sh₁ sh₂ _ => Free.append (freeShape sh₁.val) (freeShape sh₂.val)
  | .vextternop sh₁ sh₂ _ => Free.append (freeShape sh₁.val) (freeShape sh₂.val)
  | .vnarrow sh₁ sh₂ _ => Free.append (freeShape sh₁.val) (freeShape sh₂.val)
  | .vcvtop sh₁ sh₂ _ => Free.append (freeShape sh₁) (freeShape sh₂)
  | .vsplat sh => freeShape sh
  | .vextractLane sh _ _ => freeShape sh
  | .vreplaceLane sh _ => freeShape sh

/-- `$free_instr` joined over an `instr*`, i.e. `$free_expr`. -/
def freeInstrSeq : InstrSeq → Free
  | .nil => Free.empty
  | .cons i rest => Free.append (freeInstr i) (freeInstrSeq rest)

/-- `def $free_block(instr*) = free[.LABELS = $shift_labelidxs(free.LABELS)]
    -- if free = $free_list($free_instr(instr)*)`. -/
def freeBlock (is : InstrSeq) : Free :=
  let f := freeInstrSeq is
  { f with labels := shiftLabelIdxs f.labels }

end

/-- `def $free_expr(instr*) = $free_list($free_instr(instr)*)`. -/
def freeExpr (e : Expr) : Free := freeInstrSeq e

/-! ## Free indices of modules

`1.4-syntax.modules.spectec`. -/

/-- `def $free_type(TYPE rectype) = $free_rectype(rectype)`. -/
def freeTypeDef (td : TypeDef) : Free := freeRecType td.rectype

/-- `def $free_tag(TAG tagtype) = $free_tagtype(tagtype)`. -/
def freeTag (tg : Tag) : Free := freeTagType tg.tagtype

/-- `def $free_global(GLOBAL globaltype expr)
    = $free_globaltype(globaltype) ++ $free_expr(expr)`. -/
def freeGlobal (g : Global) : Free :=
  Free.append (freeGlobalType g.globaltype) (freeExpr g.init)

/-- `def $free_mem(MEMORY memtype) = $free_memtype(memtype)`. -/
def freeMem (m : Mem) : Free := freeMemType m.memtype

/-- `def $free_table(TABLE tabletype expr)
    = $free_tabletype(tabletype) ++ $free_expr(expr)`. -/
def freeTable (t : Table) : Free :=
  Free.append (freeTableType t.tabletype) (freeExpr t.init)

/-- `def $free_local(LOCAL t) = $free_valtype(t)`. -/
def freeLocal (l : Local) : Free := freeValType l.valtype

/-- `def $free_func(FUNC typeidx local* expr)
    = $free_typeidx(typeidx) ++ $free_list($free_local(local)*)
      ++ $free_block(expr)[.LOCALS = eps]`. -/
def freeFunc (f : Func) : Free :=
  Free.append (Free.ofTypeIdx f.typeidx)
    (Free.append (Free.join (f.locals.map freeLocal))
      { freeBlock f.body with locals := [] })

/-- `def $free_datamode`, both equations. -/
def freeDataMode : DataMode → Free
  | .active x e => Free.append (Free.ofMemIdx x) (freeExpr e)
  | .passive => Free.empty

/-- `def $free_data(DATA byte* datamode) = $free_datamode(datamode)`. -/
def freeData (d : Data) : Free := freeDataMode d.mode

/-- `def $free_elemmode`, all three equations. -/
def freeElemMode : ElemMode → Free
  | .active x e => Free.append (Free.ofTableIdx x) (freeExpr e)
  | .passive => Free.empty
  | .declare => Free.empty

/-- `def $free_elem(ELEM reftype expr* elemmode)
    = $free_reftype(reftype) ++ $free_list($free_expr(expr)*) ++ $free_elemmode(elemmode)`. -/
def freeElem (e : Elem) : Free :=
  Free.append (freeRefType e.reftype)
    (Free.append (Free.join (e.init.map freeExpr)) (freeElemMode e.mode))

/-- `def $free_start(START funcidx) = $free_funcidx(funcidx)`. -/
def freeStart (s : Start) : Free := Free.ofFuncIdx s.funcidx

/-- `def $free_import(IMPORT name_1 name_2 externtype) = $free_externtype(externtype)`. -/
def freeImport (i : Import) : Free := freeExternType i.externtype

/-- `def $free_export(EXPORT name externidx) = $free_externidx(externidx)`. -/
def freeExport (e : Export) : Free := Free.ofExternIdx e.externidx

/-- `def $free_module(MODULE type* import* tag* global* mem* table* func* data*
    elem* start? export*)`, in the source's own join order. -/
def freeModule (m : Module) : Free :=
  Free.join
    [ Free.join (m.types.map freeTypeDef),
      Free.join (m.tags.map freeTag),
      Free.join (m.globals.map freeGlobal),
      Free.join (m.mems.map freeMem),
      Free.join (m.tables.map freeTable),
      Free.join (m.funcs.map freeFunc),
      Free.join (m.datas.map freeData),
      Free.join (m.elems.map freeElem),
      Free.ofOption (m.start.map freeStart),
      Free.join (m.imports.map freeImport),
      Free.join (m.exports.map freeExport) ]

/-- `def $funcidx_module(module) = $free_module(module).FUNCS`. -/
def funcidxModule (m : Module) : List FuncIdx := (freeModule m).funcs

/-- `def $dataidx_funcs(func*) = $free_list($free_func(func)*).DATAS`. -/
def dataidxFuncs (fs : List Func) : List DataIdx := (Free.join (fs.map freeFunc)).datas

/-- `def $funcidx_nonfuncs(global* mem* table* elem*)
    = $funcidx_module(MODULE eps eps eps global* mem* table* eps eps elem* eps eps)`,
the `REFS` component of `Module_ok`. -/
def funcidxNonfuncs (globals : List Global) (mems : List Mem) (tables : List Table)
    (elems : List Elem) : List FuncIdx :=
  funcidxModule
    { types := [], imports := [], tags := [], globals := globals, mems := mems,
      tables := tables, funcs := [], datas := [], elems := elems, start := none,
      exports := [] }

end WasmGemmGnaf.Wasm.Core
