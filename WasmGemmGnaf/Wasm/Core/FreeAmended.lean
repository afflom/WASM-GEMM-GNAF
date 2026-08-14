/-
  Wasm/Core/FreeAmended.lean --- the coverage-neutral free-index repair carried
  by AMD-009 / DEV-009.

  The vendored Core 3.0 sources omit the `TAGS` component of `free`, the
  `$free_tagidx` equation, the tag case of `$free_externidx`, `$free_catch`, and
  all three exception-instruction equations.  This file states exactly the
  repaired equations recorded by `core3ExceptionFreeAuthorityAmendment` while
  leaving the byte-identical pinned transcription in `Values.lean` and
  `Free.lean` unchanged.

  No declaration here carries a pinned-source coverage marker.  The amended
  layer is identified by the canonical authority-amendment set in
  `Wasm/AuthorityAmendments.lean` and the profile semantics identities.
-/
import WasmGemmGnaf.Wasm.Core.Free
import WasmGemmGnaf.Wasm.AuthorityAmendments

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- The amended `free` record: the pinned components plus the omitted `TAGS`
component.  Extending the pinned record makes erasure explicit and keeps every
unchanged component definitionally shared with the transcription. -/
structure Free' extends Free where
  tags : List TagIdx := []
  deriving DecidableEq, Repr, Inhabited

namespace Free'

/-- Forget only the amended `TAGS` component. -/
def erase (f : Free') : Free := f.toFree

/-- Embed a pinned free-index result; it has no tag indices. -/
def ofPinned (f : Free) : Free' := { toFree := f, tags := [] }

def empty : Free' := ofPinned Free.empty

def append (a b : Free') : Free' :=
  { toFree := Free.append a.toFree b.toFree
    tags := a.tags ++ b.tags }

instance : Append Free' := ⟨append⟩

def ofOption : Option Free' → Free'
  | none => empty
  | some f => f

def join : List Free' → Free'
  | [] => empty
  | f :: fs => append f (join fs)

/-- The repaired `$free_tagidx(tagidx) = {TAGS tagidx}`. -/
def ofTagIdx (x : TagIdx) : Free' := { toFree := Free.empty, tags := [x] }

/-- The repaired `$free_externidx`, including its omitted `TAG` equation. -/
def ofExternIdx : ExternIdx → Free'
  | .func x => ofPinned (Free.ofFuncIdx x)
  | .global x => ofPinned (Free.ofGlobalIdx x)
  | .table x => ofPinned (Free.ofTableIdx x)
  | .mem x => ofPinned (Free.ofMemIdx x)
  | .tag x => ofTagIdx x

@[simp] theorem erase_ofPinned (f : Free) : (ofPinned f).erase = f := rfl

@[simp] theorem tags_ofPinned (f : Free) : (ofPinned f).tags = [] := rfl

@[simp] theorem tags_ofTagIdx (x : TagIdx) : (ofTagIdx x).tags = [x] := rfl

@[simp] theorem erase_append (a b : Free') : (append a b).erase =
    Free.append a.erase b.erase := rfl

@[simp] theorem tags_append (a b : Free') : (append a b).tags =
    a.tags ++ b.tags := rfl

end Free'

/-- The four repaired `$free_catch` equations. -/
def freeCatch' : Catch → Free'
  | .tag x l =>
      Free'.append (Free'.ofTagIdx x) (Free'.ofPinned (Free.ofLabelIdx l))
  | .tagRef x l =>
      Free'.append (Free'.ofTagIdx x) (Free'.ofPinned (Free.ofLabelIdx l))
  | .all l => Free'.ofPinned (Free.ofLabelIdx l)
  | .allRef l => Free'.ofPinned (Free.ofLabelIdx l)

mutual

/-- The repaired `$free_instr`.  Every unchanged leaf delegates to the pinned
definition.  Block-shaped instructions recurse through this amended function,
and the three exception alternatives are the exact repaired equations. -/
def freeInstr' : Instr → Free'
  | .block bt body =>
      Free'.append (Free'.ofPinned (freeBlockType bt)) (freeBlock' body)
  | .loop bt body =>
      Free'.append (Free'.ofPinned (freeBlockType bt)) (freeBlock' body)
  | .ifElse bt thn els =>
      Free'.append (Free'.ofPinned (freeBlockType bt))
        (Free'.append (freeBlock' thn) (freeBlock' els))
  | .throw x => Free'.ofTagIdx x
  | .throwRef => Free'.empty
  | .tryTable bt cs body =>
      Free'.append (Free'.ofPinned (freeBlockType bt))
        (Free'.append (Free'.join (cs.val.map freeCatch')) (freeInstrSeq' body))
  | instr => Free'.ofPinned (freeInstr instr)

/-- `$free_list($free_instr(instr)*)` for the amended instruction function. -/
def freeInstrSeq' : InstrSeq → Free'
  | .nil => Free'.empty
  | .cons instr rest => Free'.append (freeInstr' instr) (freeInstrSeq' rest)

/-- The unchanged `$free_block` label shift, applied to every amended
component accumulated from the body. -/
def freeBlock' (body : InstrSeq) : Free' :=
  let f := freeInstrSeq' body
  { toFree := { f.toFree with labels := shiftLabelIdxs f.labels }
    tags := f.tags }

end

/-- The amended `$free_expr`. -/
def freeExpr' (e : Expr) : Free' := freeInstrSeq' e

@[simp] theorem freeCatch'_tag_tags (x : TagIdx) (l : LabelIdx) :
    (freeCatch' (.tag x l)).tags = [x] := rfl

@[simp] theorem freeCatch'_tagRef_tags (x : TagIdx) (l : LabelIdx) :
    (freeCatch' (.tagRef x l)).tags = [x] := rfl

@[simp] theorem freeInstr'_throw_tags (x : TagIdx) :
    (freeInstr' (.throw x)).tags = [x] := by simp [freeInstr']

@[simp] theorem freeInstr'_throwRef : freeInstr' .throwRef = Free'.empty := by
  simp [freeInstr']

theorem freeInstr'_tryTable (bt : BlockType) (cs : List_ Catch) (body : InstrSeq) :
    freeInstr' (.tryTable bt cs body) =
      Free'.append (Free'.ofPinned (freeBlockType bt))
        (Free'.append (Free'.join (cs.val.map freeCatch')) (freeInstrSeq' body)) := by
  simp [freeInstr']

/-! ## Module-level lifts

These are the existing module free-index equations with expression and function
bodies routed through the repaired instruction function. -/

def freeTypeDef' (td : TypeDef) : Free' := Free'.ofPinned (freeTypeDef td)
def freeTag' (tg : Tag) : Free' := Free'.ofPinned (freeTag tg)
def freeGlobal' (g : Global) : Free' :=
  Free'.append (Free'.ofPinned (freeGlobalType g.globaltype)) (freeExpr' g.init)
def freeMem' (m : Mem) : Free' := Free'.ofPinned (freeMem m)
def freeTable' (t : Table) : Free' :=
  Free'.append (Free'.ofPinned (freeTableType t.tabletype)) (freeExpr' t.init)
def freeLocal' (l : Local) : Free' := Free'.ofPinned (freeLocal l)

def freeFunc' (f : Func) : Free' :=
  Free'.append (Free'.ofPinned (Free.ofTypeIdx f.typeidx))
    (Free'.append (Free'.join (f.locals.map freeLocal'))
      (let bodyFree := freeBlock' f.body
       { toFree := { bodyFree.toFree with locals := [] }
         tags := bodyFree.tags }))

def freeDataMode' : DataMode → Free'
  | .active x e =>
      Free'.append (Free'.ofPinned (Free.ofMemIdx x)) (freeExpr' e)
  | .passive => Free'.empty

def freeData' (d : Data) : Free' := freeDataMode' d.mode

def freeElemMode' : ElemMode → Free'
  | .active x e =>
      Free'.append (Free'.ofPinned (Free.ofTableIdx x)) (freeExpr' e)
  | .passive => Free'.empty
  | .declare => Free'.empty

def freeElem' (e : Elem) : Free' :=
  Free'.append (Free'.ofPinned (freeRefType e.reftype))
    (Free'.append (Free'.join (e.init.map freeExpr')) (freeElemMode' e.mode))

def freeStart' (s : Start) : Free' := Free'.ofPinned (freeStart s)
def freeImport' (i : Import) : Free' := Free'.ofPinned (freeImport i)
def freeExport' (e : Export) : Free' := Free'.ofExternIdx e.externidx

def freeModule' (m : Module) : Free' :=
  Free'.join
    [ Free'.join (m.types.map freeTypeDef'),
      Free'.join (m.tags.map freeTag'),
      Free'.join (m.globals.map freeGlobal'),
      Free'.join (m.mems.map freeMem'),
      Free'.join (m.tables.map freeTable'),
      Free'.join (m.funcs.map freeFunc'),
      Free'.join (m.datas.map freeData'),
      Free'.join (m.elems.map freeElem'),
      Free'.ofOption (m.start.map freeStart'),
      Free'.join (m.imports.map freeImport'),
      Free'.join (m.exports.map freeExport') ]

def funcidxModule' (m : Module) : List FuncIdx := (freeModule' m).funcs

def dataidxFuncs' (fs : List Func) : List DataIdx :=
  (Free'.join (fs.map freeFunc')).datas

def funcidxNonfuncs' (globals : List Global) (mems : List Mem)
    (tables : List Table) (elems : List Elem) : List FuncIdx :=
  funcidxModule'
    { types := [], imports := [], tags := [], globals := globals, mems := mems,
      tables := tables, funcs := [], datas := [], elems := elems, start := none,
      exports := [] }

/-- The AMD-009 data record names the declarations implemented here. -/
theorem exceptionFreeAmendment_targets :
    core3ExceptionFreeAuthorityAmendment.patches.flatMap
        AuthorityPatchBody.amendedLeanDeclarations =
      [ "WasmGemmGnaf.Wasm.Core.Free'",
        "WasmGemmGnaf.Wasm.Core.Free'.ofTagIdx",
        "WasmGemmGnaf.Wasm.Core.Free'.ofTagIdx",
        "WasmGemmGnaf.Wasm.Core.Free'.ofExternIdx",
        "WasmGemmGnaf.Wasm.Core.freeCatch'",
        "WasmGemmGnaf.Wasm.Core.freeCatch'",
        "WasmGemmGnaf.Wasm.Core.freeInstr'" ] := rfl

end WasmGemmGnaf.Wasm.Core
