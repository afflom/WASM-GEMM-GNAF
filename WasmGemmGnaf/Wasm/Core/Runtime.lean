/-
  Wasm/Core/Runtime.lean --- the single authority-selected runtime hierarchy
  for WebAssembly Core 3.0.

  NORMATIVE SOURCE.  Every declaration below transcribes a production or
  definition of

      vendor/wasm-spec/specification/wasm-3.0/4.0-execution.configurations.spectec
      vendor/wasm-spec/specification/wasm-3.0/4.1-execution.values.spectec
      vendor/wasm-spec/specification/wasm-3.0/4.2-execution.types.spectec

  at the pinned commit.  The coverage marker beside a rule names the SpecTec rule
  it discharges; `xtask core` extracts the checklist from the vendored files and
  rejects a marker naming anything they do not define.  The default selector is
  the byte-identical pinned transcription.  The explicit `*A` endpoints apply
  AMD-011 to the subtyping-sensitive premises and are the release semantics.

  WHY A SECOND INSTRUCTION SORT.  `4.0` extends `syntax instr` with the
  administrative forms `addrref`, `LABEL_`, `FRAME_`, `HANDLER_` and `TRAP`.
  `Core/Instructions.lean` has already closed `Instr` over the syntactic forms of
  `1.3`, so the extension is a second sort, `AdminInstr`, with `plain` embedding
  the syntactic one.  That is a Lean necessity, not a semantic choice: `Instr` and
  `AdminInstr` together are exactly `instr/admin`, and no syntactic form is
  duplicated.

  HOST FUNCTIONS.  `syntax hostfunc = ...` is left open by the pinned source: it
  declares the sort and gives it no cases, because the embedder supplies them.  No
  rule of `4.3` inspects a host function -- `Step_read/call_ref-func` requires
  `fi.CODE = FUNC x (LOCAL t)* (instr*)`, so a host function simply has no
  reduction here.  It is transcribed as an opaque index, which is the weakest
  faithful reading available: it carries no structure the source does not give it.

  PARTIALITY.  The state accessors `$type`, `$tag`, `$global`, `$mem`, `$table`,
  `$func`, `$data`, `$elem`, `$local` and the updates `$with_...` are indexing
  operations, undefined when the index is out of range.  They are transcribed as
  `Option`-valued functions, and every rule that uses one carries the premise that
  it is defined.  Nothing is completed with a junk value.
-/
import WasmGemmGnaf.Wasm.Core.Numerics
import WasmGemmGnaf.Wasm.Core.Modules
import WasmGemmGnaf.Wasm.Core.Validation.SubtypingAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Authority selection

AMD-011 changes the subtyping premises used by runtime value typing.  The
runtime remains one inductive hierarchy: this finite selector chooses either
the byte-identical pinned premises or the exact amended premises.  The sole
global instance is pinned for audit compatibility; release consumers select
`amendedExecutionAuthority` explicitly.
-/

/-- The two exact Core execution authorities carried by this repository. -/
inductive ExecutionAuthorityRevision where
  /-- The byte-identical transcription of the pinned Core 3.0 SpecTec tree. -/
  | pinned
  /-- The pinned tree with AMD-011 applied to subtyping-sensitive premises. -/
  | amended
deriving DecidableEq

/-- A finite selector threaded through the single runtime/execution hierarchy. -/
class ExecutionAuthority where
  revision : ExecutionAuthorityRevision

/-- The default, byte-identical pinned execution authority. -/
@[reducible] def pinnedExecutionAuthority : ExecutionAuthority :=
  { revision := .pinned }

/-- The exact release execution authority after AMD-011. -/
@[reducible] def amendedExecutionAuthority : ExecutionAuthority :=
  { revision := .amended }

/-- Existing unqualified execution-relation uses remain pinned. -/
instance : ExecutionAuthority := pinnedExecutionAuthority

/-- Heap-type subtyping selected by the current execution authority. -/
def HeaptypeSubFor [authority : ExecutionAuthority]
    (C : Context) (ht₁ ht₂ : HeapType) : Prop :=
  match authority.revision with
  | .pinned => Heaptype_sub C ht₁ ht₂
  | .amended => Heaptype_subA C ht₁ ht₂

/-- Reference-type subtyping selected by the current execution authority. -/
def ReftypeSubFor [authority : ExecutionAuthority]
    (C : Context) (rt₁ rt₂ : RefType) : Prop :=
  match authority.revision with
  | .pinned => Reftype_sub C rt₁ rt₂
  | .amended => Reftype_subA C rt₁ rt₂

/-- External-type subtyping selected by the current execution authority. -/
def ExterntypeSubFor [authority : ExecutionAuthority]
    (C : Context) (xt₁ xt₂ : ExternType) : Prop :=
  match authority.revision with
  | .pinned => Externtype_sub C xt₁ xt₂
  | .amended => Externtype_subA C xt₁ xt₂

@[simp] theorem HeaptypeSubFor_pinned :
    @HeaptypeSubFor pinnedExecutionAuthority = Heaptype_sub := rfl

@[simp] theorem HeaptypeSubFor_amended :
    @HeaptypeSubFor amendedExecutionAuthority = Heaptype_subA := rfl

@[simp] theorem ReftypeSubFor_pinned :
    @ReftypeSubFor pinnedExecutionAuthority = Reftype_sub := rfl

@[simp] theorem ReftypeSubFor_amended :
    @ReftypeSubFor amendedExecutionAuthority = Reftype_subA := rfl

@[simp] theorem ExterntypeSubFor_pinned :
    @ExterntypeSubFor pinnedExecutionAuthority = Externtype_sub := rfl

@[simp] theorem ExterntypeSubFor_amended :
    @ExterntypeSubFor amendedExecutionAuthority = Externtype_subA := rfl

/-! ## Sequence helpers

The source writes `w*[i]`, `w*[i : n]` and `w*[[i] = w']`; `4.3` also writes
`w*[i : n] = w'*`.  These are the Lean readings, all total or `Option`-valued and
none of them inventing a value. -/

/-- `w*[i : n]`, the length-`n` slice at offset `i`. -/
def slice {α : Type} (l : List α) (i n : Nat) : List α := (l.drop i).take n

/-- `w*[[i] = w']`, defined only when `i` is in range. -/
def setAt? {α : Type} (l : List α) (i : Nat) (a : α) : Option (List α) :=
  if i < l.length then some (l.set i a) else none

/-- `w*[i : n] = w'*` as an update, defined only when the whole window is in
range.  Used by `$with_mem`. -/
def spliceAt? {α : Type} (l : List α) (i n : Nat) (r : List α) : Option (List α) :=
  if i + n ≤ l.length then some (l.take i ++ r ++ l.drop (i + n)) else none

/-! ## Addresses

`4.0`: `syntax addr = nat` and the eleven address kinds that abbreviate it. -/

/-- `syntax addr = nat`. -/
abbrev Addr : Type := Nat
/-- `syntax tagaddr = addr`. -/
abbrev TagAddr : Type := Addr
/-- `syntax globaladdr = addr`. -/
abbrev GlobalAddr : Type := Addr
/-- `syntax memaddr = addr`. -/
abbrev MemAddr : Type := Addr
/-- `syntax tableaddr = addr`. -/
abbrev TableAddr : Type := Addr
/-- `syntax funcaddr = addr`. -/
abbrev FuncAddr : Type := Addr
/-- `syntax dataaddr = addr`. -/
abbrev DataAddr : Type := Addr
/-- `syntax elemaddr = addr`. -/
abbrev ElemAddr : Type := Addr
/-- `syntax structaddr = addr`. -/
abbrev StructAddr : Type := Addr
/-- `syntax arrayaddr = addr`. -/
abbrev ArrayAddr : Type := Addr
/-- `syntax exnaddr = addr`. -/
abbrev ExnAddr : Type := Addr
/-- `syntax hostaddr = addr`. -/
abbrev HostAddr : Type := Addr

/-- `syntax externaddr = TAG tagaddr | GLOBAL globaladdr | MEM memaddr
    | TABLE tableaddr | FUNC funcaddr`. -/
inductive ExternAddr where
  | tag (a : TagAddr)
  | global (a : GlobalAddr)
  | mem (a : MemAddr)
  | table (a : TableAddr)
  | func (a : FuncAddr)
  deriving DecidableEq, Repr, Inhabited

/-! ## Values -/

/-- `syntax num = CONST numtype num_(numtype)`. -/
structure NumVal where
  nt : NumType
  c : Num_ nt

/-- `syntax vec = VCONST vectype vec_(vectype)`. -/
structure VecVal where
  vt : VecType
  c : VecLit vt.toVnn

/-- `syntax addrref = REF.I31_NUM u31 | REF.STRUCT_ADDR structaddr
    | REF.ARRAY_ADDR arrayaddr | REF.FUNC_ADDR funcaddr | REF.EXN_ADDR exnaddr
    | REF.HOST_ADDR hostaddr | REF.EXTERN addrref`. -/
inductive AddrRef where
  | i31 (i : U31)
  | structAddr (a : StructAddr)
  | arrayAddr (a : ArrayAddr)
  | funcAddr (a : FuncAddr)
  | exnAddr (a : ExnAddr)
  | hostAddr (a : HostAddr)
  | extern (r : AddrRef)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax ref = addrref | REF.NULL heaptype`. -/
inductive Ref where
  | addr (r : AddrRef)
  | null (ht : HeapType)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax val = num | vec | ref`. -/
inductive Val where
  | num (n : NumVal)
  | vec (v : VecVal)
  | ref (r : Ref)

/-- `syntax result = _VALS val* | `(REF.EXN_ADDR exnaddr) THROW_REF | TRAP`. -/
inductive Result where
  | vals (vs : List Val)
  | throwRef (a : ExnAddr)
  | trap

/-! ## Instances -/

/-- `syntax hostfunc = ...`: opaque in the pinned source.  See the header. -/
abbrev HostFunc : Type := Nat

/-- `syntax funccode = func | hostfunc`. -/
inductive FuncCode where
  | func (f : Func)
  | host (h : HostFunc)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax taginst = { TYPE tagtype }`. -/
structure TagInst where
  type : TagType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax globalinst = { TYPE globaltype, VALUE val }`. -/
structure GlobalInst where
  type : GlobalType
  value : Val

/-- `syntax meminst = { TYPE memtype, BYTES byte* }`. -/
structure MemInst where
  type : MemType
  bytes : List Byte
  deriving DecidableEq, Repr, Inhabited

/-- `syntax tableinst = { TYPE tabletype, REFS ref* }`. -/
structure TableInst where
  type : TableType
  refs : List Ref
  deriving DecidableEq, Repr, Inhabited

/-- `syntax datainst = { BYTES byte* }`. -/
structure DataInst where
  bytes : List Byte
  deriving DecidableEq, Repr, Inhabited

/-- `syntax eleminst = { TYPE elemtype, REFS ref* }`. -/
structure ElemInst where
  type : ElemType
  refs : List Ref
  deriving DecidableEq, Repr, Inhabited

/-- `syntax exportinst = { NAME name, ADDR externaddr }`. -/
structure ExportInst where
  name : Name
  addr : ExternAddr
  deriving DecidableEq, Repr, Inhabited

/-- `syntax packval = PACK packtype iN($psizenn(packtype))`. -/
structure PackVal where
  pt : PackType
  c : IN pt.size

/-- `syntax fieldval = val | packval`. -/
inductive FieldVal where
  | val (v : Val)
  | pack (p : PackVal)

/-- `syntax moduleinst = { TYPES deftype*, TAGS tagaddr*, GLOBALS globaladdr*,
    MEMS memaddr*, TABLES tableaddr*, FUNCS funcaddr*, DATAS dataaddr*,
    ELEMS elemaddr*, EXPORTS exportinst* }`. -/
structure ModuleInst where
  types : List DefType := []
  tags : List TagAddr := []
  globals : List GlobalAddr := []
  mems : List MemAddr := []
  tables : List TableAddr := []
  funcs : List FuncAddr := []
  datas : List DataAddr := []
  elems : List ElemAddr := []
  exports : List ExportInst := []
  deriving DecidableEq, Repr, Inhabited

/-- `syntax funcinst = { TYPE deftype, MODULE moduleinst, CODE funccode }`. -/
structure FuncInst where
  type : DefType
  mod : ModuleInst
  code : FuncCode
  deriving DecidableEq, Repr, Inhabited

/-- `syntax structinst = { TYPE deftype, FIELDS fieldval* }`. -/
structure StructInst where
  type : DefType
  fields : List FieldVal

/-- `syntax arrayinst = { TYPE deftype, FIELDS fieldval* }`. -/
structure ArrayInst where
  type : DefType
  fields : List FieldVal

/-- `syntax exninst = { TAG tagaddr, FIELDS val* }`. -/
structure ExnInst where
  tag : TagAddr
  fields : List Val

/-! ## State -/

/-- `syntax store = { TAGS taginst*, GLOBALS globalinst*, MEMS meminst*,
    TABLES tableinst*, FUNCS funcinst*, DATAS datainst*, ELEMS eleminst*,
    STRUCTS structinst*, ARRAYS arrayinst*, EXNS exninst* }`. -/
structure Store where
  tags : List TagInst := []
  globals : List GlobalInst := []
  mems : List MemInst := []
  tables : List TableInst := []
  funcs : List FuncInst := []
  datas : List DataInst := []
  elems : List ElemInst := []
  structs : List StructInst := []
  arrays : List ArrayInst := []
  exns : List ExnInst := []

/-- `syntax frame = { LOCALS (val?)*, MODULE moduleinst }`. -/
structure Frame where
  locals : List (Option Val) := []
  mod : ModuleInst := {}

/-! ## Administrative instructions

`syntax instr/admin = ... | addrref | LABEL_ n `{instr*} instr*
    | FRAME_ n `{frame} instr* | HANDLER_ n `{catch*} instr* | TRAP`. -/

/-- `instr/admin`: a syntactic instruction or one of the five administrative
forms `4.0` adds. -/
inductive AdminInstr where
  /-- A syntactic instruction of `1.3`. -/
  | plain (i : Instr)
  /-- `addrref`. -/
  | addrref (r : AddrRef)
  /-- ``LABEL_ n `{instr*} instr*``. -/
  | label (n : Nat) (cont : List AdminInstr) (body : List AdminInstr)
  /-- ``FRAME_ n `{frame} instr*``. -/
  | frame (n : Nat) (f : Frame) (body : List AdminInstr)
  /-- ``HANDLER_ n `{catch*} instr*``. -/
  | handler (n : Nat) (cs : List Catch) (body : List AdminInstr)
  /-- `TRAP`. -/
  | trap

instance : Inhabited AdminInstr := ⟨.trap⟩

/-- `val` read as an administrative instruction, i.e. the coercion the source
leaves implicit when it writes `val*` inside `instr*`. -/
def Val.toAdmin : Val → AdminInstr
  | .num n => .plain (.const n.nt n.c)
  | .vec v => .plain (.vconst v.vt v.c)
  | .ref (.null ht) => .plain (.refNull ht)
  | .ref (.addr r) => .addrref r

/-- `val*` read as `instr*`. -/
def vals (vs : List Val) : List AdminInstr := vs.map Val.toAdmin

/-- `ref` read as an administrative instruction. -/
def Ref.toAdmin (r : Ref) : AdminInstr := Val.toAdmin (.ref r)

/-- `syntax state = store; frame`. -/
structure State where
  store : Store
  frame : Frame

/-- `syntax config = state; instr*`. -/
abbrev Config : Type := State × List AdminInstr

/-! ## Constants -/

/-- `def $Ki = 1024`. -/
def Ki : Nat := 1024

/-! ## Packed fields -/

namespace Numerics

variable (N : Numerics)

/-- `def $packfield_(valtype, val) = val`,
`def $packfield_(packtype, CONST I32 i) = PACK packtype $wrap__(32, $psize(packtype), i)`.

The second equation applies only to an `I32` constant, which is what the source
writes; on any other value at a `packtype` the source gives no equation. -/
def packfield_ : StorageType → Val → Option FieldVal
  | .val _, v => some (.val v)
  | .pack pt, .num ⟨.i32, i⟩ => some (.pack ⟨pt, N.wrap__ 32 pt.size i⟩)
  | .pack _, _ => none

/-- `def $unpackfield_(valtype, eps, val) = val`,
`def $unpackfield_(packtype, sx, PACK packtype i) = CONST I32 $extend__($psize(packtype), 32, sx, i)`. -/
def unpackfield_ : StorageType → Option Sx → FieldVal → Option Val
  | .val _, none, .val v => some v
  | .pack pt, some sx, .pack p =>
      if h : p.pt = pt then
        some (.num ⟨.i32, N.extend__ pt.size 32 sx (h ▸ p.c)⟩)
      else none
  | _, _, _ => none

end Numerics

/-! ## Address filtering

`def $tagsxa`, `$globalsxa`, `$memsxa`, `$tablesxa`, `$funcsxa`. -/

/-- `def $tagsxa(externaddr*) : tagaddr*`. -/
def tagsxa : List ExternAddr → List TagAddr
  | [] => []
  | .tag a :: xs => a :: tagsxa xs
  | _ :: xs => tagsxa xs

/-- `def $globalsxa(externaddr*) : globaladdr*`. -/
def globalsxa : List ExternAddr → List GlobalAddr
  | [] => []
  | .global a :: xs => a :: globalsxa xs
  | _ :: xs => globalsxa xs

/-- `def $memsxa(externaddr*) : memaddr*`. -/
def memsxa : List ExternAddr → List MemAddr
  | [] => []
  | .mem a :: xs => a :: memsxa xs
  | _ :: xs => memsxa xs

/-- `def $tablesxa(externaddr*) : tableaddr*`. -/
def tablesxa : List ExternAddr → List TableAddr
  | [] => []
  | .table a :: xs => a :: tablesxa xs
  | _ :: xs => tablesxa xs

/-- `def $funcsxa(externaddr*) : funcaddr*`. -/
def funcsxa : List ExternAddr → List FuncAddr
  | [] => []
  | .func a :: xs => a :: funcsxa xs
  | _ :: xs => funcsxa xs

/-! ## State access -/

namespace State

variable (z : State)

/-- `def $moduleinst((s; f)) = f.MODULE`. -/
def moduleinst : ModuleInst := z.frame.mod
/-- `def $tagaddr((s; f)) = f.MODULE.TAGS`. -/
def tagaddr : List TagAddr := z.frame.mod.tags
/-- `def $taginst((s; f)) = s.TAGS`. -/
def taginst : List TagInst := z.store.tags
/-- `def $globalinst((s; f)) = s.GLOBALS`. -/
def globalinst : List GlobalInst := z.store.globals
/-- `def $meminst((s; f)) = s.MEMS`. -/
def meminst : List MemInst := z.store.mems
/-- `def $tableinst((s; f)) = s.TABLES`. -/
def tableinst : List TableInst := z.store.tables
/-- `def $funcinst((s; f)) = s.FUNCS`. -/
def funcinst : List FuncInst := z.store.funcs
/-- `def $datainst((s; f)) = s.DATAS`. -/
def datainst : List DataInst := z.store.datas
/-- `def $eleminst((s; f)) = s.ELEMS`. -/
def eleminst : List ElemInst := z.store.elems
/-- `def $structinst((s; f)) = s.STRUCTS`. -/
def structinst : List StructInst := z.store.structs
/-- `def $arrayinst((s; f)) = s.ARRAYS`. -/
def arrayinst : List ArrayInst := z.store.arrays
/-- `def $exninst((s; f)) = s.EXNS`. -/
def exninst : List ExnInst := z.store.exns

/-- `def $type((s; f), x) = f.MODULE.TYPES[x]`. -/
def typeOf (x : TypeIdx) : Option DefType := z.frame.mod.types[x.val]?
/-- `def $tag((s; f), x) = s.TAGS[f.MODULE.TAGS[x]]`. -/
def tagOf (x : TagIdx) : Option TagInst :=
  z.frame.mod.tags[x.val]?.bind fun a => z.store.tags[a]?
/-- `def $global((s; f), x) = s.GLOBALS[f.MODULE.GLOBALS[x]]`. -/
def globalOf (x : GlobalIdx) : Option GlobalInst :=
  z.frame.mod.globals[x.val]?.bind fun a => z.store.globals[a]?
/-- `def $mem((s; f), x) = s.MEMS[f.MODULE.MEMS[x]]`. -/
def memOf (x : MemIdx) : Option MemInst :=
  z.frame.mod.mems[x.val]?.bind fun a => z.store.mems[a]?
/-- `def $table((s; f), x) = s.TABLES[f.MODULE.TABLES[x]]`. -/
def tableOf (x : TableIdx) : Option TableInst :=
  z.frame.mod.tables[x.val]?.bind fun a => z.store.tables[a]?
/-- `def $func((s; f), x) = s.FUNCS[f.MODULE.FUNCS[x]]`. -/
def funcOf (x : FuncIdx) : Option FuncInst :=
  z.frame.mod.funcs[x.val]?.bind fun a => z.store.funcs[a]?
/-- `def $data((s; f), x) = s.DATAS[f.MODULE.DATAS[x]]`. -/
def dataOf (x : DataIdx) : Option DataInst :=
  z.frame.mod.datas[x.val]?.bind fun a => z.store.datas[a]?
/-- `def $elem((s; f), x) = s.ELEMS[f.MODULE.ELEMS[x]]`. -/
def elemOf (x : ElemIdx) : Option ElemInst :=
  z.frame.mod.elems[x.val]?.bind fun a => z.store.elems[a]?
/-- `def $local((s; f), x) = f.LOCALS[x]`.  Doubly partial: the slot may be out of
range, and an in-range slot may be uninitialised. -/
def localOf (x : LocalIdx) : Option (Option Val) := z.frame.locals[x.val]?

/-! ## State update -/

/-- `def $with_local((s; f), x, v) = s; f[.LOCALS[x] = v]`. -/
def withLocal (x : LocalIdx) (v : Val) : Option State :=
  (setAt? z.frame.locals x.val (some v)).map fun ls =>
    { z with frame := { z.frame with locals := ls } }

/-- `def $with_global((s; f), x, v) = s[.GLOBALS[f.MODULE.GLOBALS[x]].VALUE = v]; f`. -/
def withGlobal (x : GlobalIdx) (v : Val) : Option State := do
  let a ← z.frame.mod.globals[x.val]?
  let gi ← z.store.globals[a]?
  let gs ← setAt? z.store.globals a { gi with value := v }
  pure { z with store := { z.store with globals := gs } }

/-- `def $with_table((s; f), x, i, r) = s[.TABLES[f.MODULE.TABLES[x]].REFS[i] = r]; f`. -/
def withTable (x : TableIdx) (i : Nat) (r : Ref) : Option State := do
  let a ← z.frame.mod.tables[x.val]?
  let ti ← z.store.tables[a]?
  let rs ← setAt? ti.refs i r
  let ts ← setAt? z.store.tables a { ti with refs := rs }
  pure { z with store := { z.store with tables := ts } }

/-- `def $with_tableinst((s; f), x, ti) = s[.TABLES[f.MODULE.TABLES[x]] = ti]; f`. -/
def withTableInst (x : TableIdx) (ti : TableInst) : Option State := do
  let a ← z.frame.mod.tables[x.val]?
  let ts ← setAt? z.store.tables a ti
  pure { z with store := { z.store with tables := ts } }

/-- `def $with_mem((s; f), x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] = b*]; f`. -/
def withMem (x : MemIdx) (i j : Nat) (bs : List Byte) : Option State := do
  let a ← z.frame.mod.mems[x.val]?
  let mi ← z.store.mems[a]?
  let bs' ← spliceAt? mi.bytes i j bs
  let ms ← setAt? z.store.mems a { mi with bytes := bs' }
  pure { z with store := { z.store with mems := ms } }

/-- `def $with_meminst((s; f), x, mi) = s[.MEMS[f.MODULE.MEMS[x]] = mi]; f`. -/
def withMemInst (x : MemIdx) (mi : MemInst) : Option State := do
  let a ← z.frame.mod.mems[x.val]?
  let ms ← setAt? z.store.mems a mi
  pure { z with store := { z.store with mems := ms } }

/-- `def $with_elem((s; f), x, r*) = s[.ELEMS[f.MODULE.ELEMS[x]].REFS = r*]; f`. -/
def withElem (x : ElemIdx) (rs : List Ref) : Option State := do
  let a ← z.frame.mod.elems[x.val]?
  let ei ← z.store.elems[a]?
  let es ← setAt? z.store.elems a { ei with refs := rs }
  pure { z with store := { z.store with elems := es } }

/-- `def $with_data((s; f), x, b*) = s[.DATAS[f.MODULE.DATAS[x]].BYTES = b*]; f`. -/
def withData (x : DataIdx) (bs : List Byte) : Option State := do
  let a ← z.frame.mod.datas[x.val]?
  let di ← z.store.datas[a]?
  let ds ← setAt? z.store.datas a { di with bytes := bs }
  pure { z with store := { z.store with datas := ds } }

/-- `def $with_struct((s; f), a, i, fv) = s[.STRUCTS[a].FIELDS[i] = fv]; f`. -/
def withStruct (a : StructAddr) (i : Nat) (fv : FieldVal) : Option State := do
  let si ← z.store.structs[a]?
  let fs ← setAt? si.fields i fv
  let ss ← setAt? z.store.structs a { si with fields := fs }
  pure { z with store := { z.store with structs := ss } }

/-- `def $with_array((s; f), a, i, fv) = s[.ARRAYS[a].FIELDS[i] = fv]; f`. -/
def withArray (a : ArrayAddr) (i : Nat) (fv : FieldVal) : Option State := do
  let ai ← z.store.arrays[a]?
  let fs ← setAt? ai.fields i fv
  let as' ← setAt? z.store.arrays a { ai with fields := fs }
  pure { z with store := { z.store with arrays := as' } }

/-- `def $add_structinst((s; f), si*) = s[.STRUCTS =++ si*]; f`. -/
def addStructInst (sis : List StructInst) : State :=
  { z with store := { z.store with structs := z.store.structs ++ sis } }

/-- `def $add_arrayinst((s; f), ai*) = s[.ARRAYS =++ ai*]; f`. -/
def addArrayInst (ais : List ArrayInst) : State :=
  { z with store := { z.store with arrays := z.store.arrays ++ ais } }

/-- `def $add_exninst((s; f), exn*) = s[.EXNS =++ exn*]; f`. -/
def addExnInst (exs : List ExnInst) : State :=
  { z with store := { z.store with exns := z.store.exns ++ exs } }

end State

/-! ## Growing -/

/-- `def $growtable(tableinst, n, r) = tableinst'` with
`tableinst' = { TYPE (at `[i' .. j?] rt), REFS r'* r^n }`, `i' = |r'*| + n`, and
`(if i' <= j)?`.  The source marks it `hint(partial)`. -/
def growTable (ti : TableInst) (n : Nat) (r : Ref) : Option TableInst :=
  let i' := ti.refs.length + n
  if h : i' < 2 ^ 64 then
    let ok : Bool := match ti.type.lim.max with
      | some j => decide (i' ≤ j.val)
      | none => true
    if ok then
      some { ti with
        type := { ti.type with lim := { ti.type.lim with min := ⟨i', h⟩ } },
        refs := ti.refs ++ List.replicate n r }
    else none
  else none

/-- `def $growmem(meminst, n) = meminst'` with
`meminst' = { TYPE (at `[i' .. j?] PAGE), BYTES b* (0x00)^(n * 64 * $Ki) }`,
`i' = |b*| / (64 * $Ki) + n`, and `(if i' <= j)?`. -/
def growMem (mi : MemInst) (n : Nat) : Option MemInst :=
  let i' := mi.bytes.length / (64 * Ki) + n
  if h : i' < 2 ^ 64 then
    let ok : Bool := match mi.type.lim.max with
      | some j => decide (i' ≤ j.val)
      | none => true
    if ok then
      some { mi with
        type := { mi.type with lim := { mi.type.lim with min := ⟨i', h⟩ } },
        bytes := mi.bytes ++ List.replicate (n * (64 * Ki)) ⟨0, by decide⟩ }
    else none
  else none

/-! ## Default values

`4.1-execution.values.spectec`. -/

/-- `def $default_(Inn) = (CONST Inn 0)`, `def $default_(Fnn) = (CONST Fnn $fzero)`,
`def $default_(Vnn) = (VCONST Vnn 0)`, `def $default_(REF NULL ht) = (REF.NULL ht)`,
`def $default_(REF ht) = eps`. -/
def default_ : ValType → Option Val
  | .num .i32 => some (.num ⟨.i32, ⟨0, two_pow_pos 32⟩⟩)
  | .num .i64 => some (.num ⟨.i64, ⟨0, two_pow_pos 64⟩⟩)
  | .num .f32 => some (.num ⟨.f32, .pos (.subnorm 0)⟩)
  | .num .f64 => some (.num ⟨.f64, .pos (.subnorm 0)⟩)
  | .vec .v128 => some (.vec ⟨.v128, ⟨0, two_pow_pos 128⟩⟩)
  | .ref (.ref (some .null) ht) => some (.ref (.null ht))
  | .ref (.ref none _) => none
  | .bot => none

/-- `relation Defaultable: |- valtype DEFAULTABLE`. -/
inductive Defaultable : ValType → Prop where
  /-- `rule Defaultable: |- t DEFAULTABLE  -- if $default_(t) =/= eps`. -/
  -- core-exec: Defaultable
  | mk {t : ValType} : default_ t ≠ none → Defaultable t

/-- `relation Nondefaultable: |- valtype NONDEFAULTABLE`. -/
inductive Nondefaultable : ValType → Prop where
  /-- `rule Nondefaultable: |- t NONDEFAULTABLE  -- if $default_(t) = eps`. -/
  -- core-exec: Nondefaultable
  | mk {t : ValType} : default_ t = none → Nondefaultable t

/-! ## Runtime typing of values

`relation Num_ok`, `Vec_ok`, `Ref_ok`, `Val_ok` of `4.1`.  The subtyping premises
are selected from the byte-identical transcription in `Validation/Types.lean`
or its exact AMD-011 repair in `Validation/SubtypingAmended.lean`, at the empty
context `{}` the source writes. -/

/-- `relation Num_ok: store |- num : numtype`. -/
inductive Num_ok : Store → NumVal → NumType → Prop where
  /-- `rule Num_ok: s |- CONST nt c : nt`. -/
  -- core-exec: Num_ok
  | mk {s : Store} {nt : NumType} {c : Num_ nt} : Num_ok s ⟨nt, c⟩ nt

/-- `relation Vec_ok: store |- vec : vectype`. -/
inductive Vec_ok : Store → VecVal → VecType → Prop where
  /-- `rule Vec_ok: s |- VCONST vt c : vt`. -/
  -- core-exec: Vec_ok
  | mk {s : Store} {vt : VecType} {c : VecLit vt.toVnn} : Vec_ok s ⟨vt, c⟩ vt

variable [authority : ExecutionAuthority]

/-- `relation Ref_ok: store |- ref : reftype`, under the selected authority. -/
inductive Ref_ok : Store → Ref → RefType → Prop where
  /-- `rule Ref_ok/null: s |- REF.NULL ht : (REF NULL ht')
      -- Heaptype_sub: {} |- ht' <: ht`. -/
  -- core-exec: Ref_ok/null
  | null {s : Store} {ht ht' : HeapType} :
      HeaptypeSubFor Context.empty ht' ht →
      Ref_ok s (.null ht) (.ref (some .null) ht')
  /-- `rule Ref_ok/i31: s |- REF.I31_NUM i : (REF I31)`. -/
  -- core-exec: Ref_ok/i31
  | i31 {s : Store} {i : U31} :
      Ref_ok s (.addr (.i31 i)) (.ref none (.abs .i31))
  /-- `rule Ref_ok/struct: s |- REF.STRUCT_ADDR a : (REF dt)
      -- if s.STRUCTS[a].TYPE = dt`. -/
  -- core-exec: Ref_ok/struct
  | «struct» {s : Store} {a : StructAddr} {si : StructInst} {dt : DefType} :
      s.structs[a]? = some si → si.type = dt →
      Ref_ok s (.addr (.structAddr a)) (.ref none (.use (.defd dt)))
  /-- `rule Ref_ok/array: s |- REF.ARRAY_ADDR a : (REF dt)
      -- if s.ARRAYS[a].TYPE = dt`. -/
  -- core-exec: Ref_ok/array
  | array {s : Store} {a : ArrayAddr} {ai : ArrayInst} {dt : DefType} :
      s.arrays[a]? = some ai → ai.type = dt →
      Ref_ok s (.addr (.arrayAddr a)) (.ref none (.use (.defd dt)))
  /-- `rule Ref_ok/func: s |- REF.FUNC_ADDR a : (REF dt)
      -- if s.FUNCS[a].TYPE = dt`. -/
  -- core-exec: Ref_ok/func
  | func {s : Store} {a : FuncAddr} {fi : FuncInst} {dt : DefType} :
      s.funcs[a]? = some fi → fi.type = dt →
      Ref_ok s (.addr (.funcAddr a)) (.ref none (.use (.defd dt)))
  /-- `rule Ref_ok/exn: s |- REF.EXN_ADDR a : (REF EXN)  -- if s.EXNS[a] = exn`. -/
  -- core-exec: Ref_ok/exn
  | exn {s : Store} {a : ExnAddr} {ex : ExnInst} :
      s.exns[a]? = some ex →
      Ref_ok s (.addr (.exnAddr a)) (.ref none (.abs .exn))
  /-- `rule Ref_ok/host: s |- REF.HOST_ADDR a : (REF ANY)`. -/
  -- core-exec: Ref_ok/host
  | host {s : Store} {a : HostAddr} :
      Ref_ok s (.addr (.hostAddr a)) (.ref none (.abs .any))
  /-- `rule Ref_ok/extern: s |- REF.EXTERN addrref : (REF EXTERN)
      -- Ref_ok: s |- addrref : (REF ANY)`. -/
  -- core-exec: Ref_ok/extern
  | «extern» {s : Store} {r : AddrRef} :
      Ref_ok s (.addr r) (.ref none (.abs .any)) →
      Ref_ok s (.addr (.extern r)) (.ref none (.abs .extern))
  /-- `rule Ref_ok/sub: s |- ref : rt  -- Ref_ok: s |- ref : rt'
      -- Reftype_sub: {} |- rt' <: rt`. -/
  -- core-exec: Ref_ok/sub
  | sub {s : Store} {r : Ref} {rt rt' : RefType} :
      Ref_ok s r rt' → ReftypeSubFor Context.empty rt' rt → Ref_ok s r rt

/-- `relation Val_ok: store |- val : valtype`. -/
inductive Val_ok : Store → Val → ValType → Prop where
  /-- `rule Val_ok/num: s |- num : nt  -- Num_ok: s |- num : nt`. -/
  -- core-exec: Val_ok/num
  | num {s : Store} {n : NumVal} {nt : NumType} :
      Num_ok s n nt → Val_ok s (.num n) (.num nt)
  /-- `rule Val_ok/vec: s |- vec : vt  -- Vec_ok: s |- vec : vt`. -/
  -- core-exec: Val_ok/vec
  | vec {s : Store} {v : VecVal} {vt : VecType} :
      Vec_ok s v vt → Val_ok s (.vec v) (.vec vt)
  /-- `rule Val_ok/ref: s |- ref : rt  -- Ref_ok: s |- ref : rt`. -/
  -- core-exec: Val_ok/ref
  | ref {s : Store} {r : Ref} {rt : RefType} :
      Ref_ok s r rt → Val_ok s (.ref r) (.ref rt)

/-- `relation Externaddr_ok: store |- externaddr : externtype`. -/
inductive Externaddr_ok : Store → ExternAddr → ExternType → Prop where
  /-- `rule Externaddr_ok/tag: s |- TAG a : TAG taginst.TYPE
      -- if s.TAGS[a] = taginst`. -/
  -- core-exec: Externaddr_ok/tag
  | tag {s : Store} {a : TagAddr} {ti : TagInst} :
      s.tags[a]? = some ti → Externaddr_ok s (.tag a) (.tag ti.type)
  /-- `rule Externaddr_ok/global: s |- GLOBAL a : GLOBAL globalinst.TYPE
      -- if s.GLOBALS[a] = globalinst`. -/
  -- core-exec: Externaddr_ok/global
  | global {s : Store} {a : GlobalAddr} {gi : GlobalInst} :
      s.globals[a]? = some gi → Externaddr_ok s (.global a) (.global gi.type)
  /-- `rule Externaddr_ok/mem: s |- MEM a : MEM meminst.TYPE
      -- if s.MEMS[a] = meminst`. -/
  -- core-exec: Externaddr_ok/mem
  | mem {s : Store} {a : MemAddr} {mi : MemInst} :
      s.mems[a]? = some mi → Externaddr_ok s (.mem a) (.mem mi.type)
  /-- `rule Externaddr_ok/table: s |- TABLE a : TABLE tableinst.TYPE
      -- if s.TABLES[a] = tableinst`. -/
  -- core-exec: Externaddr_ok/table
  | table {s : Store} {a : TableAddr} {ti : TableInst} :
      s.tables[a]? = some ti → Externaddr_ok s (.table a) (.table ti.type)
  /-- `rule Externaddr_ok/func: s |- FUNC a : FUNC funcinst.TYPE
      -- if s.FUNCS[a] = funcinst`. -/
  -- core-exec: Externaddr_ok/func
  | func {s : Store} {a : FuncAddr} {fi : FuncInst} :
      s.funcs[a]? = some fi → Externaddr_ok s (.func a) (.func (.defd fi.type))
  /-- `rule Externaddr_ok/sub: s |- externaddr : xt
      -- Externaddr_ok: s |- externaddr : xt'
      -- Externtype_sub: {} |- xt' <: xt`. -/
  -- core-exec: Externaddr_ok/sub
  | sub {s : Store} {xa : ExternAddr} {xt xt' : ExternType} :
      Externaddr_ok s xa xt' → ExterntypeSubFor Context.empty xt' xt →
      Externaddr_ok s xa xt

/-- The explicit byte-identical pinned runtime reference-typing relation. -/
abbrev Ref_okPinned := @Ref_ok pinnedExecutionAuthority

/-- The exact AMD-011 runtime reference-typing relation. -/
abbrev Ref_okA := @Ref_ok amendedExecutionAuthority

/-- The explicit byte-identical pinned runtime value-typing relation. -/
abbrev Val_okPinned := @Val_ok pinnedExecutionAuthority

/-- The exact AMD-011 runtime value-typing relation. -/
abbrev Val_okA := @Val_ok amendedExecutionAuthority

/-- The explicit byte-identical pinned external-address typing relation. -/
abbrev Externaddr_okPinned := @Externaddr_ok pinnedExecutionAuthority

/-- The exact AMD-011 external-address typing relation. -/
abbrev Externaddr_okA := @Externaddr_ok amendedExecutionAuthority

/-! ## Coverage-neutral inclusion

The amended runtime relations only remove the bad AMD-011 bottom-collapse
derivations.  Every amended derivation therefore remains a derivation of the
byte-identical pinned transcription.
-/

def Ref_okA.to_pinned {s : Store} {r : Ref} {rt : RefType}
    (h : Ref_okA s r rt) : Ref_okPinned s r rt := by
  letI : ExecutionAuthority := pinnedExecutionAuthority
  induction h with
  | null hs => exact .null hs.to_pinned
  | i31 => exact .i31
  | «struct» h₁ h₂ => exact .struct h₁ h₂
  | array h₁ h₂ => exact .array h₁ h₂
  | func h₁ h₂ => exact .func h₁ h₂
  | exn h => exact .exn h
  | host => exact .host
  | «extern» _ ih => exact .extern ih
  | sub _ hs ih => exact .sub ih hs.to_pinned

def Val_okA.to_pinned {s : Store} {v : Val} {t : ValType}
    (h : Val_okA s v t) : Val_okPinned s v t := by
  letI : ExecutionAuthority := pinnedExecutionAuthority
  cases h with
  | num h => exact .num h
  | vec h => exact .vec h
  | ref h => exact .ref (Ref_okA.to_pinned h)

def Externaddr_okA.to_pinned {s : Store} {xa : ExternAddr} {xt : ExternType}
    (h : Externaddr_okA s xa xt) : Externaddr_okPinned s xa xt := by
  letI : ExecutionAuthority := pinnedExecutionAuthority
  induction h with
  | tag h => exact .tag h
  | global h => exact .global h
  | mem h => exact .mem h
  | table h => exact .table h
  | func h => exact .func h
  | sub _ hs ih => exact .sub ih hs.to_pinned

/-! ## Type instantiation

`4.2-execution.types.spectec`. -/

/-- `def $inst_valtype(moduleinst, t) = $subst_all_valtype(t, dt*)
    -- if dt* = moduleinst.TYPES`. -/
def instValType (mm : ModuleInst) (t : ValType) : ValType :=
  substAllValType t (mm.types.map TypeUse.defd)

/-- `def $inst_reftype(moduleinst, rt) = $subst_all_reftype(rt, dt*)`. -/
def instRefType (mm : ModuleInst) (rt : RefType) : RefType :=
  substAllRefType rt (mm.types.map TypeUse.defd)

/-- `def $inst_globaltype(moduleinst, gt) = $subst_all_globaltype(gt, dt*)`. -/
def instGlobalType (mm : ModuleInst) (gt : GlobalType) : GlobalType :=
  substAllGlobalType gt (mm.types.map TypeUse.defd)

/-- `def $inst_memtype(moduleinst, mt) = $subst_all_memtype(mt, dt*)`. -/
def instMemType (mm : ModuleInst) (mt : MemType) : MemType :=
  substAllMemType mt (mm.types.map TypeUse.defd)

/-- `def $inst_tabletype(moduleinst, tt) = $subst_all_tabletype(tt, dt*)`. -/
def instTableType (mm : ModuleInst) (tt : TableType) : TableType :=
  substAllTableType tt (mm.types.map TypeUse.defd)

end WasmGemmGnaf.Wasm.Core.Exec
