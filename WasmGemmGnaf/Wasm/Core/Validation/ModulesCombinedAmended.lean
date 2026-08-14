/-
  Coverage-neutral combined module-validation amendment.

  All module judgments route through the combined instruction and corrected
  type hierarchy.  The module context uses AMD-009 amended free-index traversal.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Modules
import WasmGemmGnaf.Wasm.Core.Validation.InstructionsCombinedAmended
import WasmGemmGnaf.Wasm.Core.FreeAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

inductive Type_okA : Context → TypeDef → List DefType → Prop where
  /-- `rule Type_okA:
        C |- TYPE rectype : dt*
        -- if x = |C.TYPES|
        -- if dt* = $rolldt(x, rectype)
        -- Rectype_okA: C ++ {TYPES dt*} |- rectype : OK(x)`. -/
  | mk {C : Context} {td : TypeDef} {dts : List DefType} {x : TypeIdx} :
      TypeGroupRangeOk C td →
      x.val = C.types.length →
      dts = rollDt x td.rectype →
      Rectype_okA (Context.append C { types := dts }) td.rectype x →
      Type_okA C td dts

/-- `relation Tag_okA: context |- tag : tagtype`. -/
inductive Tag_okA : Context → Tag → TagType → Prop where
  /-- `rule Tag_okA: C |- TAG tagtype : $clos_tagtype(C, tagtype)
      -- Tagtype_okA: C |- tagtype : OK`. -/
  | mk {C : Context} {tg : Tag} :
      Tagtype_okA C tg.tagtype → Tag_okA C tg (C.closTagType tg.tagtype)

/-- `relation Global_okA: context |- global : globaltype`. -/
inductive Global_okA : Context → Global → GlobalType → Prop where
  /-- `rule Global_okA:
        C |- GLOBAL globaltype expr : globaltype
        -- Globaltype_okA: C |- globaltype : OK
        -- if globaltype = MUT? t
        -- Expr_ok_constA: C |- expr : t CONST`. -/
  | mk {C : Context} {g : Global} :
      Globaltype_okA C g.globaltype →
      Expr_ok_constA C g.init g.globaltype.valtype →
      Global_okA C g g.globaltype

/-- `relation Mem_okA: context |- mem : memtype`. -/
inductive Mem_okA : Context → Mem → MemType → Prop where
  /-- `rule Mem_okA: C |- MEMORY memtype : memtype -- Memtype_ok: C |- memtype : OK`. -/
  | mk {C : Context} {m : Mem} : Memtype_ok C m.memtype → Mem_okA C m m.memtype

/-- `relation Table_okA: context |- table : tabletype`. -/
inductive Table_okA : Context → Table → TableType → Prop where
  /-- `rule Table_okA:
        C |- TABLE tabletype expr : tabletype
        -- Tabletype_okA: C |- tabletype : OK
        -- if tabletype = at lim rt
        -- Expr_ok_constA: C |- expr : rt CONST`. -/
  | mk {C : Context} {t : Table} :
      Tabletype_okA C t.tabletype →
      Expr_ok_constA C t.init (.ref t.tabletype.elem) →
      Table_okA C t t.tabletype

/-- `relation Local_okA: context |- local : localtype`. -/
inductive Local_okA : Context → Local → LocalType → Prop where
  /-- `rule Local_okA/set: C |- LOCAL t : SET t -- Defaultable: |- t DEFAULTABLE`. -/
  | set {C : Context} {l : Local} :
      Defaultable l.valtype → Local_okA C l ⟨.set, l.valtype⟩
  /-- `rule Local_okA/unset: C |- LOCAL t : UNSET t
      -- Nondefaultable: |- t NONDEFAULTABLE`. -/
  | unset {C : Context} {l : Local} :
      Nondefaultable l.valtype → Local_okA C l ⟨.unset, l.valtype⟩

/-- `relation Func_okA: context |- func : deftype`. -/
inductive Func_okA : Context → Func → DefType → Prop where
  /-- `rule Func_okA:
        C |- FUNC x local* expr : C.TYPES[x]
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*
        -- (Local_okA: C |- local : lct)*
        -- Expr_okA: C ++ {LOCALS (SET t_1)* lct*, LABELS (t_2*), RETURN (t_2*)}
                     |- expr : t_2*`. -/
  | mk {C : Context} {f : Func} {dt : DefType} {dom cod : ValTypes}
      {lcts : List LocalType} :
      C.types[f.typeidx.val]? = some dt →
      Expand dt (.func dom cod) →
      SeqLen₂ f.locals lcts →
      SeqAll₂ (Local_okA C) f.locals lcts →
      Expr_okA (Context.append C
          { locals := (ValTypes.toList dom).map (fun t => ⟨.set, t⟩) ++ lcts,
            labels := [ValTypes.toList cod],
            ret := some (ValTypes.toList cod) })
        f.body (ValTypes.toList cod) →
      Func_okA C f dt

/-- `relation Datamode_okA: context |- datamode : datatype`. -/
inductive Datamode_okA : Context → DataMode → DataType → Prop where
  /-- `rule Datamode_okA/passive: C |- PASSIVE : OK`. -/
  | passive {C : Context} : Datamode_okA C .passive .ok
  /-- `rule Datamode_okA/active:
        C |- ACTIVE x expr : OK
        -- if C.MEMS[x] = at lim PAGE
        -- Expr_ok_constA: C |- expr : at CONST`. -/
  | active {C : Context} {x : MemIdx} {e : Expr} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Expr_ok_constA C e mt.addr.toValType →
      Datamode_okA C (.active x e) .ok

/-- `relation Elemmode_okA: context |- elemmode : elemtype`. -/
inductive Elemmode_okA : Context → ElemMode → ElemType → Prop where
  /-- `rule Elemmode_okA/passive: C |- PASSIVE : rt`. -/
  | passive {C : Context} {rt : ElemType} : Elemmode_okA C .passive rt
  /-- `rule Elemmode_okA/declare: C |- DECLARE : rt`. -/
  | declare {C : Context} {rt : ElemType} : Elemmode_okA C .declare rt
  /-- `rule Elemmode_okA/active:
        C |- ACTIVE x expr : rt
        -- if C.TABLES[x] = at lim rt'
        -- Reftype_subA: C |- rt <: rt'
        -- Expr_ok_constA: C |- expr : at CONST`. -/
  | active {C : Context} {x : TableIdx} {e : Expr} {tt : TableType} {rt : ElemType} :
      C.tables[x.val]? = some tt →
      Reftype_subA C rt tt.elem →
      Expr_ok_constA C e tt.addr.toValType →
      Elemmode_okA C (.active x e) rt

/-- `relation Data_okA: context |- data : datatype`. -/
inductive Data_okA : Context → Data → DataType → Prop where
  /-- `rule Data_okA: C |- DATA b* datamode : OK
      -- Datamode_okA: C |- datamode : OK`. -/
  | mk {C : Context} {d : Data} : Datamode_okA C d.mode .ok → Data_okA C d .ok

/-- `relation Elem_okA: context |- elem : elemtype`. -/
inductive Elem_okA : Context → Elem → ElemType → Prop where
  /-- `rule Elem_okA:
        C |- ELEM elemtype expr* elemmode : elemtype
        -- Reftype_okA: C |- elemtype : OK
        -- (Expr_ok_constA: C |- expr : elemtype CONST)*
        -- Elemmode_okA: C |- elemmode : elemtype`. -/
  | mk {C : Context} {e : Elem} :
      Reftype_okA C e.reftype →
      SeqAll (fun (ex : Expr) => Expr_ok_constA C ex (.ref e.reftype)) e.init →
      Elemmode_okA C e.mode e.reftype →
      Elem_okA C e e.reftype

/-- `relation Start_okA: context |- start : OK`. -/
inductive Start_okA : Context → Start → Prop where
  /-- `rule Start_okA: C |- START x : OK -- Expand: C.FUNCS[x] ~~ FUNC eps -> eps`. -/
  | mk {C : Context} {s : Start} {dt : DefType} :
      C.funcs[s.funcidx.val]? = some dt →
      Expand dt (.func .nil .nil) →
      Start_okA C s

/-! ## Im/exports -/

/-- `relation Externidx_okA: context |- externidx : externtype`. -/
inductive Externidx_okA : Context → ExternIdx → ExternType → Prop where
  /-- `rule Externidx_okA/tag: C |- TAG x : TAG jt -- if C.TAGS[x] = jt`. -/
  | tag {C : Context} {x : TagIdx} {jt : TagType} :
      C.tags[x.val]? = some jt → Externidx_okA C (.tag x) (.tag jt)
  /-- `rule Externidx_okA/global: C |- GLOBAL x : GLOBAL gt -- if C.GLOBALS[x] = gt`. -/
  | global {C : Context} {x : GlobalIdx} {gt : GlobalType} :
      C.globals[x.val]? = some gt → Externidx_okA C (.global x) (.global gt)
  /-- `rule Externidx_okA/mem: C |- MEM x : MEM mt -- if C.MEMS[x] = mt`. -/
  | mem {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt → Externidx_okA C (.mem x) (.mem mt)
  /-- `rule Externidx_okA/table: C |- TABLE x : TABLE tt -- if C.TABLES[x] = tt`. -/
  | table {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt → Externidx_okA C (.table x) (.table tt)
  /-- `rule Externidx_okA/func: C |- FUNC x : FUNC dt -- if C.FUNCS[x] = dt`. -/
  | func {C : Context} {x : FuncIdx} {dt : DefType} :
      C.funcs[x.val]? = some dt → Externidx_okA C (.func x) (.func (.defd dt))

/-- `relation Import_okA: context |- import : externtype`. -/
inductive Import_okA : Context → Import → ExternType → Prop where
  /-- `rule Import_okA: C |- IMPORT name_1 name_2 xt : $clos_externtype(C, xt)
      -- Externtype_okA: C |- xt : OK`. -/
  | mk {C : Context} {i : Import} :
      Externtype_okA C i.externtype → Import_okA C i (C.closExternType i.externtype)

/-- `relation Export_okA: context |- export : name externtype`. -/
inductive Export_okA : Context → Export → Name → ExternType → Prop where
  /-- `rule Export_okA: C |- EXPORT name externidx : name xt
      -- Externidx_okA: C |- externidx : xt`. -/
  | mk {C : Context} {e : Export} {xt : ExternType} :
      Externidx_okA C e.externidx xt → Export_okA C e e.name xt

/-! ## Modules -/

/-- `relation Types_okA: context |- type* : deftype*`. -/
inductive Types_okA : Context → List TypeDef → List DefType → Prop where
  /-- `rule Types_okA/empty: C |- eps : eps`. -/
  | empty {C : Context} : Types_okA C [] []
  /-- `rule Types_okA/cons:
        C |- type_1 type* : dt_1* dt*
        -- Type_okA: C |- type_1 : dt_1*
        -- Types_okA: C ++ {TYPES dt_1*} |- type* : dt*`. -/
  | cons {C : Context} {td : TypeDef} {tds : List TypeDef}
      {dts₁ dts : List DefType} :
      Type_okA C td dts₁ →
      Types_okA (Context.append C { types := dts₁ }) tds dts →
      Types_okA C (td :: tds) (dts₁ ++ dts)

/-- `relation Globals_okA: context |- global* : globaltype*`. -/
inductive Globals_okA : Context → List Global → List GlobalType → Prop where
  /-- `rule Globals_okA/empty: C |- eps : eps`. -/
  | empty {C : Context} : Globals_okA C [] []
  /-- `rule Globals_okA/cons:
        C |- global_1 global* : gt_1 gt*
        -- Global_okA: C |- global_1 : gt_1
        -- Globals_okA: C ++ {GLOBALS gt_1} |- global* : gt*`. -/
  | cons {C : Context} {g : Global} {gs : List Global}
      {gt₁ : GlobalType} {gts : List GlobalType} :
      Global_okA C g gt₁ →
      Globals_okA (Context.append C { globals := [gt₁] }) gs gts →
      Globals_okA C (g :: gs) (gt₁ :: gts)

/-- `relation Module_okA: |- module : moduletype`. -/
inductive Module_okA : Module → ModuleType → Prop where
  /-- `rule Module_okA:
        |- MODULE type* import* tag* global* mem* table* func* data* elem* start* export*
           : $clos_moduletype(C, xt_I* -> xt_E*)
        -- Types_okA: {} |- type* : dt'*
        -- (Import_okA: {TYPES dt'*} |- import : xt_I)*
        -- (Tag_okA: C' |- tag : jt)*
        -- Globals_okA: C' |- global* : gt*
        -- (Mem_okA: C' |- mem : mt)*
        -- (Table_okA: C' |- table : tt)*
        -- (Func_okA: C |- func : dt)*
        -- (Data_okA: C |- data : ok)*
        -- (Elem_okA: C |- elem : rt)*
        -- (Start_okA: C |- start : OK)?
        -- (Export_okA: C |- export : nm xt_E)*
        -- if $disjoint_(name, nm*)
        -- if C = C' ++ {TAGS jt_I* jt*, GLOBALS gt*, MEMS mt_I* mt*,
                        TABLES tt_I* tt*, DATAS ok*, ELEMS rt*}
        -- if C' = {TYPES dt'*, GLOBALS gt_I*, FUNCS dt_I* dt*, REFS x*}
        -- if x* = $funcidx_nonfuncs(global* mem* table* elem*)
        -- if jt_I* = $tagsxt(xt_I*)
        -- if gt_I* = $globalsxt(xt_I*)
        -- if mt_I* = $memsxt(xt_I*)
        -- if tt_I* = $tablesxt(xt_I*)
        -- if dt_I* = $funcsxt(xt_I*)`

  `C` and `C'` are mutually constrained in the source (`C` extends `C'`, and
  `C'` mentions the `dt*` that `Func_okA` derives under `C`); they are
  existentials here, exactly as SpecTec's free metavariables are. -/
  | mk {m : Module} {C C' : Context}
      {dts' : List DefType} {xtsI xtsE : List ExternType}
      {jts : List TagType} {gts : List GlobalType} {mts : List MemType}
      {tts : List TableType} {dts : List DefType} {oks : List DataType}
      {rts : List ElemType} {nms : List Name}
      {jtsI : List TagType} {gtsI : List GlobalType} {mtsI : List MemType}
      {ttsI : List TableType} {dtsI : List DefType} {xs : List FuncIdx} :
      Types_okA Context.empty m.types dts' →
      SeqLen₂ m.imports xtsI →
      SeqAll₂ (Import_okA { Context.empty with types := dts' }) m.imports xtsI →
      SeqLen₂ m.tags jts →
      SeqAll₂ (Tag_okA C') m.tags jts →
      Globals_okA C' m.globals gts →
      SeqLen₂ m.mems mts →
      SeqAll₂ (Mem_okA C') m.mems mts →
      SeqLen₂ m.tables tts →
      SeqAll₂ (Table_okA C') m.tables tts →
      SeqLen₂ m.funcs dts →
      SeqAll₂ (Func_okA C) m.funcs dts →
      SeqLen₂ m.datas oks →
      SeqAll₂ (Data_okA C) m.datas oks →
      SeqLen₂ m.elems rts →
      SeqAll₂ (Elem_okA C) m.elems rts →
      OptAll (Start_okA C) m.start →
      SeqLen₃ m.exports nms xtsE →
      SeqAll₃ (Export_okA C) m.exports nms xtsE →
      disjoint nms = true →
      C = Context.append C'
        { tags := jtsI ++ jts, globals := gts, mems := mtsI ++ mts,
          tables := ttsI ++ tts, datas := oks, elems := rts } →
      C' = { types := dts', globals := gtsI, funcs := dtsI ++ dts, refs := xs } →
      xs = funcidxNonfuncs' m.globals m.mems m.tables m.elems →
      jtsI = ExternType.tags xtsI →
      gtsI = ExternType.globals xtsI →
      mtsI = ExternType.mems xtsI →
      ttsI = ExternType.tables xtsI →
      funcsXt xtsI = some dtsI →
      Module_okA m (C.closModuleType ⟨xtsI, xtsE⟩)

/-! ## AMD-005 function-level non-vacuity -/

/-- The defined function type used by the smallest pinned sequencing-gap
witness. -/
def gapDefType : DefType :=
  .defd (.recr (.cons (.sub (some .final) .nil
    (.func .nil (ValTypes.ofList [ValType.i32]))) .nil)) 0

/-- A context containing only `gapDefType`. -/
def gapContext : Context := { Context.empty with types := [gapDefType] }

/-- `(func (result i32) i32.const 0; i32.const 0; i32.add)`. -/
def gapFunc : Func :=
  { typeidx := TypeIdx.ofNat 0, locals := [],
    body := InstrSeq.ofList
      [Instr.const .i32 default, Instr.const .i32 default,
       Instr.binop .i32 (.int .add)] }

/-- The combined corrected hierarchy types the function that the pinned
sequencing rule cannot type. -/
theorem Func_okA.gapFunc : Func_okA gapContext gapFunc gapDefType := by
  refine .mk (dom := .nil) (cod := ValTypes.ofList [ValType.i32]) (lcts := [])
    rfl (.mk rfl) rfl (fun _ _ _ h _ => nomatch h) ?_
  refine .mk ?_
  simp only [ValTypes.toList_ofList]
  exact Instrs_okA.const_const_binop rfl

end WasmGemmGnaf.Wasm.Core
