/-
  Wasm/Core/Validation/Modules.lean --- the declarative validation judgment on
  MODULES of the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every constructor below transcribes one `rule` of

      vendor/wasm-spec/specification/wasm-3.0/2.4-validation.modules.spectec

  at the pinned commit, one Lean constructor per SpecTec rule, carrying that
  rule's premises as hypotheses and nothing else.

  ORDER.  The source declares `Types_ok` and `Globals_ok` next to `Module_ok`
  and gives their rules after it.  Lean needs a relation to exist before it is
  used, so the two auxiliary relations are declared just before `Module_ok`
  here; nothing else is reordered.

  WHAT `Module_ok` PINS DOWN, and why each part matters:

  * EXPORT-NAME UNIQUENESS.  `-- if $disjoint_(name, nm*)`, transcribed as
    `disjoint nms = true` over the exported names.  An external audit named
    export validity specifically.
  * EXPORT-INDEX VALIDITY.  `Externidx_ok` requires the index each export names
    to be in range in the component it selects, and `Export_ok` requires
    `Externidx_ok`.
  * THE `REFS` COMPONENT.  `x* = $funcidx_nonfuncs(global* mem* table* elem*)`
    fixes exactly which function indices `Instr_ok/ref.func` may take.  It is
    computed by `Core/Free.lean`; without it the rule would have to leave `REFS`
    free, which would let `REF.FUNC` name any declared function.
  * THE TWO-STAGE CONTEXT.  `C'` (types, imported globals, all functions,
    refs) types tags, globals, memories and tables; the full `C` types
    functions, data, elements, the start function and the exports.  The
    staging is what stops a global initialiser from reading a later global.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Instructions
import WasmGemmGnaf.Wasm.Core.Free

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- `def $funcsxt(externtype*) : deftype*`.

`Core/Types.lean` transcribes this as `ExternType.funcs`, returning the
`typeuse*` the syntax layer stores.  The source's equation matches the `FUNC`
payload as a `deftype`, so read at its declared result sort the function is
PARTIAL: it is undefined on an import whose function type is written as a type
index rather than a defined type.  `Module_ok` needs the `deftype*` reading,
because `C.FUNCS` is a `deftype*`. -/
def funcsXt : List ExternType → Option (List DefType)
  | [] => some []
  | .func tu :: xs =>
      match asDefType tu, funcsXt xs with
      | some dt, some rest => some (dt :: rest)
      | _, _ => none
  | _ :: xs => funcsXt xs

/-! ## Definitions -/

/-- The mathematical base index `|C.TYPES|` and every occupied member of a
source recursive type group fit exactly in the 32-bit type-index sort.  The
base conjunct is needed even for an empty group, whose rule still names `x`.
This makes the source equation `x = |C.TYPES|` faithful in Lean rather than
silently interpreting it modulo `2^32`. -/
def TypeGroupRangeOk (C : Context) (td : TypeDef) : Prop :=
  C.types.length < 2 ^ 32 ∧
  C.types.length + td.rectype.count ≤ 2 ^ 32

instance (C : Context) (td : TypeDef) : Decidable (TypeGroupRangeOk C td) := by
  unfold TypeGroupRangeOk
  infer_instance

/-- `relation Type_ok: context |- type : deftype*`. -/
inductive Type_ok : Context → TypeDef → List DefType → Prop where
  /-- `rule Type_ok:
        C |- TYPE rectype : dt*
        -- if x = |C.TYPES|
        -- if dt* = $rolldt(x, rectype)
        -- Rectype_ok: C ++ {TYPES dt*} |- rectype : OK(x)`. -/
  -- core-rule: Type_ok
  | mk {C : Context} {td : TypeDef} {dts : List DefType} {x : TypeIdx} :
      TypeGroupRangeOk C td →
      x.val = C.types.length →
      dts = rollDt x td.rectype →
      Rectype_ok (Context.append C { types := dts }) td.rectype x →
      Type_ok C td dts

/-- `relation Tag_ok: context |- tag : tagtype`. -/
inductive Tag_ok : Context → Tag → TagType → Prop where
  /-- `rule Tag_ok: C |- TAG tagtype : $clos_tagtype(C, tagtype)
      -- Tagtype_ok: C |- tagtype : OK`. -/
  -- core-rule: Tag_ok
  | mk {C : Context} {tg : Tag} :
      Tagtype_ok C tg.tagtype → Tag_ok C tg (C.closTagType tg.tagtype)

/-- `relation Global_ok: context |- global : globaltype`. -/
inductive Global_ok : Context → Global → GlobalType → Prop where
  /-- `rule Global_ok:
        C |- GLOBAL globaltype expr : globaltype
        -- Globaltype_ok: C |- globaltype : OK
        -- if globaltype = MUT? t
        -- Expr_ok_const: C |- expr : t CONST`. -/
  -- core-rule: Global_ok
  | mk {C : Context} {g : Global} :
      Globaltype_ok C g.globaltype →
      Expr_ok_const C g.init g.globaltype.valtype →
      Global_ok C g g.globaltype

/-- `relation Mem_ok: context |- mem : memtype`. -/
inductive Mem_ok : Context → Mem → MemType → Prop where
  /-- `rule Mem_ok: C |- MEMORY memtype : memtype -- Memtype_ok: C |- memtype : OK`. -/
  -- core-rule: Mem_ok
  | mk {C : Context} {m : Mem} : Memtype_ok C m.memtype → Mem_ok C m m.memtype

/-- `relation Table_ok: context |- table : tabletype`. -/
inductive Table_ok : Context → Table → TableType → Prop where
  /-- `rule Table_ok:
        C |- TABLE tabletype expr : tabletype
        -- Tabletype_ok: C |- tabletype : OK
        -- if tabletype = at lim rt
        -- Expr_ok_const: C |- expr : rt CONST`. -/
  -- core-rule: Table_ok
  | mk {C : Context} {t : Table} :
      Tabletype_ok C t.tabletype →
      Expr_ok_const C t.init (.ref t.tabletype.elem) →
      Table_ok C t t.tabletype

/-- `relation Local_ok: context |- local : localtype`. -/
inductive Local_ok : Context → Local → LocalType → Prop where
  /-- `rule Local_ok/set: C |- LOCAL t : SET t -- Defaultable: |- t DEFAULTABLE`. -/
  -- core-rule: Local_ok/set
  | set {C : Context} {l : Local} :
      Defaultable l.valtype → Local_ok C l ⟨.set, l.valtype⟩
  /-- `rule Local_ok/unset: C |- LOCAL t : UNSET t
      -- Nondefaultable: |- t NONDEFAULTABLE`. -/
  -- core-rule: Local_ok/unset
  | unset {C : Context} {l : Local} :
      Nondefaultable l.valtype → Local_ok C l ⟨.unset, l.valtype⟩

/-- `relation Func_ok: context |- func : deftype`. -/
inductive Func_ok : Context → Func → DefType → Prop where
  /-- `rule Func_ok:
        C |- FUNC x local* expr : C.TYPES[x]
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*
        -- (Local_ok: C |- local : lct)*
        -- Expr_ok: C ++ {LOCALS (SET t_1)* lct*, LABELS (t_2*), RETURN (t_2*)}
                     |- expr : t_2*`. -/
  -- core-rule: Func_ok
  | mk {C : Context} {f : Func} {dt : DefType} {dom cod : ValTypes}
      {lcts : List LocalType} :
      C.types[f.typeidx.val]? = some dt →
      Expand dt (.func dom cod) →
      SeqLen₂ f.locals lcts →
      SeqAll₂ (Local_ok C) f.locals lcts →
      Expr_ok (Context.append C
          { locals := (ValTypes.toList dom).map (fun t => ⟨.set, t⟩) ++ lcts,
            labels := [ValTypes.toList cod],
            ret := some (ValTypes.toList cod) })
        f.body (ValTypes.toList cod) →
      Func_ok C f dt

/-- `relation Datamode_ok: context |- datamode : datatype`. -/
inductive Datamode_ok : Context → DataMode → DataType → Prop where
  /-- `rule Datamode_ok/passive: C |- PASSIVE : OK`. -/
  -- core-rule: Datamode_ok/passive
  | passive {C : Context} : Datamode_ok C .passive .ok
  /-- `rule Datamode_ok/active:
        C |- ACTIVE x expr : OK
        -- if C.MEMS[x] = at lim PAGE
        -- Expr_ok_const: C |- expr : at CONST`. -/
  -- core-rule: Datamode_ok/active
  | active {C : Context} {x : MemIdx} {e : Expr} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Expr_ok_const C e mt.addr.toValType →
      Datamode_ok C (.active x e) .ok

/-- `relation Elemmode_ok: context |- elemmode : elemtype`. -/
inductive Elemmode_ok : Context → ElemMode → ElemType → Prop where
  /-- `rule Elemmode_ok/passive: C |- PASSIVE : rt`. -/
  -- core-rule: Elemmode_ok/passive
  | passive {C : Context} {rt : ElemType} : Elemmode_ok C .passive rt
  /-- `rule Elemmode_ok/declare: C |- DECLARE : rt`. -/
  -- core-rule: Elemmode_ok/declare
  | declare {C : Context} {rt : ElemType} : Elemmode_ok C .declare rt
  /-- `rule Elemmode_ok/active:
        C |- ACTIVE x expr : rt
        -- if C.TABLES[x] = at lim rt'
        -- Reftype_sub: C |- rt <: rt'
        -- Expr_ok_const: C |- expr : at CONST`. -/
  -- core-rule: Elemmode_ok/active
  | active {C : Context} {x : TableIdx} {e : Expr} {tt : TableType} {rt : ElemType} :
      C.tables[x.val]? = some tt →
      Reftype_sub C rt tt.elem →
      Expr_ok_const C e tt.addr.toValType →
      Elemmode_ok C (.active x e) rt

/-- `relation Data_ok: context |- data : datatype`. -/
inductive Data_ok : Context → Data → DataType → Prop where
  /-- `rule Data_ok: C |- DATA b* datamode : OK
      -- Datamode_ok: C |- datamode : OK`. -/
  -- core-rule: Data_ok
  | mk {C : Context} {d : Data} : Datamode_ok C d.mode .ok → Data_ok C d .ok

/-- `relation Elem_ok: context |- elem : elemtype`. -/
inductive Elem_ok : Context → Elem → ElemType → Prop where
  /-- `rule Elem_ok:
        C |- ELEM elemtype expr* elemmode : elemtype
        -- Reftype_ok: C |- elemtype : OK
        -- (Expr_ok_const: C |- expr : elemtype CONST)*
        -- Elemmode_ok: C |- elemmode : elemtype`. -/
  -- core-rule: Elem_ok
  | mk {C : Context} {e : Elem} :
      Reftype_ok C e.reftype →
      SeqAll (fun (ex : Expr) => Expr_ok_const C ex (.ref e.reftype)) e.init →
      Elemmode_ok C e.mode e.reftype →
      Elem_ok C e e.reftype

/-- `relation Start_ok: context |- start : OK`. -/
inductive Start_ok : Context → Start → Prop where
  /-- `rule Start_ok: C |- START x : OK -- Expand: C.FUNCS[x] ~~ FUNC eps -> eps`. -/
  -- core-rule: Start_ok
  | mk {C : Context} {s : Start} {dt : DefType} :
      C.funcs[s.funcidx.val]? = some dt →
      Expand dt (.func .nil .nil) →
      Start_ok C s

/-! ## Im/exports -/

/-- `relation Externidx_ok: context |- externidx : externtype`. -/
inductive Externidx_ok : Context → ExternIdx → ExternType → Prop where
  /-- `rule Externidx_ok/tag: C |- TAG x : TAG jt -- if C.TAGS[x] = jt`. -/
  -- core-rule: Externidx_ok/tag
  | tag {C : Context} {x : TagIdx} {jt : TagType} :
      C.tags[x.val]? = some jt → Externidx_ok C (.tag x) (.tag jt)
  /-- `rule Externidx_ok/global: C |- GLOBAL x : GLOBAL gt -- if C.GLOBALS[x] = gt`. -/
  -- core-rule: Externidx_ok/global
  | global {C : Context} {x : GlobalIdx} {gt : GlobalType} :
      C.globals[x.val]? = some gt → Externidx_ok C (.global x) (.global gt)
  /-- `rule Externidx_ok/mem: C |- MEM x : MEM mt -- if C.MEMS[x] = mt`. -/
  -- core-rule: Externidx_ok/mem
  | mem {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt → Externidx_ok C (.mem x) (.mem mt)
  /-- `rule Externidx_ok/table: C |- TABLE x : TABLE tt -- if C.TABLES[x] = tt`. -/
  -- core-rule: Externidx_ok/table
  | table {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt → Externidx_ok C (.table x) (.table tt)
  /-- `rule Externidx_ok/func: C |- FUNC x : FUNC dt -- if C.FUNCS[x] = dt`. -/
  -- core-rule: Externidx_ok/func
  | func {C : Context} {x : FuncIdx} {dt : DefType} :
      C.funcs[x.val]? = some dt → Externidx_ok C (.func x) (.func (.defd dt))

/-- `relation Import_ok: context |- import : externtype`. -/
inductive Import_ok : Context → Import → ExternType → Prop where
  /-- `rule Import_ok: C |- IMPORT name_1 name_2 xt : $clos_externtype(C, xt)
      -- Externtype_ok: C |- xt : OK`. -/
  -- core-rule: Import_ok
  | mk {C : Context} {i : Import} :
      Externtype_ok C i.externtype → Import_ok C i (C.closExternType i.externtype)

/-- `relation Export_ok: context |- export : name externtype`. -/
inductive Export_ok : Context → Export → Name → ExternType → Prop where
  /-- `rule Export_ok: C |- EXPORT name externidx : name xt
      -- Externidx_ok: C |- externidx : xt`. -/
  -- core-rule: Export_ok
  | mk {C : Context} {e : Export} {xt : ExternType} :
      Externidx_ok C e.externidx xt → Export_ok C e e.name xt

/-! ## Modules -/

/-- `relation Types_ok: context |- type* : deftype*`. -/
inductive Types_ok : Context → List TypeDef → List DefType → Prop where
  /-- `rule Types_ok/empty: C |- eps : eps`. -/
  -- core-rule: Types_ok/empty
  | empty {C : Context} : Types_ok C [] []
  /-- `rule Types_ok/cons:
        C |- type_1 type* : dt_1* dt*
        -- Type_ok: C |- type_1 : dt_1*
        -- Types_ok: C ++ {TYPES dt_1*} |- type* : dt*`. -/
  -- core-rule: Types_ok/cons
  | cons {C : Context} {td : TypeDef} {tds : List TypeDef}
      {dts₁ dts : List DefType} :
      Type_ok C td dts₁ →
      Types_ok (Context.append C { types := dts₁ }) tds dts →
      Types_ok C (td :: tds) (dts₁ ++ dts)

/-- `relation Globals_ok: context |- global* : globaltype*`. -/
inductive Globals_ok : Context → List Global → List GlobalType → Prop where
  /-- `rule Globals_ok/empty: C |- eps : eps`. -/
  -- core-rule: Globals_ok/empty
  | empty {C : Context} : Globals_ok C [] []
  /-- `rule Globals_ok/cons:
        C |- global_1 global* : gt_1 gt*
        -- Global_ok: C |- global_1 : gt_1
        -- Globals_ok: C ++ {GLOBALS gt_1} |- global* : gt*`. -/
  -- core-rule: Globals_ok/cons
  | cons {C : Context} {g : Global} {gs : List Global}
      {gt₁ : GlobalType} {gts : List GlobalType} :
      Global_ok C g gt₁ →
      Globals_ok (Context.append C { globals := [gt₁] }) gs gts →
      Globals_ok C (g :: gs) (gt₁ :: gts)

/-- `relation Module_ok: |- module : moduletype`. -/
inductive Module_ok : Module → ModuleType → Prop where
  /-- `rule Module_ok:
        |- MODULE type* import* tag* global* mem* table* func* data* elem* start* export*
           : $clos_moduletype(C, xt_I* -> xt_E*)
        -- Types_ok: {} |- type* : dt'*
        -- (Import_ok: {TYPES dt'*} |- import : xt_I)*
        -- (Tag_ok: C' |- tag : jt)*
        -- Globals_ok: C' |- global* : gt*
        -- (Mem_ok: C' |- mem : mt)*
        -- (Table_ok: C' |- table : tt)*
        -- (Func_ok: C |- func : dt)*
        -- (Data_ok: C |- data : ok)*
        -- (Elem_ok: C |- elem : rt)*
        -- (Start_ok: C |- start : OK)?
        -- (Export_ok: C |- export : nm xt_E)*
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
  `C'` mentions the `dt*` that `Func_ok` derives under `C`); they are
  existentials here, exactly as SpecTec's free metavariables are. -/
  -- core-rule: Module_ok
  | mk {m : Module} {C C' : Context}
      {dts' : List DefType} {xtsI xtsE : List ExternType}
      {jts : List TagType} {gts : List GlobalType} {mts : List MemType}
      {tts : List TableType} {dts : List DefType} {oks : List DataType}
      {rts : List ElemType} {nms : List Name}
      {jtsI : List TagType} {gtsI : List GlobalType} {mtsI : List MemType}
      {ttsI : List TableType} {dtsI : List DefType} {xs : List FuncIdx} :
      Types_ok Context.empty m.types dts' →
      SeqLen₂ m.imports xtsI →
      SeqAll₂ (Import_ok { Context.empty with types := dts' }) m.imports xtsI →
      SeqLen₂ m.tags jts →
      SeqAll₂ (Tag_ok C') m.tags jts →
      Globals_ok C' m.globals gts →
      SeqLen₂ m.mems mts →
      SeqAll₂ (Mem_ok C') m.mems mts →
      SeqLen₂ m.tables tts →
      SeqAll₂ (Table_ok C') m.tables tts →
      SeqLen₂ m.funcs dts →
      SeqAll₂ (Func_ok C) m.funcs dts →
      SeqLen₂ m.datas oks →
      SeqAll₂ (Data_ok C) m.datas oks →
      SeqLen₂ m.elems rts →
      SeqAll₂ (Elem_ok C) m.elems rts →
      OptAll (Start_ok C) m.start →
      SeqLen₃ m.exports nms xtsE →
      SeqAll₃ (Export_ok C) m.exports nms xtsE →
      disjoint nms = true →
      C = Context.append C'
        { tags := jtsI ++ jts, globals := gts, mems := mtsI ++ mts,
          tables := ttsI ++ tts, datas := oks, elems := rts } →
      C' = { types := dts', globals := gtsI, funcs := dtsI ++ dts, refs := xs } →
      xs = funcidxNonfuncs m.globals m.mems m.tables m.elems →
      jtsI = ExternType.tags xtsI →
      gtsI = ExternType.globals xtsI →
      mtsI = ExternType.mems xtsI →
      ttsI = ExternType.tables xtsI →
      funcsXt xtsI = some dtsI →
      Module_ok m (C.closModuleType ⟨xtsI, xtsE⟩)

/-! ## The instruction side conditions reach the module level

`Instr_ok` now carries the membership condition of every indexed operator and
shape it mentions, and `Instr_ok.wf_of` turns that into: a typable instruction
satisfies every `-- if` the pinned syntax fragments carry.  The module rules
reach the instruction judgment only through `Expr_ok`, so the same holds of
every expression of every module `Module_ok` accepts --- the initialisers, the
offsets and the function bodies alike.  That is what the theorems below say, and
it is the statement the width defect was about: the accepted set is Core's, not
a superset of it.

What they do NOT say is anything about the `/syn` phase invariant.  The pinned
validation admits `BOT` outright (`rule Valtype_ok/bot`), so `Module_ok` cannot
imply `Module.isSyn` and does not carry it as a premise: adding one would make
the judgment NARROWER than Core's, which is the same kind of error in the other
direction.  The phase invariant belongs to the module SORT, and lives in
`Core/Modules.lean` as `Module.isSyn`. -/

/-- From a lockstep `(...)* ` premise together with the length agreement it
comes with: every member of the left sequence is related to SOME member of the
right one.  `SeqAll₂` is indexed rather than membership-based, for the
strict-positivity reason given in `Core/Context.lean`. -/
private theorem seqAll₂_mem {α β : Type} {R : α → β → Prop}
    {as : List α} {bs : List β} (hlen : SeqLen₂ as bs) (h : SeqAll₂ R as bs) :
    ∀ a ∈ as, ∃ b, R a b := by
  intro a ha
  rcases List.mem_iff_getElem.mp ha with ⟨i, hi, rfl⟩
  have hb : i < bs.length := by omega
  exact ⟨bs[i], h i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hb)⟩

/-- A validated global's initialiser satisfies every instruction side
condition. -/
theorem Global_ok.wf_of {C : Context} {g : Global} {gt : GlobalType}
    (h : Global_ok C g gt) : Global.wf g = true := by
  cases h with
  | mk _ hc => cases hc with | mk he _ => exact Expr_ok.wf_of he

/-- ... and so does a validated table's. -/
theorem Table_ok.wf_of {C : Context} {t : Table} {tt : TableType}
    (h : Table_ok C t tt) : Table.wf t = true := by
  cases h with
  | mk _ hc => cases hc with | mk he _ => exact Expr_ok.wf_of he

/-- ... and a validated function's body. -/
theorem Func_ok.wf_of {C : Context} {f : Func} {dt : DefType}
    (h : Func_ok C f dt) : Func.wf f = true := by
  cases h with
  | mk _ _ _ _ he => exact Expr_ok.wf_of he

/-- ... and the offset expression of a validated `datamode`. -/
theorem Datamode_ok.wf_of {C : Context} {dm : DataMode} {dt : DataType}
    (h : Datamode_ok C dm dt) : DataMode.wf dm = true := by
  cases h with
  | passive => rfl
  | active _ hc => cases hc with | mk he _ => exact Expr_ok.wf_of he

/-- ... hence of a validated data segment. -/
theorem Data_ok.wf_of {C : Context} {d : Data} {dt : DataType}
    (h : Data_ok C d dt) : Data.wf d = true := by
  cases h with
  | mk h => exact Datamode_ok.wf_of h

/-- ... and the offset expression of a validated `elemmode`. -/
theorem Elemmode_ok.wf_of {C : Context} {em : ElemMode} {rt : ElemType}
    (h : Elemmode_ok C em rt) : ElemMode.wf em = true := by
  cases h with
  | passive => rfl
  | declare => rfl
  | active _ _ hc => cases hc with | mk he _ => exact Expr_ok.wf_of he

/-- ... hence of a validated element segment, initialisers included. -/
theorem Elem_ok.wf_of {C : Context} {e : Elem} {rt : ElemType}
    (h : Elem_ok C e rt) : Elem.wf e = true := by
  cases h with
  | mk _ hinit hmode =>
      have h₁ : e.init.all InstrSeq.wf = true :=
        List.all_eq_true.mpr (fun ex hex => by
          cases hinit ex hex with | mk he _ => exact Expr_ok.wf_of he)
      simp [Elem.wf, h₁, Elemmode_ok.wf_of hmode]

/-- ... and of every global in a validated global section. -/
theorem Globals_ok.wf_of {C : Context} {gs : List Global} {gts : List GlobalType}
    (h : Globals_ok C gs gts) : gs.all Global.wf = true := by
  induction h with
  | empty => rfl
  | cons hg _ ih => simp [Global_ok.wf_of hg, ih]

/-- EVERY expression of a validated module is an expression of Core 3.0: no
instruction in it is outside the operator family, shape or width its own form
requires.  This is the module-level form of `Instr_ok.wf_of`, and it is the
property a validator that admitted `F32.CLZ` would not have. -/
theorem Module_ok.exprs_wf {m : Module} {mt : ModuleType} (h : Module_ok m mt) :
    (m.globals.all Global.wf && m.tables.all Table.wf && m.funcs.all Func.wf &&
      m.datas.all Data.wf && m.elems.all Elem.wf) = true := by
  cases h with
  | mk _ _ _ _ _ hg _ _ hlt htt hlf hf hld hd hle he _ _ _ _ _ _ _ _ _ _ _ _ =>
      have hglob : m.globals.all Global.wf = true := Globals_ok.wf_of hg
      have htab : m.tables.all Table.wf = true :=
        List.all_eq_true.mpr (fun t ht => by
          rcases seqAll₂_mem hlt htt t ht with ⟨_, hok⟩
          exact Table_ok.wf_of hok)
      have hfun : m.funcs.all Func.wf = true :=
        List.all_eq_true.mpr (fun f hfm => by
          rcases seqAll₂_mem hlf hf f hfm with ⟨_, hok⟩
          exact Func_ok.wf_of hok)
      have hdat : m.datas.all Data.wf = true :=
        List.all_eq_true.mpr (fun d hdm => by
          rcases seqAll₂_mem hld hd d hdm with ⟨_, hok⟩
          exact Data_ok.wf_of hok)
      have hele : m.elems.all Elem.wf = true :=
        List.all_eq_true.mpr (fun e hem => by
          rcases seqAll₂_mem hle he e hem with ⟨_, hok⟩
          exact Elem_ok.wf_of hok)
      simp [hglob, htab, hfun, hdat, hele]

/-! ## Sanity checks

Kernel-checked derivations, not tests. -/

/-- A `(...)* ` premise over two empty sequences. -/
private theorem seq_all₂_nil' {α β : Type} {R : α → β → Prop} : SeqAll₂ R [] [] :=
  fun _ _ _ h _ => by simp at h

/-- A `(...)* ` premise over three empty sequences. -/
private theorem seq_all₃_nil' {α β γ : Type} {R : α → β → γ → Prop} :
    SeqAll₃ R [] [] [] := fun _ _ _ _ h _ _ => by simp at h

/-- The module type `Module_ok` assigns the empty module reduces to
`eps -> eps`; `$clos_moduletype` over an empty type section is the identity. -/
example : Context.empty.closModuleType (⟨[], []⟩ : ModuleType) = ⟨[], []⟩ := rfl

/-- The empty module validates.  This is the end-to-end check that `Module_ok`
is inhabited at all --- every one of its twenty-eight premises has to be
discharged, including `$disjoint_` on the exported names and the `REFS`
equation that `$funcidx_nonfuncs` computes. -/
example :
    Module_ok
      { types := [], imports := [], tags := [], globals := [], mems := [],
        tables := [], funcs := [], datas := [], elems := [], start := none,
        exports := [] }
      (Context.empty.closModuleType ⟨[], []⟩) := by
  refine Module_ok.mk (C := Context.empty) (C' := Context.empty)
    (dts' := []) (xtsI := []) (xtsE := []) (jts := []) (gts := []) (mts := [])
    (tts := []) (dts := []) (oks := []) (rts := []) (nms := [])
    (jtsI := []) (gtsI := []) (mtsI := []) (ttsI := []) (dtsI := []) (xs := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
      | exact Types_ok.empty
      | exact Globals_ok.empty
      | exact seq_all₂_nil'
      | exact seq_all₃_nil'
      | exact (fun _ h => nomatch h)
      | exact ⟨rfl, rfl⟩
      | rfl

end WasmGemmGnaf.Wasm.Core
