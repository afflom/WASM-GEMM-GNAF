/-
  Wasm/Core/Instantiation.lean --- allocation, instantiation and invocation of
  the pinned WebAssembly Core 3.0 semantics.

  NORMATIVE SOURCE.  Every declaration below transcribes a definition of

      vendor/wasm-spec/specification/wasm-3.0/4.4-execution.modules.spectec

  at the pinned commit.

  NO COVERAGE MARKERS.  `4.4` states no `rule`; it is entirely `def`.  `xtask core`
  extracts its checklist from `rule` lines, so this file discharges no checklist
  item and carries no marker.  It is here because `$instantiate` and `$invoke` are
  what turn the step relation of `4.3` into statements about real runs: without
  them a progress or preservation theorem is an invariant with nothing anchoring
  it to a module that was actually loaded.

  FUNCTIONS AND RELATIONS.  The pure allocation definitions are functions.
  `$allocmodule`, `$evalglobals`, `$instantiate` and `$invoke` carry premises that
  are themselves relations (`Module_ok`, `Externaddr_ok`, `Eval_expr`, `Expand`,
  `Val_ok`), so they are transcribed as inductive relations with one constructor
  carrying exactly the source's premises.  A relation is also the honest reading
  of `$instantiate`: `$evalglobals` invokes `Eval_expr`, which is `~>*`, and `~>*`
  is not a function.

  PARTIALITY.  `$allocexport` indexes a module instance and `$rundata_` /
  `$runelem_` emit `(CONST I32 n)` for a segment length `n`; both are `Option`
  here, defined exactly where the source's equation applies.
-/
import WasmGemmGnaf.Wasm.Core.Execution
import WasmGemmGnaf.Wasm.Core.Validation.Modules

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- `u32` from a natural, defined exactly on the range `u32` has. -/
def u32? (n : Nat) : Option U32 := if h : n < 2 ^ 32 then some ⟨n, h⟩ else none

/-- `u64` from a natural, defined exactly on the range `u64` has. -/
def u64? (n : Nat) : Option U64 := if h : n < 2 ^ 64 then some ⟨n, h⟩ else none

/-! ## Allocation -/

/-- `def $alloctypes(eps) = eps`,
`def $alloctypes(type'* type) = deftype'* deftype*`
`  -- if deftype'* = $alloctypes(type'*)`
`  -- if type = TYPE rectype`
`  -- if deftype* = $subst_all_deftypes($rolldt(x, rectype), deftype'*)`
`  -- if x = |deftype'*|`.

The source recurses on the last element; the left fold below produces the same
sequence, since each step extends the prefix already allocated. -/
def allocTypes (ts : List TypeDef) : List DefType :=
  ts.foldl
    (fun dts t =>
      dts ++ substAllDefTypes (rollDt (TypeIdx.ofNat dts.length) t.rectype)
        (dts.map TypeUse.defd))
    []

/-- `def $alloctag(s, tagtype) = (s ++ {TAGS taginst}, |s.TAGS|)`
`  -- if taginst = { TYPE tagtype }`. -/
def allocTag (s : Store) (jt : TagType) : Store × TagAddr :=
  ({ s with tags := s.tags ++ [{ type := jt }] }, s.tags.length)

/-- `def $alloctags(s, eps) = (s, eps)`,
`def $alloctags(s, tagtype tagtype'*) = (s_2, ja ja'*)`. -/
def allocTags (s : Store) : List TagType → Store × List TagAddr
  | [] => (s, [])
  | jt :: jts =>
      let (s₁, a) := allocTag s jt
      let (s₂, as') := allocTags s₁ jts
      (s₂, a :: as')

/-- `def $allocglobal(s, globaltype, val) = (s ++ {GLOBALS globalinst}, |s.GLOBALS|)`
`  -- if globalinst = { TYPE globaltype, VALUE val }`. -/
def allocGlobal (s : Store) (gt : GlobalType) (v : Val) : Store × GlobalAddr :=
  ({ s with globals := s.globals ++ [{ type := gt, value := v }] }, s.globals.length)

/-- `def $allocglobals(s, eps, eps) = (s, eps)`,
`def $allocglobals(s, globaltype globaltype'*, val val'*) = (s_2, ga ga'*)`.

The source states no equation where the two sequences have different lengths, so
this is `Option`-valued rather than completed with a junk store. -/
def allocGlobals (s : Store) : List GlobalType → List Val →
    Option (Store × List GlobalAddr)
  | [], [] => some (s, [])
  | gt :: gts, v :: vs =>
      let (s₁, a) := allocGlobal s gt v
      (allocGlobals s₁ gts vs).map fun p => (p.1, a :: p.2)
  | _, _ => none

/-- ``def $allocmem(s, at `[i .. j?] PAGE) = (s ++ {MEMS meminst}, |s.MEMS|)``
`  -- if meminst = { TYPE ..., BYTES (0x00)^(i * $($(64 * $Ki))) }`. -/
def allocMem (s : Store) (mt : MemType) : Store × MemAddr :=
  ({ s with
      mems := s.mems ++
        [{ type := mt,
           bytes := List.replicate (mt.lim.min.val * (64 * Ki)) ⟨0, by decide⟩ }] },
   s.mems.length)

/-- `def $allocmems(s, eps) = (s, eps)`,
`def $allocmems(s, memtype memtype'*) = (s_2, ma ma'*)`. -/
def allocMems (s : Store) : List MemType → Store × List MemAddr
  | [] => (s, [])
  | mt :: mts =>
      let (s₁, a) := allocMem s mt
      let (s₂, as') := allocMems s₁ mts
      (s₂, a :: as')

/-- ``def $alloctable(s, at `[i .. j?] rt, ref) = (s ++ {TABLES tableinst}, |s.TABLES|)``
`  -- if tableinst = { TYPE ..., REFS ref^i }`. -/
def allocTable (s : Store) (tt : TableType) (r : Ref) : Store × TableAddr :=
  ({ s with
      tables := s.tables ++
        [{ type := tt, refs := List.replicate tt.lim.min.val r }] },
   s.tables.length)

/-- `def $alloctables(s, eps, eps) = (s, eps)`,
`def $alloctables(s, tabletype tabletype'*, ref ref'*) = (s_2, ta ta'*)`. -/
def allocTables (s : Store) : List TableType → List Ref →
    Option (Store × List TableAddr)
  | [], [] => some (s, [])
  | tt :: tts, r :: rs =>
      let (s₁, a) := allocTable s tt r
      (allocTables s₁ tts rs).map fun p => (p.1, a :: p.2)
  | _, _ => none

/-- `def $allocfunc(s, deftype, funccode, moduleinst) = (s ++ {FUNCS funcinst}, |s.FUNCS|)`
`  -- if funcinst = { TYPE deftype, MODULE moduleinst, CODE funccode }`. -/
def allocFunc (s : Store) (dt : DefType) (code : FuncCode) (mm : ModuleInst) :
    Store × FuncAddr :=
  ({ s with funcs := s.funcs ++ [{ type := dt, mod := mm, code := code }] },
   s.funcs.length)

/-- `def $allocfuncs(s, eps, eps, eps) = (s, eps)`,
`def $allocfuncs(s, dt dt'*, funccode funccode'*, moduleinst moduleinst'*) = (s_2, fa fa'*)`. -/
def allocFuncs (s : Store) : List DefType → List FuncCode → List ModuleInst →
    Option (Store × List FuncAddr)
  | [], [], [] => some (s, [])
  | dt :: dts, c :: cs, mm :: mms =>
      let (s₁, a) := allocFunc s dt c mm
      (allocFuncs s₁ dts cs mms).map fun p => (p.1, a :: p.2)
  | _, _, _ => none

/-- `def $allocdata(s, OK, byte*) = (s ++ {DATAS datainst}, |s.DATAS|)`
`  -- if datainst = { BYTES byte* }`. -/
def allocData (s : Store) (_ : DataType) (bs : List Byte) : Store × DataAddr :=
  ({ s with datas := s.datas ++ [{ bytes := bs }] }, s.datas.length)

/-- `def $allocdatas(s, eps, eps) = (s, eps)`,
`def $allocdatas(s, ok ok'*, (b*) (b'*)*) = (s_2, da da'*)`. -/
def allocDatas (s : Store) : List DataType → List (List Byte) →
    Option (Store × List DataAddr)
  | [], [] => some (s, [])
  | dty :: oks, bs :: bss =>
      let (s₁, a) := allocData s dty bs
      (allocDatas s₁ oks bss).map fun p => (p.1, a :: p.2)
  | _, _ => none

/-- `def $allocelem(s, elemtype, ref*) = (s ++ {ELEMS eleminst}, |s.ELEMS|)`
`  -- if eleminst = { TYPE elemtype, REFS ref* }`. -/
def allocElem (s : Store) (rt : ElemType) (rs : List Ref) : Store × ElemAddr :=
  ({ s with elems := s.elems ++ [{ type := rt, refs := rs }] }, s.elems.length)

/-- `def $allocelems(s, eps, eps) = (s, eps)`,
`def $allocelems(s, rt rt'*, (ref*) (ref'*)*) = (s_2, ea ea'*)`. -/
def allocElems (s : Store) : List ElemType → List (List Ref) →
    Option (Store × List ElemAddr)
  | [], [] => some (s, [])
  | rt :: rts, rs :: rss =>
      let (s₁, a) := allocElem s rt rs
      (allocElems s₁ rts rss).map fun p => (p.1, a :: p.2)
  | _, _ => none

/-- `def $allocexport(moduleinst, EXPORT name (TAG x)) = { NAME name, ADDR (TAG moduleinst.TAGS[x]) }`
and the four companion equations for `GLOBAL`, `MEM`, `TABLE` and `FUNC`. -/
def allocExport (mm : ModuleInst) (e : Export) : Option ExportInst :=
  match e.externidx with
  | .tag x => (mm.tags[x.val]?).map fun a => { name := e.name, addr := .tag a }
  | .global x => (mm.globals[x.val]?).map fun a => { name := e.name, addr := .global a }
  | .mem x => (mm.mems[x.val]?).map fun a => { name := e.name, addr := .mem a }
  | .table x => (mm.tables[x.val]?).map fun a => { name := e.name, addr := .table a }
  | .func x => (mm.funcs[x.val]?).map fun a => { name := e.name, addr := .func a }

/-- `def $allocexports(moduleinst, export*) = $allocexport(moduleinst, export)*`. -/
def allocExports (mm : ModuleInst) (es : List Export) : Option (List ExportInst) :=
  es.mapM (allocExport mm)

/-- `def $allocmodule(s, module, externaddr*, val_G*, ref_T*, (ref_E*)*) = (s_7, moduleinst)`,
transcribed as a relation because the source states it as a conjunction of
sixteen side conditions rather than as a computation. -/
inductive AllocModule :
    Store → Module → List ExternAddr → List Val → List Ref → List (List Ref) →
    Store → ModuleInst → Prop where
  /-- The single equation of `def $allocmodule`, premise for premise.

  `moduleinst` occurs in the premise that allocates the functions and is fixed by
  a later premise; that is the source's own shape, which its comment marks
  "TODO: use moduleinst here and remove hack above".  As a relation this is a
  fixed-point condition rather than a circular definition. -/
  | mk {s s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Store} {m : Module} {xas : List ExternAddr}
      {valG : List Val} {refT : List Ref} {refE : List (List Ref)}
      {dts fdts : List DefType} {aaI gaI maI taI faI : List Addr}
      {aa ga ma ta fa da ea : List Addr} {xis : List ExportInst}
      {mm mm₀ : ModuleInst} :
      dts = allocTypes m.types →
      aaI = tagsxa xas → gaI = globalsxa xas → maI = memsxa xas →
      taI = tablesxa xas → faI = funcsxa xas →
      fa = (List.range m.funcs.length).map (fun i => s.funcs.length + i) →
      allocTags s (m.tags.map fun t => substAllTagType t.tagtype (dts.map TypeUse.defd))
        = (s₁, aa) →
      allocGlobals s₁
        (m.globals.map fun g => substAllGlobalType g.globaltype (dts.map TypeUse.defd))
        valG = some (s₂, ga) →
      allocMems s₂
        (m.mems.map fun mem => substAllMemType mem.memtype (dts.map TypeUse.defd))
        = (s₃, ma) →
      allocTables s₃
        (m.tables.map fun t => substAllTableType t.tabletype (dts.map TypeUse.defd))
        refT = some (s₄, ta) →
      allocDatas s₄ (m.datas.map fun _ => DataType.ok) (m.datas.map Data.bytes)
        = some (s₅, da) →
      allocElems s₅
        (m.elems.map fun e => substAllRefType e.reftype (dts.map TypeUse.defd))
        refE = some (s₆, ea) →
      (m.funcs.mapM fun f => dts[f.typeidx.val]?) = some fdts →
      allocFuncs s₆ fdts (m.funcs.map FuncCode.func)
        (List.replicate m.funcs.length mm) = some (s₇, fa) →
      mm₀ = { tags := aaI ++ aa, globals := gaI ++ ga, mems := maI ++ ma,
              tables := taI ++ ta, funcs := faI ++ fa } →
      allocExports mm₀ m.exports = some xis →
      mm = { types := dts, tags := aaI ++ aa, globals := gaI ++ ga,
             mems := maI ++ ma, tables := taI ++ ta, funcs := faI ++ fa,
             datas := da, elems := ea, exports := xis } →
      AllocModule s m xas valG refT refE s₇ mm

/-! ## Closed type-section origin

Runtime subtype search sees the closed `DefType`s stored in a module instance,
not the indexed source type section.  The equality below is the structural
origin certificate that connects those two presentations.  It is deliberately
weaker than a subtype-completeness assertion: completeness must be proved from
this equality together with the module's `Types_okA` derivation. -/

/-- A module instance carries exactly the closed types produced by the pinned
allocation function from its source module. -/
def ModuleInst.AllocatedTypesFrom (m : Module) (mm : ModuleInst) : Prop :=
  mm.types = allocTypes m.types

/-- The allocation relation fixes the module instance's closed type section;
it cannot be supplied independently by a runtime caller. -/
theorem AllocModule.allocatedTypesFrom {s s' : Store} {m : Module}
    {xas : List ExternAddr} {valG : List Val} {refT : List Ref}
    {refE : List (List Ref)} {mm : ModuleInst}
    (h : AllocModule s m xas valG refT refE s' mm) :
    mm.AllocatedTypesFrom m := by
  cases h
  simp_all [ModuleInst.AllocatedTypesFrom]

/-! ## Instantiation -/

variable [authority : ExecutionAuthority]

/-- `def $rundata_(x, DATA b^n (PASSIVE)) = eps`,
`def $rundata_(x, DATA b^n (ACTIVE y instr*)) =
   instr* (CONST I32 0) (CONST I32 n) (MEMORY.INIT y x) (DATA.DROP x)`. -/
def runData_ (x : DataIdx) (d : Data) : Option (List Instr) :=
  match d.mode with
  | .passive => some []
  | .active y offset => do
      let n ← u32? d.bytes.length
      let zero ← u32? 0
      pure (offset.toList ++
        [.const .i32 zero, .const .i32 n, .memoryInit y x, .dataDrop x])

/-- `def $runelem_(x, ELEM rt e^n (PASSIVE)) = eps`,
`def $runelem_(x, ELEM rt e^n (DECLARE)) = (ELEM.DROP x)`,
`def $runelem_(x, ELEM rt e^n (ACTIVE y instr*)) =
   instr* (CONST I32 0) (CONST I32 n) (TABLE.INIT y x) (ELEM.DROP x)`. -/
def runElem_ (x : ElemIdx) (e : Elem) : Option (List Instr) :=
  match e.mode with
  | .passive => some []
  | .declare => some [.elemDrop x]
  | .active y offset => do
      let n ← u32? e.init.length
      let zero ← u32? 0
      pure (offset.toList ++
        [.const .i32 zero, .const .i32 n, .tableInit y x, .elemDrop x])

/-- `def $evalglobals(z, eps, eps) = (z, eps)`,
`def $evalglobals(z, gt gt'*, expr expr'*) = (z', val val'*)`
`  -- Eval_expr: z; expr ~>* z; val`
`  -- if z = s; f`
`  -- if (s', a) = $allocglobal(s, gt, val)`
`  -- if (z', val'*) = $evalglobals((s'; f[.MODULE.GLOBALS =++ a]), gt'*, expr'*)`. -/
inductive EvalGlobals (Nm : Numerics) :
    State → List GlobalType → List Expr → State → List Val → Prop where
  /-- `def $evalglobals(z, eps, eps) = (z, eps)`. -/
  | nil {z : State} : EvalGlobals Nm z [] [] z []
  /-- The recursive equation. -/
  | cons {z z' : State} {s s' : Store} {f : Frame} {a : GlobalAddr}
      {gt : GlobalType} {gts : List GlobalType} {e : Expr} {es : List Expr}
      {v : Val} {vs : List Val} :
      Eval_expr Nm z e z [v] →
      z = ⟨s, f⟩ →
      allocGlobal s gt v = (s', a) →
      EvalGlobals Nm
        ⟨s', { f with mod := { f.mod with globals := f.mod.globals ++ [a] } }⟩
        gts es z' vs →
      EvalGlobals Nm z (gt :: gts) (e :: es) z' (v :: vs)

/-- `def $instantiate(s, module, externaddr*) =
    s'; {MODULE moduleinst}; instr_E* instr_D* instr_S?`, with every premise the
source states: the module validates, each supplied external address has the
matching import type, the global, table and element expressions evaluate, the
module is allocated, and the resulting configuration runs the element segments,
then the data segments, then the start function. -/
inductive Instantiate (Nm : Numerics) : Store → Module → List ExternAddr → Config → Prop where
  /-- The single equation of `def $instantiate`, premise for premise. -/
  | mk {s s' : Store} {m : Module} {xas : List ExternAddr} {mt : ModuleType}
      {z z' : State} {mm₀ mm : ModuleInst} {valG : List Val} {refT : List Ref}
      {refE : List (List Ref)} {instrD instrE : List Instr}
      {dss ess : List (List Instr)} {instrS : Option Instr} :
      Module_ok m mt →
      SeqLen₂ xas mt.imports →
      SeqAll₂ (fun xa xt => Externaddr_ok s xa xt) xas mt.imports →
      mm₀ = { types := allocTypes m.types,
              globals := globalsxa xas,
              funcs := funcsxa xas ++
                (List.range m.funcs.length).map (fun i => s.funcs.length + i) } →
      z = ⟨s, { mod := mm₀ }⟩ →
      EvalGlobals Nm z (m.globals.map Global.globaltype) (m.globals.map Global.init)
        z' valG →
      SeqLen₂ m.tables refT →
      SeqAll₂ (fun t r => Eval_expr Nm z' t.init z' [.ref r]) m.tables refT →
      SeqLen₂ m.elems refE →
      SeqAll₂
        (fun e rs => SeqLen₂ e.init rs ∧
          SeqAll₂ (fun ex r => Eval_expr Nm z' ex z' [.ref r]) e.init rs)
        m.elems refE →
      AllocModule s m xas valG refT refE s' mm →
      (m.datas.zipIdx.mapM fun p => runData_ (TypeIdx.ofNat p.2) p.1) = some dss →
      instrD = dss.flatten →
      (m.elems.zipIdx.mapM fun p => runElem_ (TypeIdx.ofNat p.2) p.1) = some ess →
      instrE = ess.flatten →
      instrS = m.start.map (fun st => Instr.call st.funcidx) →
      Instantiate Nm s m xas
        (⟨s', { mod := mm }⟩,
         plains instrE ++ plains instrD ++ plains instrS.toList)

omit authority in
/-- Every instantiated configuration exposes the allocation-derived closed
type section in its active module frame.  This is the runtime origin half of
the later fixed-fuel subtype-completeness theorem. -/
theorem Instantiate.allocatedTypesFrom {execAuthority : ExecutionAuthority}
    {Nm : Numerics} {s : Store} {m : Module} {xas : List ExternAddr}
    {core : Config} (h : @Instantiate execAuthority Nm s m xas core) :
    core.1.frame.mod.AllocatedTypesFrom m := by
  cases h
  apply AllocModule.allocatedTypesFrom
  assumption

/-! ## Invocation -/

/-- `def $invoke(s, funcaddr, val*) =
    s; {MODULE {}}; val* (REF.FUNC_ADDR funcaddr) (CALL_REF s.FUNCS[funcaddr].TYPE)`
`  -- Expand: s.FUNCS[funcaddr].TYPE ~~ FUNC t_1* -> t_2*`
`  -- (Val_ok: s |- val : t_1)*`. -/
inductive Invoke : Store → FuncAddr → List Val → Config → Prop where
  /-- The single equation of `def $invoke`, premise for premise. -/
  | mk {s : Store} {a : FuncAddr} {vs : List Val} {fi : FuncInst}
      {t₁ t₂ : ValTypes} :
      s.funcs[a]? = some fi →
      Expand fi.type (.func t₁ t₂) →
      SeqLen₂ vs t₁.toList →
      SeqAll₂ (fun v t => Val_ok s v t) vs t₁.toList →
      Invoke s a vs
        (⟨s, { mod := {} }⟩,
         vals vs ++ [.addrref (.funcAddr a), .plain (.callRef (.defd fi.type))])

/-! ## Explicit released endpoints -/

/-- Byte-identical pinned instantiation, retained as the authority reference. -/
abbrev InstantiatePinned := @Instantiate pinnedExecutionAuthority

/-- AMD-011 instantiation with an explicit numeric provider. -/
abbrev InstantiateAmendedFor := @Instantiate amendedExecutionAuthority

/-- Byte-identical pinned invocation, retained as the authority reference. -/
abbrev InvokePinned := @Invoke pinnedExecutionAuthority

/-- Released invocation with amended runtime typing fixed. -/
abbrev InvokeA := @Invoke amendedExecutionAuthority

end WasmGemmGnaf.Wasm.Core.Exec
