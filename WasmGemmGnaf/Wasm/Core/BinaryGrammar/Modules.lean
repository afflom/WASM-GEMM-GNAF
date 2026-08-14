/-
  Wasm/Core/BinaryGrammar/Modules.lean --- the DECLARATIVE binary grammar of
  modules and sections, for the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/5.4-binary.modules.spectec

  at the pinned commit.  Nothing here imports or mentions a decoder.

  THE FOUR THINGS THE AUDIT NAMED, AND WHERE THEY ARE:

  * OPTIONAL SECTIONS.  `Bsection_(N, BX)` has an `eps` alternative, so every
    section may be absent; `Bsection.absent` is that alternative.  A section is
    not "a section that may be empty" -- an absent section and a present but
    empty one are different byte sequences and both are derivable.

  * CUSTOM SECTIONS BETWEEN ANY TWO SECTIONS.  `Bmodule` interleaves
    `Bcustomsec*` at all FOURTEEN positions the pinned source writes: before
    each of the thirteen sections and after the last.  `Bcustomsec` is
    `Bsection_(0, Bcustom)` and `Bcustom` is `Bname Bbyte*`, so a custom
    section's payload is arbitrary bytes and its name must still be valid UTF-8.

  * THE FUNCTION / CODE SPLIT.  The function section carries `typeidx*` and the
    code section carries `(local*, expr)*`; the abstract `func*` is the pointwise
    pairing, which the source states as `-- (if func = FUNC typeidx local* expr)*`
    and which appears below as a `List.zipWith` together with the equal-length
    condition that makes the starred side condition meaningful.

  * THE DATA COUNT SECTION.  `Bdatacntsec` is `Bsection_(12, Bdatacnt)` and the
    two side conditions of `Bmodule` are transcribed: the count must agree with
    the number of data segments when it is present, and it must be present at
    all whenever any function body mentions a data index.

  COMPRESSED LOCALS.  `Blocals` is `n:Bu32 t:Bvaltype => (LOCAL t)^n`, a run
  length and a type; `Bfunc` concatenates the runs and carries the source's
  `-- if |$concat_(local, loc**)| < 2^32`.

  `$dataidx_funcs` IS TRANSCRIBED ONLY IN ITS `DATAS` COMPONENT.
  `1.4-syntax.modules.spectec` defines it as `$free_list($free_func(func)*).DATAS`,
  and `$free_func` reaches `$free_instr`, which the syntax layer of this
  repository does not yet carry.  Rather than assume it, the `DATAS` component
  alone is defined below, case by case against the `$free_instr` equations of
  `1.3-syntax.instructions.spectec`; that is exactly and only what `Bmodule`
  needs.  Two gaps in the pinned source are recorded at the definition.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Expressions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

/-! ## Sections -/

/-- `grammar Bsection_(N, grammar BX : en*) : en*`:

    | N:Bbyte len:Bu32 en*:BX => en*  -- if len = ||BX||
    | eps => eps

`||BX||` is the number of bytes the inner grammar consumes, which is why the
`present` alternative carries `len.val = bs.length`. -/
inductive Bsection {α : Type} (N : Nat) (G : Bytes → List α → Prop) :
    Bytes → List α → Prop where
  | present (blen bs : Bytes) (len : U32) (xs : List α) :
      Bu32 blen len → G bs xs → len.val = bs.length →
      Bsection N G (tb N :: (blen ++ bs)) xs
  | absent : Bsection N G [] []

/-! ## Custom sections -/

/-- `grammar Bcustom : ()* = | Bname Bbyte* => ()`.

The name and the payload are not bound on the right, so a custom section
carries no information into the abstract module -- but its name still has to be
a `Bname`, hence valid UTF-8. -/
inductive Bcustom : Bytes → List Unit → Prop where
  | mk (bn bb : Bytes) (nm : Name) (bl : List Byte) :
      Bname bn nm → Star Bbyte bb bl → Bcustom (bn ++ bb) [()]

/-- `grammar Bcustomsec : () = | Bsection_(0, Bcustom) => ()`. -/
inductive Bcustomsec : Bytes → Unit → Prop where
  | mk (bs : Bytes) (us : List Unit) : Bsection 0 Bcustom bs us → Bcustomsec bs ()

/-! ## Type section -/

/-- `grammar Btype : type = | qt:Brectype => TYPE qt`. -/
inductive Btype : Bytes → TypeDef → Prop where
  | mk (bs : Bytes) (qt : RecType) : Brectype bs qt → Btype bs { rectype := qt }

/-- `grammar Btypesec : type* = | ty*:Bsection_(1, Blist(Btype)) => ty*`. -/
def Btypesec (bs : Bytes) (ts : List TypeDef) : Prop :=
  Bsection 1 (Blist Btype) bs ts

/-! ## Import section -/

/-- `grammar Bimport : import
    = | nm_1:Bname nm_2:Bname xt:Bexterntype => IMPORT nm_1 nm_2 xt`. -/
inductive Bimport : Bytes → Import → Prop where
  | mk (b₁ b₂ b₃ : Bytes) (nm₁ nm₂ : Name) (xt : ExternType) :
      Bname b₁ nm₁ → Bname b₂ nm₂ → Bexterntype b₃ xt →
      Bimport (b₁ ++ b₂ ++ b₃)
        { moduleName := nm₁, itemName := nm₂, externtype := xt }

/-- `grammar Bimportsec : import*
    = | im*:Bsection_(2, Blist(Bimport)) => im*`. -/
def Bimportsec (bs : Bytes) (ims : List Import) : Prop :=
  Bsection 2 (Blist Bimport) bs ims

/-! ## Function section -/

/-- `grammar Bfuncsec : typeidx*
    = | x*:Bsection_(3, Blist(Btypeidx)) => x*`. -/
def Bfuncsec (bs : Bytes) (xs : List TypeIdx) : Prop :=
  Bsection 3 (Blist Btypeidx) bs xs

/-! ## Table section -/

/-- `grammar Btable : table`.

The first alternative is the shorthand form: a bare `tabletype` whose element
type is `REF NULL? ht`, initialised by `REF.NULL ht`.  Its side condition
`-- if tt = at lim (REF NULL? ht)` is what ties the initialiser to the element
type. -/
inductive Btable : Bytes → Table → Prop where
  | shorthand (bs : Bytes) (tt : TableType) (nul : Option Null) (ht : HeapType) :
      Btabletype bs tt → tt.elem = .ref nul ht →
      Btable bs { tabletype := tt, init := .cons (.refNull ht) .nil }
  -- core-opcode: 0x40 TABLE
  | withInit (bt be : Bytes) (tt : TableType) (e : Expr) :
      Btabletype bt tt → Bexpr be e →
      Btable (tb 0x40 :: tb 0x00 :: (bt ++ be)) { tabletype := tt, init := e }

/-- `grammar Btablesec : table*
    = | tab*:Bsection_(4, Blist(Btable)) => tab*`. -/
def Btablesec (bs : Bytes) (tabs : List Table) : Prop :=
  Bsection 4 (Blist Btable) bs tabs

/-! ## Memory section -/

/-- `grammar Bmem : mem = | mt:Bmemtype => MEMORY mt`. -/
inductive Bmem : Bytes → Mem → Prop where
  | mk (bs : Bytes) (mt : MemType) : Bmemtype bs mt → Bmem bs { memtype := mt }

/-- `grammar Bmemsec : mem* = | mem*:Bsection_(5, Blist(Bmem)) => mem*`. -/
def Bmemsec (bs : Bytes) (ms : List Mem) : Prop :=
  Bsection 5 (Blist Bmem) bs ms

/-! ## Global section -/

/-- `grammar Bglobal : global = | gt:Bglobaltype e:Bexpr => GLOBAL gt e`. -/
inductive Bglobal : Bytes → Global → Prop where
  | mk (bg be : Bytes) (gt : GlobalType) (e : Expr) :
      Bglobaltype bg gt → Bexpr be e →
      Bglobal (bg ++ be) { globaltype := gt, init := e }

/-- `grammar Bglobalsec : global*
    = | glob*:Bsection_(6, Blist(Bglobal)) => glob*`. -/
def Bglobalsec (bs : Bytes) (gs : List Global) : Prop :=
  Bsection 6 (Blist Bglobal) bs gs

/-! ## Export section -/

/-- `grammar Bexport : export = | nm:Bname xx:Bexternidx => EXPORT nm xx`. -/
inductive Bexport : Bytes → Export → Prop where
  | mk (bn bx : Bytes) (nm : Name) (xx : ExternIdx) :
      Bname bn nm → Bexternidx bx xx →
      Bexport (bn ++ bx) { name := nm, externidx := xx }

/-- `grammar Bexportsec : export*
    = | ex*:Bsection_(7, Blist(Bexport)) => ex*`. -/
def Bexportsec (bs : Bytes) (exs : List Export) : Prop :=
  Bsection 7 (Blist Bexport) bs exs

/-! ## Start section -/

/-- `grammar Bstart : start* = | x:Bfuncidx => (START x)`. -/
inductive Bstart : Bytes → List Start → Prop where
  | mk (bs : Bytes) (x : FuncIdx) : Bfuncidx bs x → Bstart bs [{ funcidx := x }]

/-- `grammar Bstartsec : start?
    = | startopt:Bsection_(8, Bstart) => $opt_(start, startopt)`.

`$opt_` is defined in `0.3-aux.seq.spectec` on exactly two patterns, `eps` and a
single element; the two constructors below are those two equations, so no
completion of `$opt_` to longer sequences is invented here. -/
inductive Bstartsec : Bytes → Option Start → Prop where
  | absent (bs : Bytes) : Bsection 8 Bstart bs [] → Bstartsec bs none
  | present (bs : Bytes) (s : Start) :
      Bsection 8 Bstart bs [s] → Bstartsec bs (some s)

/-! ## Element section -/

/-- `grammar Belemkind : reftype = | 0x00 => REF NULL FUNC`. -/
inductive Belemkind : Bytes → RefType → Prop where
  -- core-opcode: 0x00 REF
  | funcref : Belemkind [tb 0x00] (.ref (some .null) (.abs .func))

/-- `(REF.FUNC y)*`, the initialiser expressions the function-index forms of
`Belem` build. -/
def refFuncExprs (ys : List FuncIdx) : List Expr :=
  ys.map (fun y => .cons (.refFunc y) .nil)

/-- `grammar Belem : elem`, all eight tag forms.

The tags are `Bu32`s, not raw bytes, so a non-minimal encoding of the tag is
admitted here exactly as it is for an opcode selector. -/
inductive Belem : Bytes → Elem → Prop where
  /-- `| 0:Bu32 e_o:Bexpr y*:Blist(Bfuncidx)
        => ELEM (REF FUNC) (REF.FUNC y)* (ACTIVE 0 e_o)`. -/
  | activeFuncrefZero (bt be by' : Bytes) (e : Expr) (ys : List FuncIdx)
      (x : TableIdx) :
      Bu32lit 0 bt → Bexpr be e → Blist Bfuncidx by' ys → x.val = 0 →
      Belem (bt ++ be ++ by')
        { reftype := .ref none (.abs .func), init := refFuncExprs ys,
          mode := .active x e }
  /-- `| 1:Bu32 rt:Belemkind y*:Blist(Bfuncidx)
        => ELEM rt (REF.FUNC y)* PASSIVE`. -/
  | passiveFuncref (bt bk by' : Bytes) (rt : RefType) (ys : List FuncIdx) :
      Bu32lit 1 bt → Belemkind bk rt → Blist Bfuncidx by' ys →
      Belem (bt ++ bk ++ by')
        { reftype := rt, init := refFuncExprs ys, mode := .passive }
  /-- `| 2:Bu32 x:Btableidx e:Bexpr rt:Belemkind y*:Blist(Bfuncidx)
        => ELEM rt (REF.FUNC y)* (ACTIVE x e)`. -/
  | activeFuncref (bt bx be bk by' : Bytes) (x : TableIdx) (e : Expr)
      (rt : RefType) (ys : List FuncIdx) :
      Bu32lit 2 bt → Btableidx bx x → Bexpr be e → Belemkind bk rt →
      Blist Bfuncidx by' ys →
      Belem (bt ++ bx ++ be ++ bk ++ by')
        { reftype := rt, init := refFuncExprs ys, mode := .active x e }
  /-- `| 3:Bu32 rt:Belemkind y*:Blist(Bfuncidx)
        => ELEM rt (REF.FUNC y)* DECLARE`. -/
  | declareFuncref (bt bk by' : Bytes) (rt : RefType) (ys : List FuncIdx) :
      Bu32lit 3 bt → Belemkind bk rt → Blist Bfuncidx by' ys →
      Belem (bt ++ bk ++ by')
        { reftype := rt, init := refFuncExprs ys, mode := .declare }
  /-- `| 4:Bu32 e_O:Bexpr e*:Blist(Bexpr)
        => ELEM (REF NULL FUNC) e* (ACTIVE 0 e_O)`. -/
  | activeExprZero (bt be bl : Bytes) (e : Expr) (es : List Expr) (x : TableIdx) :
      Bu32lit 4 bt → Bexpr be e → Blist Bexpr bl es → x.val = 0 →
      Belem (bt ++ be ++ bl)
        { reftype := .ref (some .null) (.abs .func), init := es,
          mode := .active x e }
  /-- `| 5:Bu32 rt:Breftype e*:Blist(Bexpr) => ELEM rt e* PASSIVE`. -/
  | passiveExpr (bt br bl : Bytes) (rt : RefType) (es : List Expr) :
      Bu32lit 5 bt → Breftype br rt → Blist Bexpr bl es →
      Belem (bt ++ br ++ bl) { reftype := rt, init := es, mode := .passive }
  /-- `| 6:Bu32 x:Btableidx e_O:Bexpr e*:Blist(Bexpr)
        => ELEM (REF NULL FUNC) e* (ACTIVE x e_O)`. -/
  | activeExpr (bt bx be bl : Bytes) (x : TableIdx) (e : Expr) (es : List Expr) :
      Bu32lit 6 bt → Btableidx bx x → Bexpr be e → Blist Bexpr bl es →
      Belem (bt ++ bx ++ be ++ bl)
        { reftype := .ref (some .null) (.abs .func), init := es,
          mode := .active x e }
  /-- `| 7:Bu32 rt:Breftype e*:Blist(Bexpr) => ELEM rt e* DECLARE`. -/
  | declareExpr (bt br bl : Bytes) (rt : RefType) (es : List Expr) :
      Bu32lit 7 bt → Breftype br rt → Blist Bexpr bl es →
      Belem (bt ++ br ++ bl) { reftype := rt, init := es, mode := .declare }

/-- `grammar Belemsec : elem*
    = | elem*:Bsection_(9, Blist(Belem)) => elem*`. -/
def Belemsec (bs : Bytes) (es : List Elem) : Prop :=
  Bsection 9 (Blist Belem) bs es

/-! ## Code section -/

/-- `syntax code hint(macro none) = (local*, expr)`. -/
abbrev Code : Type := List Local × Expr

/-- `grammar Blocals : local* = | n:Bu32 t:Bvaltype => (LOCAL t)^n`.

This is the run-length ("compressed") encoding of a function's locals: one
`Bu32` count and one value type per run. -/
inductive Blocals : Bytes → List Local → Prop where
  | mk (bn bt : Bytes) (n : U32) (t : ValType) :
      Bu32 bn n → Bvaltype bt t →
      Blocals (bn ++ bt) (List.replicate n.val { valtype := t })

/-- `grammar Bfunc : code
    = | loc**:Blist(Blocals) e:Bexpr => ($concat_(local, loc**), e)
        -- if $(|$concat_(local, loc**)| < 2^32)`.

The bound is on the CONCATENATION, not on the number of runs: a function may be
encoded with few runs and still exceed the limit. -/
inductive Bfunc : Bytes → Code → Prop where
  | mk (bl be : Bytes) (locss : List (List Local)) (e : Expr) :
      Blist Blocals bl locss → Bexpr be e →
      locss.flatten.length < 2 ^ 32 →
      Bfunc (bl ++ be) (locss.flatten, e)

/-- `grammar Bcode : code = | len:Bu32 code:Bfunc => code  -- if len = ||Bfunc||`. -/
inductive Bcode : Bytes → Code → Prop where
  | mk (blen bs : Bytes) (len : U32) (c : Code) :
      Bu32 blen len → Bfunc bs c → len.val = bs.length →
      Bcode (blen ++ bs) c

/-- `grammar Bcodesec : code*
    = | code*:Bsection_(10, Blist(Bcode)) => code*`. -/
def Bcodesec (bs : Bytes) (cs : List Code) : Prop :=
  Bsection 10 (Blist Bcode) bs cs

/-! ## Data section -/

/-- `grammar Bdata : data`. -/
inductive Bdata : Bytes → Data → Prop where
  /-- `| 0:Bu32 e:Bexpr b*:Blist(Bbyte) => DATA b* (ACTIVE 0 e)`. -/
  | activeZero (bt be bb : Bytes) (e : Expr) (bl : List Byte) (x : MemIdx) :
      Bu32lit 0 bt → Bexpr be e → Blist Bbyte bb bl → x.val = 0 →
      Bdata (bt ++ be ++ bb) { bytes := bl, mode := .active x e }
  /-- `| 1:Bu32 b*:Blist(Bbyte) => DATA b* PASSIVE`. -/
  | passive (bt bb : Bytes) (bl : List Byte) :
      Bu32lit 1 bt → Blist Bbyte bb bl →
      Bdata (bt ++ bb) { bytes := bl, mode := .passive }
  /-- `| 2:Bu32 x:Bmemidx e:Bexpr b*:Blist(Bbyte) => DATA b* (ACTIVE x e)`. -/
  | active (bt bx be bb : Bytes) (x : MemIdx) (e : Expr) (bl : List Byte) :
      Bu32lit 2 bt → Bmemidx bx x → Bexpr be e → Blist Bbyte bb bl →
      Bdata (bt ++ bx ++ be ++ bb) { bytes := bl, mode := .active x e }

/-- `grammar Bdatasec : data*
    = | data*:Bsection_(11, Blist(Bdata)) => data*`. -/
def Bdatasec (bs : Bytes) (ds : List Data) : Prop :=
  Bsection 11 (Blist Bdata) bs ds

/-! ## Data count section -/

/-- `grammar Bdatacnt : u32* = | n:Bu32 => n`. -/
inductive Bdatacnt : Bytes → List U32 → Prop where
  | mk (bs : Bytes) (n : U32) : Bu32 bs n → Bdatacnt bs [n]

/-- `grammar Bdatacntsec : u32?
    = | nopt:Bsection_(12, Bdatacnt) => $opt_(u32, nopt)`. -/
inductive Bdatacntsec : Bytes → Option U32 → Prop where
  | absent (bs : Bytes) : Bsection 12 Bdatacnt bs [] → Bdatacntsec bs none
  | present (bs : Bytes) (n : U32) :
      Bsection 12 Bdatacnt bs [n] → Bdatacntsec bs (some n)

/-! ## Tag section -/

/-- `grammar Btag : tag = | jt:Btagtype => TAG jt`. -/
inductive Btag : Bytes → Tag → Prop where
  | mk (bs : Bytes) (jt : TagType) : Btagtype bs jt → Btag bs { tagtype := jt }

/-- `grammar Btagsec : tag* = | tag*:Bsection_(13, Blist(Btag)) => tag*`. -/
def Btagsec (bs : Bytes) (ts : List Tag) : Prop :=
  Bsection 13 (Blist Btag) bs ts

/-! ## `$dataidx_funcs`

`def $dataidx_funcs(func*) = $free_list($free_func(func)*).DATAS`
(`1.4-syntax.modules.spectec`).  Only the `DATAS` component is defined here,
directly from the `$free_instr` equations of `1.3-syntax.instructions.spectec`:
the four instructions whose equation mentions `$free_dataidx` are
`ARRAY.NEW_DATA`, `ARRAY.INIT_DATA`, `MEMORY.INIT` and `DATA.DROP`, and the
block-shaped instructions recur through `$free_block`, which changes only the
`LABELS` component and so leaves `DATAS` alone.

TWO GAPS IN THE PINNED SOURCE, recorded rather than hidden.  `$free_instr` has
NO equation for `THROW`, `THROW_REF` or `TRY_TABLE`.  `THROW` and `THROW_REF`
carry no data index under any reading, so their value here is forced.
`TRY_TABLE` carries an instruction sequence, and the completion taken below is
the one every other block-shaped instruction uses -- recur into the body -- which
is the only choice that does not silently lose data indices a function really
does mention. -/
mutual

/-- The `DATAS` component of `$free_instr`. -/
def dataIdxInstr : Instr → List DataIdx
  | .block _ body => dataIdxInstrs body
  | .loop _ body => dataIdxInstrs body
  | .ifElse _ thn els => dataIdxInstrs thn ++ dataIdxInstrs els
  | .tryTable _ _ body => dataIdxInstrs body
  | .memoryInit _ y => [y]
  | .dataDrop y => [y]
  | .arrayNewData _ y => [y]
  | .arrayInitData _ y => [y]
  | _ => []

/-- The `DATAS` component of `$free_block` / `$free_expr`. -/
def dataIdxInstrs : InstrSeq → List DataIdx
  | .nil => []
  | .cons i rest => dataIdxInstr i ++ dataIdxInstrs rest

end

/-- The `DATAS` component of `$free_func`. -/
def dataIdxFunc (f : Func) : List DataIdx := dataIdxInstrs f.body

/-- `def $dataidx_funcs(func*)`, in its `DATAS` component. -/
def dataIdxFuncs (fs : List Func) : List DataIdx := fs.flatMap dataIdxFunc

/-! ## Modules -/

/-- `grammar Bmagic : () = 0x00 0x61 0x73 0x6D => ()`. -/
inductive Bmagic : Bytes → Unit → Prop where
  | mk : Bmagic [tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ()

/-- `grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()`. -/
inductive Bversion : Bytes → Unit → Prop where
  | mk : Bversion [tb 0x01, tb 0x00, tb 0x00, tb 0x00] ()

/-- `grammar Bmodule : module`, the whole pinned production.

The byte sequence is the source's concatenation, in the source's SECTION ORDER
-- which is not the numeric order of the section ids: the tag section (13) comes
between the memory (5) and global (6) sections, and the data count section (12)
between the element (9) and code (10) sections.  All fourteen `Bcustomsec*`
positions are present.

The three side conditions of the pinned production are the last four hypotheses:

    -- (if n = |data*|)?
    -- if (n? =/= eps \/ $dataidx_funcs(func*) = eps)
    -- (if func = FUNC typeidx local* expr)*

The starred third condition needs the two lists to have the same length for the
pointwise reading to be the intended one, so that equality is stated as well as
the pairing. -/
inductive Bmodule : Bytes → Module → Prop where
  | mk
      (bmag bver : Bytes)
      (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes)
      (u₀ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ : List Unit)
      (bty bim bfu bta bme btg bgl bex bst bel bdc bco bda : Bytes)
      (types : List TypeDef) (imports : List Import) (typeidxs : List TypeIdx)
      (tables : List Table) (mems : List Mem) (tags : List Tag)
      (globals : List Global) (exports : List Export) (start : Option Start)
      (elems : List Elem) (n : Option U32) (codes : List Code)
      (datas : List Data) (funcs : List Func) :
      Bmagic bmag () → Bversion bver () →
      Star Bcustomsec c₀ u₀ → Btypesec bty types →
      Star Bcustomsec c₁ u₁ → Bimportsec bim imports →
      Star Bcustomsec c₂ u₂ → Bfuncsec bfu typeidxs →
      Star Bcustomsec c₃ u₃ → Btablesec bta tables →
      Star Bcustomsec c₄ u₄ → Bmemsec bme mems →
      Star Bcustomsec c₅ u₅ → Btagsec btg tags →
      Star Bcustomsec c₆ u₆ → Bglobalsec bgl globals →
      Star Bcustomsec c₇ u₇ → Bexportsec bex exports →
      Star Bcustomsec c₈ u₈ → Bstartsec bst start →
      Star Bcustomsec c₉ u₉ → Belemsec bel elems →
      Star Bcustomsec c₁₀ u₁₀ → Bdatacntsec bdc n →
      Star Bcustomsec c₁₁ u₁₁ → Bcodesec bco codes →
      Star Bcustomsec c₁₂ u₁₂ → Bdatasec bda datas →
      Star Bcustomsec c₁₃ u₁₃ →
      (∀ k : U32, n = some k → k.val = datas.length) →
      (n ≠ none ∨ dataIdxFuncs funcs = []) →
      typeidxs.length = codes.length →
      funcs = List.zipWith
        (fun (x : TypeIdx) (c : Code) =>
          ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes →
      Bmodule
        (bmag ++ bver ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfu ++ c₃ ++ bta ++
          c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++
          c₉ ++ bel ++ c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃)
        { types := types, imports := imports, tags := tags, globals := globals,
          mems := mems, tables := tables, funcs := funcs, datas := datas,
          elems := elems, start := start, exports := exports }

/-- The explicit byte-identical pinned whole-module relation. -/
abbrev BmodulePinned := @Bmodule pinnedBinaryAuthority

/-- The whole-module relation under the exact AMD-007/008/010 authority. -/
abbrev BmoduleA := @Bmodule amendedBinaryAuthority

end WasmGemmGnaf.Wasm.Core.Binary
