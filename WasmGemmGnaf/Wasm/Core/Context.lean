/-
  Wasm/Core/Context.lean --- validation contexts of the pinned WebAssembly Core
  3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production or `def` of

      vendor/wasm-spec/specification/wasm-3.0/2.0-validation.contexts.spectec

  at the pinned commit, plus the two internal type sorts (`localtype`,
  `instrtype`) that file introduces.

  ONE REPRESENTATION CHOICE.  `resulttype = list(valtype)`; inside the recursive
  type knot of `Core/Types.lean` it has to be the companion cons-list `ValTypes`,
  because Lean forbids a `Subtype` in a nested-inductive position.  Outside the
  knot there is no such restriction, so the context and the typing judgment use
  an honest `List ValType`, and `ValTypes.toList` (proved a bijection in
  `Core/Types.lean`) mediates at the boundary --- for instance where
  `Expand: dt ~~ FUNC t_1* -> t_2*` hands a `comptype`'s `ValTypes` to a rule
  that concatenates result types.  Nothing is lost: the `|X*| < 2^32` bound of
  `list(...)` is `ValTypes.wfList`'s business either way.

  `RETURN resulttype?` is an `Option`.  SpecTec's `++` on contexts is a
  componentwise sequence concatenation, which on a `?` component is defined only
  when at most one side is present; `Context.append` therefore takes the left
  one when both are, and every use in the pinned rules (`Func_ok` is the only
  one that touches RETURN) has an absent left component.  The doc comment on
  `append` says so, so a reader does not have to reconstruct it.
-/
import WasmGemmGnaf.Wasm.Core.Subst

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## SpecTec premise iteration

A premise written `(P)*` in SpecTec is `P` iterated over the sequences it
mentions, `(P)?` is `P` on an optional.  These three abbreviations are how the
typing rules below spell that, and they are `abbrev`s so that Lean's
strict-positivity check sees through them inside the inductive relations. -/

/-- `(P(x))*` over one sequence. -/
abbrev SeqAll {α : Type} (P : α → Prop) (as : List α) : Prop := ∀ a, a ∈ as → P a

/-- `(P(x, y))*` over two sequences advancing in lockstep: the ELEMENTWISE half.

The agreement of lengths that SpecTec's `(...)*` also implies is carried as a
separate premise (`SeqLen₂`) at every use, rather than conjoined here.  That is
not cosmetic: Lean's kernel accepts a recursive occurrence only at the end of a
hypothesis, never inside a conjunction, so an inductive relation whose premise
were `len ∧ elementwise` would be rejected. -/
abbrev SeqAll₂ {α β : Type} (R : α → β → Prop) (as : List α) (bs : List β) : Prop :=
  ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b

/-- Two sequences a `(...)* ` premise advances over have the same length. -/
abbrev SeqLen₂ {α β : Type} (as : List α) (bs : List β) : Prop := as.length = bs.length

/-- `(P(x, y, z))*` over three sequences advancing in lockstep, elementwise
half; see `SeqAll₂`. -/
abbrev SeqAll₃ {α β γ : Type} (R : α → β → γ → Prop)
    (as : List α) (bs : List β) (cs : List γ) : Prop :=
  ∀ (i : Nat) a b c, as[i]? = some a → bs[i]? = some b → cs[i]? = some c → R a b c

/-- Three sequences a `(...)*` premise advances over have the same length. -/
abbrev SeqLen₃ {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) : Prop :=
  as.length = bs.length ∧ bs.length = cs.length

/-- `(P(x))?` on an optional. -/
abbrev OptAll {α : Type} (P : α → Prop) (o : Option α) : Prop := ∀ a, o = some a → P a

/-- `(P(x, y))?` on two optionals, elementwise half; the presence agreement is
`OptLen₂`, kept separate for the reason given on `SeqAll₂`. -/
abbrev OptAll₂ {α β : Type} (R : α → β → Prop) (o : Option α) (p : Option β) : Prop :=
  ∀ a b, o = some a → p = some b → R a b

/-- Two optionals a `(...)?` premise advances over are present together. -/
abbrev OptLen₂ {α β : Type} (o : Option α) (p : Option β) : Prop := o.isSome = p.isSome

/-! ## Internal types -/

/-- `syntax init = SET | UNSET`. -/
inductive Init where
  | set
  | unset
  deriving DecidableEq, Repr, Inhabited

/-- `syntax localtype = init valtype`. -/
structure LocalType where
  init : Init
  valtype : ValType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax instrtype = resulttype ->_ localidx* resulttype`.

`dom ->_(locals) cod`: the operand types consumed, the locals this instruction
sequence initialises, and the operand types produced. -/
structure InstrType where
  dom : List ValType
  locals : List LocalIdx
  cod : List ValType
  deriving DecidableEq, Repr, Inhabited

/-! ## Contexts -/

/-- `syntax context = { TYPES deftype*, RECS subtype*, TAGS tagtype*,
    GLOBALS globaltype*, MEMS memtype*, TABLES tabletype*, FUNCS deftype*,
    DATAS datatype*, ELEMS elemtype*, LOCALS localtype*, LABELS resulttype*,
    RETURN resulttype?, REFS funcidx* }`. -/
structure Context where
  types : List DefType := []
  recs : List SubType := []
  tags : List TagType := []
  globals : List GlobalType := []
  mems : List MemType := []
  tables : List TableType := []
  funcs : List DefType := []
  datas : List DataType := []
  elems : List ElemType := []
  locals : List LocalType := []
  labels : List (List ValType) := []
  ret : Option (List ValType) := none
  refs : List FuncIdx := []
  deriving DecidableEq, Repr, Inhabited

namespace Context

/-- `{}`: the context every component of which is empty. -/
def empty : Context := {}

/-- `context ++ context`, componentwise sequence concatenation.

`RETURN` is a `?` component, on which SpecTec's `++` is defined only when at
most one side is present; the left one is taken when both are.  `Func_ok` is
the only rule in the pinned sources that concatenates a context carrying a
`RETURN`, and there the left component is absent. -/
def append (C₁ C₂ : Context) : Context where
  types := C₁.types ++ C₂.types
  recs := C₁.recs ++ C₂.recs
  tags := C₁.tags ++ C₂.tags
  globals := C₁.globals ++ C₂.globals
  mems := C₁.mems ++ C₂.mems
  tables := C₁.tables ++ C₂.tables
  funcs := C₁.funcs ++ C₂.funcs
  datas := C₁.datas ++ C₂.datas
  elems := C₁.elems ++ C₂.elems
  locals := C₁.locals ++ C₂.locals
  labels := C₁.labels ++ C₂.labels
  ret := match C₁.ret with
    | some r => some r
    | none => C₂.ret
  refs := C₁.refs ++ C₂.refs

instance : Append Context := ⟨append⟩

/-- `{LABELS (t*)} ++ C`: the block rules' context extension.  Every other
component of the left record is empty, so this is exactly a push onto
`LABELS`. -/
def pushLabel (ts : List ValType) (C : Context) : Context :=
  { C with labels := ts :: C.labels }

/-- `C, RECS subtype*`: the context of `Rectype_ok/_rec2`, which replaces the
`RECS` component rather than extending it. -/
def withRecs (C : Context) (sts : List SubType) : Context :=
  { C with recs := sts }

/-- `C[.LOCALS[x] = lct]`. -/
def setLocal (C : Context) (x : LocalIdx) (lct : LocalType) : Context :=
  { C with locals := C.locals.set x.val lct }

/-- `def $with_locals(context, localidx*, localtype*) : context`:

    $with_locals(C, eps, eps) = C
    $with_locals(C, x_1 x*, lct_1 lct*) = $with_locals(C[.LOCALS[x_1] = lct_1], x*, lct*)
-/
def withLocals : Context → List LocalIdx → List LocalType → Context
  | C, x :: xs, lct :: lcts => withLocals (C.setLocal x lct) xs lcts
  | C, _, _ => C

end Context

/-! ## Type closure

`def $clos_deftypes(deftype*) : deftype*`:

    $clos_deftypes(eps) = eps
    $clos_deftypes(dt* dt_n) = dt'* $subst_all_deftype(dt_n, dt'*)
      -- if dt'* = $clos_deftypes(dt*)

i.e. each entry is closed by substituting the already-closed entries before it
for the type indices it mentions. -/

/-- `$clos_deftypes` as a left fold: `acc` is the closure of the prefix already
processed. -/
def closDefTypesAux : List DefType → List DefType → List DefType
  | acc, [] => acc
  | acc, dt :: rest => closDefTypesAux (acc ++ [substAllDefType dt (acc.map TypeUse.defd)]) rest

/-- `def $clos_deftypes(deftype*) : deftype*`. -/
def closDefTypes (dts : List DefType) : List DefType := closDefTypesAux [] dts

namespace Context

/-- The closed type section of a context, read as `typeuse*` --- the second
argument of every `$subst_all_*` a `$clos_*` calls. -/
def closTypes (C : Context) : List TypeUse := (closDefTypes C.types).map TypeUse.defd

/-- `def $clos_valtype(C, t) = $subst_all_valtype(t, dt*) -- if dt* = $clos_deftypes(C.TYPES)`. -/
def closValType (C : Context) (t : ValType) : ValType := substAllValType t C.closTypes

/-- `def $clos_deftype(C, dt)`. -/
def closDefType (C : Context) (dt : DefType) : DefType := substAllDefType dt C.closTypes

/-- `def $clos_tagtype(C, jt)`. -/
def closTagType (C : Context) (jt : TagType) : TagType := substAllTagType jt C.closTypes

/-- `def $clos_externtype(C, xt)`. -/
def closExternType (C : Context) (xt : ExternType) : ExternType :=
  substAllExternType xt C.closTypes

/-- `def $clos_moduletype(C, mmt)`. -/
def closModuleType (C : Context) (mmt : ModuleType) : ModuleType :=
  substAllModuleType mmt C.closTypes

/-- `def $unrollht(C, heaptype) : subtype`:

    $unrollht(C, deftype) = $unrolldt(deftype)
    $unrollht(C, _IDX typeidx) = $unrolldt(C.TYPES[typeidx])
    $unrollht(C, REC i) = C.RECS[i]

The source declares the argument as a `heaptype` but gives equations only for
the three `typeuse` cases, so an abstract heap type is `none` here. -/
def unrollHt (C : Context) : HeapType → Option SubType
  | .use (.defd dt) => unrollDt dt
  | .use (.idx x) => match C.types[x.val]? with
      | some dt => unrollDt dt
      | none => none
  | .use (.recu i) => C.recs[i]?
  | .abs _ => none

end Context

/-! ## Default values

`Defaultable` and `Nondefaultable` are declared in
`2.3-validation.instructions.spectec` and used as premises by `Local_ok`,
`Instr_ok/struct.new_default` and `Instr_ok/array.new_default`, but their rules
live in `4.1-execution.values.spectec`:

    def $default_(Inn) = (CONST Inn 0)
    def $default_(Fnn) = (CONST Fnn $fzero($size(Fnn)))
    def $default_(Vnn) = (VCONST Vnn 0)
    def $default_(REF NULL ht) = (REF.NULL ht)
    def $default_(REF ht) = eps
    rule Defaultable: |- t DEFAULTABLE     -- if $default_(t) =/= eps
    rule Nondefaultable: |- t NONDEFAULTABLE -- if $default_(t) = eps

`$default_` is a partial function: it has no equation at `BOT`.  The two
predicates below are therefore separate, not complements --- at `BOT` neither
holds, which is what "no equation" means.  Only whether a default exists is
needed here; the value itself belongs to the execution layer. -/

/-- `$default_(t) =/= eps`: the equations of `$default_` that produce a value. -/
def ValType.hasDefault : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref (.ref (some .null) _) => true
  | .ref (.ref none _) => false
  | .bot => false

/-- `$default_(t) = eps`: the single equation of `$default_` that produces `eps`. -/
def ValType.noDefault : ValType → Bool
  | .ref (.ref none _) => true
  | _ => false

end WasmGemmGnaf.Wasm.Core
