/-
  Wasm/Core/Validation/Instructions.lean --- the declarative typing judgment on
  INSTRUCTIONS of the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every constructor below transcribes one `rule` of

      vendor/wasm-spec/specification/wasm-3.0/2.3-validation.instructions.spectec

  at the pinned commit, in source order, one Lean constructor per SpecTec rule,
  carrying that rule's premises as hypotheses and nothing else.

  SCOPE.  The whole released feature surface, because the pinned source has no
  other: SIMD (`VLOAD`, `VBINOP`, `VSHUFFLE`, `VCVTOP`, ...), GC and references
  (`STRUCT.*`, `ARRAY.*`, `REF.CAST`, `BR_ON_CAST`, `EXTERN.CONVERT_ANY`, ...),
  tables (`TABLE.*`, `ELEM.DROP`), bulk memory (`MEMORY.COPY`, `MEMORY.INIT`,
  `DATA.DROP`), tail calls (`RETURN_CALL*`), exception handling (`THROW`,
  `THROW_REF`, `TRY_TABLE`, `Catch_ok`), multi-value (every `resulttype` is a
  sequence, and `Blocktype_ok/typeidx` gives a block a full function type) and
  extended constant expressions (`Instr_const/global.get`,
  `Instr_const/binop`, `Instr_const/struct.new`, ...).

  STACK POLYMORPHISM IS THE POINT.  `UNREACHABLE`, `BR`, `BR_TABLE`, `RETURN`,
  `RETURN_CALL*`, `THROW` and `THROW_REF` are typed in Core 3.0 by instruction
  types with FREE result-type variables, constrained only by `Instrtype_ok`.
  That is exactly how they appear below: `unreachable` relates `.unreachable` to
  EVERY well-formed `t_1* -> t_2*`, not to one concrete pair.  A transcription
  that fixed those types would reject code Core accepts, which is the defect an
  external audit named in the previous validator.

  WHAT IS NOT HERE.  No decision procedure, and no theorem relating this
  relation to one.  `Instrs_ok/sub` and `Instrs_ok/frame` make the judgment
  visibly non-syntax-directed; recovering an algorithm from it is a separate
  obligation and is not discharged by this file.

  TWO RULES THAT THE PINNED SOURCE CARRIES INSIDE A `(; ... ;)` BLOCK COMMENT.
  `Instr_ok/load` and `Instr_ok/store` are the COMBINED forms that the split
  `-val` / `-pack` rules replaced; the source keeps their text, commented out,
  immediately above the split rules.  They are transcribed here, verbatim,
  because the text is in the pinned file --- and this paragraph says plainly
  that they are commented out there, so that no reader mistakes their presence
  for a claim that the pinned grammar still uses them.  They admit nothing the
  split rules do not: the combined rule's own side conditions
  (`2^align <= N/8 < $size(nt)/8` when the pack width is present) are strictly
  stronger.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Types
import WasmGemmGnaf.Wasm.Core.Instructions

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## Coercions and projections the pinned rules use implicitly

SpecTec coerces `addrtype` into `numtype` (both are spelled `I32`/`I64`) and
projects the two components of a `fieldtype`.  Lean has neither for free. -/

/-- `addrtype` read as a `numtype`; the two sorts share their constructors. -/
def AddrType.toNumType : AddrType → NumType
  | .i32 => .i32
  | .i64 => .i64

/-- `addrtype` read as a `valtype`, as every `... : at -> ...` conclusion does. -/
def AddrType.toValType (a : AddrType) : ValType := .num a.toNumType

/-- The `mut?` of a `fieldtype = mut? storagetype`. -/
def FieldType.mutability : FieldType → Option Mut
  | .mk m _ => m

/-- The `storagetype` of a `fieldtype = mut? storagetype`. -/
def FieldType.storage : FieldType → StorageType
  | .mk _ zt => zt

/-- `$unpack(zt)*` over the fields of a `STRUCT`. -/
def FieldTypes.unpacked (fts : FieldTypes) : List ValType :=
  (FieldTypes.toList fts).map (fun ft => StorageType.unpack ft.storage)

/-- `t = numtype \/ t = vectype`, the side condition of `Instr_ok/select-impl`
and (through `$unpack`) of `Instr_ok/array.new_data` and
`Instr_ok/array.init_data`. -/
def ValType.isNumOrVec : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | _ => false

/-- `I32`, as a `valtype`; it occurs in a great many instruction types. -/
abbrev ValType.i32 : ValType := .num .i32

/-- `V128`, as a `valtype`. -/
abbrev ValType.v128 : ValType := .vec .v128

/-! ## Defaultability

`relation Defaultable: |- valtype DEFAULTABLE` and
`relation Nondefaultable: |- valtype NONDEFAULTABLE` are declared in
`2.3-validation.instructions.spectec` and used as premises by
`Instr_ok/struct.new_default`, `Instr_ok/array.new_default` and `Local_ok`;
their rules are given in `4.1-execution.values.spectec` in terms of `$default_`.
See `Core/Context.lean` for why the two are separate predicates rather than
complements. -/

/-- `rule Defaultable: |- t DEFAULTABLE -- if $default_(t) =/= eps`. -/
inductive Defaultable : ValType → Prop where
  | mk {t : ValType} : t.hasDefault = true → Defaultable t

/-- `rule Nondefaultable: |- t NONDEFAULTABLE -- if $default_(t) = eps`. -/
inductive Nondefaultable : ValType → Prop where
  | mk {t : ValType} : t.noDefault = true → Nondefaultable t

/-! ## Block types -/

/-- `relation Blocktype_ok: context |- blocktype : instrtype`. -/
inductive Blocktype_ok : Context → BlockType → InstrType → Prop where
  /-- `rule Blocktype_ok/valtype: C |- _RESULT valtype? : eps -> valtype?
      -- (Valtype_ok: C |- valtype : OK)?`. -/
  -- core-rule: Blocktype_ok/valtype
  | valtype {C : Context} {t : Option ValType} :
      OptAll (Valtype_ok C) t → Blocktype_ok C (.result t) ⟨[], [], t.toList⟩
  /-- `rule Blocktype_ok/typeidx: C |- _IDX typeidx : t_1* -> t_2*
      -- Expand: C.TYPES[typeidx] ~~ FUNC t_1* -> t_2*`. -/
  -- core-rule: Blocktype_ok/typeidx
  | typeidx {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      Blocktype_ok C (.idx x) ⟨ValTypes.toList dom, [], ValTypes.toList cod⟩

/-! ## Exception handlers -/

/-- `relation Catch_ok: context |- catch : OK`. -/
inductive Catch_ok : Context → Catch → Prop where
  /-- `rule Catch_ok/catch:
        C |- CATCH x l : OK
        -- Expand: $as_deftype(C.TAGS[x]) ~~ FUNC t* -> eps
        -- Resulttype_sub: C |- t* <: C.LABELS[l]`. -/
  -- core-rule: Catch_ok/catch
  | catch {C : Context} {x : TagIdx} {l : LabelIdx} {jt : TagType} {dt : DefType}
      {dom : ValTypes} {ts' : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) →
      C.labels[l.val]? = some ts' →
      Resulttype_sub C (ValTypes.toList dom) ts' →
      Catch_ok C (.tag x l)
  /-- `rule Catch_ok/catch_ref:
        C |- CATCH_REF x l : OK
        -- Expand: $as_deftype(C.TAGS[x]) ~~ FUNC t* -> eps
        -- Resulttype_sub: C |- t* (REF EXN) <: C.LABELS[l]`. -/
  -- core-rule: Catch_ok/catch_ref
  | catch_ref {C : Context} {x : TagIdx} {l : LabelIdx} {jt : TagType} {dt : DefType}
      {dom : ValTypes} {ts' : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) →
      C.labels[l.val]? = some ts' →
      Resulttype_sub C (ValTypes.toList dom ++ [.ref (.ref none (.abs .exn))]) ts' →
      Catch_ok C (.tagRef x l)
  /-- `rule Catch_ok/catch_all: C |- CATCH_ALL l : OK
      -- Resulttype_sub: C |- eps <: C.LABELS[l]`. -/
  -- core-rule: Catch_ok/catch_all
  | catch_all {C : Context} {l : LabelIdx} {ts' : List ValType} :
      C.labels[l.val]? = some ts' → Resulttype_sub C [] ts' → Catch_ok C (.all l)
  /-- `rule Catch_ok/catch_all_ref: C |- CATCH_ALL_REF l : OK
      -- Resulttype_sub: C |- (REF EXN) <: C.LABELS[l]`. -/
  -- core-rule: Catch_ok/catch_all_ref
  | catch_all_ref {C : Context} {l : LabelIdx} {ts' : List ValType} :
      C.labels[l.val]? = some ts' →
      Resulttype_sub C [.ref (.ref none (.abs .exn))] ts' →
      Catch_ok C (.allRef l)

/-! ## The instruction judgment

`Instr_ok` and `Instrs_ok` are mutually inductive: a block's body is an
instruction sequence, and an instruction sequence is a head instruction
followed by a sequence. -/

mutual

/-- `relation Instr_ok: context |- instr : instrtype`. -/
inductive Instr_ok : Context → Instr → InstrType → Prop where
  -- Parametric instructions
  /-- `rule Instr_ok/nop: C |- NOP : eps -> eps`. -/
  -- core-rule: Instr_ok/nop
  | nop {C : Context} : Instr_ok C .nop ⟨[], [], []⟩
  /-- `rule Instr_ok/unreachable: C |- UNREACHABLE : t_1* -> t_2*
      -- Instrtype_ok: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic: `t_1*` and `t_2*` are free. -/
  -- core-rule: Instr_ok/unreachable
  | unreachable {C : Context} {ts₁ ts₂ : List ValType} :
      Instrtype_ok C ⟨ts₁, [], ts₂⟩ → Instr_ok C .unreachable ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_ok/drop: C |- DROP : t -> eps -- Valtype_ok: C |- t : OK`. -/
  -- core-rule: Instr_ok/drop
  | drop {C : Context} {t : ValType} : Valtype_ok C t → Instr_ok C .drop ⟨[t], [], []⟩
  /-- `rule Instr_ok/select-expl: C |- SELECT t : t t I32 -> t
      -- Valtype_ok: C |- t : OK`. -/
  -- core-rule: Instr_ok/select-expl
  | select_expl {C : Context} {t : ValType} :
      Valtype_ok C t →
      Instr_ok C (.select (some [t])) ⟨[t, t, ValType.i32], [], [t]⟩
  /-- `rule Instr_ok/select-impl:
        C |- SELECT : t t I32 -> t
        -- Valtype_ok: C |- t : OK
        -- Valtype_sub: C |- t <: t'
        -- if t' = numtype \/ t' = vectype`. -/
  -- core-rule: Instr_ok/select-impl
  | select_impl {C : Context} {t t' : ValType} :
      Valtype_ok C t → Valtype_sub C t t' → t'.isNumOrVec = true →
      Instr_ok C (.select none) ⟨[t, t, ValType.i32], [], [t]⟩

  -- Block instructions
  /-- `rule Instr_ok/block:
        C |- BLOCK bt instr* : t_1* -> t_2*
        -- Blocktype_ok: C |- bt : t_1* -> t_2*
        -- Instrs_ok: {LABELS (t_2*)} ++ C |- instr* : t_1* ->_(x*) t_2*`. -/
  -- core-rule: Instr_ok/block
  | block {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_ok C (.block bt body) ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_ok/loop:
        C |- LOOP bt instr* : t_1* -> t_2*
        -- Blocktype_ok: C |- bt : t_1* -> t_2*
        -- Instrs_ok: {LABELS (t_1*)} ++ C |- instr* : t_1* ->_(x*) t_2*`.

  The loop's label carries the block's ARGUMENTS, not its results. -/
  -- core-rule: Instr_ok/loop
  | loop {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok (Context.pushLabel ts₁ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_ok C (.loop bt body) ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_ok/if:
        C |- IF bt instr_1* ELSE instr_2* : t_1* I32 -> t_2*
        -- Blocktype_ok: C |- bt : t_1* -> t_2*
        -- Instrs_ok: {LABELS (t_2*)} ++ C |- instr_1* : t_1* ->_(x_1*) t_2*
        -- Instrs_ok: {LABELS (t_2*)} ++ C |- instr_2* : t_1* ->_(x_2*) t_2*`. -/
  -- core-rule: Instr_ok/if
  | if_ {C : Context} {bt : BlockType} {thn els : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok (Context.pushLabel ts₂ C) (InstrSeq.toList thn) ⟨ts₁, xs₁, ts₂⟩ →
      Instrs_ok (Context.pushLabel ts₂ C) (InstrSeq.toList els) ⟨ts₁, xs₂, ts₂⟩ →
      Instr_ok C (.ifElse bt thn els) ⟨ts₁ ++ [ValType.i32], [], ts₂⟩

  -- Branch instructions
  /-- `rule Instr_ok/br:
        C |- BR l : t_1* t* -> t_2*
        -- if C.LABELS[l] = t*
        -- Instrtype_ok: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic in `t_1*` and `t_2*`. -/
  -- core-rule: Instr_ok/br
  | br {C : Context} {l : LabelIdx} {ts ts₁ ts₂ : List ValType} :
      C.labels[l.val]? = some ts →
      Instrtype_ok C ⟨ts₁, [], ts₂⟩ →
      Instr_ok C (.br l) ⟨ts₁ ++ ts, [], ts₂⟩
  /-- `rule Instr_ok/br_if: C |- BR_IF l : t* I32 -> t* -- if C.LABELS[l] = t*`. -/
  -- core-rule: Instr_ok/br_if
  | br_if {C : Context} {l : LabelIdx} {ts : List ValType} :
      C.labels[l.val]? = some ts →
      Instr_ok C (.brIf l) ⟨ts ++ [ValType.i32], [], ts⟩
  /-- `rule Instr_ok/br_table:
        C |- BR_TABLE l* l' : t_1* t* I32 -> t_2*
        -- (Resulttype_sub: C |- t* <: C.LABELS[l])*
        -- Resulttype_sub: C |- t* <: C.LABELS[l']
        -- Instrtype_ok: C |- t_1* t* I32 -> t_2* : OK`. -/
  -- core-rule: Instr_ok/br_table
  | br_table {C : Context} {ls : List LabelIdx} {l' : LabelIdx}
      {ts ts₁ ts₂ ts'' : List ValType} :
      SeqAll (fun (l : LabelIdx) =>
          ∃ ts', C.labels[l.val]? = some ts' ∧ Resulttype_sub C ts ts') ls →
      C.labels[l'.val]? = some ts'' → Resulttype_sub C ts ts'' →
      Instrtype_ok C ⟨ts₁ ++ ts ++ [ValType.i32], [], ts₂⟩ →
      Instr_ok C (.brTable ls l') ⟨ts₁ ++ ts ++ [ValType.i32], [], ts₂⟩
  /-- `rule Instr_ok/br_on_null:
        C |- BR_ON_NULL l : t* (REF NULL ht) -> t* (REF ht)
        -- if C.LABELS[l] = t*
        -- Heaptype_ok: C |- ht : OK`. -/
  -- core-rule: Instr_ok/br_on_null
  | br_on_null {C : Context} {l : LabelIdx} {ts : List ValType} {ht : HeapType} :
      C.labels[l.val]? = some ts → Heaptype_ok C ht →
      Instr_ok C (.brOnNull l)
        ⟨ts ++ [.ref (.ref (some .null) ht)], [], ts ++ [.ref (.ref none ht)]⟩
  /-- `rule Instr_ok/br_on_non_null:
        C |- BR_ON_NON_NULL l : t* (REF NULL ht) -> t*
        -- if C.LABELS[l] = t* (REF NULL? ht)`. -/
  -- core-rule: Instr_ok/br_on_non_null
  | br_on_non_null {C : Context} {l : LabelIdx} {ts : List ValType}
      {nul : Option Null} {ht : HeapType} :
      C.labels[l.val]? = some (ts ++ [.ref (.ref nul ht)]) →
      Instr_ok C (.brOnNonNull l) ⟨ts ++ [.ref (.ref (some .null) ht)], [], ts⟩
  /-- `rule Instr_ok/br_on_cast:
        C |- BR_ON_CAST l rt_1 rt_2 : t* rt_1 -> t* ($diffrt(rt_1, rt_2))
        -- if C.LABELS[l] = t* rt
        -- Reftype_ok: C |- rt_1 : OK
        -- Reftype_ok: C |- rt_2 : OK
        -- Reftype_sub: C |- rt_2 <: rt_1
        -- Reftype_sub: C |- rt_2 <: rt`. -/
  -- core-rule: Instr_ok/br_on_cast
  | br_on_cast {C : Context} {l : LabelIdx} {rt₁ rt₂ rt : RefType} {ts : List ValType} :
      C.labels[l.val]? = some (ts ++ [.ref rt]) →
      Reftype_ok C rt₁ → Reftype_ok C rt₂ →
      Reftype_sub C rt₂ rt₁ → Reftype_sub C rt₂ rt →
      Instr_ok C (.brOnCast l rt₁ rt₂)
        ⟨ts ++ [.ref rt₁], [], ts ++ [.ref (RefType.diff rt₁ rt₂)]⟩
  /-- `rule Instr_ok/br_on_cast_fail:
        C |- BR_ON_CAST_FAIL l rt_1 rt_2 : t* rt_1 -> t* rt_2
        -- if C.LABELS[l] = t* rt
        -- Reftype_ok: C |- rt_1 : OK
        -- Reftype_ok: C |- rt_2 : OK
        -- Reftype_sub: C |- rt_2 <: rt_1
        -- Reftype_sub: C |- $diffrt(rt_1, rt_2) <: rt`. -/
  -- core-rule: Instr_ok/br_on_cast_fail
  | br_on_cast_fail {C : Context} {l : LabelIdx} {rt₁ rt₂ rt : RefType}
      {ts : List ValType} :
      C.labels[l.val]? = some (ts ++ [.ref rt]) →
      Reftype_ok C rt₁ → Reftype_ok C rt₂ →
      Reftype_sub C rt₂ rt₁ → Reftype_sub C (RefType.diff rt₁ rt₂) rt →
      Instr_ok C (.brOnCastFail l rt₁ rt₂) ⟨ts ++ [.ref rt₁], [], ts ++ [.ref rt₂]⟩

  -- Function instructions
  /-- `rule Instr_ok/call: C |- CALL x : t_1* -> t_2*
      -- Expand: C.FUNCS[x] ~~ FUNC t_1* -> t_2*`. -/
  -- core-rule: Instr_ok/call
  | call {C : Context} {x : FuncIdx} {dt : DefType} {dom cod : ValTypes} :
      C.funcs[x.val]? = some dt → Expand dt (.func dom cod) →
      Instr_ok C (.call x) ⟨ValTypes.toList dom, [], ValTypes.toList cod⟩
  /-- `rule Instr_ok/call_ref:
        C |- CALL_REF (_IDX x) : t_1* (REF NULL (_IDX x)) -> t_2*
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*`. -/
  -- core-rule: Instr_ok/call_ref
  | call_ref {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      Instr_ok C (.callRef (.idx x))
        ⟨ValTypes.toList dom ++ [.ref (.ref (some .null) (.use (.idx x)))], [],
         ValTypes.toList cod⟩
  /-- `rule Instr_ok/call_indirect:
        C |- CALL_INDIRECT x (_IDX y) : t_1* at -> t_2*
        -- if C.TABLES[x] = at lim rt
        -- Reftype_sub: C |- rt <: (REF NULL FUNC)
        -- Expand: C.TYPES[y] ~~ FUNC t_1* -> t_2*`. -/
  -- core-rule: Instr_ok/call_indirect
  | call_indirect {C : Context} {x : TableIdx} {y : TypeIdx} {tt : TableType}
      {dt : DefType} {dom cod : ValTypes} :
      C.tables[x.val]? = some tt →
      Reftype_sub C tt.elem RefType.funcref →
      C.types[y.val]? = some dt → Expand dt (.func dom cod) →
      Instr_ok C (.callIndirect x (.idx y))
        ⟨ValTypes.toList dom ++ [tt.addr.toValType], [], ValTypes.toList cod⟩
  /-- `rule Instr_ok/return:
        C |- RETURN : t_1* t* -> t_2*
        -- if C.RETURN = (t*)
        -- Instrtype_ok: C |- t_1* -> t_2* : OK`. -/
  -- core-rule: Instr_ok/return
  | ret {C : Context} {ts ts₁ ts₂ : List ValType} :
      C.ret = some ts → Instrtype_ok C ⟨ts₁, [], ts₂⟩ →
      Instr_ok C .ret ⟨ts₁ ++ ts, [], ts₂⟩
  /-- `rule Instr_ok/return_call:
        C |- RETURN_CALL x : t_3* t_1* -> t_4*
        -- Expand: C.FUNCS[x] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_sub: C |- t_2* <: t'_2*
        -- Instrtype_ok: C |- t_3* -> t_4* : OK`. -/
  -- core-rule: Instr_ok/return_call
  | return_call {C : Context} {x : FuncIdx} {dt : DefType} {dom cod : ValTypes}
      {ts₂' ts₃ ts₄ : List ValType} :
      C.funcs[x.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_sub C (ValTypes.toList cod) ts₂' →
      Instrtype_ok C ⟨ts₃, [], ts₄⟩ →
      Instr_ok C (.returnCall x) ⟨ts₃ ++ ValTypes.toList dom, [], ts₄⟩
  /-- `rule Instr_ok/return_call_ref:
        C |- RETURN_CALL_REF (_IDX x) : t_3* t_1* (REF NULL (_IDX x)) -> t_4*
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_sub: C |- t_2* <: t'_2*
        -- Instrtype_ok: C |- t_3* -> t_4* : OK`. -/
  -- core-rule: Instr_ok/return_call_ref
  | return_call_ref {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes}
      {ts₂' ts₃ ts₄ : List ValType} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_sub C (ValTypes.toList cod) ts₂' →
      Instrtype_ok C ⟨ts₃, [], ts₄⟩ →
      Instr_ok C (.returnCallRef (.idx x))
        ⟨ts₃ ++ ValTypes.toList dom ++ [.ref (.ref (some .null) (.use (.idx x)))], [], ts₄⟩
  /-- `rule Instr_ok/return_call_indirect:
        C |- RETURN_CALL_INDIRECT x (_IDX y) : t_3* t_1* at -> t_4*
        -- if C.TABLES[x] = at lim rt
        -- Reftype_sub: C |- rt <: (REF NULL FUNC)
        -- Expand: C.TYPES[y] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_sub: C |- t_2* <: t'_2*
        -- Instrtype_ok: C |- t_3* -> t_4* : OK`. -/
  -- core-rule: Instr_ok/return_call_indirect
  | return_call_indirect {C : Context} {x : TableIdx} {y : TypeIdx} {tt : TableType}
      {dt : DefType} {dom cod : ValTypes} {ts₂' ts₃ ts₄ : List ValType} :
      C.tables[x.val]? = some tt →
      Reftype_sub C tt.elem RefType.funcref →
      C.types[y.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_sub C (ValTypes.toList cod) ts₂' →
      Instrtype_ok C ⟨ts₃, [], ts₄⟩ →
      Instr_ok C (.returnCallIndirect x (.idx y))
        ⟨ts₃ ++ ValTypes.toList dom ++ [tt.addr.toValType], [], ts₄⟩

  -- Exception instructions
  /-- `rule Instr_ok/throw:
        C |- THROW x : t_1* t* -> t_2*
        -- Expand: $as_deftype(C.TAGS[x]) ~~ FUNC t* -> eps
        -- Instrtype_ok: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic in `t_1*` and `t_2*`. -/
  -- core-rule: Instr_ok/throw
  | throw_ {C : Context} {x : TagIdx} {jt : TagType} {dt : DefType} {dom : ValTypes}
      {ts₁ ts₂ : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) →
      Instrtype_ok C ⟨ts₁, [], ts₂⟩ →
      Instr_ok C (.throw x) ⟨ts₁ ++ ValTypes.toList dom, [], ts₂⟩
  /-- `rule Instr_ok/throw_ref:
        C |- THROW_REF : t_1* (REF NULL EXN) -> t_2*
        -- Instrtype_ok: C |- t_1* -> t_2* : OK`. -/
  -- core-rule: Instr_ok/throw_ref
  | throw_ref {C : Context} {ts₁ ts₂ : List ValType} :
      Instrtype_ok C ⟨ts₁, [], ts₂⟩ →
      Instr_ok C .throwRef
        ⟨ts₁ ++ [.ref (.ref (some .null) (.abs .exn))], [], ts₂⟩
  /-- `rule Instr_ok/try_table:
        C |- TRY_TABLE bt catch* instr* : t_1* -> t_2*
        -- Blocktype_ok: C |- bt : t_1* -> t_2*
        -- Instrs_ok: {LABELS (t_2*)} ++ C |- instr* : t_1* ->_(x*) t_2*
        -- (Catch_ok: C |- catch : OK)*`. -/
  -- core-rule: Instr_ok/try_table
  | try_table {C : Context} {bt : BlockType} {cs : List_ Catch} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_ok C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_ok (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      SeqAll (Catch_ok C) cs.val →
      Instr_ok C (.tryTable bt cs body) ⟨ts₁, [], ts₂⟩

  -- Reference instructions
  /-- `rule Instr_ok/ref.null: C |- REF.NULL ht : eps -> (REF NULL ht)
      -- Heaptype_ok: C |- ht : OK`. -/
  -- core-rule: Instr_ok/ref.null
  | ref_null {C : Context} {ht : HeapType} :
      Heaptype_ok C ht →
      Instr_ok C (.refNull ht) ⟨[], [], [.ref (.ref (some .null) ht)]⟩
  /-- `rule Instr_ok/ref.func: C |- REF.FUNC x : eps -> (REF dt)
      -- if C.FUNCS[x] = dt -- if x <- C.REFS`. -/
  -- core-rule: Instr_ok/ref.func
  | ref_func {C : Context} {x : FuncIdx} {dt : DefType} :
      C.funcs[x.val]? = some dt → x ∈ C.refs →
      Instr_ok C (.refFunc x) ⟨[], [], [.ref (.ref none (.use (.defd dt)))]⟩
  /-- `rule Instr_ok/ref.i31: C |- REF.I31 : I32 -> (REF I31)`. -/
  -- core-rule: Instr_ok/ref.i31
  | ref_i31 {C : Context} :
      Instr_ok C .refI31 ⟨[ValType.i32], [], [.ref (.ref none (.abs .i31))]⟩
  /-- `rule Instr_ok/ref.is_null: C |- REF.IS_NULL : (REF NULL ht) -> I32
      -- Heaptype_ok: C |- ht : OK`. -/
  -- core-rule: Instr_ok/ref.is_null
  | ref_is_null {C : Context} {ht : HeapType} :
      Heaptype_ok C ht →
      Instr_ok C .refIsNull ⟨[.ref (.ref (some .null) ht)], [], [ValType.i32]⟩
  /-- `rule Instr_ok/ref.as_non_null: C |- REF.AS_NON_NULL : (REF NULL ht) -> (REF ht)
      -- Heaptype_ok: C |- ht : OK`. -/
  -- core-rule: Instr_ok/ref.as_non_null
  | ref_as_non_null {C : Context} {ht : HeapType} :
      Heaptype_ok C ht →
      Instr_ok C .refAsNonNull
        ⟨[.ref (.ref (some .null) ht)], [], [.ref (.ref none ht)]⟩
  /-- `rule Instr_ok/ref.eq: C |- REF.EQ : (REF NULL EQ) (REF NULL EQ) -> I32`. -/
  -- core-rule: Instr_ok/ref.eq
  | ref_eq {C : Context} :
      Instr_ok C .refEq
        ⟨[.ref RefType.eqref, .ref RefType.eqref], [], [ValType.i32]⟩
  /-- `rule Instr_ok/ref.test:
        C |- REF.TEST rt : rt' -> I32
        -- Reftype_ok: C |- rt : OK
        -- Reftype_ok: C |- rt' : OK
        -- Reftype_sub: C |- rt <: rt'`. -/
  -- core-rule: Instr_ok/ref.test
  | ref_test {C : Context} {rt rt' : RefType} :
      Reftype_ok C rt → Reftype_ok C rt' → Reftype_sub C rt rt' →
      Instr_ok C (.refTest rt) ⟨[.ref rt'], [], [ValType.i32]⟩
  /-- `rule Instr_ok/ref.cast:
        C |- REF.CAST rt : rt' -> rt
        -- Reftype_ok: C |- rt : OK
        -- Reftype_ok: C |- rt' : OK
        -- Reftype_sub: C |- rt <: rt'`. -/
  -- core-rule: Instr_ok/ref.cast
  | ref_cast {C : Context} {rt rt' : RefType} :
      Reftype_ok C rt → Reftype_ok C rt' → Reftype_sub C rt rt' →
      Instr_ok C (.refCast rt) ⟨[.ref rt'], [], [.ref rt]⟩

  -- Scalar reference instructions
  /-- `rule Instr_ok/i31.get: C |- I31.GET sx : (REF NULL I31) -> I32`. -/
  -- core-rule: Instr_ok/i31.get
  | i31_get {C : Context} {sx : Sx} :
      Instr_ok C (.i31Get sx) ⟨[.ref RefType.i31ref], [], [ValType.i32]⟩

  -- Structure instructions
  /-- `rule Instr_ok/struct.new: C |- STRUCT.NEW x : $unpack(zt)* -> (REF (_IDX x))
      -- Expand: C.TYPES[x] ~~ STRUCT (mut? zt)*`. -/
  -- core-rule: Instr_ok/struct.new
  | struct_new {C : Context} {x : TypeIdx} {dt : DefType} {fts : FieldTypes} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      Instr_ok C (.structNew x)
        ⟨fts.unpacked, [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/struct.new_default:
        C |- STRUCT.NEW_DEFAULT x : eps -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ STRUCT (mut? zt)*
        -- (Defaultable: |- $unpack(zt) DEFAULTABLE)*`. -/
  -- core-rule: Instr_ok/struct.new_default
  | struct_new_default {C : Context} {x : TypeIdx} {dt : DefType} {fts : FieldTypes} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      SeqAll Defaultable fts.unpacked →
      Instr_ok C (.structNewDefault x) ⟨[], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/struct.get:
        C |- STRUCT.GET sx? x i : (REF NULL (_IDX x)) -> $unpack(zt)
        -- Expand: C.TYPES[x] ~~ STRUCT ft*
        -- if ft*[i] = mut? zt
        -- if sx? = eps <=> $is_packtype(zt)`

  See `StorageType.isUnpacked` for what the source's `$is_packtype` actually
  computes. -/
  -- core-rule: Instr_ok/struct.get
  | struct_get {C : Context} {sx : Option Sx} {x : TypeIdx} {i : U32}
      {dt : DefType} {fts : FieldTypes} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      (FieldTypes.toList fts)[i.val]? = some ft →
      ((sx = none) ↔ StorageType.isUnpacked ft.storage = true) →
      Instr_ok C (.structGet sx x i)
        ⟨[.ref (.ref (some .null) (.use (.idx x)))], [],
         [StorageType.unpack ft.storage]⟩
  /-- `rule Instr_ok/struct.set:
        C |- STRUCT.SET x i : (REF NULL (_IDX x)) $unpack(zt) -> eps
        -- Expand: C.TYPES[x] ~~ STRUCT ft*
        -- if ft*[i] = MUT zt`. -/
  -- core-rule: Instr_ok/struct.set
  | struct_set {C : Context} {x : TypeIdx} {i : U32} {dt : DefType}
      {fts : FieldTypes} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      (FieldTypes.toList fts)[i.val]? = some (.mk (some .mut) zt) →
      Instr_ok C (.structSet x i)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), StorageType.unpack zt], [], []⟩

  -- Array instructions
  /-- `rule Instr_ok/array.new: C |- ARRAY.NEW x : $unpack(zt) I32 -> (REF (_IDX x))
      -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)`. -/
  -- core-rule: Instr_ok/array.new
  | array_new {C : Context} {x : TypeIdx} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Instr_ok C (.arrayNew x)
        ⟨[StorageType.unpack ft.storage, ValType.i32], [],
         [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/array.new_default:
        C |- ARRAY.NEW_DEFAULT x : I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- Defaultable: |- $unpack(zt) DEFAULTABLE`. -/
  -- core-rule: Instr_ok/array.new_default
  | array_new_default {C : Context} {x : TypeIdx} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Defaultable (StorageType.unpack ft.storage) →
      Instr_ok C (.arrayNewDefault x)
        ⟨[ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/array.new_fixed:
        C |- ARRAY.NEW_FIXED x n : $unpack(zt)^n -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)`. -/
  -- core-rule: Instr_ok/array.new_fixed
  | array_new_fixed {C : Context} {x : TypeIdx} {n : U32} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Instr_ok C (.arrayNewFixed x n)
        ⟨List.replicate n.val (StorageType.unpack ft.storage), [],
         [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/array.new_elem:
        C |- ARRAY.NEW_ELEM x y : I32 I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? rt)
        -- Reftype_sub: C |- C.ELEMS[y] <: rt`

  The array's storage type is matched as a `reftype`, so the rule applies only
  to arrays of references. -/
  -- core-rule: Instr_ok/array.new_elem
  | array_new_elem {C : Context} {x : TypeIdx} {y : ElemIdx} {dt : DefType}
      {m : Option Mut} {rt rt' : RefType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk m (.val (.ref rt)))) →
      C.elems[y.val]? = some rt' → Reftype_sub C rt' rt →
      Instr_ok C (.arrayNewElem x y)
        ⟨[ValType.i32, ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/array.new_data:
        C |- ARRAY.NEW_DATA x y : I32 I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- if $unpack(zt) = numtype \/ $unpack(zt) = vectype
        -- if C.DATAS[y] = OK`. -/
  -- core-rule: Instr_ok/array.new_data
  | array_new_data {C : Context} {x : TypeIdx} {y : DataIdx} {dt : DefType}
      {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      (StorageType.unpack ft.storage).isNumOrVec = true →
      C.datas[y.val]? = some .ok →
      Instr_ok C (.arrayNewData x y)
        ⟨[ValType.i32, ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_ok/array.get:
        C |- ARRAY.GET sx? x : (REF NULL (_IDX x)) I32 -> $unpack(zt)
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- if sx? = eps <=> $is_packtype(zt)`. -/
  -- core-rule: Instr_ok/array.get
  | array_get {C : Context} {sx : Option Sx} {x : TypeIdx} {dt : DefType}
      {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      ((sx = none) ↔ StorageType.isUnpacked ft.storage = true) →
      Instr_ok C (.arrayGet sx x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32], [],
         [StorageType.unpack ft.storage]⟩
  /-- `rule Instr_ok/array.set:
        C |- ARRAY.SET x : (REF NULL (_IDX x)) I32 $unpack(zt) -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)`. -/
  -- core-rule: Instr_ok/array.set
  | array_set {C : Context} {x : TypeIdx} {dt : DefType} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      Instr_ok C (.arraySet x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
          StorageType.unpack zt], [], []⟩
  /-- `rule Instr_ok/array.len: C |- ARRAY.LEN : (REF NULL ARRAY) -> I32`. -/
  -- core-rule: Instr_ok/array.len
  | array_len {C : Context} :
      Instr_ok C .arrayLen ⟨[.ref RefType.arrayref], [], [ValType.i32]⟩
  /-- `rule Instr_ok/array.fill:
        C |- ARRAY.FILL x : (REF NULL (_IDX x)) I32 $unpack(zt) I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)`. -/
  -- core-rule: Instr_ok/array.fill
  | array_fill {C : Context} {x : TypeIdx} {dt : DefType} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      Instr_ok C (.arrayFill x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
          StorageType.unpack zt, ValType.i32], [], []⟩
  /-- `rule Instr_ok/array.copy:
        C |- ARRAY.COPY x_1 x_2 :
          (REF NULL (_IDX x_1)) I32 (REF NULL (_IDX x_2)) I32 I32 -> eps
        -- Expand: C.TYPES[x_1] ~~ ARRAY (MUT zt_1)
        -- Expand: C.TYPES[x_2] ~~ ARRAY (mut? zt_2)
        -- Storagetype_sub: C |- zt_2 <: zt_1`. -/
  -- core-rule: Instr_ok/array.copy
  | array_copy {C : Context} {x₁ x₂ : TypeIdx} {dt₁ dt₂ : DefType}
      {zt₁ zt₂ : StorageType} {m : Option Mut} :
      C.types[x₁.val]? = some dt₁ → Expand dt₁ (.array (.mk (some .mut) zt₁)) →
      C.types[x₂.val]? = some dt₂ → Expand dt₂ (.array (.mk m zt₂)) →
      Storagetype_sub C zt₂ zt₁ →
      Instr_ok C (.arrayCopy x₁ x₂)
        ⟨[.ref (.ref (some .null) (.use (.idx x₁))), ValType.i32,
          .ref (.ref (some .null) (.use (.idx x₂))), ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_ok/array.init_elem:
        C |- ARRAY.INIT_ELEM x y : (REF NULL (_IDX x)) I32 I32 I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)
        -- Storagetype_sub: C |- C.ELEMS[y] <: zt`. -/
  -- core-rule: Instr_ok/array.init_elem
  | array_init_elem {C : Context} {x : TypeIdx} {y : ElemIdx} {dt : DefType}
      {zt : StorageType} {rt : RefType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      C.elems[y.val]? = some rt → Storagetype_sub C (.val (.ref rt)) zt →
      Instr_ok C (.arrayInitElem x y)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32, ValType.i32,
          ValType.i32], [], []⟩
  /-- `rule Instr_ok/array.init_data:
        C |- ARRAY.INIT_DATA x y : (REF NULL (_IDX x)) I32 I32 I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)
        -- if $unpack(zt) = numtype \/ $unpack(zt) = vectype
        -- if C.DATAS[y] = OK`. -/
  -- core-rule: Instr_ok/array.init_data
  | array_init_data {C : Context} {x : TypeIdx} {y : DataIdx} {dt : DefType}
      {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      (StorageType.unpack zt).isNumOrVec = true →
      C.datas[y.val]? = some .ok →
      Instr_ok C (.arrayInitData x y)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32, ValType.i32,
          ValType.i32], [], []⟩

  -- External reference instructions
  /-- `rule Instr_ok/extern.convert_any:
        C |- EXTERN.CONVERT_ANY : (REF null_1? ANY) -> (REF null_2? EXTERN)
        -- if null_1? = null_2?`. -/
  -- core-rule: Instr_ok/extern.convert_any
  | extern_convert_any {C : Context} {nul : Option Null} :
      Instr_ok C .externConvertAny
        ⟨[.ref (.ref nul (.abs .any))], [], [.ref (.ref nul (.abs .extern))]⟩
  /-- `rule Instr_ok/any.convert_extern:
        C |- ANY.CONVERT_EXTERN : (REF null_1? EXTERN) -> (REF null_2? ANY)
        -- if null_1? = null_2?`. -/
  -- core-rule: Instr_ok/any.convert_extern
  | any_convert_extern {C : Context} {nul : Option Null} :
      Instr_ok C .anyConvertExtern
        ⟨[.ref (.ref nul (.abs .extern))], [], [.ref (.ref nul (.abs .any))]⟩

  -- Local instructions
  /-- `rule Instr_ok/local.get: C |- LOCAL.GET x : eps -> t
      -- if C.LOCALS[x] = SET t`. -/
  -- core-rule: Instr_ok/local.get
  | local_get {C : Context} {x : LocalIdx} {t : ValType} :
      C.locals[x.val]? = some ⟨.set, t⟩ → Instr_ok C (.localGet x) ⟨[], [], [t]⟩
  /-- `rule Instr_ok/local.set: C |- LOCAL.SET x : t ->_(x) eps
      -- if C.LOCALS[x] = init t`. -/
  -- core-rule: Instr_ok/local.set
  | local_set {C : Context} {x : LocalIdx} {ini : Init} {t : ValType} :
      C.locals[x.val]? = some ⟨ini, t⟩ → Instr_ok C (.localSet x) ⟨[t], [x], []⟩
  /-- `rule Instr_ok/local.tee: C |- LOCAL.TEE x : t ->_(x) t
      -- if C.LOCALS[x] = init t`. -/
  -- core-rule: Instr_ok/local.tee
  | local_tee {C : Context} {x : LocalIdx} {ini : Init} {t : ValType} :
      C.locals[x.val]? = some ⟨ini, t⟩ → Instr_ok C (.localTee x) ⟨[t], [x], [t]⟩

  -- Global instructions
  /-- `rule Instr_ok/global.get: C |- GLOBAL.GET x : eps -> t
      -- if C.GLOBALS[x] = mut? t`. -/
  -- core-rule: Instr_ok/global.get
  | global_get {C : Context} {x : GlobalIdx} {m : Option Mut} {t : ValType} :
      C.globals[x.val]? = some ⟨m, t⟩ → Instr_ok C (.globalGet x) ⟨[], [], [t]⟩
  /-- `rule Instr_ok/global.set: C |- GLOBAL.SET x : t -> eps
      -- if C.GLOBALS[x] = MUT t`. -/
  -- core-rule: Instr_ok/global.set
  | global_set {C : Context} {x : GlobalIdx} {t : ValType} :
      C.globals[x.val]? = some ⟨some .mut, t⟩ → Instr_ok C (.globalSet x) ⟨[t], [], []⟩

  -- Table instructions
  /-- `rule Instr_ok/table.get: C |- TABLE.GET x : at -> rt
      -- if C.TABLES[x] = at lim rt`. -/
  -- core-rule: Instr_ok/table.get
  | table_get {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_ok C (.tableGet x) ⟨[tt.addr.toValType], [], [.ref tt.elem]⟩
  /-- `rule Instr_ok/table.set: C |- TABLE.SET x : at rt -> eps
      -- if C.TABLES[x] = at lim rt`. -/
  -- core-rule: Instr_ok/table.set
  | table_set {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_ok C (.tableSet x) ⟨[tt.addr.toValType, .ref tt.elem], [], []⟩
  /-- `rule Instr_ok/table.size: C |- TABLE.SIZE x : eps -> at
      -- if C.TABLES[x] = at lim rt`. -/
  -- core-rule: Instr_ok/table.size
  | table_size {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_ok C (.tableSize x) ⟨[], [], [tt.addr.toValType]⟩
  /-- `rule Instr_ok/table.grow: C |- TABLE.GROW x : rt at -> I32
      -- if C.TABLES[x] = at lim rt`. -/
  -- core-rule: Instr_ok/table.grow
  | table_grow {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_ok C (.tableGrow x)
        ⟨[.ref tt.elem, tt.addr.toValType], [], [ValType.i32]⟩
  /-- `rule Instr_ok/table.fill: C |- TABLE.FILL x : at rt at -> eps
      -- if C.TABLES[x] = at lim rt`. -/
  -- core-rule: Instr_ok/table.fill
  | table_fill {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_ok C (.tableFill x)
        ⟨[tt.addr.toValType, .ref tt.elem, tt.addr.toValType], [], []⟩
  /-- `rule Instr_ok/table.copy:
        C |- TABLE.COPY x_1 x_2 : at_1 at_2 $minat(at_1, at_2) -> eps
        -- if C.TABLES[x_1] = at_1 lim_1 rt_1
        -- if C.TABLES[x_2] = at_2 lim_2 rt_2
        -- Reftype_sub: C |- rt_2 <: rt_1`. -/
  -- core-rule: Instr_ok/table.copy
  | table_copy {C : Context} {x₁ x₂ : TableIdx} {tt₁ tt₂ : TableType} :
      C.tables[x₁.val]? = some tt₁ → C.tables[x₂.val]? = some tt₂ →
      Reftype_sub C tt₂.elem tt₁.elem →
      Instr_ok C (.tableCopy x₁ x₂)
        ⟨[tt₁.addr.toValType, tt₂.addr.toValType,
          (AddrType.min tt₁.addr tt₂.addr).toValType], [], []⟩
  /-- `rule Instr_ok/table.init:
        C |- TABLE.INIT x y : at I32 I32 -> eps
        -- if C.TABLES[x] = at lim rt_1
        -- if C.ELEMS[y] = rt_2
        -- Reftype_sub: C |- rt_2 <: rt_1`. -/
  -- core-rule: Instr_ok/table.init
  | table_init {C : Context} {x : TableIdx} {y : ElemIdx} {tt : TableType}
      {rt₂ : RefType} :
      C.tables[x.val]? = some tt → C.elems[y.val]? = some rt₂ →
      Reftype_sub C rt₂ tt.elem →
      Instr_ok C (.tableInit x y)
        ⟨[tt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_ok/elem.drop: C |- ELEM.DROP x : eps -> eps
      -- if C.ELEMS[x] = rt`. -/
  -- core-rule: Instr_ok/elem.drop
  | elem_drop {C : Context} {x : ElemIdx} {rt : RefType} :
      C.elems[x.val]? = some rt → Instr_ok C (.elemDrop x) ⟨[], [], []⟩

  -- Memory instructions
  /-- `rule Instr_ok/memory.size: C |- MEMORY.SIZE x : eps -> at
      -- if C.MEMS[x] = at lim PAGE`. -/
  -- core-rule: Instr_ok/memory.size
  | memory_size {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_ok C (.memorySize x) ⟨[], [], [mt.addr.toValType]⟩
  /-- `rule Instr_ok/memory.grow: C |- MEMORY.GROW x : at -> at
      -- if C.MEMS[x] = at lim PAGE`. -/
  -- core-rule: Instr_ok/memory.grow
  | memory_grow {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_ok C (.memoryGrow x) ⟨[mt.addr.toValType], [], [mt.addr.toValType]⟩
  /-- `rule Instr_ok/memory.fill: C |- MEMORY.FILL x : at I32 at -> eps
      -- if C.MEMS[x] = at lim PAGE`. -/
  -- core-rule: Instr_ok/memory.fill
  | memory_fill {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_ok C (.memoryFill x)
        ⟨[mt.addr.toValType, ValType.i32, mt.addr.toValType], [], []⟩
  /-- `rule Instr_ok/memory.copy:
        C |- MEMORY.COPY x_1 x_2 : at_1 at_2 $minat(at_1, at_2) -> eps
        -- if C.MEMS[x_1] = at_1 lim_1 PAGE
        -- if C.MEMS[x_2] = at_2 lim_2 PAGE`. -/
  -- core-rule: Instr_ok/memory.copy
  | memory_copy {C : Context} {x₁ x₂ : MemIdx} {mt₁ mt₂ : MemType} :
      C.mems[x₁.val]? = some mt₁ → C.mems[x₂.val]? = some mt₂ →
      Instr_ok C (.memoryCopy x₁ x₂)
        ⟨[mt₁.addr.toValType, mt₂.addr.toValType,
          (AddrType.min mt₁.addr mt₂.addr).toValType], [], []⟩
  /-- `rule Instr_ok/memory.init:
        C |- MEMORY.INIT x y : at I32 I32 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if C.DATAS[y] = OK`. -/
  -- core-rule: Instr_ok/memory.init
  | memory_init {C : Context} {x : MemIdx} {y : DataIdx} {mt : MemType} :
      C.mems[x.val]? = some mt → C.datas[y.val]? = some .ok →
      Instr_ok C (.memoryInit x y)
        ⟨[mt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_ok/data.drop: C |- DATA.DROP x : eps -> eps
      -- if C.DATAS[x] = OK`. -/
  -- core-rule: Instr_ok/data.drop
  | data_drop {C : Context} {x : DataIdx} :
      C.datas[x.val]? = some .ok → Instr_ok C (.dataDrop x) ⟨[], [], []⟩
  /-- `rule Instr_ok/load:
        C |- LOAD nt (N _ sx)? x memarg : at -> nt
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)
        -- if $(2^(memarg.ALIGN) <= N/8 < $size(nt)/8)?
        -- if N? = eps \/ nt = Inn`

  COMMENTED OUT in the pinned source (`(; ... ;)`), superseded by the split
  `-val` / `-pack` rules below; transcribed because the text is there.  See the
  file header. -/
  | load {C : Context} {nt : NumType} {op : Option LoadOp} {x : MemIdx}
      {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      OptAll (fun (o : LoadOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op →
      (op = none ∨ nt.toInn?.isSome = true) →
      Instr_ok C (.load nt op x ao) ⟨[mt.addr.toValType], [], [.num nt]⟩
  /-- `rule Instr_ok/load-val:
        C |- LOAD nt x memarg : at -> nt
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)`. -/
  -- core-rule: Instr_ok/load-val
  | load_val {C : Context} {nt : NumType} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      Instr_ok C (.load nt none x ao) ⟨[mt.addr.toValType], [], [.num nt]⟩
  /-- `rule Instr_ok/load-pack:
        C |- LOAD Inn (M _ sx) x memarg : at -> Inn
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8)`. -/
  -- core-rule: Instr_ok/load-pack
  | load_pack {C : Context} {n : Inn} {op : LoadOp} {x : MemIdx} {ao : MemArg}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ op.sz.toNat / 8 →
      Instr_ok C (.load n.toNumType (some op) x ao)
        ⟨[mt.addr.toValType], [], [.num n.toNumType]⟩
  /-- `rule Instr_ok/store:
        C |- STORE nt N? x memarg : at nt -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)
        -- if $(2^(memarg.ALIGN) <= N/8 < $size(nt)/8)?
        -- if N? = eps \/ nt = Inn`

  COMMENTED OUT in the pinned source, as `Instr_ok/load` is. -/
  | store {C : Context} {nt : NumType} {op : Option StoreOp} {x : MemIdx}
      {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      OptAll (fun (o : StoreOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op →
      (op = none ∨ nt.toInn?.isSome = true) →
      Instr_ok C (.store nt op x ao) ⟨[mt.addr.toValType, .num nt], [], []⟩
  /-- `rule Instr_ok/store-val:
        C |- STORE nt x memarg : at nt -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)`. -/
  -- core-rule: Instr_ok/store-val
  | store_val {C : Context} {nt : NumType} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      Instr_ok C (.store nt none x ao) ⟨[mt.addr.toValType, .num nt], [], []⟩
  /-- `rule Instr_ok/store-pack:
        C |- STORE Inn M x memarg : at Inn -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8)`. -/
  -- core-rule: Instr_ok/store-pack
  | store_pack {C : Context} {n : Inn} {op : StoreOp} {x : MemIdx} {ao : MemArg}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ op.sz.toNat / 8 →
      Instr_ok C (.store n.toNumType (some op) x ao)
        ⟨[mt.addr.toValType, .num n.toNumType], [], []⟩
  /-- `rule Instr_ok/vload-val:
        C |- VLOAD V128 x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $vsize(V128)/8)`. -/
  -- core-rule: Instr_ok/vload-val
  | vload_val {C : Context} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ VecType.size .v128 / 8 →
      Instr_ok C (.vload .v128 none x ao) ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vload-pack:
        C |- VLOAD V128 (SHAPE M X N _ sx) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8 * N)`. -/
  -- core-rule: Instr_ok/vload-pack
  | vload_pack {C : Context} {sz : Sz} {n : Nat} {sx : Sx} {x : MemIdx}
      {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 * n →
      Instr_ok C (.vload .v128 (some (.shape sz n sx)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vload-splat:
        C |- VLOAD V128 (SPLAT N) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)`. -/
  -- core-rule: Instr_ok/vload-splat
  | vload_splat {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      Instr_ok C (.vload .v128 (some (.splat sz)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vload-zero:
        C |- VLOAD V128 (ZERO N) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)`. -/
  -- core-rule: Instr_ok/vload-zero
  | vload_zero {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      Instr_ok C (.vload .v128 (some (.zero sz)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vload_lane:
        C |- VLOAD_LANE V128 N x memarg i : at V128 -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)
        -- if $(i < 128/N)`. -/
  -- core-rule: Instr_ok/vload_lane
  | vload_lane {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {i : LaneIdx}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      i.val < 128 / sz.toNat →
      Instr_ok C (.vloadLane .v128 sz x ao i)
        ⟨[mt.addr.toValType, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vstore:
        C |- VSTORE V128 x memarg : at V128 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $vsize(V128)/8)`. -/
  -- core-rule: Instr_ok/vstore
  | vstore {C : Context} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ VecType.size .v128 / 8 →
      Instr_ok C (.vstore .v128 x ao) ⟨[mt.addr.toValType, ValType.v128], [], []⟩
  /-- `rule Instr_ok/vstore_lane:
        C |- VSTORE_LANE V128 N x memarg i : at V128 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)
        -- if $(i < 128/N)`. -/
  -- core-rule: Instr_ok/vstore_lane
  | vstore_lane {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {i : LaneIdx}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      i.val < 128 / sz.toNat →
      Instr_ok C (.vstoreLane .v128 sz x ao i)
        ⟨[mt.addr.toValType, ValType.v128], [], []⟩

  -- Numeric instructions
  /-- `rule Instr_ok/const: C |- CONST nt c_nt : eps -> nt`. -/
  -- core-rule: Instr_ok/const
  | const {C : Context} {nt : NumType} {c : Num_ nt} :
      Instr_ok C (.const nt c) ⟨[], [], [.num nt]⟩
  /-- `rule Instr_ok/unop: C |- UNOP nt unop_nt : nt -> nt`. -/
  -- core-rule: Instr_ok/unop
  | unop {C : Context} {nt : NumType} {op : Unop} :
      Instr_ok C (.unop nt op) ⟨[.num nt], [], [.num nt]⟩
  /-- `rule Instr_ok/binop: C |- BINOP nt binop_nt : nt nt -> nt`. -/
  -- core-rule: Instr_ok/binop
  | binop {C : Context} {nt : NumType} {op : Binop} :
      Instr_ok C (.binop nt op) ⟨[.num nt, .num nt], [], [.num nt]⟩
  /-- `rule Instr_ok/testop: C |- TESTOP nt testop_nt : nt -> I32`. -/
  -- core-rule: Instr_ok/testop
  | testop {C : Context} {nt : NumType} {op : Testop} :
      Instr_ok C (.testop nt op) ⟨[.num nt], [], [ValType.i32]⟩
  /-- `rule Instr_ok/relop: C |- RELOP nt relop_nt : nt nt -> I32`. -/
  -- core-rule: Instr_ok/relop
  | relop {C : Context} {nt : NumType} {op : Relop} :
      Instr_ok C (.relop nt op) ⟨[.num nt, .num nt], [], [ValType.i32]⟩
  /-- `rule Instr_ok/cvtop: C |- CVTOP nt_1 nt_2 cvtop : nt_2 -> nt_1`. -/
  -- core-rule: Instr_ok/cvtop
  | cvtop {C : Context} {nt₁ nt₂ : NumType} {op : Cvtop} :
      Instr_ok C (.cvtop nt₁ nt₂ op) ⟨[.num nt₂], [], [.num nt₁]⟩

  -- Vector instructions
  /-- `rule Instr_ok/vconst: C |- VCONST V128 c : eps -> V128`. -/
  -- core-rule: Instr_ok/vconst
  | vconst {C : Context} {c : VecLit (VecType.toVnn .v128)} :
      Instr_ok C (.vconst .v128 c) ⟨[], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vvunop: C |- VVUNOP V128 vvunop : V128 -> V128`. -/
  -- core-rule: Instr_ok/vvunop
  | vvunop {C : Context} {op : VVUnop} :
      Instr_ok C (.vvunop .v128 op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vvbinop: C |- VVBINOP V128 vvbinop : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vvbinop
  | vvbinop {C : Context} {op : VVBinop} :
      Instr_ok C (.vvbinop .v128 op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vvternop: C |- VVTERNOP V128 vvternop : V128 V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vvternop
  | vvternop {C : Context} {op : VVTernop} :
      Instr_ok C (.vvternop .v128 op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vvtestop: C |- VVTESTOP V128 vvtestop : V128 -> I32`. -/
  -- core-rule: Instr_ok/vvtestop
  | vvtestop {C : Context} {op : VVTestop} :
      Instr_ok C (.vvtestop .v128 op) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_ok/vunop: C |- VUNOP sh vunop : V128 -> V128`. -/
  -- core-rule: Instr_ok/vunop
  | vunop {C : Context} {sh : Shape} {op : VUnop} :
      Instr_ok C (.vunop sh op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vbinop: C |- VBINOP sh vbinop : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vbinop
  | vbinop {C : Context} {sh : Shape} {op : VBinop} :
      Instr_ok C (.vbinop sh op) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vternop: C |- VTERNOP sh vternop : V128 V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vternop
  | vternop {C : Context} {sh : Shape} {op : VTernop} :
      Instr_ok C (.vternop sh op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vtestop: C |- VTESTOP sh vtestop : V128 -> I32`. -/
  -- core-rule: Instr_ok/vtestop
  | vtestop {C : Context} {sh : Shape} {op : VTestop} :
      Instr_ok C (.vtestop sh op) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_ok/vrelop: C |- VRELOP sh vrelop : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vrelop
  | vrelop {C : Context} {sh : Shape} {op : VRelop} :
      Instr_ok C (.vrelop sh op) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vshiftop: C |- VSHIFTOP sh vshiftop : V128 I32 -> V128`. -/
  -- core-rule: Instr_ok/vshiftop
  | vshiftop {C : Context} {sh : IShape} {op : VShiftop} :
      Instr_ok C (.vshiftop sh op) ⟨[ValType.v128, ValType.i32], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vbitmask: C |- VBITMASK sh : V128 -> I32`. -/
  -- core-rule: Instr_ok/vbitmask
  | vbitmask {C : Context} {sh : IShape} :
      Instr_ok C (.vbitmask sh) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_ok/vswizzlop: C |- VSWIZZLOP sh vswizzlop : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vswizzlop
  | vswizzlop {C : Context} {sh : BShape} {op : VSwizzlop} :
      Instr_ok C (.vswizzlop sh op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vshuffle: C |- VSHUFFLE sh i* : V128 V128 -> V128
      -- (if $(i < 2*$dim(sh)))*`. -/
  -- core-rule: Instr_ok/vshuffle
  | vshuffle {C : Context} {sh : BShape} {is : List LaneIdx} :
      SeqAll (fun (i : LaneIdx) => i.val < 2 * sh.val.dim.toNat) is →
      Instr_ok C (.vshuffle sh is) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vsplat: C |- VSPLAT sh : $unpackshape(sh) -> V128`. -/
  -- core-rule: Instr_ok/vsplat
  | vsplat {C : Context} {sh : Shape} :
      Instr_ok C (.vsplat sh) ⟨[.num sh.unpack], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vextract_lane:
        C |- VEXTRACT_LANE sh sx? i : V128 -> $unpackshape(sh)
        -- if i < $dim(sh)`. -/
  -- core-rule: Instr_ok/vextract_lane
  | vextract_lane {C : Context} {sh : Shape} {sx : Option Sx} {i : LaneIdx} :
      i.val < sh.dim.toNat →
      Instr_ok C (.vextractLane sh sx i) ⟨[ValType.v128], [], [.num sh.unpack]⟩
  /-- `rule Instr_ok/vreplace_lane:
        C |- VREPLACE_LANE sh i : V128 $unpackshape(sh) -> V128
        -- if i < $dim(sh)`. -/
  -- core-rule: Instr_ok/vreplace_lane
  | vreplace_lane {C : Context} {sh : Shape} {i : LaneIdx} :
      i.val < sh.dim.toNat →
      Instr_ok C (.vreplaceLane sh i)
        ⟨[ValType.v128, .num sh.unpack], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vextunop: C |- VEXTUNOP sh_1 sh_2 vextunop : V128 -> V128`. -/
  -- core-rule: Instr_ok/vextunop
  | vextunop {C : Context} {sh₁ sh₂ : IShape} {op : VExtUnop} :
      Instr_ok C (.vextunop sh₁ sh₂ op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vextbinop: C |- VEXTBINOP sh_1 sh_2 vextbinop : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vextbinop
  | vextbinop {C : Context} {sh₁ sh₂ : IShape} {op : VExtBinop} :
      Instr_ok C (.vextbinop sh₁ sh₂ op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vextternop:
      C |- VEXTTERNOP sh_1 sh_2 vextternop : V128 V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vextternop
  | vextternop {C : Context} {sh₁ sh₂ : IShape} {op : VExtTernop} :
      Instr_ok C (.vextternop sh₁ sh₂ op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vnarrow: C |- VNARROW sh_1 sh_2 sx : V128 V128 -> V128`. -/
  -- core-rule: Instr_ok/vnarrow
  | vnarrow {C : Context} {sh₁ sh₂ : IShape} {sx : Sx} :
      Instr_ok C (.vnarrow sh₁ sh₂ sx)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_ok/vcvtop: C |- VCVTOP sh_1 sh_2 vcvtop : V128 -> V128`. -/
  -- core-rule: Instr_ok/vcvtop
  | vcvtop {C : Context} {sh₁ sh₂ : Shape} {op : VCvtop} :
      Instr_ok C (.vcvtop sh₁ sh₂ op) ⟨[ValType.v128], [], [ValType.v128]⟩

/-- `relation Instrs_ok: context |- instr* : instrtype`. -/
inductive Instrs_ok : Context → List Instr → InstrType → Prop where
  /-- `rule Instrs_ok/empty: C |- eps : eps -> eps`. -/
  -- core-rule: Instrs_ok/empty
  | empty {C : Context} : Instrs_ok C [] ⟨[], [], []⟩
  /-- `rule Instrs_ok/seq:
        C |- instr_1 instr_2* : t_1* ->_(x_1* x_2*) t_3*
        -- Instr_ok: C |- instr_1 : t_1* ->_(x_1*) t_2*
        -- (if C.LOCALS[x_1] = init t)*
        -- Instrs_ok: $with_locals(C, x_1*, (SET t)*) |- instr_2* : t_2* ->_(x_2*) t_3*`. -/
  -- core-rule: Instrs_ok/seq
  | seq {C : Context} {i₁ : Instr} {is : List Instr}
      {ts₁ ts₂ ts₃ ts : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Instr_ok C i₁ ⟨ts₁, xs₁, ts₂⟩ →
      SeqLen₂ xs₁ ts →
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs₁ ts →
      Instrs_ok (Context.withLocals C xs₁ (ts.map (fun t => ⟨.set, t⟩))) is
        ⟨ts₂, xs₂, ts₃⟩ →
      Instrs_ok C (i₁ :: is) ⟨ts₁, xs₁ ++ xs₂, ts₃⟩
  /-- `rule Instrs_ok/sub:
        C |- instr* : it'
        -- Instrs_ok: C |- instr* : it
        -- Instrtype_sub: C |- it <: it'
        -- Instrtype_ok: C |- it' : OK`. -/
  -- core-rule: Instrs_ok/sub
  | sub {C : Context} {is : List Instr} {it it' : InstrType} :
      Instrs_ok C is it → Instrtype_sub C it it' → Instrtype_ok C it' →
      Instrs_ok C is it'
  /-- `rule Instrs_ok/frame:
        C |- instr* : (t* t_1*) ->_(x*) (t* t_2*)
        -- Instrs_ok: C |- instr* : t_1* ->_(x*) t_2*
        -- Resulttype_ok: C |- t* : OK`. -/
  -- core-rule: Instrs_ok/frame
  | frame {C : Context} {is : List Instr} {ts ts₁ ts₂ : List ValType}
      {xs : List LocalIdx} :
      Instrs_ok C is ⟨ts₁, xs, ts₂⟩ → Resulttype_ok C ts →
      Instrs_ok C is ⟨ts ++ ts₁, xs, ts ++ ts₂⟩

end

/-! ## Expressions -/

/-- `relation Expr_ok: context |- expr : resulttype`. -/
inductive Expr_ok : Context → Expr → List ValType → Prop where
  /-- `rule Expr_ok: C |- instr* : t* -- Instrs_ok: C |- instr* : eps ->_(eps) t*`. -/
  -- core-rule: Expr_ok
  | mk {C : Context} {e : Expr} {ts : List ValType} :
      Instrs_ok C (InstrSeq.toList e) ⟨[], [], ts⟩ → Expr_ok C e ts

/-! ## Constant expressions -/

/-- `relation Instr_const: context |- instr CONST`. -/
inductive Instr_const : Context → Instr → Prop where
  /-- `rule Instr_const/const: C |- (CONST nt c_nt) CONST`. -/
  -- core-rule: Instr_const/const
  | const {C : Context} {nt : NumType} {c : Num_ nt} : Instr_const C (.const nt c)
  /-- `rule Instr_const/vconst: C |- (VCONST vt c_vt) CONST`. -/
  -- core-rule: Instr_const/vconst
  | vconst {C : Context} {vt : VecType} {c : VecLit vt.toVnn} :
      Instr_const C (.vconst vt c)
  /-- `rule Instr_const/ref.null: C |- (REF.NULL ht) CONST`. -/
  -- core-rule: Instr_const/ref.null
  | ref_null {C : Context} {ht : HeapType} : Instr_const C (.refNull ht)
  /-- `rule Instr_const/ref.i31: C |- (REF.I31) CONST`. -/
  -- core-rule: Instr_const/ref.i31
  | ref_i31 {C : Context} : Instr_const C .refI31
  /-- `rule Instr_const/ref.func: C |- (REF.FUNC x) CONST`. -/
  -- core-rule: Instr_const/ref.func
  | ref_func {C : Context} {x : FuncIdx} : Instr_const C (.refFunc x)
  /-- `rule Instr_const/struct.new: C |- (STRUCT.NEW x) CONST`. -/
  -- core-rule: Instr_const/struct.new
  | struct_new {C : Context} {x : TypeIdx} : Instr_const C (.structNew x)
  /-- `rule Instr_const/struct.new_default: C |- (STRUCT.NEW_DEFAULT x) CONST`. -/
  -- core-rule: Instr_const/struct.new_default
  | struct_new_default {C : Context} {x : TypeIdx} : Instr_const C (.structNewDefault x)
  /-- `rule Instr_const/array.new: C |- (ARRAY.NEW x) CONST`. -/
  -- core-rule: Instr_const/array.new
  | array_new {C : Context} {x : TypeIdx} : Instr_const C (.arrayNew x)
  /-- `rule Instr_const/array.new_default: C |- (ARRAY.NEW_DEFAULT x) CONST`. -/
  -- core-rule: Instr_const/array.new_default
  | array_new_default {C : Context} {x : TypeIdx} : Instr_const C (.arrayNewDefault x)
  /-- `rule Instr_const/array.new_fixed: C |- (ARRAY.NEW_FIXED x n) CONST`. -/
  -- core-rule: Instr_const/array.new_fixed
  | array_new_fixed {C : Context} {x : TypeIdx} {n : U32} :
      Instr_const C (.arrayNewFixed x n)
  /-- `rule Instr_const/any.convert_extern: C |- (ANY.CONVERT_EXTERN) CONST`. -/
  -- core-rule: Instr_const/any.convert_extern
  | any_convert_extern {C : Context} : Instr_const C .anyConvertExtern
  /-- `rule Instr_const/extern.convert_any: C |- (EXTERN.CONVERT_ANY) CONST`. -/
  -- core-rule: Instr_const/extern.convert_any
  | extern_convert_any {C : Context} : Instr_const C .externConvertAny
  /-- `rule Instr_const/global.get: C |- (GLOBAL.GET x) CONST
      -- if C.GLOBALS[x] = t`

  The global type is matched as a bare `valtype`, i.e. WITHOUT `MUT`: only an
  immutable global may be read by a constant expression. -/
  -- core-rule: Instr_const/global.get
  | global_get {C : Context} {x : GlobalIdx} {t : ValType} :
      C.globals[x.val]? = some ⟨none, t⟩ → Instr_const C (.globalGet x)
  /-- `rule Instr_const/binop: C |- (BINOP Inn binop) CONST
      -- if Inn <- I32 I64 -- if binop <- ADD SUB MUL`. -/
  -- core-rule: Instr_const/binop
  | binop {C : Context} {n : Inn} {op : BinopI} :
      (op = .add ∨ op = .sub ∨ op = .mul) →
      Instr_const C (.binop n.toNumType (.int op))

/-- `relation Expr_const: context |- expr CONST`. -/
inductive Expr_const : Context → Expr → Prop where
  /-- `rule Expr_const: C |- instr* CONST -- (Instr_const: C |- instr CONST)*`. -/
  -- core-rule: Expr_const
  | mk {C : Context} {e : Expr} :
      SeqAll (Instr_const C) (InstrSeq.toList e) → Expr_const C e

/-- `relation Expr_ok_const: context |- expr : valtype CONST`. -/
inductive Expr_ok_const : Context → Expr → ValType → Prop where
  /-- `rule Expr_ok_const: C |- expr : t CONST
      -- Expr_ok: C |- expr : t -- Expr_const: C |- expr CONST`

  `Expr_ok`'s result is a `resulttype`; the single `valtype` `t` of the
  conclusion is that sequence of length one. -/
  -- core-rule: Expr_ok_const
  | mk {C : Context} {e : Expr} {t : ValType} :
      Expr_ok C e [t] → Expr_const C e → Expr_ok_const C e t

/-! ## Sanity checks

Kernel-checked derivations, not tests.  The point of the middle two is that the
stack-polymorphic rules really are polymorphic: `UNREACHABLE` and `BR` get
instruction types that no concrete typing would give them, and that is exactly
what the audit found missing from the previous validator. -/

/-- An empty result type is well-formed in any context. -/
private theorem rt_ok_nil {C : Context} : Resulttype_ok C [] := .mk (fun _ h => nomatch h)

/-- Result-type well-formedness is closed under cons. -/
private theorem rt_ok_cons {C : Context} {t : ValType} {ts : List ValType}
    (h : Valtype_ok C t) (hs : Resulttype_ok C ts) : Resulttype_ok C (t :: ts) := by
  cases hs with
  | mk hall =>
      refine .mk (fun a ha => ?_)
      cases ha with
      | head => exact h
      | tail _ ha => exact hall a ha

/-- A `(...)* ` premise over an empty sequence. -/
private theorem seq_all_nil {α : Type} {P : α → Prop} : SeqAll P [] := fun _ h => nomatch h

/-- A `(...)* ` premise over two empty sequences. -/
private theorem seq_all₂_nil {α β : Type} {R : α → β → Prop} : SeqAll₂ R [] [] :=
  fun _ _ _ h _ => by simp at h

/-- `NOP : eps -> eps`. -/
example : Instr_ok Context.empty .nop ⟨[], [], []⟩ := .nop

/-- `UNREACHABLE` has EVERY well-formed instruction type --- here
`I32 -> F64 V128`, whose domain and codomain share nothing.  A validator that
typed `UNREACHABLE` concretely could not derive this. -/
example :
    Instr_ok Context.empty .unreachable ⟨[ValType.i32], [], [.num .f64, ValType.v128]⟩ :=
  .unreachable
    (.mk (rt_ok_cons (.num .mk) rt_ok_nil)
      (rt_ok_cons (.num .mk) (rt_ok_cons (.vec .mk) rt_ok_nil))
      seq_all_nil)

/-- `BR 0`, in a context whose innermost label is empty, likewise has an
arbitrary type: here `V128 -> I32`, consuming a `V128` no rule ever mentions. -/
example :
    Instr_ok { Context.empty with labels := [[]] } (.br ⟨0, two_pow_pos 32⟩)
      ⟨[ValType.v128], [], [ValType.i32]⟩ :=
  .br rfl
    (.mk (rt_ok_cons (.vec .mk) rt_ok_nil) (rt_ok_cons (.num .mk) rt_ok_nil) seq_all_nil)

/-- `(I32.CONST 0)` is a constant expression of type `I32`; the derivation goes
through `Instrs_ok/seq`, `Instrs_ok/frame` and `Instrs_ok/empty`. -/
example :
    Expr_ok_const Context.empty (InstrSeq.ofList [.const .i32 default]) ValType.i32 := by
  refine Expr_ok_const.mk (Expr_ok.mk ?_) (Expr_const.mk ?_)
  · rw [InstrSeq.toList_ofList]
    exact Instrs_ok.seq (ts := []) Instr_ok.const rfl seq_all₂_nil
      (Instrs_ok.frame Instrs_ok.empty (rt_ok_cons (.num .mk) rt_ok_nil))
  · rw [InstrSeq.toList_ofList]
    refine fun i h => ?_
    cases h with
    | head => exact .const
    | tail _ h => nomatch h

end WasmGemmGnaf.Wasm.Core
