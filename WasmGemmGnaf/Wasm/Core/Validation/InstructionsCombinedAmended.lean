/-
  Coverage-neutral combined instruction-validation amendment.

  This hierarchy composes AMD-005 (framed instruction-sequence composition)
  with the corrected bottom-subtyping and type-validity hierarchy.  It mirrors
  every pinned instruction constructor, but every dependent validity/subtyping
  premise and every recursive body is routed through the amended family.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Instructions
import WasmGemmGnaf.Wasm.Core.Validation.SubtypingAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

inductive Blocktype_okA : Context → BlockType → InstrType → Prop where
  | valtype {C : Context} {t : Option ValType} :
      OptAll (Valtype_okA C) t → Blocktype_okA C (.result t) ⟨[], [], t.toList⟩
  | typeidx {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      Blocktype_okA C (.idx x) ⟨ValTypes.toList dom, [], ValTypes.toList cod⟩

inductive Catch_okA : Context → Catch → Prop where
  | catch {C : Context} {x : TagIdx} {l : LabelIdx} {jt : TagType} {dt : DefType}
      {dom : ValTypes} {ts : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) → C.labels[l.val]? = some ts →
      Resulttype_subA C (ValTypes.toList dom) ts → Catch_okA C (.tag x l)
  | catch_ref {C : Context} {x : TagIdx} {l : LabelIdx} {jt : TagType}
      {dt : DefType} {dom : ValTypes} {ts : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) → C.labels[l.val]? = some ts →
      Resulttype_subA C
        (ValTypes.toList dom ++ [.ref (.ref none (.abs .exn))]) ts →
      Catch_okA C (.tagRef x l)
  | catch_all {C : Context} {l : LabelIdx} {ts : List ValType} :
      C.labels[l.val]? = some ts → Resulttype_subA C [] ts → Catch_okA C (.all l)
  | catch_all_ref {C : Context} {l : LabelIdx} {ts : List ValType} :
      C.labels[l.val]? = some ts →
      Resulttype_subA C [.ref (.ref none (.abs .exn))] ts →
      Catch_okA C (.allRef l)

mutual

/-- `relation Instr_okA: context |- instr : instrtype`. -/
inductive Instr_okA : Context → Instr → InstrType → Prop where
  -- Parametric instructions
  /-- `rule Instr_okA/nop: C |- NOP : eps -> eps`. -/
  | nop {C : Context} : Instr_okA C .nop ⟨[], [], []⟩
  /-- `rule Instr_okA/unreachable: C |- UNREACHABLE : t_1* -> t_2*
      -- Instrtype_okA: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic: `t_1*` and `t_2*` are free. -/
  | unreachable {C : Context} {ts₁ ts₂ : List ValType} :
      Instrtype_okA C ⟨ts₁, [], ts₂⟩ → Instr_okA C .unreachable ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_okA/drop: C |- DROP : t -> eps -- Valtype_okA: C |- t : OK`. -/
  | drop {C : Context} {t : ValType} : Valtype_okA C t → Instr_okA C .drop ⟨[t], [], []⟩
  /-- `rule Instr_okA/select-expl: C |- SELECT t : t t I32 -> t
      -- Valtype_okA: C |- t : OK`. -/
  | select_expl {C : Context} {t : ValType} :
      Valtype_okA C t →
      Instr_okA C (.select (some [t])) ⟨[t, t, ValType.i32], [], [t]⟩
  /-- `rule Instr_okA/select-impl:
        C |- SELECT : t t I32 -> t
        -- Valtype_okA: C |- t : OK
        -- Valtype_subA: C |- t <: t'
        -- if t' = numtype \/ t' = vectype`. -/
  | select_impl {C : Context} {t t' : ValType} :
      Valtype_okA C t → Valtype_subA C t t' → t'.isNumOrVec = true →
      Instr_okA C (.select none) ⟨[t, t, ValType.i32], [], [t]⟩

  -- Block instructions
  /-- `rule Instr_okA/block:
        C |- BLOCK bt instr* : t_1* -> t_2*
        -- Blocktype_okA: C |- bt : t_1* -> t_2*
        -- Instrs_okA: {LABELS (t_2*)} ++ C |- instr* : t_1* ->_(x*) t_2*`. -/
  | block {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_okA C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_okA C (.block bt body) ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_okA/loop:
        C |- LOOP bt instr* : t_1* -> t_2*
        -- Blocktype_okA: C |- bt : t_1* -> t_2*
        -- Instrs_okA: {LABELS (t_1*)} ++ C |- instr* : t_1* ->_(x*) t_2*`.

  The loop's label carries the block's ARGUMENTS, not its results. -/
  | loop {C : Context} {bt : BlockType} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_okA C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_okA (Context.pushLabel ts₁ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      Instr_okA C (.loop bt body) ⟨ts₁, [], ts₂⟩
  /-- `rule Instr_okA/if:
        C |- IF bt instr_1* ELSE instr_2* : t_1* I32 -> t_2*
        -- Blocktype_okA: C |- bt : t_1* -> t_2*
        -- Instrs_okA: {LABELS (t_2*)} ++ C |- instr_1* : t_1* ->_(x_1*) t_2*
        -- Instrs_okA: {LABELS (t_2*)} ++ C |- instr_2* : t_1* ->_(x_2*) t_2*`. -/
  | if_ {C : Context} {bt : BlockType} {thn els : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Blocktype_okA C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList thn) ⟨ts₁, xs₁, ts₂⟩ →
      Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList els) ⟨ts₁, xs₂, ts₂⟩ →
      Instr_okA C (.ifElse bt thn els) ⟨ts₁ ++ [ValType.i32], [], ts₂⟩

  -- Branch instructions
  /-- `rule Instr_okA/br:
        C |- BR l : t_1* t* -> t_2*
        -- if C.LABELS[l] = t*
        -- Instrtype_okA: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic in `t_1*` and `t_2*`. -/
  | br {C : Context} {l : LabelIdx} {ts ts₁ ts₂ : List ValType} :
      C.labels[l.val]? = some ts →
      Instrtype_okA C ⟨ts₁, [], ts₂⟩ →
      Instr_okA C (.br l) ⟨ts₁ ++ ts, [], ts₂⟩
  /-- `rule Instr_okA/br_if: C |- BR_IF l : t* I32 -> t* -- if C.LABELS[l] = t*`. -/
  | br_if {C : Context} {l : LabelIdx} {ts : List ValType} :
      C.labels[l.val]? = some ts →
      Instr_okA C (.brIf l) ⟨ts ++ [ValType.i32], [], ts⟩
  /-- `rule Instr_okA/br_table:
        C |- BR_TABLE l* l' : t_1* t* I32 -> t_2*
        -- (Resulttype_subA: C |- t* <: C.LABELS[l])*
        -- Resulttype_subA: C |- t* <: C.LABELS[l']
        -- Instrtype_okA: C |- t_1* t* I32 -> t_2* : OK`. -/
  | br_table {C : Context} {ls : List LabelIdx} {l' : LabelIdx}
      {ts ts₁ ts₂ ts'' : List ValType} :
      SeqAll (fun (l : LabelIdx) =>
          ∃ ts', C.labels[l.val]? = some ts' ∧ Resulttype_subA C ts ts') ls →
      C.labels[l'.val]? = some ts'' → Resulttype_subA C ts ts'' →
      Instrtype_okA C ⟨ts₁ ++ ts ++ [ValType.i32], [], ts₂⟩ →
      Instr_okA C (.brTable ls l') ⟨ts₁ ++ ts ++ [ValType.i32], [], ts₂⟩
  /-- `rule Instr_okA/br_on_null:
        C |- BR_ON_NULL l : t* (REF NULL ht) -> t* (REF ht)
        -- if C.LABELS[l] = t*
        -- Heaptype_okA: C |- ht : OK`. -/
  | br_on_null {C : Context} {l : LabelIdx} {ts : List ValType} {ht : HeapType} :
      C.labels[l.val]? = some ts → Heaptype_okA C ht →
      Instr_okA C (.brOnNull l)
        ⟨ts ++ [.ref (.ref (some .null) ht)], [], ts ++ [.ref (.ref none ht)]⟩
  /-- `rule Instr_okA/br_on_non_null:
        C |- BR_ON_NON_NULL l : t* (REF NULL ht) -> t*
        -- if C.LABELS[l] = t* (REF NULL? ht)`. -/
  | br_on_non_null {C : Context} {l : LabelIdx} {ts : List ValType}
      {nul : Option Null} {ht : HeapType} :
      C.labels[l.val]? = some (ts ++ [.ref (.ref nul ht)]) →
      Instr_okA C (.brOnNonNull l) ⟨ts ++ [.ref (.ref (some .null) ht)], [], ts⟩
  /-- `rule Instr_okA/br_on_cast:
        C |- BR_ON_CAST l rt_1 rt_2 : t* rt_1 -> t* ($diffrt(rt_1, rt_2))
        -- if C.LABELS[l] = t* rt
        -- Reftype_okA: C |- rt_1 : OK
        -- Reftype_okA: C |- rt_2 : OK
        -- Reftype_subA: C |- rt_2 <: rt_1
        -- Reftype_subA: C |- rt_2 <: rt`. -/
  | br_on_cast {C : Context} {l : LabelIdx} {rt₁ rt₂ rt : RefType} {ts : List ValType} :
      C.labels[l.val]? = some (ts ++ [.ref rt]) →
      Reftype_okA C rt₁ → Reftype_okA C rt₂ →
      Reftype_subA C rt₂ rt₁ → Reftype_subA C rt₂ rt →
      Instr_okA C (.brOnCast l rt₁ rt₂)
        ⟨ts ++ [.ref rt₁], [], ts ++ [.ref (RefType.diff rt₁ rt₂)]⟩
  /-- `rule Instr_okA/br_on_cast_fail:
        C |- BR_ON_CAST_FAIL l rt_1 rt_2 : t* rt_1 -> t* rt_2
        -- if C.LABELS[l] = t* rt
        -- Reftype_okA: C |- rt_1 : OK
        -- Reftype_okA: C |- rt_2 : OK
        -- Reftype_subA: C |- rt_2 <: rt_1
        -- Reftype_subA: C |- $diffrt(rt_1, rt_2) <: rt`. -/
  | br_on_cast_fail {C : Context} {l : LabelIdx} {rt₁ rt₂ rt : RefType}
      {ts : List ValType} :
      C.labels[l.val]? = some (ts ++ [.ref rt]) →
      Reftype_okA C rt₁ → Reftype_okA C rt₂ →
      Reftype_subA C rt₂ rt₁ → Reftype_subA C (RefType.diff rt₁ rt₂) rt →
      Instr_okA C (.brOnCastFail l rt₁ rt₂) ⟨ts ++ [.ref rt₁], [], ts ++ [.ref rt₂]⟩

  -- Function instructions
  /-- `rule Instr_okA/call: C |- CALL x : t_1* -> t_2*
      -- Expand: C.FUNCS[x] ~~ FUNC t_1* -> t_2*`. -/
  | call {C : Context} {x : FuncIdx} {dt : DefType} {dom cod : ValTypes} :
      C.funcs[x.val]? = some dt → Expand dt (.func dom cod) →
      Instr_okA C (.call x) ⟨ValTypes.toList dom, [], ValTypes.toList cod⟩
  /-- `rule Instr_okA/call_ref:
        C |- CALL_REF (_IDX x) : t_1* (REF NULL (_IDX x)) -> t_2*
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*`. -/
  | call_ref {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      Instr_okA C (.callRef (.idx x))
        ⟨ValTypes.toList dom ++ [.ref (.ref (some .null) (.use (.idx x)))], [],
         ValTypes.toList cod⟩
  /-- `rule Instr_okA/call_indirect:
        C |- CALL_INDIRECT x (_IDX y) : t_1* at -> t_2*
        -- if C.TABLES[x] = at lim rt
        -- Reftype_subA: C |- rt <: (REF NULL FUNC)
        -- Expand: C.TYPES[y] ~~ FUNC t_1* -> t_2*`. -/
  | call_indirect {C : Context} {x : TableIdx} {y : TypeIdx} {tt : TableType}
      {dt : DefType} {dom cod : ValTypes} :
      C.tables[x.val]? = some tt →
      Reftype_subA C tt.elem RefType.funcref →
      C.types[y.val]? = some dt → Expand dt (.func dom cod) →
      Instr_okA C (.callIndirect x (.idx y))
        ⟨ValTypes.toList dom ++ [tt.addr.toValType], [], ValTypes.toList cod⟩
  /-- `rule Instr_okA/return:
        C |- RETURN : t_1* t* -> t_2*
        -- if C.RETURN = (t*)
        -- Instrtype_okA: C |- t_1* -> t_2* : OK`. -/
  | ret {C : Context} {ts ts₁ ts₂ : List ValType} :
      C.ret = some ts → Instrtype_okA C ⟨ts₁, [], ts₂⟩ →
      Instr_okA C .ret ⟨ts₁ ++ ts, [], ts₂⟩
  /-- `rule Instr_okA/return_call:
        C |- RETURN_CALL x : t_3* t_1* -> t_4*
        -- Expand: C.FUNCS[x] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_subA: C |- t_2* <: t'_2*
        -- Instrtype_okA: C |- t_3* -> t_4* : OK`. -/
  | return_call {C : Context} {x : FuncIdx} {dt : DefType} {dom cod : ValTypes}
      {ts₂' ts₃ ts₄ : List ValType} :
      C.funcs[x.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_subA C (ValTypes.toList cod) ts₂' →
      Instrtype_okA C ⟨ts₃, [], ts₄⟩ →
      Instr_okA C (.returnCall x) ⟨ts₃ ++ ValTypes.toList dom, [], ts₄⟩
  /-- `rule Instr_okA/return_call_ref:
        C |- RETURN_CALL_REF (_IDX x) : t_3* t_1* (REF NULL (_IDX x)) -> t_4*
        -- Expand: C.TYPES[x] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_subA: C |- t_2* <: t'_2*
        -- Instrtype_okA: C |- t_3* -> t_4* : OK`. -/
  | return_call_ref {C : Context} {x : TypeIdx} {dt : DefType} {dom cod : ValTypes}
      {ts₂' ts₃ ts₄ : List ValType} :
      C.types[x.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_subA C (ValTypes.toList cod) ts₂' →
      Instrtype_okA C ⟨ts₃, [], ts₄⟩ →
      Instr_okA C (.returnCallRef (.idx x))
        ⟨ts₃ ++ ValTypes.toList dom ++ [.ref (.ref (some .null) (.use (.idx x)))], [], ts₄⟩
  /-- `rule Instr_okA/return_call_indirect:
        C |- RETURN_CALL_INDIRECT x (_IDX y) : t_3* t_1* at -> t_4*
        -- if C.TABLES[x] = at lim rt
        -- Reftype_subA: C |- rt <: (REF NULL FUNC)
        -- Expand: C.TYPES[y] ~~ FUNC t_1* -> t_2*
        -- if C.RETURN = (t'_2*)
        -- Resulttype_subA: C |- t_2* <: t'_2*
        -- Instrtype_okA: C |- t_3* -> t_4* : OK`. -/
  | return_call_indirect {C : Context} {x : TableIdx} {y : TypeIdx} {tt : TableType}
      {dt : DefType} {dom cod : ValTypes} {ts₂' ts₃ ts₄ : List ValType} :
      C.tables[x.val]? = some tt →
      Reftype_subA C tt.elem RefType.funcref →
      C.types[y.val]? = some dt → Expand dt (.func dom cod) →
      C.ret = some ts₂' → Resulttype_subA C (ValTypes.toList cod) ts₂' →
      Instrtype_okA C ⟨ts₃, [], ts₄⟩ →
      Instr_okA C (.returnCallIndirect x (.idx y))
        ⟨ts₃ ++ ValTypes.toList dom ++ [tt.addr.toValType], [], ts₄⟩

  -- Exception instructions
  /-- `rule Instr_okA/throw:
        C |- THROW x : t_1* t* -> t_2*
        -- Expand: $as_deftype(C.TAGS[x]) ~~ FUNC t* -> eps
        -- Instrtype_okA: C |- t_1* -> t_2* : OK`.

  Stack-polymorphic in `t_1*` and `t_2*`. -/
  | throw_ {C : Context} {x : TagIdx} {jt : TagType} {dt : DefType} {dom : ValTypes}
      {ts₁ ts₂ : List ValType} :
      C.tags[x.val]? = some jt → asDefType jt = some dt →
      Expand dt (.func dom .nil) →
      Instrtype_okA C ⟨ts₁, [], ts₂⟩ →
      Instr_okA C (.throw x) ⟨ts₁ ++ ValTypes.toList dom, [], ts₂⟩
  /-- `rule Instr_okA/throw_ref:
        C |- THROW_REF : t_1* (REF NULL EXN) -> t_2*
        -- Instrtype_okA: C |- t_1* -> t_2* : OK`. -/
  | throw_ref {C : Context} {ts₁ ts₂ : List ValType} :
      Instrtype_okA C ⟨ts₁, [], ts₂⟩ →
      Instr_okA C .throwRef
        ⟨ts₁ ++ [.ref (.ref (some .null) (.abs .exn))], [], ts₂⟩
  /-- `rule Instr_okA/try_table:
        C |- TRY_TABLE bt catch* instr* : t_1* -> t_2*
        -- Blocktype_okA: C |- bt : t_1* -> t_2*
        -- Instrs_okA: {LABELS (t_2*)} ++ C |- instr* : t_1* ->_(x*) t_2*
        -- (Catch_okA: C |- catch : OK)*`. -/
  | try_table {C : Context} {bt : BlockType} {cs : List_ Catch} {body : InstrSeq}
      {ts₁ ts₂ : List ValType} {xs : List LocalIdx} :
      Blocktype_okA C bt ⟨ts₁, [], ts₂⟩ →
      Instrs_okA (Context.pushLabel ts₂ C) (InstrSeq.toList body) ⟨ts₁, xs, ts₂⟩ →
      SeqAll (Catch_okA C) cs.val →
      Instr_okA C (.tryTable bt cs body) ⟨ts₁, [], ts₂⟩

  -- Reference instructions
  /-- `rule Instr_okA/ref.null: C |- REF.NULL ht : eps -> (REF NULL ht)
      -- Heaptype_okA: C |- ht : OK`. -/
  | ref_null {C : Context} {ht : HeapType} :
      Heaptype_okA C ht →
      Instr_okA C (.refNull ht) ⟨[], [], [.ref (.ref (some .null) ht)]⟩
  /-- `rule Instr_okA/ref.func: C |- REF.FUNC x : eps -> (REF dt)
      -- if C.FUNCS[x] = dt -- if x <- C.REFS`. -/
  | ref_func {C : Context} {x : FuncIdx} {dt : DefType} :
      C.funcs[x.val]? = some dt → x ∈ C.refs →
      Instr_okA C (.refFunc x) ⟨[], [], [.ref (.ref none (.use (.defd dt)))]⟩
  /-- `rule Instr_okA/ref.i31: C |- REF.I31 : I32 -> (REF I31)`. -/
  | ref_i31 {C : Context} :
      Instr_okA C .refI31 ⟨[ValType.i32], [], [.ref (.ref none (.abs .i31))]⟩
  /-- `rule Instr_okA/ref.is_null: C |- REF.IS_NULL : (REF NULL ht) -> I32
      -- Heaptype_okA: C |- ht : OK`. -/
  | ref_is_null {C : Context} {ht : HeapType} :
      Heaptype_okA C ht →
      Instr_okA C .refIsNull ⟨[.ref (.ref (some .null) ht)], [], [ValType.i32]⟩
  /-- `rule Instr_okA/ref.as_non_null: C |- REF.AS_NON_NULL : (REF NULL ht) -> (REF ht)
      -- Heaptype_okA: C |- ht : OK`. -/
  | ref_as_non_null {C : Context} {ht : HeapType} :
      Heaptype_okA C ht →
      Instr_okA C .refAsNonNull
        ⟨[.ref (.ref (some .null) ht)], [], [.ref (.ref none ht)]⟩
  /-- `rule Instr_okA/ref.eq: C |- REF.EQ : (REF NULL EQ) (REF NULL EQ) -> I32`. -/
  | ref_eq {C : Context} :
      Instr_okA C .refEq
        ⟨[.ref RefType.eqref, .ref RefType.eqref], [], [ValType.i32]⟩
  /-- `rule Instr_okA/ref.test:
        C |- REF.TEST rt : rt' -> I32
        -- Reftype_okA: C |- rt : OK
        -- Reftype_okA: C |- rt' : OK
        -- Reftype_subA: C |- rt <: rt'`. -/
  | ref_test {C : Context} {rt rt' : RefType} :
      Reftype_okA C rt → Reftype_okA C rt' → Reftype_subA C rt rt' →
      Instr_okA C (.refTest rt) ⟨[.ref rt'], [], [ValType.i32]⟩
  /-- `rule Instr_okA/ref.cast:
        C |- REF.CAST rt : rt' -> rt
        -- Reftype_okA: C |- rt : OK
        -- Reftype_okA: C |- rt' : OK
        -- Reftype_subA: C |- rt <: rt'`. -/
  | ref_cast {C : Context} {rt rt' : RefType} :
      Reftype_okA C rt → Reftype_okA C rt' → Reftype_subA C rt rt' →
      Instr_okA C (.refCast rt) ⟨[.ref rt'], [], [.ref rt]⟩

  -- Scalar reference instructions
  /-- `rule Instr_okA/i31.get: C |- I31.GET sx : (REF NULL I31) -> I32`. -/
  | i31_get {C : Context} {sx : Sx} :
      Instr_okA C (.i31Get sx) ⟨[.ref RefType.i31ref], [], [ValType.i32]⟩

  -- Structure instructions
  /-- `rule Instr_okA/struct.new: C |- STRUCT.NEW x : $unpack(zt)* -> (REF (_IDX x))
      -- Expand: C.TYPES[x] ~~ STRUCT (mut? zt)*`. -/
  | struct_new {C : Context} {x : TypeIdx} {dt : DefType} {fts : FieldTypes} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      Instr_okA C (.structNew x)
        ⟨fts.unpacked, [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/struct.new_default:
        C |- STRUCT.NEW_DEFAULT x : eps -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ STRUCT (mut? zt)*
        -- (Defaultable: |- $unpack(zt) DEFAULTABLE)*`. -/
  | struct_new_default {C : Context} {x : TypeIdx} {dt : DefType} {fts : FieldTypes} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      SeqAll Defaultable fts.unpacked →
      Instr_okA C (.structNewDefault x) ⟨[], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/struct.get:
        C |- STRUCT.GET sx? x i : (REF NULL (_IDX x)) -> $unpack(zt)
        -- Expand: C.TYPES[x] ~~ STRUCT ft*
        -- if ft*[i] = mut? zt
        -- if sx? = eps <=> $is_packtype(zt)`

  See `StorageType.isUnpacked` for what the source's `$is_packtype` actually
  computes. -/
  | struct_get {C : Context} {sx : Option Sx} {x : TypeIdx} {i : U32}
      {dt : DefType} {fts : FieldTypes} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      (FieldTypes.toList fts)[i.val]? = some ft →
      ((sx = none) ↔ StorageType.isUnpacked ft.storage = true) →
      Instr_okA C (.structGet sx x i)
        ⟨[.ref (.ref (some .null) (.use (.idx x)))], [],
         [StorageType.unpack ft.storage]⟩
  /-- `rule Instr_okA/struct.set:
        C |- STRUCT.SET x i : (REF NULL (_IDX x)) $unpack(zt) -> eps
        -- Expand: C.TYPES[x] ~~ STRUCT ft*
        -- if ft*[i] = MUT zt`. -/
  | struct_set {C : Context} {x : TypeIdx} {i : U32} {dt : DefType}
      {fts : FieldTypes} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.struct fts) →
      (FieldTypes.toList fts)[i.val]? = some (.mk (some .mut) zt) →
      Instr_okA C (.structSet x i)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), StorageType.unpack zt], [], []⟩

  -- Array instructions
  /-- `rule Instr_okA/array.new: C |- ARRAY.NEW x : $unpack(zt) I32 -> (REF (_IDX x))
      -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)`. -/
  | array_new {C : Context} {x : TypeIdx} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Instr_okA C (.arrayNew x)
        ⟨[StorageType.unpack ft.storage, ValType.i32], [],
         [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/array.new_default:
        C |- ARRAY.NEW_DEFAULT x : I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- Defaultable: |- $unpack(zt) DEFAULTABLE`. -/
  | array_new_default {C : Context} {x : TypeIdx} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Defaultable (StorageType.unpack ft.storage) →
      Instr_okA C (.arrayNewDefault x)
        ⟨[ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/array.new_fixed:
        C |- ARRAY.NEW_FIXED x n : $unpack(zt)^n -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)`. -/
  | array_new_fixed {C : Context} {x : TypeIdx} {n : U32} {dt : DefType} {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      Instr_okA C (.arrayNewFixed x n)
        ⟨List.replicate n.val (StorageType.unpack ft.storage), [],
         [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/array.new_elem:
        C |- ARRAY.NEW_ELEM x y : I32 I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? rt)
        -- Reftype_subA: C |- C.ELEMS[y] <: rt`

  The array's storage type is matched as a `reftype`, so the rule applies only
  to arrays of references. -/
  | array_new_elem {C : Context} {x : TypeIdx} {y : ElemIdx} {dt : DefType}
      {m : Option Mut} {rt rt' : RefType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk m (.val (.ref rt)))) →
      C.elems[y.val]? = some rt' → Reftype_subA C rt' rt →
      Instr_okA C (.arrayNewElem x y)
        ⟨[ValType.i32, ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/array.new_data:
        C |- ARRAY.NEW_DATA x y : I32 I32 -> (REF (_IDX x))
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- if $unpack(zt) = numtype \/ $unpack(zt) = vectype
        -- if C.DATAS[y] = OK`. -/
  | array_new_data {C : Context} {x : TypeIdx} {y : DataIdx} {dt : DefType}
      {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      (StorageType.unpack ft.storage).isNumOrVec = true →
      C.datas[y.val]? = some .ok →
      Instr_okA C (.arrayNewData x y)
        ⟨[ValType.i32, ValType.i32], [], [.ref (.ref none (.use (.idx x)))]⟩
  /-- `rule Instr_okA/array.get:
        C |- ARRAY.GET sx? x : (REF NULL (_IDX x)) I32 -> $unpack(zt)
        -- Expand: C.TYPES[x] ~~ ARRAY (mut? zt)
        -- if sx? = eps <=> $is_packtype(zt)`. -/
  | array_get {C : Context} {sx : Option Sx} {x : TypeIdx} {dt : DefType}
      {ft : FieldType} :
      C.types[x.val]? = some dt → Expand dt (.array ft) →
      ((sx = none) ↔ StorageType.isUnpacked ft.storage = true) →
      Instr_okA C (.arrayGet sx x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32], [],
         [StorageType.unpack ft.storage]⟩
  /-- `rule Instr_okA/array.set:
        C |- ARRAY.SET x : (REF NULL (_IDX x)) I32 $unpack(zt) -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)`. -/
  | array_set {C : Context} {x : TypeIdx} {dt : DefType} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      Instr_okA C (.arraySet x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
          StorageType.unpack zt], [], []⟩
  /-- `rule Instr_okA/array.len: C |- ARRAY.LEN : (REF NULL ARRAY) -> I32`. -/
  | array_len {C : Context} :
      Instr_okA C .arrayLen ⟨[.ref RefType.arrayref], [], [ValType.i32]⟩
  /-- `rule Instr_okA/array.fill:
        C |- ARRAY.FILL x : (REF NULL (_IDX x)) I32 $unpack(zt) I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)`. -/
  | array_fill {C : Context} {x : TypeIdx} {dt : DefType} {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      Instr_okA C (.arrayFill x)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32,
          StorageType.unpack zt, ValType.i32], [], []⟩
  /-- `rule Instr_okA/array.copy:
        C |- ARRAY.COPY x_1 x_2 :
          (REF NULL (_IDX x_1)) I32 (REF NULL (_IDX x_2)) I32 I32 -> eps
        -- Expand: C.TYPES[x_1] ~~ ARRAY (MUT zt_1)
        -- Expand: C.TYPES[x_2] ~~ ARRAY (mut? zt_2)
        -- Storagetype_subA: C |- zt_2 <: zt_1`. -/
  | array_copy {C : Context} {x₁ x₂ : TypeIdx} {dt₁ dt₂ : DefType}
      {zt₁ zt₂ : StorageType} {m : Option Mut} :
      C.types[x₁.val]? = some dt₁ → Expand dt₁ (.array (.mk (some .mut) zt₁)) →
      C.types[x₂.val]? = some dt₂ → Expand dt₂ (.array (.mk m zt₂)) →
      Storagetype_subA C zt₂ zt₁ →
      Instr_okA C (.arrayCopy x₁ x₂)
        ⟨[.ref (.ref (some .null) (.use (.idx x₁))), ValType.i32,
          .ref (.ref (some .null) (.use (.idx x₂))), ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_okA/array.init_elem:
        C |- ARRAY.INIT_ELEM x y : (REF NULL (_IDX x)) I32 I32 I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)
        -- Storagetype_subA: C |- C.ELEMS[y] <: zt`. -/
  | array_init_elem {C : Context} {x : TypeIdx} {y : ElemIdx} {dt : DefType}
      {zt : StorageType} {rt : RefType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      C.elems[y.val]? = some rt → Storagetype_subA C (.val (.ref rt)) zt →
      Instr_okA C (.arrayInitElem x y)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32, ValType.i32,
          ValType.i32], [], []⟩
  /-- `rule Instr_okA/array.init_data:
        C |- ARRAY.INIT_DATA x y : (REF NULL (_IDX x)) I32 I32 I32 -> eps
        -- Expand: C.TYPES[x] ~~ ARRAY (MUT zt)
        -- if $unpack(zt) = numtype \/ $unpack(zt) = vectype
        -- if C.DATAS[y] = OK`. -/
  | array_init_data {C : Context} {x : TypeIdx} {y : DataIdx} {dt : DefType}
      {zt : StorageType} :
      C.types[x.val]? = some dt → Expand dt (.array (.mk (some .mut) zt)) →
      (StorageType.unpack zt).isNumOrVec = true →
      C.datas[y.val]? = some .ok →
      Instr_okA C (.arrayInitData x y)
        ⟨[.ref (.ref (some .null) (.use (.idx x))), ValType.i32, ValType.i32,
          ValType.i32], [], []⟩

  -- External reference instructions
  /-- `rule Instr_okA/extern.convert_any:
        C |- EXTERN.CONVERT_ANY : (REF null_1? ANY) -> (REF null_2? EXTERN)
        -- if null_1? = null_2?`. -/
  | extern_convert_any {C : Context} {nul : Option Null} :
      Instr_okA C .externConvertAny
        ⟨[.ref (.ref nul (.abs .any))], [], [.ref (.ref nul (.abs .extern))]⟩
  /-- `rule Instr_okA/any.convert_extern:
        C |- ANY.CONVERT_EXTERN : (REF null_1? EXTERN) -> (REF null_2? ANY)
        -- if null_1? = null_2?`. -/
  | any_convert_extern {C : Context} {nul : Option Null} :
      Instr_okA C .anyConvertExtern
        ⟨[.ref (.ref nul (.abs .extern))], [], [.ref (.ref nul (.abs .any))]⟩

  -- Local instructions
  /-- `rule Instr_okA/local.get: C |- LOCAL.GET x : eps -> t
      -- if C.LOCALS[x] = SET t`. -/
  | local_get {C : Context} {x : LocalIdx} {t : ValType} :
      C.locals[x.val]? = some ⟨.set, t⟩ → Instr_okA C (.localGet x) ⟨[], [], [t]⟩
  /-- `rule Instr_okA/local.set: C |- LOCAL.SET x : t ->_(x) eps
      -- if C.LOCALS[x] = init t`. -/
  | local_set {C : Context} {x : LocalIdx} {ini : Init} {t : ValType} :
      C.locals[x.val]? = some ⟨ini, t⟩ → Instr_okA C (.localSet x) ⟨[t], [x], []⟩
  /-- `rule Instr_okA/local.tee: C |- LOCAL.TEE x : t ->_(x) t
      -- if C.LOCALS[x] = init t`. -/
  | local_tee {C : Context} {x : LocalIdx} {ini : Init} {t : ValType} :
      C.locals[x.val]? = some ⟨ini, t⟩ → Instr_okA C (.localTee x) ⟨[t], [x], [t]⟩

  -- Global instructions
  /-- `rule Instr_okA/global.get: C |- GLOBAL.GET x : eps -> t
      -- if C.GLOBALS[x] = mut? t`. -/
  | global_get {C : Context} {x : GlobalIdx} {m : Option Mut} {t : ValType} :
      C.globals[x.val]? = some ⟨m, t⟩ → Instr_okA C (.globalGet x) ⟨[], [], [t]⟩
  /-- `rule Instr_okA/global.set: C |- GLOBAL.SET x : t -> eps
      -- if C.GLOBALS[x] = MUT t`. -/
  | global_set {C : Context} {x : GlobalIdx} {t : ValType} :
      C.globals[x.val]? = some ⟨some .mut, t⟩ → Instr_okA C (.globalSet x) ⟨[t], [], []⟩

  -- Table instructions
  /-- `rule Instr_okA/table.get: C |- TABLE.GET x : at -> rt
      -- if C.TABLES[x] = at lim rt`. -/
  | table_get {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_okA C (.tableGet x) ⟨[tt.addr.toValType], [], [.ref tt.elem]⟩
  /-- `rule Instr_okA/table.set: C |- TABLE.SET x : at rt -> eps
      -- if C.TABLES[x] = at lim rt`. -/
  | table_set {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_okA C (.tableSet x) ⟨[tt.addr.toValType, .ref tt.elem], [], []⟩
  /-- `rule Instr_okA/table.size: C |- TABLE.SIZE x : eps -> at
      -- if C.TABLES[x] = at lim rt`. -/
  | table_size {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_okA C (.tableSize x) ⟨[], [], [tt.addr.toValType]⟩
  /-- `rule Instr_okA/table.grow: C |- TABLE.GROW x : rt at -> I32
      -- if C.TABLES[x] = at lim rt`. -/
  | table_grow {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_okA C (.tableGrow x)
        ⟨[.ref tt.elem, tt.addr.toValType], [], [ValType.i32]⟩
  /-- `rule Instr_okA/table.fill: C |- TABLE.FILL x : at rt at -> eps
      -- if C.TABLES[x] = at lim rt`. -/
  | table_fill {C : Context} {x : TableIdx} {tt : TableType} :
      C.tables[x.val]? = some tt →
      Instr_okA C (.tableFill x)
        ⟨[tt.addr.toValType, .ref tt.elem, tt.addr.toValType], [], []⟩
  /-- `rule Instr_okA/table.copy:
        C |- TABLE.COPY x_1 x_2 : at_1 at_2 $minat(at_1, at_2) -> eps
        -- if C.TABLES[x_1] = at_1 lim_1 rt_1
        -- if C.TABLES[x_2] = at_2 lim_2 rt_2
        -- Reftype_subA: C |- rt_2 <: rt_1`. -/
  | table_copy {C : Context} {x₁ x₂ : TableIdx} {tt₁ tt₂ : TableType} :
      C.tables[x₁.val]? = some tt₁ → C.tables[x₂.val]? = some tt₂ →
      Reftype_subA C tt₂.elem tt₁.elem →
      Instr_okA C (.tableCopy x₁ x₂)
        ⟨[tt₁.addr.toValType, tt₂.addr.toValType,
          (AddrType.min tt₁.addr tt₂.addr).toValType], [], []⟩
  /-- `rule Instr_okA/table.init:
        C |- TABLE.INIT x y : at I32 I32 -> eps
        -- if C.TABLES[x] = at lim rt_1
        -- if C.ELEMS[y] = rt_2
        -- Reftype_subA: C |- rt_2 <: rt_1`. -/
  | table_init {C : Context} {x : TableIdx} {y : ElemIdx} {tt : TableType}
      {rt₂ : RefType} :
      C.tables[x.val]? = some tt → C.elems[y.val]? = some rt₂ →
      Reftype_subA C rt₂ tt.elem →
      Instr_okA C (.tableInit x y)
        ⟨[tt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_okA/elem.drop: C |- ELEM.DROP x : eps -> eps
      -- if C.ELEMS[x] = rt`. -/
  | elem_drop {C : Context} {x : ElemIdx} {rt : RefType} :
      C.elems[x.val]? = some rt → Instr_okA C (.elemDrop x) ⟨[], [], []⟩

  -- Memory instructions
  /-- `rule Instr_okA/memory.size: C |- MEMORY.SIZE x : eps -> at
      -- if C.MEMS[x] = at lim PAGE`. -/
  | memory_size {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_okA C (.memorySize x) ⟨[], [], [mt.addr.toValType]⟩
  /-- `rule Instr_okA/memory.grow: C |- MEMORY.GROW x : at -> at
      -- if C.MEMS[x] = at lim PAGE`. -/
  | memory_grow {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_okA C (.memoryGrow x) ⟨[mt.addr.toValType], [], [mt.addr.toValType]⟩
  /-- `rule Instr_okA/memory.fill: C |- MEMORY.FILL x : at I32 at -> eps
      -- if C.MEMS[x] = at lim PAGE`. -/
  | memory_fill {C : Context} {x : MemIdx} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Instr_okA C (.memoryFill x)
        ⟨[mt.addr.toValType, ValType.i32, mt.addr.toValType], [], []⟩
  /-- `rule Instr_okA/memory.copy:
        C |- MEMORY.COPY x_1 x_2 : at_1 at_2 $minat(at_1, at_2) -> eps
        -- if C.MEMS[x_1] = at_1 lim_1 PAGE
        -- if C.MEMS[x_2] = at_2 lim_2 PAGE`. -/
  | memory_copy {C : Context} {x₁ x₂ : MemIdx} {mt₁ mt₂ : MemType} :
      C.mems[x₁.val]? = some mt₁ → C.mems[x₂.val]? = some mt₂ →
      Instr_okA C (.memoryCopy x₁ x₂)
        ⟨[mt₁.addr.toValType, mt₂.addr.toValType,
          (AddrType.min mt₁.addr mt₂.addr).toValType], [], []⟩
  /-- `rule Instr_okA/memory.init:
        C |- MEMORY.INIT x y : at I32 I32 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if C.DATAS[y] = OK`. -/
  | memory_init {C : Context} {x : MemIdx} {y : DataIdx} {mt : MemType} :
      C.mems[x.val]? = some mt → C.datas[y.val]? = some .ok →
      Instr_okA C (.memoryInit x y)
        ⟨[mt.addr.toValType, ValType.i32, ValType.i32], [], []⟩
  /-- `rule Instr_okA/data.drop: C |- DATA.DROP x : eps -> eps
      -- if C.DATAS[x] = OK`. -/
  | data_drop {C : Context} {x : DataIdx} :
      C.datas[x.val]? = some .ok → Instr_okA C (.dataDrop x) ⟨[], [], []⟩
  /-- `rule Instr_okA/load:
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
      OptAll (fun (o : LoadOp) => LoadOp.wf nt o = true) op →
      OptAll (fun (o : LoadOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op →
      (op = none ∨ nt.toInn?.isSome = true) →
      Instr_okA C (.load nt op x ao) ⟨[mt.addr.toValType], [], [.num nt]⟩
  /-- `rule Instr_okA/load-val:
        C |- LOAD nt x memarg : at -> nt
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)`. -/
  | load_val {C : Context} {nt : NumType} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      Instr_okA C (.load nt none x ao) ⟨[mt.addr.toValType], [], [.num nt]⟩
  /-- `rule Instr_okA/load-pack:
        C |- LOAD Inn (M _ sx) x memarg : at -> Inn
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8)`.

  `(M _ sx)` is a `loadop_(Inn)`, whose own `-- if sz < $sizenn(Inn)` says the
  packed width is strictly narrower than the operand type; that is `LoadOp.wf`,
  and it is what distinguishes `I32.LOAD8_S` from a `loadop_`-shaped spelling of
  a plain `I32.LOAD`. -/
  | load_pack {C : Context} {n : Inn} {op : LoadOp} {x : MemIdx} {ao : MemArg}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      LoadOp.wf n.toNumType op = true →
      2 ^ ao.align.val ≤ op.sz.toNat / 8 →
      Instr_okA C (.load n.toNumType (some op) x ao)
        ⟨[mt.addr.toValType], [], [.num n.toNumType]⟩
  /-- `rule Instr_okA/store:
        C |- STORE nt N? x memarg : at nt -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)
        -- if $(2^(memarg.ALIGN) <= N/8 < $size(nt)/8)?
        -- if N? = eps \/ nt = Inn`

  COMMENTED OUT in the pinned source, as `Instr_okA/load` is. -/
  | store {C : Context} {nt : NumType} {op : Option StoreOp} {x : MemIdx}
      {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      OptAll (fun (o : StoreOp) => StoreOp.wf nt o = true) op →
      OptAll (fun (o : StoreOp) =>
          2 ^ ao.align.val ≤ o.sz.toNat / 8 ∧ o.sz.toNat / 8 < nt.size / 8) op →
      (op = none ∨ nt.toInn?.isSome = true) →
      Instr_okA C (.store nt op x ao) ⟨[mt.addr.toValType, .num nt], [], []⟩
  /-- `rule Instr_okA/store-val:
        C |- STORE nt x memarg : at nt -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $size(nt)/8)`. -/
  | store_val {C : Context} {nt : NumType} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ nt.size / 8 →
      Instr_okA C (.store nt none x ao) ⟨[mt.addr.toValType, .num nt], [], []⟩
  /-- `rule Instr_okA/store-pack:
        C |- STORE Inn M x memarg : at Inn -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8)`.

  `M` is a `storeop_(Inn)`, whose `-- if sz < $sizenn(Inn)` is `StoreOp.wf`. -/
  | store_pack {C : Context} {n : Inn} {op : StoreOp} {x : MemIdx} {ao : MemArg}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      StoreOp.wf n.toNumType op = true →
      2 ^ ao.align.val ≤ op.sz.toNat / 8 →
      Instr_okA C (.store n.toNumType (some op) x ao)
        ⟨[mt.addr.toValType, .num n.toNumType], [], []⟩
  /-- `rule Instr_okA/vload-val:
        C |- VLOAD V128 x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $vsize(V128)/8)`. -/
  | vload_val {C : Context} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ VecType.size .v128 / 8 →
      Instr_okA C (.vload .v128 none x ao) ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vload-pack:
        C |- VLOAD V128 (SHAPE M X N _ sx) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= M/8 * N)`.

  `(SHAPE M X N _ sx)` is a `vloadop_(V128)`, whose own
  `-- if $(sz * M = $vsize(vectype)/2)` fixes the packed half-vector: the shape
  covers exactly 64 of the 128 bits. -/
  | vload_pack {C : Context} {sz : Sz} {n : Nat} {sx : Sx} {x : MemIdx}
      {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      VLoadOp.wf .v128 (.shape sz n sx) = true →
      2 ^ ao.align.val ≤ sz.toNat / 8 * n →
      Instr_okA C (.vload .v128 (some (.shape sz n sx)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vload-splat:
        C |- VLOAD V128 (SPLAT N) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)`. -/
  | vload_splat {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      Instr_okA C (.vload .v128 (some (.splat sz)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vload-zero:
        C |- VLOAD V128 (ZERO N) x memarg : at -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)`.

  `(ZERO N)` is a `vloadop_(V128)`, whose own `-- if sz >= 32` rules out an
  8- or 16-bit zero-extending vector load. -/
  | vload_zero {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      VLoadOp.wf .v128 (.zero sz) = true →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      Instr_okA C (.vload .v128 (some (.zero sz)) x ao)
        ⟨[mt.addr.toValType], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vload_lane:
        C |- VLOAD_LANE V128 N x memarg i : at V128 -> V128
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)
        -- if $(i < 128/N)`. -/
  | vload_lane {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {i : LaneIdx}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      i.val < 128 / sz.toNat →
      Instr_okA C (.vloadLane .v128 sz x ao i)
        ⟨[mt.addr.toValType, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vstore:
        C |- VSTORE V128 x memarg : at V128 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= $vsize(V128)/8)`. -/
  | vstore {C : Context} {x : MemIdx} {ao : MemArg} {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ VecType.size .v128 / 8 →
      Instr_okA C (.vstore .v128 x ao) ⟨[mt.addr.toValType, ValType.v128], [], []⟩
  /-- `rule Instr_okA/vstore_lane:
        C |- VSTORE_LANE V128 N x memarg i : at V128 -> eps
        -- if C.MEMS[x] = at lim PAGE
        -- if $(2^(memarg.ALIGN) <= N/8)
        -- if $(i < 128/N)`. -/
  | vstore_lane {C : Context} {sz : Sz} {x : MemIdx} {ao : MemArg} {i : LaneIdx}
      {mt : MemType} :
      C.mems[x.val]? = some mt →
      2 ^ ao.align.val ≤ sz.toNat / 8 →
      i.val < 128 / sz.toNat →
      Instr_okA C (.vstoreLane .v128 sz x ao i)
        ⟨[mt.addr.toValType, ValType.v128], [], []⟩

  -- Numeric instructions
  /-- `rule Instr_okA/const: C |- CONST nt c_nt : eps -> nt`.

  `c_nt` is a `num_(nt)`, whose float instances are bounded by `fNmag`;
  `Num_.wf` is that bound. -/
  | const {C : Context} {nt : NumType} {c : Num_ nt} :
      Num_.wf nt c = true →
      Instr_okA C (.const nt c) ⟨[], [], [.num nt]⟩
  /-- `rule Instr_okA/unop: C |- UNOP nt unop_nt : nt -> nt`.

  `unop_nt` is a member of the family `unop_(numtype)` AT `nt`, which is what
  `Unop.wf nt` says; the flat Lean `Unop` cannot say it by typing. -/
  | unop {C : Context} {nt : NumType} {op : Unop} :
      Unop.wf nt op = true →
      Instr_okA C (.unop nt op) ⟨[.num nt], [], [.num nt]⟩
  /-- `rule Instr_okA/binop: C |- BINOP nt binop_nt : nt nt -> nt`. -/
  | binop {C : Context} {nt : NumType} {op : Binop} :
      Binop.wf nt op = true →
      Instr_okA C (.binop nt op) ⟨[.num nt, .num nt], [], [.num nt]⟩
  /-- `rule Instr_okA/testop: C |- TESTOP nt testop_nt : nt -> I32`. -/
  | testop {C : Context} {nt : NumType} {op : Testop} :
      Testop.wf nt op = true →
      Instr_okA C (.testop nt op) ⟨[.num nt], [], [ValType.i32]⟩
  /-- `rule Instr_okA/relop: C |- RELOP nt relop_nt : nt nt -> I32`. -/
  | relop {C : Context} {nt : NumType} {op : Relop} :
      Relop.wf nt op = true →
      Instr_okA C (.relop nt op) ⟨[.num nt, .num nt], [], [ValType.i32]⟩
  /-- `rule Instr_okA/cvtop: C |- CVTOP nt_1 nt_2 cvtop : nt_2 -> nt_1`.

  `cvtop` is a member of `cvtop__(nt_2, nt_1)` --- operand type first --- which
  carries `WRAP`'s `size_1 > size_2`, `EXTEND`'s converse and `REINTERPRET`'s
  equal-width condition. -/
  | cvtop {C : Context} {nt₁ nt₂ : NumType} {op : Cvtop} :
      Cvtop.wf nt₂ nt₁ op = true →
      Instr_okA C (.cvtop nt₁ nt₂ op) ⟨[.num nt₂], [], [.num nt₁]⟩

  -- Vector instructions
  /-- `rule Instr_okA/vconst: C |- VCONST V128 c : eps -> V128`. -/
  | vconst {C : Context} {c : VecLit (VecType.toVnn .v128)} :
      Instr_okA C (.vconst .v128 c) ⟨[], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vvunop: C |- VVUNOP V128 vvunop : V128 -> V128`. -/
  | vvunop {C : Context} {op : VVUnop} :
      Instr_okA C (.vvunop .v128 op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vvbinop: C |- VVBINOP V128 vvbinop : V128 V128 -> V128`. -/
  | vvbinop {C : Context} {op : VVBinop} :
      Instr_okA C (.vvbinop .v128 op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vvternop: C |- VVTERNOP V128 vvternop : V128 V128 V128 -> V128`. -/
  | vvternop {C : Context} {op : VVTernop} :
      Instr_okA C (.vvternop .v128 op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vvtestop: C |- VVTESTOP V128 vvtestop : V128 -> I32`. -/
  | vvtestop {C : Context} {op : VVTestop} :
      Instr_okA C (.vvtestop .v128 op) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_okA/vunop: C |- VUNOP sh vunop : V128 -> V128`.

  `sh` is a `shape`, whose `$lsize(lanetype) * dim = 128` is `Shape.wf`, and
  `vunop` is a member of `vunop_(sh)`, which carries `POPCNT`'s
  `$lsizenn(Jnn) = 8`. -/
  | vunop {C : Context} {sh : Shape} {op : VUnop} :
      sh.wf = true → VUnop.wf sh op = true →
      Instr_okA C (.vunop sh op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vbinop: C |- VBINOP sh vbinop : V128 V128 -> V128`. -/
  | vbinop {C : Context} {sh : Shape} {op : VBinop} :
      sh.wf = true → VBinop.wf sh op = true →
      Instr_okA C (.vbinop sh op) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vternop: C |- VTERNOP sh vternop : V128 V128 V128 -> V128`. -/
  | vternop {C : Context} {sh : Shape} {op : VTernop} :
      sh.wf = true → VTernop.wf sh op = true →
      Instr_okA C (.vternop sh op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vtestop: C |- VTESTOP sh vtestop : V128 -> I32`. -/
  | vtestop {C : Context} {sh : Shape} {op : VTestop} :
      sh.wf = true → VTestop.wf sh op = true →
      Instr_okA C (.vtestop sh op) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_okA/vrelop: C |- VRELOP sh vrelop : V128 V128 -> V128`. -/
  | vrelop {C : Context} {sh : Shape} {op : VRelop} :
      sh.wf = true → VRelop.wf sh op = true →
      Instr_okA C (.vrelop sh op) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vshiftop: C |- VSHIFTOP sh vshiftop : V128 I32 -> V128`.

  `ishape`'s own `-- if $lanetype(shape) = Jnn` is carried by the subtype; what
  is left is `shape`'s `$lsize(lanetype) * dim = 128`. -/
  | vshiftop {C : Context} {sh : IShape} {op : VShiftop} :
      sh.val.wf = true →
      Instr_okA C (.vshiftop sh op) ⟨[ValType.v128, ValType.i32], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vbitmask: C |- VBITMASK sh : V128 -> I32`. -/
  | vbitmask {C : Context} {sh : IShape} :
      sh.val.wf = true →
      Instr_okA C (.vbitmask sh) ⟨[ValType.v128], [], [ValType.i32]⟩
  /-- `rule Instr_okA/vswizzlop: C |- VSWIZZLOP sh vswizzlop : V128 V128 -> V128`. -/
  | vswizzlop {C : Context} {sh : BShape} {op : VSwizzlop} :
      sh.val.wf = true →
      Instr_okA C (.vswizzlop sh op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vshuffle: C |- VSHUFFLE sh i* : V128 V128 -> V128
      -- (if $(i < 2*$dim(sh)))*`.

  The syntax of `VSHUFFLE bshape laneidx*` additionally carries
  `-- if |laneidx*| = $dim(bshape)`: a shuffle names exactly as many lanes as
  the shape has. -/
  | vshuffle {C : Context} {sh : BShape} {is : List LaneIdx} :
      sh.val.wf = true → is.length = sh.val.dim.toNat →
      SeqAll (fun (i : LaneIdx) => i.val < 2 * sh.val.dim.toNat) is →
      Instr_okA C (.vshuffle sh is) ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vsplat: C |- VSPLAT sh : $unpackshape(sh) -> V128`. -/
  | vsplat {C : Context} {sh : Shape} :
      sh.wf = true →
      Instr_okA C (.vsplat sh) ⟨[.num sh.unpack], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vextract_lane:
        C |- VEXTRACT_LANE sh sx? i : V128 -> $unpackshape(sh)
        -- if i < $dim(sh)`.

  The syntax of `VEXTRACT_LANE shape sx? laneidx` additionally carries
  `-- if sx? = eps <=> $lanetype(shape) <- I32 I64 F32 F64`: the signedness is
  present exactly when the lane type is packed. -/
  | vextract_lane {C : Context} {sh : Shape} {sx : Option Sx} {i : LaneIdx} :
      sh.wf = true → sx.isNone = sh.laneIsNum →
      i.val < sh.dim.toNat →
      Instr_okA C (.vextractLane sh sx i) ⟨[ValType.v128], [], [.num sh.unpack]⟩
  /-- `rule Instr_okA/vreplace_lane:
        C |- VREPLACE_LANE sh i : V128 $unpackshape(sh) -> V128
        -- if i < $dim(sh)`. -/
  | vreplace_lane {C : Context} {sh : Shape} {i : LaneIdx} :
      sh.wf = true → i.val < sh.dim.toNat →
      Instr_okA C (.vreplaceLane sh i)
        ⟨[ValType.v128, .num sh.unpack], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vextunop: C |- VEXTUNOP sh_1 sh_2 vextunop : V128 -> V128`.

  `vextunop` is a member of `vextunop__(sh_2, sh_1)` --- operand shape first ---
  which carries `EXTADD_PAIRWISE`'s
  `16 <= 2 * $lsizenn1(Jnn_1) = $lsizenn2(Jnn_2) <= 32`. -/
  | vextunop {C : Context} {sh₁ sh₂ : IShape} {op : VExtUnop} :
      sh₁.val.wf = true → sh₂.val.wf = true → VExtUnop.wf sh₂ sh₁ op = true →
      Instr_okA C (.vextunop sh₁ sh₂ op) ⟨[ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vextbinop: C |- VEXTBINOP sh_1 sh_2 vextbinop : V128 V128 -> V128`. -/
  | vextbinop {C : Context} {sh₁ sh₂ : IShape} {op : VExtBinop} :
      sh₁.val.wf = true → sh₂.val.wf = true → VExtBinop.wf sh₂ sh₁ op = true →
      Instr_okA C (.vextbinop sh₁ sh₂ op)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vextternop:
      C |- VEXTTERNOP sh_1 sh_2 vextternop : V128 V128 V128 -> V128`. -/
  | vextternop {C : Context} {sh₁ sh₂ : IShape} {op : VExtTernop} :
      sh₁.val.wf = true → sh₂.val.wf = true → VExtTernop.wf sh₂ sh₁ op = true →
      Instr_okA C (.vextternop sh₁ sh₂ op)
        ⟨[ValType.v128, ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vnarrow: C |- VNARROW sh_1 sh_2 sx : V128 V128 -> V128`.

  The syntax of `VNARROW ishape_1 ishape_2 sx` carries
  `-- if $($lsize($lanetype(ishape_2)) = 2*$lsize($lanetype(ishape_1)) <= 32)`:
  the operand lanes are twice the result lanes, and at most 32 bits wide. -/
  | vnarrow {C : Context} {sh₁ sh₂ : IShape} {sx : Sx} :
      sh₁.val.wf = true → sh₂.val.wf = true →
      sh₂.laneSize = 2 * sh₁.laneSize → 2 * sh₁.laneSize ≤ 32 →
      Instr_okA C (.vnarrow sh₁ sh₂ sx)
        ⟨[ValType.v128, ValType.v128], [], [ValType.v128]⟩
  /-- `rule Instr_okA/vcvtop: C |- VCVTOP sh_1 sh_2 vcvtop : V128 -> V128`.

  `vcvtop` is a member of `vcvtop__(sh_2, sh_1)` --- operand shape first ---
  which carries every width and `half?`/`zero?` condition of the four
  instances. -/
  | vcvtop {C : Context} {sh₁ sh₂ : Shape} {op : VCvtop} :
      sh₁.wf = true → sh₂.wf = true → VCvtop.wf sh₂ sh₁ op = true →
      Instr_okA C (.vcvtop sh₁ sh₂ op) ⟨[ValType.v128], [], [ValType.v128]⟩

/-- `relation Instrs_okA: context |- instr* : instrtype`. -/
inductive Instrs_okA : Context → List Instr → InstrType → Prop where
  /-- `rule Instrs_okA/empty: C |- eps : eps -> eps`. -/
  | empty {C : Context} : Instrs_okA C [] ⟨[], [], []⟩
  /-- AMD-005 sequence composition with the carried stack frame `ts₀`. -/
  | seq {C : Context} {i₁ : Instr} {is : List Instr}
      {ts₀ ts₁ ts₂ ts₃ ts : List ValType} {xs₁ xs₂ : List LocalIdx} :
      Instr_okA C i₁ ⟨ts₁, xs₁, ts₂⟩ →
      SeqLen₂ xs₁ ts →
      SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
          ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs₁ ts →
      Resulttype_okA C ts₀ →
      Instrs_okA (Context.withLocals C xs₁ (ts.map (fun t => ⟨.set, t⟩))) is
        ⟨ts₀ ++ ts₂, xs₂, ts₃⟩ →
      Instrs_okA C (i₁ :: is) ⟨ts₀ ++ ts₁, xs₁ ++ xs₂, ts₃⟩
  /-- `rule Instrs_okA/sub:
        C |- instr* : it'
        -- Instrs_okA: C |- instr* : it
        -- Instrtype_subA: C |- it <: it'
        -- Instrtype_okA: C |- it' : OK`. -/
  | sub {C : Context} {is : List Instr} {it it' : InstrType} :
      Instrs_okA C is it → Instrtype_subA C it it' → Instrtype_okA C it' →
      Instrs_okA C is it'
  /-- `rule Instrs_okA/frame:
        C |- instr* : (t* t_1*) ->_(x*) (t* t_2*)
        -- Instrs_okA: C |- instr* : t_1* ->_(x*) t_2*
        -- Resulttype_okA: C |- t* : OK`. -/
  | frame {C : Context} {is : List Instr} {ts ts₁ ts₂ : List ValType}
      {xs : List LocalIdx} :
      Instrs_okA C is ⟨ts₁, xs, ts₂⟩ → Resulttype_okA C ts →
      Instrs_okA C is ⟨ts ++ ts₁, xs, ts ++ ts₂⟩

end

/-- Every instruction admitted by the combined amended hierarchy satisfies
the syntax-level operator and shape side conditions. -/
theorem Instr_okA.wf_of {C : Context} {i : Instr} {it : InstrType}
    (h : Instr_okA C i it) : Instr.wf i = true := by
  induction h using Instr_okA.rec
    (motive_2 := fun _ is _ _ => ∀ j ∈ is, Instr.wf j = true)
  case load _ _ op _ _ _ _ _ hwf _ _ =>
    cases op with
    | none => rfl
    | some o => exact hwf o rfl
  case store _ _ op _ _ _ _ _ hwf _ _ =>
    cases op with
    | none => rfl
    | some o => exact hwf o rfl
  case seq =>
    rename_i ih₁ ih₂ j hj
    cases hj with
    | head => exact ih₁
    | tail _ hj => exact ih₂ j hj
  all_goals
    first
      | rfl
      | assumption
      | (rw [InstrSeq.wf_iff_forall]; assumption)
      | simp_all [Instr.wf, InstrSeq.wf_iff_forall]

/-- Sequence form of `Instr_okA.wf_of`. -/
theorem Instrs_okA.wf_of {C : Context} {is : List Instr} {it : InstrType}
    (h : Instrs_okA C is it) : ∀ i ∈ is, Instr.wf i = true := by
  induction h using Instrs_okA.rec
    (motive_1 := fun _ i _ _ => Instr.wf i = true)
  case load _ _ op _ _ _ _ _ hwf _ _ =>
    cases op with
    | none => rfl
    | some o => exact hwf o rfl
  case store _ _ op _ _ _ _ _ hwf _ _ =>
    cases op with
    | none => rfl
    | some o => exact hwf o rfl
  case seq =>
    rename_i ih₁ ih₂
    intro j hj
    cases hj with
    | head => exact ih₁
    | tail _ hj => exact ih₂ j hj
  all_goals
    first
      | rfl
      | assumption
      | (rw [InstrSeq.wf_iff_forall]; assumption)
      | simp_all [Instr.wf, InstrSeq.wf_iff_forall]

inductive Expr_okA : Context → Expr → List ValType → Prop where
  | mk {C : Context} {e : Expr} {ts : List ValType} :
      Instrs_okA C (InstrSeq.toList e) ⟨[], [], ts⟩ → Expr_okA C e ts

inductive Expr_ok_constA : Context → Expr → ValType → Prop where
  | mk {C : Context} {e : Expr} {t : ValType} :
      Expr_okA C e [t] → Expr_const C e → Expr_ok_constA C e t

/-! ## AMD-005 non-vacuity and arity discipline

These witnesses live on the sole combined hierarchy.  They replace the
corresponding declarations from the deleted intermediate AMD-005-only path. -/

private theorem rt_okA_nil {C : Context} : Resulttype_okA C [] :=
  .mk (fun _ h => nomatch h)

private theorem rt_okA_cons {C : Context} {t : ValType} {ts : List ValType}
    (ht : Valtype_okA C t) (hts : Resulttype_okA C ts) :
    Resulttype_okA C (t :: ts) := by
  cases hts with
  | mk hall => exact .mk (fun a ha => by cases ha with
      | head => exact ht
      | tail _ ha => exact hall a ha)

private theorem seqAll₂_nilA {α β : Type} {R : α → β → Prop} :
    SeqAll₂ R [] [] := fun _ _ _ h _ => nomatch h

/-- The empty sequence remains balanced: subsumption preserves both lengths
and framing grows both sides equally. -/
theorem Instrs_okA.nil_length {C : Context} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_okA C is it →
      is = [] → it.dom.length = it.cod.length := by
  intro is it h
  induction h using Instrs_okA.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro _; rfl
  case seq => intro he; exact absurd he (by simp)
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, hcod, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      obtain ⟨hcl, _⟩ := hcod
      have hih := ih he
      simp only [] at hdl hcl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

/-- Every combined-amended type of a singleton binary instruction still
requires at least two operands. -/
theorem Instrs_okA.binop_dom_length {C : Context} {nt : NumType} {op : Binop} :
    ∀ {is : List Instr} {it : InstrType}, Instrs_okA C is it →
      is = [Instr.binop nt op] → 2 ≤ it.dom.length := by
  intro is it h
  induction h using Instrs_okA.rec (motive_1 := fun _ _ _ _ => True)
  case empty => intro he; exact absurd he (by simp)
  case seq _ _ _ _ _ _ _ _ _ _ hi _ _ _ _ _ _ =>
      intro he
      simp only [List.cons.injEq] at he
      obtain ⟨he₁, _⟩ := he
      subst he₁
      cases hi
      simp
  case sub _ _ _ _ _ hsub _ ih =>
      intro he
      obtain ⟨hdom, _, _⟩ := hsub
      obtain ⟨hdl, _⟩ := hdom
      have hih := ih he
      simp only [] at hdl hih ⊢
      omega
  case frame _ _ _ _ _ _ _ _ ih =>
      intro he
      have hih := ih he
      simp only [] at hih ⊢
      simp only [List.length_append]
      omega
  all_goals trivial

private theorem rt_okA_i32 {C : Context} : Resulttype_okA C [ValType.i32] :=
  rt_okA_cons (.num .mk) rt_okA_nil

private theorem instrs_okA_nil_i32 {C : Context} :
    Instrs_okA C [] ⟨[ValType.i32], [], [ValType.i32]⟩ :=
  Instrs_okA.frame (ts := [ValType.i32]) Instrs_okA.empty rt_okA_i32

private theorem instrs_okA_binop {C : Context} :
    Instrs_okA C [Instr.binop .i32 (.int .add)]
      ⟨[ValType.i32, ValType.i32], [], [ValType.i32]⟩ := by
  have h := Instrs_okA.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_okA.binop (nt := .i32) (op := .int .add) rfl) rfl seqAll₂_nilA
    rt_okA_nil (by simpa using instrs_okA_nil_i32)
  simpa using h

/-- The framed composition missing from the pinned sequence rule. -/
theorem Instrs_okA.const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_okA C [Instr.const .i32 c, Instr.binop .i32 (.int .add)]
      ⟨[ValType.i32], [], [ValType.i32]⟩ := by
  have h := Instrs_okA.seq (C := C) (ts₀ := [ValType.i32]) (ts := [])
    (Instr_okA.const hc) rfl seqAll₂_nilA rt_okA_i32
    (by simpa using instrs_okA_binop)
  simpa using h

/-- The ordinary constant-folded arithmetic expression has a combined amended
derivation. -/
theorem Instrs_okA.const_const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Instrs_okA C
      [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)]
      ⟨[], [], [ValType.i32]⟩ := by
  have h := Instrs_okA.seq (C := C) (ts₀ := []) (ts := [])
    (Instr_okA.const hc) rfl seqAll₂_nilA rt_okA_nil
    (by simpa using Instrs_okA.const_binop (C := _) hc)
  simpa using h

/-- Expression-level AMD-005 non-vacuity on the corrected hierarchy. -/
theorem Expr_okA.const_const_binop {C : Context} {c : Num_ .i32}
    (hc : Num_.wf .i32 c = true) :
    Expr_okA C (InstrSeq.ofList
      [Instr.const .i32 c, Instr.const .i32 c, Instr.binop .i32 (.int .add)])
      [ValType.i32] := by
  refine .mk ?_
  rw [InstrSeq.toList_ofList]
  exact Instrs_okA.const_const_binop hc

end WasmGemmGnaf.Wasm.Core
