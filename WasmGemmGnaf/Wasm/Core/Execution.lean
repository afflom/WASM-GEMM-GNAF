/-
  Wasm/Core/Execution.lean --- the single authority-selected step hierarchy for
  WebAssembly Core 3.0.

  NORMATIVE SOURCE.  Every constructor below transcribes one rule of

      vendor/wasm-spec/specification/wasm-3.0/4.3-execution.instructions.spectec

  at the pinned commit.  The coverage marker beside a constructor names the
  SpecTec rule it discharges; `xtask core` extracts the checklist from the
  vendored file itself and rejects a marker naming anything it does not define.

  THE RELATION IS RELATIONAL.  `Step_pure`, `Step_read` and `Step` are three
  distinct relations in the source and are three distinct inductive relations
  here.  Nothing below is an evaluator: `memory.grow`, `table.grow` and the
  set-valued numeric operators are genuinely nondeterministic, and a `Prop`-valued
  relation is what lets every permitted successor be a member rather than one
  chosen path.

  ORDER.  The source states `Step/pure`, `Step/read`, `Steps/*` and `Step/ctxt-*`
  first and the `Step_pure`/`Step_read` rules after.  Lean requires a relation to
  be defined before it is referred to, so the file defines `Step_pure`, then
  `Step_read`, then `Step`, then `Steps`, then `Eval_expr`.  No rule is dropped or
  merged by the reordering, and none of the four relations is mutually recursive
  with another: `Step` refers to `Step_pure`, `Step_read` and itself, and `Steps`
  refers to `Step` and itself.  The default selector retains the byte-identical
  pinned transcription for audit compatibility; the explicit erased endpoints
  below apply AMD-011.  `Core/EventExecution.lean` supplies the sole public,
  event-labelled `StepA`, `StepsA`, and `Eval_exprA` machine relations.

  `-- otherwise`.  SpecTec reads `-- otherwise` as the negation of the premises of
  every preceding rule of the same relation whose conclusion has the same shape.
  Each such rule below carries that negation written out.  Nothing is left
  implicit, because an implicit `otherwise` is a rule that claims more than it
  states.

  WHAT `Numerics` IS.  The lanewise meaning of the vector operators
  (`3.2-numerics.vector.spectec`) is transcribed in `Core/Numerics.lean` and is
  reached below through `Numerics` by ordinary dot notation: `Nm.vbinop_`,
  `Nm.vcvtop__` and the rest are DEFINITIONS, not fields, so the relation is
  pinned to the source's own equations rather than quantified over every
  interpretation of them.  What `Nm` still quantifies over is exactly what the
  pinned source leaves abstract -- its 74 `hint(builtin)` primitives, of which
  this development calls 61 -- and `Core/Numerics.lean`'s header names them.
-/
import WasmGemmGnaf.Wasm.Core.ConcreteNumerics
import WasmGemmGnaf.Wasm.Core.HandlerExecutionAmendment

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Reading the source's notation -/

/-- `instr*` of the syntactic sort, read as administrative instructions. -/
def plains (is : List Instr) : List AdminInstr := is.map AdminInstr.plain

/-- `expr` read as an administrative instruction sequence. -/
def exprAdmin (e : Expr) : List AdminInstr := plains e.toList

/-- The `numtype` an `addrtype` is. -/
def addrNumType : AddrType → NumType
  | .i32 => .i32
  | .i64 => .i64

/-- `$size(at)`. -/
def addrSize (att : AddrType) : Nat := (addrNumType att).size

/-- `num_(at)`, spelled so that the bound `i < 2^$size(at)` is visible to
`Subtype.val` without a case split. -/
abbrev AddrLit (att : AddrType) : Type := IN (addrSize att)

/-- `num_(at)` and `num_(addrtype-as-numtype)` are the same carrier. -/
def addrLitToNum : (att : AddrType) → AddrLit att → Num_ (addrNumType att)
  | .i32, c => c
  | .i64, c => c

/-- `(CONST at i)`. -/
def constAddr (att : AddrType) (i : AddrLit att) : AdminInstr :=
  .plain (.const (addrNumType att) (addrLitToNum att i))

/-- `(CONST I32 c)`. -/
def constI32 (c : U32) : AdminInstr := .plain (.const .i32 c)

/-- `num_(Inn)` with a visible bound. -/
abbrev InnLit (inn : Inn) : Type := IN inn.size

/-- `num_(Inn)` and `num_(Inn-as-numtype)` are the same carrier. -/
def innLitToNum : (inn : Inn) → InnLit inn → Num_ inn.toNumType
  | .i32, c => c
  | .i64, c => c

/-- `(CONST Inn c)`. -/
def constInn (inn : Inn) (c : InnLit inn) : AdminInstr :=
  .plain (.const inn.toNumType (innLitToNum inn c))

/-- The storage type of a `fieldtype`; `FieldType` is a one-constructor
inductive, so this is its second projection. -/
def fieldStorage : FieldType → StorageType
  | .mk _ zt => zt

/-- `lane_(lanetype)` from `iN($lsize(lanetype))`.  The two are the same carrier
at every integer lane type, and the source's `Jnn` side conditions exclude the
float lane types, where this is `none`. -/
def inToLane : (lt : LaneType) → IN lt.size → Option (Lane_ lt)
  | .num .i32, c => some c
  | .num .i64, c => some c
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, c => some c

/-- `iN($lsize(lanetype))` from `lane_(lanetype)`; the inverse of `inToLane`. -/
def laneToIN : (lt : LaneType) → Lane_ lt → Option (IN lt.size)
  | .num .i32, c => some c
  | .num .i64, c => some c
  | .num .f32, _ => none
  | .num .f64, _ => none
  | .pack _, c => some c

/-- `def $sx(consttype) = eps`, `def $sx(packtype) = S`. -/
def sx_ : StorageType → Option (Option Sx)
  | .val (.num _) => some none
  | .val (.vec _) => some none
  | .val (.ref _) => none
  | .val .bot => none
  | .pack _ => some (some .s)

/-- `def $blocktype_(z, _IDX x) = t_1* -> t_2*  -- Expand: $type(z, x) ~~ FUNC t_1* -> t_2*`,
`def $blocktype_(z, _RESULT t?) = eps -> t?`. -/
def blocktype_ (z : State) : BlockType → Option (List ValType × List ValType)
  | .idx x =>
      match z.typeOf x with
      | some dt =>
          match expandDt dt with
          | some (.func dom cod) => some (dom.toList, cod.toList)
          | _ => none
      | none => none
  | .result t => some ([], t.toList)

/-- Whether the head `catch` of a handler catches the exception at `a`; the
premise the four `throw_ref-handler-catch*` rules share, and the one
`throw_ref-handler-next` negates. -/
def catchMatches (z : State) (a : ExnAddr) : Catch → Prop
  | .tag x _ =>
      ∃ ex ta, z.exninst[a]? = some ex ∧ z.tagaddr[x.val]? = some ta ∧ ex.tag = ta
  | .tagRef x _ =>
      ∃ ex ta, z.exninst[a]? = some ex ∧ z.tagaddr[x.val]? = some ta ∧ ex.tag = ta
  | .all _ => True
  | .allRef _ => True

/-! ## `relation Step_pure: instr* ~> instr*`

The reductions that read neither the store nor the frame. -/

/-- `relation Step_pure: instr* ~> instr*  hint(name "E")`. -/
inductive Step_pure (Nm : Numerics) : List AdminInstr → List AdminInstr → Prop where
  /-- `rule Step_pure/unreachable: UNREACHABLE ~> TRAP`. -/
  -- core-exec: Step_pure/unreachable
  | unreachable : Step_pure Nm [.plain .unreachable] [.trap]
  /-- `rule Step_pure/nop: NOP ~> eps`. -/
  -- core-exec: Step_pure/nop
  | nop : Step_pure Nm [.plain .nop] []
  /-- `rule Step_pure/drop: val DROP ~> eps`. -/
  -- core-exec: Step_pure/drop
  | drop {v : Val} : Step_pure Nm [v.toAdmin, .plain .drop] []
  /-- `rule Step_pure/select-true:
      val_1 val_2 (CONST I32 c) (SELECT (t*)?) ~> val_1  -- if c =/= 0`. -/
  -- core-exec: Step_pure/select-true
  | selectTrue {v₁ v₂ : Val} {c : U32} {ts : Option (List ValType)} :
      c.val ≠ 0 →
      Step_pure Nm [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] [v₁.toAdmin]
  /-- `rule Step_pure/select-false:
      val_1 val_2 (CONST I32 c) (SELECT (t*)?) ~> val_2  -- if c = 0`. -/
  -- core-exec: Step_pure/select-false
  | selectFalse {v₁ v₂ : Val} {c : U32} {ts : Option (List ValType)} :
      c.val = 0 →
      Step_pure Nm [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] [v₂.toAdmin]
  /-- `rule Step_pure/if-true:
      (CONST I32 c) (IF bt instr_1* ELSE instr_2*) ~> (BLOCK bt instr_1*)
      -- if c =/= 0`. -/
  -- core-exec: Step_pure/if-true
  | ifTrue {c : U32} {bt : BlockType} {is₁ is₂ : InstrSeq} :
      c.val ≠ 0 →
      Step_pure Nm [constI32 c, .plain (.ifElse bt is₁ is₂)] [.plain (.block bt is₁)]
  /-- `rule Step_pure/if-false:
      (CONST I32 c) (IF bt instr_1* ELSE instr_2*) ~> (BLOCK bt instr_2*)
      -- if c = 0`. -/
  -- core-exec: Step_pure/if-false
  | ifFalse {c : U32} {bt : BlockType} {is₁ is₂ : InstrSeq} :
      c.val = 0 →
      Step_pure Nm [constI32 c, .plain (.ifElse bt is₁ is₂)] [.plain (.block bt is₂)]
  /-- ``rule Step_pure/label-vals: (LABEL_ n `{instr*} val*) ~> val*``. -/
  -- core-exec: Step_pure/label-vals
  | labelVals {n : Nat} {cont : List AdminInstr} {vs : List Val} :
      Step_pure Nm [.label n cont (vals vs)] (vals vs)
  /-- ``rule Step_pure/br-label-zero:
      (LABEL_ n `{instr'*} val'* val^n (BR l) instr*) ~> val^n instr'*  -- if l = 0``. -/
  -- core-exec: Step_pure/br-label-zero
  | brLabelZero {n : Nat} {cont : List AdminInstr} {vs' vs : List Val}
      {l : LabelIdx} {is : List AdminInstr} :
      vs.length = n → l.val = 0 →
      Step_pure Nm [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ is)]
        (vals vs ++ cont)
  /-- ``rule Step_pure/br-label-succ:
      (LABEL_ n `{instr'*} val* (BR l) instr*) ~> val* (BR $(l - 1))  -- if l > 0``. -/
  -- core-exec: Step_pure/br-label-succ
  | brLabelSucc {n : Nat} {cont : List AdminInstr} {vs : List Val}
      {l l' : LabelIdx} {is : List AdminInstr} :
      l.val = l'.val + 1 →
      Step_pure Nm [.label n cont (vals vs ++ [.plain (.br l)] ++ is)]
        (vals vs ++ [.plain (.br l')])
  /-- ``rule Step_pure/br-handler:
      (HANDLER_ n `{catch*} val* (BR l) instr*) ~> val* (BR l)``. -/
  -- core-exec: Step_pure/br-handler
  | brHandler {n : Nat} {cs : List Catch} {vs : List Val} {l : LabelIdx}
      {is : List AdminInstr} :
      Step_pure Nm [.handler n cs (vals vs ++ [.plain (.br l)] ++ is)]
        (vals vs ++ [.plain (.br l)])
  /-- `rule Step_pure/br_if-true: (CONST I32 c) (BR_IF l) ~> (BR l)  -- if c =/= 0`. -/
  -- core-exec: Step_pure/br_if-true
  | brIfTrue {c : U32} {l : LabelIdx} :
      c.val ≠ 0 → Step_pure Nm [constI32 c, .plain (.brIf l)] [.plain (.br l)]
  /-- `rule Step_pure/br_if-false: (CONST I32 c) (BR_IF l) ~> eps  -- if c = 0`. -/
  -- core-exec: Step_pure/br_if-false
  | brIfFalse {c : U32} {l : LabelIdx} :
      c.val = 0 → Step_pure Nm [constI32 c, .plain (.brIf l)] []
  /-- `rule Step_pure/br_table-lt:
      (CONST I32 i) (BR_TABLE l* l') ~> (BR l*[i])  -- if i < |l*|`. -/
  -- core-exec: Step_pure/br_table-lt
  | brTableLt {i : U32} {ls : List LabelIdx} {l' l : LabelIdx} :
      ls[i.val]? = some l →
      Step_pure Nm [constI32 i, .plain (.brTable ls l')] [.plain (.br l)]
  /-- `rule Step_pure/br_table-ge:
      (CONST I32 i) (BR_TABLE l* l') ~> (BR l')  -- if i >= |l*|`. -/
  -- core-exec: Step_pure/br_table-ge
  | brTableGe {i : U32} {ls : List LabelIdx} {l' : LabelIdx} :
      i.val ≥ ls.length →
      Step_pure Nm [constI32 i, .plain (.brTable ls l')] [.plain (.br l')]
  /-- `rule Step_pure/br_on_null-null:
      val (BR_ON_NULL l) ~> (BR l)  -- if val = REF.NULL ht`. -/
  -- core-exec: Step_pure/br_on_null-null
  | brOnNullNull {ht : HeapType} {l : LabelIdx} :
      Step_pure Nm [Val.toAdmin (.ref (.null ht)), .plain (.brOnNull l)] [.plain (.br l)]
  /-- `rule Step_pure/br_on_null-addr: val (BR_ON_NULL l) ~> val  -- otherwise`. -/
  -- core-exec: Step_pure/br_on_null-addr
  | brOnNullAddr {v : Val} {l : LabelIdx} :
      (∀ ht : HeapType, v ≠ .ref (.null ht)) →
      Step_pure Nm [v.toAdmin, .plain (.brOnNull l)] [v.toAdmin]
  /-- `rule Step_pure/br_on_non_null-null:
      val (BR_ON_NON_NULL l) ~> eps  -- if val = REF.NULL ht`. -/
  -- core-exec: Step_pure/br_on_non_null-null
  | brOnNonNullNull {ht : HeapType} {l : LabelIdx} :
      Step_pure Nm [Val.toAdmin (.ref (.null ht)), .plain (.brOnNonNull l)] []
  /-- `rule Step_pure/br_on_non_null-addr:
      val (BR_ON_NON_NULL l) ~> val (BR l)  -- otherwise`. -/
  -- core-exec: Step_pure/br_on_non_null-addr
  | brOnNonNullAddr {v : Val} {l : LabelIdx} :
      (∀ ht : HeapType, v ≠ .ref (.null ht)) →
      Step_pure Nm [v.toAdmin, .plain (.brOnNonNull l)] [v.toAdmin, .plain (.br l)]
  /-- `rule Step_pure/call_indirect:
      (CALL_INDIRECT x yy) ~> (TABLE.GET x) (REF.CAST (REF NULL yy)) (CALL_REF yy)`. -/
  -- core-exec: Step_pure/call_indirect
  | callIndirect {x : TableIdx} {yy : TypeUse} :
      Step_pure Nm [.plain (.callIndirect x yy)]
        [.plain (.tableGet x), .plain (.refCast (.ref (some .null) (.use yy))),
         .plain (.callRef yy)]
  /-- `rule Step_pure/return_call_indirect:
      (RETURN_CALL_INDIRECT x yy) ~>
      (TABLE.GET x) (REF.CAST (REF NULL yy)) (RETURN_CALL_REF yy)`. -/
  -- core-exec: Step_pure/return_call_indirect
  | returnCallIndirect {x : TableIdx} {yy : TypeUse} :
      Step_pure Nm [.plain (.returnCallIndirect x yy)]
        [.plain (.tableGet x), .plain (.refCast (.ref (some .null) (.use yy))),
         .plain (.returnCallRef yy)]
  /-- ``rule Step_pure/frame-vals: (FRAME_ n `{f} val^n) ~> val^n``. -/
  -- core-exec: Step_pure/frame-vals
  | frameVals {n : Nat} {f : Frame} {vs : List Val} :
      vs.length = n → Step_pure Nm [.frame n f (vals vs)] (vals vs)
  /-- ``rule Step_pure/return-frame:
      (FRAME_ n `{f} val'* val^n RETURN instr*) ~> val^n``. -/
  -- core-exec: Step_pure/return-frame
  | returnFrame {n : Nat} {f : Frame} {vs' vs : List Val} {is : List AdminInstr} :
      vs.length = n →
      Step_pure Nm [.frame n f (vals vs' ++ vals vs ++ [.plain .ret] ++ is)] (vals vs)
  /-- ``rule Step_pure/return-label:
      (LABEL_ n `{instr'*} val* RETURN instr*) ~> val* RETURN``. -/
  -- core-exec: Step_pure/return-label
  | returnLabel {n : Nat} {cont : List AdminInstr} {vs : List Val} {is : List AdminInstr} :
      Step_pure Nm [.label n cont (vals vs ++ [.plain .ret] ++ is)]
        (vals vs ++ [.plain .ret])
  /-- ``rule Step_pure/return-handler:
      (HANDLER_ n `{catch*} val* RETURN instr*) ~> val* RETURN``. -/
  -- core-exec: Step_pure/return-handler
  | returnHandler {n : Nat} {cs : List Catch} {vs : List Val} {is : List AdminInstr} :
      Step_pure Nm [.handler n cs (vals vs ++ [.plain .ret] ++ is)]
        (vals vs ++ [.plain .ret])
  /-- ``rule Step_pure/handler-vals: (HANDLER_ n `{catch*} val*) ~> val*``. -/
  -- core-exec: Step_pure/handler-vals
  | handlerVals {n : Nat} {cs : List Catch} {vs : List Val} :
      Step_pure Nm [.handler n cs (vals vs)] (vals vs)
  /-- `rule Step_pure/trap-instrs:
      val* TRAP instr* ~> TRAP  -- if val* =/= eps \/ instr* =/= eps`. -/
  -- core-exec: Step_pure/trap-instrs
  | trapInstrs {vs : List Val} {is : List AdminInstr} :
      (vs ≠ [] ∨ is ≠ []) →
      Step_pure Nm (vals vs ++ [.trap] ++ is) [.trap]
  /-- ``rule Step_pure/trap-label: (LABEL_ n `{instr'*} TRAP) ~> TRAP``. -/
  -- core-exec: Step_pure/trap-label
  | trapLabel {n : Nat} {cont : List AdminInstr} :
      Step_pure Nm [.label n cont [.trap]] [.trap]
  /-- ``rule Step_pure/trap-frame: (FRAME_ n `{f} TRAP) ~> TRAP``. -/
  -- core-exec: Step_pure/trap-frame
  | trapFrame {n : Nat} {f : Frame} :
      Step_pure Nm [.frame n f [.trap]] [.trap]
  /-- `rule Step_pure/local.tee: val (LOCAL.TEE x) ~> val val (LOCAL.SET x)`. -/
  -- core-exec: Step_pure/local.tee
  | localTee {v : Val} {x : LocalIdx} :
      Step_pure Nm [v.toAdmin, .plain (.localTee x)]
        [v.toAdmin, v.toAdmin, .plain (.localSet x)]
  /-- `rule Step_pure/ref.i31:
      (CONST I32 i) REF.I31 ~> (REF.I31_NUM $wrap__(32, 31, i))`. -/
  -- core-exec: Step_pure/ref.i31
  | refI31 {i : U32} {j : U31} :
      Nm.wrap__ 32 31 i = j →
      Step_pure Nm [constI32 i, .plain .refI31] [.addrref (.i31 j)]
  /-- `rule Step_pure/ref.is_null-true:
      ref REF.IS_NULL ~> (CONST I32 1)  -- if ref = (REF.NULL ht)`. -/
  -- core-exec: Step_pure/ref.is_null-true
  | refIsNullTrue {ht : HeapType} {c : U32} :
      c.val = 1 →
      Step_pure Nm [Ref.toAdmin (.null ht), .plain .refIsNull] [constI32 c]
  /-- `rule Step_pure/ref.is_null-false: ref REF.IS_NULL ~> (CONST I32 0)  -- otherwise`. -/
  -- core-exec: Step_pure/ref.is_null-false
  | refIsNullFalse {r : Ref} {c : U32} :
      (∀ ht : HeapType, r ≠ .null ht) → c.val = 0 →
      Step_pure Nm [r.toAdmin, .plain .refIsNull] [constI32 c]
  /-- `rule Step_pure/ref.as_non_null-null:
      ref REF.AS_NON_NULL ~> TRAP  -- if ref = (REF.NULL ht)`. -/
  -- core-exec: Step_pure/ref.as_non_null-null
  | refAsNonNullNull {ht : HeapType} :
      Step_pure Nm [Ref.toAdmin (.null ht), .plain .refAsNonNull] [.trap]
  /-- `rule Step_pure/ref.as_non_null-addr: ref REF.AS_NON_NULL ~> ref  -- otherwise`. -/
  -- core-exec: Step_pure/ref.as_non_null-addr
  | refAsNonNullAddr {r : Ref} :
      (∀ ht : HeapType, r ≠ .null ht) →
      Step_pure Nm [r.toAdmin, .plain .refAsNonNull] [r.toAdmin]
  /-- `rule Step_pure/ref.eq-null: ref_1 ref_2 REF.EQ ~> (CONST I32 1)
      -- if ref_1 = (REF.NULL ht_1) /\ ref_2 = (REF.NULL ht_2)`. -/
  -- core-exec: Step_pure/ref.eq-null
  | refEqNull {ht₁ ht₂ : HeapType} {c : U32} :
      c.val = 1 →
      Step_pure Nm [Ref.toAdmin (.null ht₁), Ref.toAdmin (.null ht₂), .plain .refEq]
        [constI32 c]
  /-- `rule Step_pure/ref.eq-true: ref_1 ref_2 REF.EQ ~> (CONST I32 1)
      -- otherwise  -- if ref_1 = ref_2`. -/
  -- core-exec: Step_pure/ref.eq-true
  | refEqTrue {r₁ r₂ : Ref} {c : U32} :
      (∀ ht₁ ht₂ : HeapType, ¬ (r₁ = .null ht₁ ∧ r₂ = .null ht₂)) →
      r₁ = r₂ → c.val = 1 →
      Step_pure Nm [r₁.toAdmin, r₂.toAdmin, .plain .refEq] [constI32 c]
  /-- `rule Step_pure/ref.eq-false: ref_1 ref_2 REF.EQ ~> (CONST I32 0)  -- otherwise`. -/
  -- core-exec: Step_pure/ref.eq-false
  | refEqFalse {r₁ r₂ : Ref} {c : U32} :
      (∀ ht₁ ht₂ : HeapType, ¬ (r₁ = .null ht₁ ∧ r₂ = .null ht₂)) →
      r₁ ≠ r₂ → c.val = 0 →
      Step_pure Nm [r₁.toAdmin, r₂.toAdmin, .plain .refEq] [constI32 c]
  /-- `rule Step_pure/i31.get-null: (REF.NULL ht) (I31.GET sx) ~> TRAP`. -/
  -- core-exec: Step_pure/i31.get-null
  | i31GetNull {ht : HeapType} {sx : Sx} :
      Step_pure Nm [Ref.toAdmin (.null ht), .plain (.i31Get sx)] [.trap]
  /-- `rule Step_pure/i31.get-num:
      (REF.I31_NUM i) (I31.GET sx) ~> (CONST I32 $extend__(31, 32, sx, i))`. -/
  -- core-exec: Step_pure/i31.get-num
  | i31GetNum {i : U31} {sx : Sx} {c : U32} :
      Nm.extend__ 31 32 sx i = c →
      Step_pure Nm [.addrref (.i31 i), .plain (.i31Get sx)] [constI32 c]
  /-- `rule Step_pure/array.new:
      val (CONST I32 n) (ARRAY.NEW x) ~> val^n (ARRAY.NEW_FIXED x n)`. -/
  -- core-exec: Step_pure/array.new
  | arrayNew {v : Val} {n : U32} {x : TypeIdx} :
      Step_pure Nm [v.toAdmin, constI32 n, .plain (.arrayNew x)]
        (vals (List.replicate n.val v) ++ [.plain (.arrayNewFixed x n)])
  /-- `rule Step_pure/extern.convert_any-null:
      (REF.NULL ht) EXTERN.CONVERT_ANY ~> (REF.NULL EXTERN)`. -/
  -- core-exec: Step_pure/extern.convert_any-null
  | externConvertAnyNull {ht : HeapType} :
      Step_pure Nm [Ref.toAdmin (.null ht), .plain .externConvertAny]
        [Ref.toAdmin (.null (.abs .extern))]
  /-- `rule Step_pure/extern.convert_any-addr:
      addrref EXTERN.CONVERT_ANY ~> (REF.EXTERN addrref)`. -/
  -- core-exec: Step_pure/extern.convert_any-addr
  | externConvertAnyAddr {r : AddrRef} :
      Step_pure Nm [.addrref r, .plain .externConvertAny] [.addrref (.extern r)]
  /-- `rule Step_pure/any.convert_extern-null:
      (REF.NULL ht) ANY.CONVERT_EXTERN ~> (REF.NULL ANY)`. -/
  -- core-exec: Step_pure/any.convert_extern-null
  | anyConvertExternNull {ht : HeapType} :
      Step_pure Nm [Ref.toAdmin (.null ht), .plain .anyConvertExtern]
        [Ref.toAdmin (.null (.abs .any))]
  /-- `rule Step_pure/any.convert_extern-addr:
      (REF.EXTERN addrref) ANY.CONVERT_EXTERN ~> addrref`. -/
  -- core-exec: Step_pure/any.convert_extern-addr
  | anyConvertExternAddr {r : AddrRef} :
      Step_pure Nm [.addrref (.extern r), .plain .anyConvertExtern] [.addrref r]
  /-- `rule Step_pure/unop-val: (CONST nt c_1) (UNOP nt unop) ~> (CONST nt c)
      -- if c <- $unop_(nt, unop, c_1)`. -/
  -- core-exec: Step_pure/unop-val
  | unopVal {nt : NumType} {op : Unop} {c₁ c : Num_ nt} :
      c ∈ Nm.unop_ nt op c₁ →
      Step_pure Nm [.plain (.const nt c₁), .plain (.unop nt op)] [.plain (.const nt c)]
  /-- `rule Step_pure/unop-trap: (CONST nt c_1) (UNOP nt unop) ~> TRAP
      -- if $unop_(nt, unop, c_1) = eps`. -/
  -- core-exec: Step_pure/unop-trap
  | unopTrap {nt : NumType} {op : Unop} {c₁ : Num_ nt} :
      Nm.unop_ nt op c₁ = [] →
      Step_pure Nm [.plain (.const nt c₁), .plain (.unop nt op)] [.trap]
  /-- `rule Step_pure/binop-val:
      (CONST nt c_1) (CONST nt c_2) (BINOP nt binop) ~> (CONST nt c)
      -- if c <- $binop_(nt, binop, c_1, c_2)`. -/
  -- core-exec: Step_pure/binop-val
  | binopVal {nt : NumType} {op : Binop} {c₁ c₂ c : Num_ nt} :
      c ∈ Nm.binop_ nt op c₁ c₂ →
      Step_pure Nm [.plain (.const nt c₁), .plain (.const nt c₂), .plain (.binop nt op)]
        [.plain (.const nt c)]
  /-- `rule Step_pure/binop-trap:
      (CONST nt c_1) (CONST nt c_2) (BINOP nt binop) ~> TRAP
      -- if $binop_(nt, binop, c_1, c_2) = eps`. -/
  -- core-exec: Step_pure/binop-trap
  | binopTrap {nt : NumType} {op : Binop} {c₁ c₂ : Num_ nt} :
      Nm.binop_ nt op c₁ c₂ = [] →
      Step_pure Nm [.plain (.const nt c₁), .plain (.const nt c₂), .plain (.binop nt op)]
        [.trap]
  /-- `rule Step_pure/testop: (CONST nt c_1) (TESTOP nt testop) ~> (CONST I32 c)
      -- if c = $testop_(nt, testop, c_1)`. -/
  -- core-exec: Step_pure/testop
  | testop {nt : NumType} {op : Testop} {c₁ : Num_ nt} {c : U32} :
      Numerics.testop_ nt op c₁ = some c →
      Step_pure Nm [.plain (.const nt c₁), .plain (.testop nt op)] [constI32 c]
  /-- `rule Step_pure/relop:
      (CONST nt c_1) (CONST nt c_2) (RELOP nt relop) ~> (CONST I32 c)
      -- if c = $relop_(nt, relop, c_1, c_2)`. -/
  -- core-exec: Step_pure/relop
  | relop {nt : NumType} {op : Relop} {c₁ c₂ : Num_ nt} {c : U32} :
      Nm.relop_ nt op c₁ c₂ = some c →
      Step_pure Nm [.plain (.const nt c₁), .plain (.const nt c₂), .plain (.relop nt op)]
        [constI32 c]
  /-- `rule Step_pure/cvtop-val:
      (CONST nt_1 c_1) (CVTOP nt_2 nt_1 cvtop) ~> (CONST nt_2 c)
      -- if c <- $cvtop__(nt_1, nt_2, cvtop, c_1)`. -/
  -- core-exec: Step_pure/cvtop-val
  | cvtopVal {nt₁ nt₂ : NumType} {op : Cvtop} {c₁ : Num_ nt₁} {c : Num_ nt₂} :
      c ∈ Nm.cvtop__ nt₁ nt₂ op c₁ →
      Step_pure Nm [.plain (.const nt₁ c₁), .plain (.cvtop nt₂ nt₁ op)]
        [.plain (.const nt₂ c)]
  /-- `rule Step_pure/cvtop-trap: (CONST nt_1 c_1) (CVTOP nt_2 nt_1 cvtop) ~> TRAP
      -- if $cvtop__(nt_1, nt_2, cvtop, c_1) = eps`. -/
  -- core-exec: Step_pure/cvtop-trap
  | cvtopTrap {nt₁ nt₂ : NumType} {op : Cvtop} {c₁ : Num_ nt₁} :
      Nm.cvtop__ nt₁ nt₂ op c₁ = [] →
      Step_pure Nm [.plain (.const nt₁ c₁), .plain (.cvtop nt₂ nt₁ op)] [.trap]
  /-- `rule Step_pure/vvunop:
      (VCONST V128 c_1) (VVUNOP V128 vvunop) ~> (VCONST V128 c)
      -- if c <- $vvunop_(V128, vvunop, c_1)`. -/
  -- core-exec: Step_pure/vvunop
  | vvunop {op : VVUnop} {c₁ c : V128Lit} :
      c ∈ Nm.vvunop_ .v128 op c₁ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vvunop .v128 op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vvbinop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VVBINOP V128 vvbinop) ~> (VCONST V128 c)
      -- if c <- $vvbinop_(V128, vvbinop, c_1, c_2)`. -/
  -- core-exec: Step_pure/vvbinop
  | vvbinop {op : VVBinop} {c₁ c₂ c : V128Lit} :
      c ∈ Nm.vvbinop_ .v128 op c₁ c₂ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vvbinop .v128 op)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vvternop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VCONST V128 c_3) (VVTERNOP V128 vvternop)
      ~> (VCONST V128 c)  -- if c <- $vvternop_(V128, vvternop, c_1, c_2, c_3)`. -/
  -- core-exec: Step_pure/vvternop
  | vvternop {op : VVTernop} {c₁ c₂ c₃ c : V128Lit} :
      c ∈ Nm.vvternop_ .v128 op c₁ c₂ c₃ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vconst .v128 c₃), .plain (.vvternop .v128 op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vvtestop:
      (VCONST V128 c_1) (VVTESTOP V128 ANY_TRUE) ~> (CONST I32 c)
      -- if c = $ine_($vsize(V128), c_1, 0)`. -/
  -- core-exec: Step_pure/vvtestop
  | vvtestop {c₁ : V128Lit} {c : U32} {z : IN 128} :
      z.val = 0 → Numerics.ine_ 128 c₁ z = c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vvtestop .v128 .anyTrue)]
        [constI32 c]
  /-- `rule Step_pure/vunop-val: (VCONST V128 c_1) (VUNOP sh vunop) ~> (VCONST V128 c)
      -- if c <- $vunop_(sh, vunop, c_1)`. -/
  -- core-exec: Step_pure/vunop-val
  | vunopVal {sh : Shape} {op : VUnop} {c₁ c : V128Lit} :
      c ∈ Nm.vunop_ sh op c₁ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vunop sh op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vunop-trap: (VCONST V128 c_1) (VUNOP sh vunop) ~> TRAP
      -- if $vunop_(sh, vunop, c_1) = eps`. -/
  -- core-exec: Step_pure/vunop-trap
  | vunopTrap {sh : Shape} {op : VUnop} {c₁ : V128Lit} :
      Nm.vunop_ sh op c₁ = [] →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vunop sh op)] [.trap]
  /-- `rule Step_pure/vbinop-val:
      (VCONST V128 c_1) (VCONST V128 c_2) (VBINOP sh vbinop) ~> (VCONST V128 c)
      -- if c <- $vbinop_(sh, vbinop, c_1, c_2)`. -/
  -- core-exec: Step_pure/vbinop-val
  | vbinopVal {sh : Shape} {op : VBinop} {c₁ c₂ c : V128Lit} :
      c ∈ Nm.vbinop_ sh op c₁ c₂ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vbinop sh op)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vbinop-trap:
      (VCONST V128 c_1) (VCONST V128 c_2) (VBINOP sh vbinop) ~> TRAP
      -- if $vbinop_(sh, vbinop, c_1, c_2) = eps`. -/
  -- core-exec: Step_pure/vbinop-trap
  | vbinopTrap {sh : Shape} {op : VBinop} {c₁ c₂ : V128Lit} :
      Nm.vbinop_ sh op c₁ c₂ = [] →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vbinop sh op)] [.trap]
  /-- `rule Step_pure/vternop-val:
      (VCONST V128 c_1) (VCONST V128 c_2) (VCONST V128 c_3) (VTERNOP sh vternop)
      ~> (VCONST V128 c)  -- if c <- $vternop_(sh, vternop, c_1, c_2, c_3)`. -/
  -- core-exec: Step_pure/vternop-val
  | vternopVal {sh : Shape} {op : VTernop} {c₁ c₂ c₃ c : V128Lit} :
      c ∈ Nm.vternop_ sh op c₁ c₂ c₃ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vconst .v128 c₃), .plain (.vternop sh op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vternop-trap:
      (VCONST V128 c_1) (VCONST V128 c_2) (VCONST V128 c_3) (VTERNOP sh vternop) ~> TRAP
      -- if $vternop_(sh, vternop, c_1, c_2, c_3) = eps`. -/
  -- core-exec: Step_pure/vternop-trap
  | vternopTrap {sh : Shape} {op : VTernop} {c₁ c₂ c₃ : V128Lit} :
      Nm.vternop_ sh op c₁ c₂ c₃ = [] →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vconst .v128 c₃), .plain (.vternop sh op)] [.trap]
  /-- `rule Step_pure/vtestop: (VCONST V128 c_1) (VTESTOP sh vtestop) ~> (CONST I32 i)
      -- if i = $vtestop_(sh, vtestop, c_1)`. -/
  -- core-exec: Step_pure/vtestop
  | vtestop {sh : Shape} {op : VTestop} {c₁ : V128Lit} {i : U32} :
      Nm.vtestop_ sh op c₁ = some i →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vtestop sh op)] [constI32 i]
  /-- `rule Step_pure/vrelop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VRELOP sh vrelop) ~> (VCONST V128 c)
      -- if c = $vrelop_(sh, vrelop, c_1, c_2)`. -/
  -- core-exec: Step_pure/vrelop
  | vrelop {sh : Shape} {op : VRelop} {c₁ c₂ c : V128Lit} :
      Nm.vrelop_ sh op c₁ c₂ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vrelop sh op)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vshiftop:
      (VCONST V128 c_1) (CONST I32 i) (VSHIFTOP sh vshiftop) ~> (VCONST V128 c)
      -- if c = $vshiftop_(sh, vshiftop, c_1, i)`. -/
  -- core-exec: Step_pure/vshiftop
  | vshiftop {sh : IShape} {op : VShiftop} {c₁ c : V128Lit} {i : U32} :
      Nm.vshiftop_ sh op c₁ i = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), constI32 i, .plain (.vshiftop sh op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vbitmask: (VCONST V128 c_1) (VBITMASK sh) ~> (CONST I32 c)
      -- if c = $vbitmaskop_(sh, c_1)`. -/
  -- core-exec: Step_pure/vbitmask
  | vbitmask {sh : IShape} {c₁ : V128Lit} {c : U32} :
      Nm.vbitmaskop_ sh c₁ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vbitmask sh)] [constI32 c]
  /-- `rule Step_pure/vswizzlop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VSWIZZLOP sh swizzlop) ~> (VCONST V128 c)
      -- if c = $vswizzlop_(sh, swizzlop, c_1, c_2)`. -/
  -- core-exec: Step_pure/vswizzlop
  | vswizzlop {sh : BShape} {op : VSwizzlop} {c₁ c₂ c : V128Lit} :
      Nm.vswizzlop_ sh op c₁ c₂ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vswizzlop sh op)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vshuffle:
      (VCONST V128 c_1) (VCONST V128 c_2) (VSHUFFLE sh i*) ~> (VCONST V128 c)
      -- if c = $vshufflop_(sh, i*, c_1, c_2)`. -/
  -- core-exec: Step_pure/vshuffle
  | vshuffle {sh : BShape} {is : List LaneIdx} {c₁ c₂ c : V128Lit} :
      Nm.vshufflop_ sh is c₁ c₂ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vshuffle sh is)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vsplat:
      (CONST $lunpack(Lnn) c_1) (VSPLAT (Lnn X M)) ~> (VCONST V128 c)
      -- if c = $inv_lanes_(Lnn X M, $lpacknum_(Lnn, c_1)^M)`. -/
  -- core-exec: Step_pure/vsplat
  | vsplat {lt : LaneType} {m : Dim} {c₁ : Num_ lt.unpack} {c : V128Lit} :
      Nm.inv_lanes_ ⟨lt, m⟩ (List.replicate m.toNat (Nm.lpacknum_ lt c₁)) = c →
      Step_pure Nm [.plain (.const lt.unpack c₁), .plain (.vsplat ⟨lt, m⟩)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vextract_lane-num:
      (VCONST V128 c_1) (VEXTRACT_LANE (nt X M) i) ~> (CONST nt c_2)
      -- if c_2 = $lanes_(nt X M, c_1)[i]`. -/
  -- core-exec: Step_pure/vextract_lane-num
  | vextractLaneNum {nt : NumType} {m : Dim} {i : LaneIdx} {c₁ : V128Lit}
      {c₂ : Num_ nt} :
      (Nm.lanes_ ⟨.num nt, m⟩ c₁)[i.val]? = some c₂ →
      Step_pure Nm [.plain (.vconst .v128 c₁),
        .plain (.vextractLane ⟨.num nt, m⟩ none i)] [.plain (.const nt c₂)]
  /-- `rule Step_pure/vextract_lane-pack:
      (VCONST V128 c_1) (VEXTRACT_LANE (pt X M) sx i) ~> (CONST I32 c_2)
      -- if c_2 = $extend__($psize(pt), 32, sx, $lanes_(pt X M, c_1)[i])`. -/
  -- core-exec: Step_pure/vextract_lane-pack
  | vextractLanePack {pt : PackType} {m : Dim} {sx : Sx} {i : LaneIdx}
      {c₁ : V128Lit} {l : IN pt.size} {c₂ : U32} :
      (Nm.lanes_ ⟨.pack pt, m⟩ c₁)[i.val]? = some l →
      Nm.extend__ pt.size 32 sx l = c₂ →
      Step_pure Nm [.plain (.vconst .v128 c₁),
        .plain (.vextractLane ⟨.pack pt, m⟩ (some sx) i)] [constI32 c₂]
  /-- `rule Step_pure/vreplace_lane:
      (VCONST V128 c_1) (CONST $lunpack(Lnn) c_2) (VREPLACE_LANE (Lnn X M) i)
      ~> (VCONST V128 c)
      -- if c = $inv_lanes_(Lnn X M, $lanes_(Lnn X M, c_1)[[i] = $lpacknum_(Lnn, c_2)])`. -/
  -- core-exec: Step_pure/vreplace_lane
  | vreplaceLane {lt : LaneType} {m : Dim} {i : LaneIdx} {c₁ c : V128Lit}
      {c₂ : Num_ lt.unpack} {ls : List (Lane_ lt)} :
      setAt? (Nm.lanes_ ⟨lt, m⟩ c₁) i.val (Nm.lpacknum_ lt c₂) = some ls →
      Nm.inv_lanes_ ⟨lt, m⟩ ls = c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.const lt.unpack c₂),
        .plain (.vreplaceLane ⟨lt, m⟩ i)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vextunop:
      (VCONST V128 c_1) (VEXTUNOP sh_2 sh_1 vextunop) ~> (VCONST V128 c)
      -- if $vextunop__(sh_1, sh_2, vextunop, c_1) = c`. -/
  -- core-exec: Step_pure/vextunop
  | vextunop {sh₁ sh₂ : IShape} {op : VExtUnop} {c₁ c : V128Lit} :
      Nm.vextunop__ sh₁ sh₂ op c₁ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vextunop sh₂ sh₁ op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vextbinop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VEXTBINOP sh_2 sh_1 vextbinop)
      ~> (VCONST V128 c)  -- if $vextbinop__(sh_1, sh_2, vextbinop, c_1, c_2) = c`. -/
  -- core-exec: Step_pure/vextbinop
  | vextbinop {sh₁ sh₂ : IShape} {op : VExtBinop} {c₁ c₂ c : V128Lit} :
      Nm.vextbinop__ sh₁ sh₂ op c₁ c₂ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vextbinop sh₂ sh₁ op)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vextternop:
      (VCONST V128 c_1) (VCONST V128 c_2) (VCONST V128 c_3)
      (VEXTTERNOP sh_2 sh_1 vextternop) ~> (VCONST V128 c)
      -- if $vextternop__(sh_1, sh_2, vextternop, c_1, c_2, c_3) = c`. -/
  -- core-exec: Step_pure/vextternop
  | vextternop {sh₁ sh₂ : IShape} {op : VExtTernop} {c₁ c₂ c₃ c : V128Lit} :
      Nm.vextternop__ sh₁ sh₂ op c₁ c₂ c₃ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vconst .v128 c₃), .plain (.vextternop sh₂ sh₁ op)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vnarrow:
      (VCONST V128 c_1) (VCONST V128 c_2) (VNARROW sh_2 sh_1 sx) ~> (VCONST V128 c)
      -- if c = $vnarrowop__(sh_1, sh_2, sx, c_1, c_2)`. -/
  -- core-exec: Step_pure/vnarrow
  | vnarrow {sh₁ sh₂ : IShape} {sx : Sx} {c₁ c₂ c : V128Lit} :
      Nm.vnarrowop__ sh₁ sh₂ sx c₁ c₂ = some c →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vconst .v128 c₂),
        .plain (.vnarrow sh₂ sh₁ sx)] [.plain (.vconst .v128 c)]
  /-- `rule Step_pure/vcvtop:
      (VCONST V128 c_1) (VCVTOP sh_2 sh_1 vcvtop) ~> (VCONST V128 c)
      -- if c = $vcvtop__(sh_1, sh_2, vcvtop, c_1)`. -/
  -- core-exec: Step_pure/vcvtop
  | vcvtop {sh₁ sh₂ : Shape} {op : VCvtop} {c₁ c : V128Lit} :
      c ∈ Nm.vcvtop__ sh₁ sh₂ op c₁ →
      Step_pure Nm [.plain (.vconst .v128 c₁), .plain (.vcvtop sh₂ sh₁ op)]
        [.plain (.vconst .v128 c)]

/-! ## `relation Step_read: config ~> instr*`

The reductions that read the store or the frame but do not write to them. -/

/-- The exact constructor of a `Step_read` derivation.  Keeping this index on
the authority transcription itself gives the released event semantics a rule
identity without introducing a second copy of the 105 semantic rules. -/
inductive ReadRule where
  | block | loop | brOnCastSucceed | brOnCastFail | brOnCastFailSucceed
  | brOnCastFailFail | call | callRefNull | callRefFunc | returnCall
  | returnCallRefLabel | returnCallRefHandler | returnCallRefFrameNull
  | returnCallRefFrameAddr | throwRefNull | throwRefInstrs | throwRefLabel
  | throwRefFrame | throwRefHandlerEmpty | throwRefHandlerCatch
  | throwRefHandlerCatchRef | throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef | throwRefHandlerNext | tryTable | localGet
  | globalGet | tableGetOob | tableGetVal | tableSize | tableFillOob
  | tableFillZero | tableFillSucc | tableCopyOob | tableCopyZero | tableCopyLe
  | tableCopyGt | tableInitOob | tableInitZero | tableInitSucc | loadNumOob
  | loadNumVal | loadPackOob | loadPackVal | vloadOob | vloadVal
  | vloadPackOob | vloadPackVal | vloadSplatOob | vloadSplatVal
  | vloadZeroOob | vloadZeroVal | vloadLaneOob | vloadLaneVal | memorySize
  | memoryFillOob | memoryFillZero | memoryFillSucc | memoryCopyOob
  | memoryCopyZero | memoryCopyLe | memoryCopyGt | memoryInitOob
  | memoryInitZero | memoryInitSucc | refNullIdx | refFunc | refTestTrue
  | refTestFalse | refCastSucceed | refCastFail | structNewDefault
  | structGetNull | structGetStruct | arrayNewDefault | arrayNewElemOob
  | arrayNewElemAlloc | arrayNewDataOob | arrayNewDataNum | arrayGetNull
  | arrayGetOob | arrayGetArray | arrayLenNull | arrayLenArray | arrayFillNull
  | arrayFillOob | arrayFillZero | arrayFillSucc | arrayCopyNull1
  | arrayCopyNull2 | arrayCopyOob1 | arrayCopyOob2 | arrayCopyZero
  | arrayCopyLe | arrayCopyGt | arrayInitElemNull | arrayInitElemOob1
  | arrayInitElemOob2 | arrayInitElemZero | arrayInitElemSucc
  | arrayInitDataNull | arrayInitDataOob1 | arrayInitDataOob2
  | arrayInitDataZero | arrayInitDataNum
  deriving DecidableEq, Repr, Inhabited

variable [authority : ExecutionAuthority]

/-- AMD-016's explicit rendering of the pinned `num_(nt)` syntax-sort side
condition at a result reconstructed only from bytes.  The pinned authority
keeps its original implicit sorted-metavariable reading; the public amended
authority excludes raw `FN` constructor terms that do not inhabit that sort. -/
def ByteSolvedNumWfFor [authority : ExecutionAuthority]
    (type : NumType) (value : Num_ type) : Prop :=
  match authority.revision with
  | .pinned => True
  | .amended => Num_.wf type value = true

/-- AMD-016's storage-literal counterpart.  Integer, vector and packed
carriers are bounded by construction; only numeric storage can expose the raw
float representation and therefore delegates to `ByteSolvedNumWfFor`. -/
def ByteSolvedLiteralWfFor [authority : ExecutionAuthority] :
    (storage : StorageType) → Lit_ storage → Prop
  | .val (.num type), value => ByteSolvedNumWfFor type value
  | .val (.vec _), _ => True
  | .val (.ref _), value => value.elim
  | .val .bot, value => value.elim
  | .pack _, _ => True

/-- `relation Step_read: config ~> instr*  hint(name "E")`, under the selected
execution authority. -/
inductive Step_read (Nm : Numerics) :
    State → ReadRule → List AdminInstr → List AdminInstr → Prop where
  /-- ``rule Step_read/block: z; val^m (BLOCK bt instr*) ~> (LABEL_ n `{eps} val^m instr*)
      -- if $blocktype_(z, bt) = t_1^m -> t_2^n``. -/
  -- core-exec: Step_read/block
  | block {z : State} {vs : List Val} {bt : BlockType} {body : InstrSeq}
      {t₁ t₂ : List ValType} {m n : Nat} :
      blocktype_ z bt = some (t₁, t₂) → t₁.length = m → t₂.length = n → vs.length = m →
      Step_read Nm z .block (vals vs ++ [.plain (.block bt body)])
        [.label n [] (vals vs ++ plains body.toList)]
  /-- ``rule Step_read/loop: z; val^m (LOOP bt instr*)
      ~> (LABEL_ m `{LOOP bt instr*} val^m instr*)
      -- if $blocktype_(z, bt) = t_1^m -> t_2^n``. -/
  -- core-exec: Step_read/loop
  | loop {z : State} {vs : List Val} {bt : BlockType} {body : InstrSeq}
      {t₁ t₂ : List ValType} {m n : Nat} :
      blocktype_ z bt = some (t₁, t₂) → t₁.length = m → t₂.length = n → vs.length = m →
      Step_read Nm z .loop (vals vs ++ [.plain (.loop bt body)])
        [.label m [.plain (.loop bt body)] (vals vs ++ plains body.toList)]
  /-- `rule Step_read/br_on_cast-succeed:
      s; f; ref (BR_ON_CAST l rt_1 rt_2) ~> ref (BR l)
      -- Ref_ok: s |- ref : rt
      -- Reftype_sub: {} |- rt <: $inst_reftype(f.MODULE, rt_2)`. -/
  -- core-exec: Step_read/br_on_cast-succeed
  | brOnCastSucceed {z : State} {r : Ref} {l : LabelIdx} {rt₁ rt₂ rt : RefType} :
      Ref_ok z.store r rt →
      ReftypeSubFor Context.empty rt (instRefType z.frame.mod rt₂) →
      Step_read Nm z .brOnCastSucceed [r.toAdmin, .plain (.brOnCast l rt₁ rt₂)]
        [r.toAdmin, .plain (.br l)]
  /-- `rule Step_read/br_on_cast-fail:
      s; f; ref (BR_ON_CAST l rt_1 rt_2) ~> ref  -- otherwise`. -/
  -- core-exec: Step_read/br_on_cast-fail
  | brOnCastFail {z : State} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} :
      (¬ ∃ rt : RefType, Ref_ok z.store r rt ∧
          ReftypeSubFor Context.empty rt (instRefType z.frame.mod rt₂)) →
      Step_read Nm z .brOnCastFail [r.toAdmin, .plain (.brOnCast l rt₁ rt₂)] [r.toAdmin]
  /-- `rule Step_read/br_on_cast_fail-succeed:
      s; f; ref (BR_ON_CAST_FAIL l rt_1 rt_2) ~> ref
      -- Ref_ok: s |- ref : rt
      -- Reftype_sub: {} |- rt <: $inst_reftype(f.MODULE, rt_2)`. -/
  -- core-exec: Step_read/br_on_cast_fail-succeed
  | brOnCastFailSucceed {z : State} {r : Ref} {l : LabelIdx} {rt₁ rt₂ rt : RefType} :
      Ref_ok z.store r rt →
      ReftypeSubFor Context.empty rt (instRefType z.frame.mod rt₂) →
      Step_read Nm z .brOnCastFailSucceed [r.toAdmin, .plain (.brOnCastFail l rt₁ rt₂)] [r.toAdmin]
  /-- `rule Step_read/br_on_cast_fail-fail:
      s; f; ref (BR_ON_CAST_FAIL l rt_1 rt_2) ~> ref (BR l)  -- otherwise`. -/
  -- core-exec: Step_read/br_on_cast_fail-fail
  | brOnCastFailFail {z : State} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} :
      (¬ ∃ rt : RefType, Ref_ok z.store r rt ∧
          ReftypeSubFor Context.empty rt (instRefType z.frame.mod rt₂)) →
      Step_read Nm z .brOnCastFailFail [r.toAdmin, .plain (.brOnCastFail l rt₁ rt₂)]
        [r.toAdmin, .plain (.br l)]
  /-- `rule Step_read/call:
      z; (CALL x) ~> (REF.FUNC_ADDR a) (CALL_REF $funcinst(z)[a].TYPE)
      -- if $moduleinst(z).FUNCS[x] = a`. -/
  -- core-exec: Step_read/call
  | call {z : State} {x : FuncIdx} {a : FuncAddr} {fi : FuncInst} :
      (z.moduleinst).funcs[x.val]? = some a → z.funcinst[a]? = some fi →
      Step_read Nm z .call [.plain (.call x)]
        [.addrref (.funcAddr a), .plain (.callRef (.defd fi.type))]
  /-- `rule Step_read/call_ref-null: z; (REF.NULL ht) (CALL_REF yy) ~> TRAP`. -/
  -- core-exec: Step_read/call_ref-null
  | callRefNull {z : State} {ht : HeapType} {yy : TypeUse} :
      Step_read Nm z .callRefNull [Ref.toAdmin (.null ht), .plain (.callRef yy)] [.trap]
  /-- ``rule Step_read/call_ref-func:
      z; val^n (REF.FUNC_ADDR a) (CALL_REF yy) ~> (FRAME_ m `{f} (LABEL_ m `{eps} instr*))
      -- if $funcinst(z)[a] = fi
      -- Expand: fi.TYPE ~~ FUNC t_1^n -> t_2^m
      -- if fi.CODE = FUNC x (LOCAL t)* (instr*)
      -- if f = {LOCALS val^n ($default_(t))*, MODULE fi.MODULE}``. -/
  -- core-exec: Step_read/call_ref-func
  | callRefFunc {z : State} {vs : List Val} {a : FuncAddr} {yy : TypeUse}
      {fi : FuncInst} {fn : Func} {t₁ t₂ : ValTypes} {n m : Nat} {f : Frame} :
      z.funcinst[a]? = some fi →
      Expand fi.type (.func t₁ t₂) →
      t₁.length = n → t₂.length = m → vs.length = n →
      fi.code = .func fn →
      f = { locals := vs.map some ++ fn.locals.map (fun lc => default_ lc.valtype),
            mod := fi.mod } →
      Step_read Nm z .callRefFunc (vals vs ++ [.addrref (.funcAddr a), .plain (.callRef yy)])
        [.frame m f [.label m [] (plains fn.body.toList)]]
  /-- `rule Step_read/return_call:
      z; (RETURN_CALL x) ~> (REF.FUNC_ADDR a) (RETURN_CALL_REF $funcinst(z)[a].TYPE)
      -- if $moduleinst(z).FUNCS[x] = a`. -/
  -- core-exec: Step_read/return_call
  | returnCall {z : State} {x : FuncIdx} {a : FuncAddr} {fi : FuncInst} :
      (z.moduleinst).funcs[x.val]? = some a → z.funcinst[a]? = some fi →
      Step_read Nm z .returnCall [.plain (.returnCall x)]
        [.addrref (.funcAddr a), .plain (.returnCallRef (.defd fi.type))]
  /-- ``rule Step_read/return_call_ref-label:
      z; (LABEL_ k `{instr'*} val* (RETURN_CALL_REF yy) instr*)
      ~> val* (RETURN_CALL_REF yy)``. -/
  -- core-exec: Step_read/return_call_ref-label
  | returnCallRefLabel {z : State} {k : Nat} {cont : List AdminInstr} {vs : List Val}
      {yy : TypeUse} {is : List AdminInstr} :
      Step_read Nm z .returnCallRefLabel
        [.label k cont (vals vs ++ [.plain (.returnCallRef yy)] ++ is)]
        (vals vs ++ [.plain (.returnCallRef yy)])
  /-- ``rule Step_read/return_call_ref-handler:
      z; (HANDLER_ k `{catch*} val* (RETURN_CALL_REF yy) instr*)
      ~> val* (RETURN_CALL_REF yy)``. -/
  -- core-exec: Step_read/return_call_ref-handler
  | returnCallRefHandler {z : State} {k : Nat} {cs : List Catch} {vs : List Val}
      {yy : TypeUse} {is : List AdminInstr} :
      Step_read Nm z .returnCallRefHandler
        [.handler k cs (vals vs ++ [.plain (.returnCallRef yy)] ++ is)]
        (vals vs ++ [.plain (.returnCallRef yy)])
  /-- ``rule Step_read/return_call_ref-frame-null:
      z; (FRAME_ k `{f} val* (REF.NULL ht) (RETURN_CALL_REF yy) instr*) ~> TRAP``. -/
  -- core-exec: Step_read/return_call_ref-frame-null
  | returnCallRefFrameNull {z : State} {k : Nat} {f : Frame} {vs : List Val}
      {ht : HeapType} {yy : TypeUse} {is : List AdminInstr} :
      Step_read Nm z .returnCallRefFrameNull
        [.frame k f (vals vs ++ [Ref.toAdmin (.null ht), .plain (.returnCallRef yy)] ++ is)]
        [.trap]
  /-- ``rule Step_read/return_call_ref-frame-addr:
      z; (FRAME_ k `{f} val'* val^n (REF.FUNC_ADDR a) (RETURN_CALL_REF yy) instr*)
      ~> val^n (REF.FUNC_ADDR a) (CALL_REF yy)
      -- Expand: $funcinst(z)[a].TYPE ~~ FUNC t_1^n -> t_2^m``. -/
  -- core-exec: Step_read/return_call_ref-frame-addr
  | returnCallRefFrameAddr {z : State} {k : Nat} {f : Frame} {vs' vs : List Val}
      {a : FuncAddr} {yy : TypeUse} {is : List AdminInstr} {fi : FuncInst}
      {t₁ t₂ : ValTypes} {n m : Nat} :
      z.funcinst[a]? = some fi → Expand fi.type (.func t₁ t₂) →
      t₁.length = n → t₂.length = m → vs.length = n →
      Step_read Nm z .returnCallRefFrameAddr
        [.frame k f (vals vs' ++ vals vs ++
          [.addrref (.funcAddr a), .plain (.returnCallRef yy)] ++ is)]
        (vals vs ++ [.addrref (.funcAddr a), .plain (.callRef yy)])
  /-- `rule Step_read/throw_ref-null: z; (REF.NULL ht) THROW_REF ~> TRAP`. -/
  -- core-exec: Step_read/throw_ref-null
  | throwRefNull {z : State} {ht : HeapType} :
      Step_read Nm z .throwRefNull [Ref.toAdmin (.null ht), .plain .throwRef] [.trap]
  /-- `rule Step_read/throw_ref-instrs:
      z; val* (REF.EXN_ADDR a) THROW_REF instr* ~> (REF.EXN_ADDR a) THROW_REF
      -- if val* =/= eps \/ instr* =/= eps`. -/
  -- core-exec: Step_read/throw_ref-instrs
  | throwRefInstrs {z : State} {vs : List Val} {a : ExnAddr} {is : List AdminInstr} :
      (vs ≠ [] ∨ is ≠ []) →
      Step_read Nm z .throwRefInstrs (vals vs ++ [.addrref (.exnAddr a), .plain .throwRef] ++ is)
        [.addrref (.exnAddr a), .plain .throwRef]
  /-- ``rule Step_read/throw_ref-label:
      z; (LABEL_ n `{instr'*} (REF.EXN_ADDR a) THROW_REF) ~> (REF.EXN_ADDR a) THROW_REF``. -/
  -- core-exec: Step_read/throw_ref-label
  | throwRefLabel {z : State} {n : Nat} {cont : List AdminInstr} {a : ExnAddr} :
      Step_read Nm z .throwRefLabel [.label n cont [.addrref (.exnAddr a), .plain .throwRef]]
        [.addrref (.exnAddr a), .plain .throwRef]
  /-- ``rule Step_read/throw_ref-frame:
      z; (FRAME_ n `{f} (REF.EXN_ADDR a) THROW_REF) ~> (REF.EXN_ADDR a) THROW_REF``. -/
  -- core-exec: Step_read/throw_ref-frame
  | throwRefFrame {z : State} {n : Nat} {f : Frame} {a : ExnAddr} :
      Step_read Nm z .throwRefFrame [.frame n f [.addrref (.exnAddr a), .plain .throwRef]]
        [.addrref (.exnAddr a), .plain .throwRef]
  /-- ``rule Step_read/throw_ref-handler-empty:
      z; (HANDLER_ n `{eps} (REF.EXN_ADDR a) THROW_REF) ~> (REF.EXN_ADDR a) THROW_REF``. -/
  -- core-exec: Step_read/throw_ref-handler-empty
  | throwRefHandlerEmpty {z : State} {n : Nat} {a : ExnAddr} :
      Step_read Nm z .throwRefHandlerEmpty [.handler n [] [.addrref (.exnAddr a), .plain .throwRef]]
        [.addrref (.exnAddr a), .plain .throwRef]
  /-- ``rule Step_read/throw_ref-handler-catch:
      z; (HANDLER_ n `{(CATCH x l) catch'*} (REF.EXN_ADDR a) THROW_REF) ~> val* (BR l)
      -- if $exninst(z)[a].TAG = $tagaddr(z)[x]
      -- if val* = $exninst(z)[a].FIELDS``. -/
  -- core-exec: Step_read/throw_ref-handler-catch
  | throwRefHandlerCatch {z : State} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : ExnAddr} {ex : ExnInst} {ta : TagAddr} :
      z.exninst[a]? = some ex → z.tagaddr[x.val]? = some ta → ex.tag = ta →
      Step_read Nm z .throwRefHandlerCatch
        [.handler n (.tag x l :: cs) [.addrref (.exnAddr a), .plain .throwRef]]
        (vals ex.fields ++ [.plain (.br l)])
  /-- ``rule Step_read/throw_ref-handler-catch_ref:
      z; (HANDLER_ n `{(CATCH_REF x l) catch'*} (REF.EXN_ADDR a) THROW_REF)
      ~> val* (REF.EXN_ADDR a) (BR l)
      -- if $exninst(z)[a].TAG = $tagaddr(z)[x]
      -- if val* = $exninst(z)[a].FIELDS``. -/
  -- core-exec: Step_read/throw_ref-handler-catch_ref
  | throwRefHandlerCatchRef {z : State} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : ExnAddr} {ex : ExnInst} {ta : TagAddr} :
      z.exninst[a]? = some ex → z.tagaddr[x.val]? = some ta → ex.tag = ta →
      Step_read Nm z .throwRefHandlerCatchRef
        [.handler n (.tagRef x l :: cs) [.addrref (.exnAddr a), .plain .throwRef]]
        (vals ex.fields ++ [.addrref (.exnAddr a), .plain (.br l)])
  /-- ``rule Step_read/throw_ref-handler-catch_all:
      z; (HANDLER_ n `{(CATCH_ALL l) catch'*} (REF.EXN_ADDR a) THROW_REF) ~> (BR l)``. -/
  -- core-exec: Step_read/throw_ref-handler-catch_all
  | throwRefHandlerCatchAll {z : State} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : ExnAddr} :
      Step_read Nm z .throwRefHandlerCatchAll
        [.handler n (.all l :: cs) [.addrref (.exnAddr a), .plain .throwRef]]
        [.plain (.br l)]
  /-- ``rule Step_read/throw_ref-handler-catch_all_ref:
      z; (HANDLER_ n `{(CATCH_ALL_REF l) catch'*} (REF.EXN_ADDR a) THROW_REF)
      ~> (REF.EXN_ADDR a) (BR l)``. -/
  -- core-exec: Step_read/throw_ref-handler-catch_all_ref
  | throwRefHandlerCatchAllRef {z : State} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : ExnAddr} :
      Step_read Nm z .throwRefHandlerCatchAllRef
        [.handler n (.allRef l :: cs) [.addrref (.exnAddr a), .plain .throwRef]]
        [.addrref (.exnAddr a), .plain (.br l)]
  /-- ``rule Step_read/throw_ref-handler-next:
      z; (HANDLER_ n `{catch catch'*} (REF.EXN_ADDR a) THROW_REF)
      ~> (HANDLER_ n `{catch'*} (REF.EXN_ADDR a) THROW_REF)  -- otherwise``. -/
  -- core-exec: Step_read/throw_ref-handler-next
  | throwRefHandlerNext {z : State} {n : Nat} {c : Catch} {cs : List Catch}
      {a : ExnAddr} :
      ¬ catchMatches z a c →
      Step_read Nm z .throwRefHandlerNext
        [.handler n (c :: cs) [.addrref (.exnAddr a), .plain .throwRef]]
        [.handler n cs [.addrref (.exnAddr a), .plain .throwRef]]
  /-- ``rule Step_read/try_table:
      z; val^m (TRY_TABLE bt catch* instr*)
      ~> (HANDLER_ n `{catch*} (LABEL_ n `{eps} val^m instr*))
      -- if $blocktype_(z, bt) = t_1^m -> t_2^n``. -/
  -- core-exec: Step_read/try_table
  | tryTable {z : State} {vs : List Val} {bt : BlockType} {cs : List_ Catch}
      {body : InstrSeq} {t₁ t₂ : List ValType} {m n : Nat} :
      blocktype_ z bt = some (t₁, t₂) → t₁.length = m → t₂.length = n → vs.length = m →
      Step_read Nm z .tryTable (vals vs ++ [.plain (.tryTable bt cs body)])
        [.handler n cs.val [.label n [] (vals vs ++ plains body.toList)]]
  /-- `rule Step_read/local.get: z; (LOCAL.GET x) ~> val  -- if $local(z, x) = val`. -/
  -- core-exec: Step_read/local.get
  | localGet {z : State} {x : LocalIdx} {v : Val} :
      z.localOf x = some (some v) →
      Step_read Nm z .localGet [.plain (.localGet x)] [v.toAdmin]
  /-- `rule Step_read/global.get: z; (GLOBAL.GET x) ~> val
      -- if $global(z, x).VALUE = val`. -/
  -- core-exec: Step_read/global.get
  | globalGet {z : State} {x : GlobalIdx} {gi : GlobalInst} :
      z.globalOf x = some gi →
      Step_read Nm z .globalGet [.plain (.globalGet x)] [gi.value.toAdmin]
  /-- `rule Step_read/table.get-oob: z; (CONST at i) (TABLE.GET x) ~> TRAP
      -- if i >= |$table(z, x).REFS|`. -/
  -- core-exec: Step_read/table.get-oob
  | tableGetOob {z : State} {att : AddrType} {i : AddrLit att} {x : TableIdx}
      {ti : TableInst} :
      z.tableOf x = some ti → i.val ≥ ti.refs.length →
      Step_read Nm z .tableGetOob [constAddr att i, .plain (.tableGet x)] [.trap]
  /-- `rule Step_read/table.get-val: z; (CONST at i) (TABLE.GET x) ~> $table(z,x).REFS[i]
      -- if i < |$table(z, x).REFS|`. -/
  -- core-exec: Step_read/table.get-val
  | tableGetVal {z : State} {att : AddrType} {i : AddrLit att} {x : TableIdx}
      {ti : TableInst} {r : Ref} :
      z.tableOf x = some ti → ti.refs[i.val]? = some r →
      Step_read Nm z .tableGetVal [constAddr att i, .plain (.tableGet x)] [r.toAdmin]
  /-- `rule Step_read/table.size: z; (TABLE.SIZE x) ~> (CONST at n)
      -- if |$table(z, x).REFS| = n  -- if $table(z, x).TYPE = at lim rt`. -/
  -- core-exec: Step_read/table.size
  | tableSize {z : State} {x : TableIdx} {ti : TableInst} {att : AddrType}
      {n : AddrLit att} :
      z.tableOf x = some ti → ti.refs.length = n.val → ti.type.addr = att →
      Step_read Nm z .tableSize [.plain (.tableSize x)] [constAddr att n]
  /-- `rule Step_read/table.fill-oob:
      z; (CONST at i) val (CONST at n) (TABLE.FILL x) ~> TRAP
      -- if $(i + n) > |$table(z, x).REFS|`. -/
  -- core-exec: Step_read/table.fill-oob
  | tableFillOob {z : State} {att : AddrType} {i n : AddrLit att} {v : Val}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → i.val + n.val > ti.refs.length →
      Step_read Nm z .tableFillOob
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.tableFill x)] [.trap]
  /-- `rule Step_read/table.fill-zero:
      z; (CONST at i) val (CONST at n) (TABLE.FILL x) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/table.fill-zero
  | tableFillZero {z : State} {att : AddrType} {i n : AddrLit att} {v : Val}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → ¬ (i.val + n.val > ti.refs.length) → n.val = 0 →
      Step_read Nm z .tableFillZero
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.tableFill x)] []
  /-- `rule Step_read/table.fill-succ:
      z; (CONST at i) val (CONST at n) (TABLE.FILL x) ~>
        (CONST at i) val (TABLE.SET x)
        (CONST at $(i+1)) val (CONST at $(n-1)) (TABLE.FILL x)  -- otherwise`. -/
  -- core-exec: Step_read/table.fill-succ
  | tableFillSucc {z : State} {att : AddrType} {i n i' n' : AddrLit att} {v : Val}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → ¬ (i.val + n.val > ti.refs.length) → n.val ≠ 0 →
      i'.val = i.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .tableFillSucc
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.tableFill x)]
        [constAddr att i, v.toAdmin, .plain (.tableSet x),
         constAddr att i', v.toAdmin, constAddr att n', .plain (.tableFill x)]
  /-- `rule Step_read/table.copy-oob:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (TABLE.COPY x_1 x_2) ~> TRAP
      -- if $(i_1 + n) > |$table(z, x_1).REFS| \/ $(i_2 + n) > |$table(z, x_2).REFS|`. -/
  -- core-exec: Step_read/table.copy-oob
  | tableCopyOob {z : State} {att₁ att₂ att' : AddrType} {i₁ : AddrLit att₁}
      {i₂ : AddrLit att₂} {n : AddrLit att'} {x₁ x₂ : TableIdx}
      {ti₁ ti₂ : TableInst} :
      z.tableOf x₁ = some ti₁ → z.tableOf x₂ = some ti₂ →
      (i₁.val + n.val > ti₁.refs.length ∨ i₂.val + n.val > ti₂.refs.length) →
      Step_read Nm z .tableCopyOob
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.tableCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/table.copy-zero:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (TABLE.COPY x y) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/table.copy-zero
  | tableCopyZero {z : State} {att₁ att₂ att' : AddrType} {i₁ : AddrLit att₁}
      {i₂ : AddrLit att₂} {n : AddrLit att'} {x y : TableIdx} {ti₁ ti₂ : TableInst} :
      z.tableOf x = some ti₁ → z.tableOf y = some ti₂ →
      ¬ (i₁.val + n.val > ti₁.refs.length ∨ i₂.val + n.val > ti₂.refs.length) →
      n.val = 0 →
      Step_read Nm z .tableCopyZero
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.tableCopy x y)] []
  /-- `rule Step_read/table.copy-le:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (TABLE.COPY x y) ~>
        (CONST at_1 i_1) (CONST at_2 i_2) (TABLE.GET y) (TABLE.SET x)
        (CONST at_1 $(i_1+1)) (CONST at_2 $(i_2+1)) (CONST at' $(n-1)) (TABLE.COPY x y)
      -- otherwise  -- if i_1 <= i_2`. -/
  -- core-exec: Step_read/table.copy-le
  | tableCopyLe {z : State} {att₁ att₂ att' : AddrType} {i₁ i₁' : AddrLit att₁}
      {i₂ i₂' : AddrLit att₂} {n n' : AddrLit att'} {x y : TableIdx}
      {ti₁ ti₂ : TableInst} :
      z.tableOf x = some ti₁ → z.tableOf y = some ti₂ →
      ¬ (i₁.val + n.val > ti₁.refs.length ∨ i₂.val + n.val > ti₂.refs.length) →
      n.val ≠ 0 → i₁.val ≤ i₂.val →
      i₁'.val = i₁.val + 1 → i₂'.val = i₂.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .tableCopyLe
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.tableCopy x y)]
        [constAddr att₁ i₁, constAddr att₂ i₂, .plain (.tableGet y), .plain (.tableSet x),
         constAddr att₁ i₁', constAddr att₂ i₂', constAddr att' n',
         .plain (.tableCopy x y)]
  /-- `rule Step_read/table.copy-gt:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (TABLE.COPY x y) ~>
        (CONST at_1 $(i_1+n-1)) (CONST at_2 $(i_2+n-1)) (TABLE.GET y) (TABLE.SET x)
        (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' $(n-1)) (TABLE.COPY x y)
      -- otherwise`. -/
  -- core-exec: Step_read/table.copy-gt
  | tableCopyGt {z : State} {att₁ att₂ att' : AddrType} {i₁ j₁ : AddrLit att₁}
      {i₂ j₂ : AddrLit att₂} {n n' : AddrLit att'} {x y : TableIdx}
      {ti₁ ti₂ : TableInst} :
      z.tableOf x = some ti₁ → z.tableOf y = some ti₂ →
      ¬ (i₁.val + n.val > ti₁.refs.length ∨ i₂.val + n.val > ti₂.refs.length) →
      n.val ≠ 0 → ¬ (i₁.val ≤ i₂.val) →
      j₁.val + 1 = i₁.val + n.val → j₂.val + 1 = i₂.val + n.val → n.val = n'.val + 1 →
      Step_read Nm z .tableCopyGt
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.tableCopy x y)]
        [constAddr att₁ j₁, constAddr att₂ j₂, .plain (.tableGet y), .plain (.tableSet x),
         constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n',
         .plain (.tableCopy x y)]
  /-- `rule Step_read/table.init-oob:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (TABLE.INIT x y) ~> TRAP
      -- if $(i + n) > |$table(z, x).REFS| \/ $(j + n) > |$elem(z, y).REFS|`. -/
  -- core-exec: Step_read/table.init-oob
  | tableInitOob {z : State} {att : AddrType} {i : AddrLit att} {j n : U32}
      {x : TableIdx} {y : ElemIdx} {ti : TableInst} {ei : ElemInst} :
      z.tableOf x = some ti → z.elemOf y = some ei →
      (i.val + n.val > ti.refs.length ∨ j.val + n.val > ei.refs.length) →
      Step_read Nm z .tableInitOob
        [constAddr att i, constI32 j, constI32 n, .plain (.tableInit x y)] [.trap]
  /-- `rule Step_read/table.init-zero:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (TABLE.INIT x y) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/table.init-zero
  | tableInitZero {z : State} {att : AddrType} {i : AddrLit att} {j n : U32}
      {x : TableIdx} {y : ElemIdx} {ti : TableInst} {ei : ElemInst} :
      z.tableOf x = some ti → z.elemOf y = some ei →
      ¬ (i.val + n.val > ti.refs.length ∨ j.val + n.val > ei.refs.length) →
      n.val = 0 →
      Step_read Nm z .tableInitZero
        [constAddr att i, constI32 j, constI32 n, .plain (.tableInit x y)] []
  /-- `rule Step_read/table.init-succ:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (TABLE.INIT x y) ~>
        (CONST at i) $elem(z,y).REFS[j] (TABLE.SET x)
        (CONST at $(i+1)) (CONST I32 $(j+1)) (CONST I32 $(n-1)) (TABLE.INIT x y)
      -- otherwise`. -/
  -- core-exec: Step_read/table.init-succ
  | tableInitSucc {z : State} {att : AddrType} {i i' : AddrLit att}
      {j j' n n' : U32} {x : TableIdx} {y : ElemIdx} {ti : TableInst}
      {ei : ElemInst} {r : Ref} :
      z.tableOf x = some ti → z.elemOf y = some ei →
      ¬ (i.val + n.val > ti.refs.length ∨ j.val + n.val > ei.refs.length) →
      n.val ≠ 0 → ei.refs[j.val]? = some r →
      i'.val = i.val + 1 → j'.val = j.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .tableInitSucc
        [constAddr att i, constI32 j, constI32 n, .plain (.tableInit x y)]
        [constAddr att i, r.toAdmin, .plain (.tableSet x),
         constAddr att i', constI32 j', constI32 n', .plain (.tableInit x y)]
  /-- `rule Step_read/load-num-oob: z; (CONST at i) (LOAD nt x ao) ~> TRAP
      -- if $(i + ao.OFFSET + $size(nt)/8 > |$mem(z, x).BYTES|)`. -/
  -- core-exec: Step_read/load-num-oob
  | loadNumOob {z : State} {att : AddrType} {i : AddrLit att} {nt : NumType}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + nt.size / 8 > mi.bytes.length →
      Step_read Nm z .loadNumOob [constAddr att i, .plain (.load nt none x ao)] [.trap]
  /-- `rule Step_read/load-num-val: z; (CONST at i) (LOAD nt x ao) ~> (CONST nt c)
      -- if $nbytes_(nt, c) = $mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]`. -/
  -- core-exec: Step_read/load-num-val
  | loadNumVal {z : State} {att : AddrType} {i : AddrLit att} {nt : NumType}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} {c : Num_ nt} :
      z.memOf x = some mi →
      Nm.nbytes_ nt c = slice mi.bytes (i.val + ao.offset.val) (nt.size / 8) →
      ByteSolvedNumWfFor nt c →
      Step_read Nm z .loadNumVal [constAddr att i, .plain (.load nt none x ao)]
        [.plain (.const nt c)]
  /-- `rule Step_read/load-pack-oob: z; (CONST at i) (LOAD Inn (n _ sx) x ao) ~> TRAP
      -- if $(i + ao.OFFSET + n/8 > |$mem(z, x).BYTES|)`. -/
  -- core-exec: Step_read/load-pack-oob
  | loadPackOob {z : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {sz : Sz} {sx : Sx} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      Step_read Nm z .loadPackOob
        [constAddr att i, .plain (.load inn.toNumType (some ⟨sz, sx⟩) x ao)] [.trap]
  /-- `rule Step_read/load-pack-val:
      z; (CONST at i) (LOAD Inn (n _ sx) x ao) ~> (CONST Inn $extend__(n, $size(Inn), sx, c))
      -- if $ibytes_(n, c) = $mem(z, x).BYTES[i + ao.OFFSET : n/8]`. -/
  -- core-exec: Step_read/load-pack-val
  | loadPackVal {z : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {sz : Sz} {sx : Sx} {x : MemIdx} {ao : MemArg} {mi : MemInst}
      {c : IN sz.toNat} {d : InnLit inn} :
      z.memOf x = some mi →
      Nm.ibytes_ sz.toNat c = slice mi.bytes (i.val + ao.offset.val) (sz.toNat / 8) →
      Nm.extend__ sz.toNat inn.size sx c = d →
      Step_read Nm z .loadPackVal
        [constAddr att i, .plain (.load inn.toNumType (some ⟨sz, sx⟩) x ao)]
        [constInn inn d]
  /-- `rule Step_read/vload-oob: z; (CONST at i) (VLOAD V128 x ao) ~> TRAP
      -- if $(i + ao.OFFSET + $vsize(V128)/8 > |$mem(z, x).BYTES|)`. -/
  -- core-exec: Step_read/vload-oob
  | vloadOob {z : State} {att : AddrType} {i : AddrLit att} {x : MemIdx}
      {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + VecType.v128.size / 8 > mi.bytes.length →
      Step_read Nm z .vloadOob [constAddr att i, .plain (.vload .v128 none x ao)] [.trap]
  /-- `rule Step_read/vload-val: z; (CONST at i) (VLOAD V128 x ao) ~> (VCONST V128 c)
      -- if $vbytes_(V128, c) = $mem(z, x).BYTES[i + ao.OFFSET : $vsize(V128)/8]`. -/
  -- core-exec: Step_read/vload-val
  | vloadVal {z : State} {att : AddrType} {i : AddrLit att} {x : MemIdx}
      {ao : MemArg} {mi : MemInst} {c : V128Lit} :
      z.memOf x = some mi →
      Nm.vbytes_ .v128 c =
        slice mi.bytes (i.val + ao.offset.val) (VecType.v128.size / 8) →
      Step_read Nm z .vloadVal [constAddr att i, .plain (.vload .v128 none x ao)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_read/vload-pack-oob:
      z; (CONST at i) (VLOAD V128 (SHAPE M X K _ sx) x ao) ~> TRAP
      -- if $(i + ao.OFFSET + M * K/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step_read/vload-pack-oob
  | vloadPackOob {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz} {k : Nat}
      {sx : Sx} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat * k / 8 > mi.bytes.length →
      Step_read Nm z .vloadPackOob
        [constAddr att i, .plain (.vload .v128 (some (.shape sz k sx)) x ao)] [.trap]
  /-- `rule Step_read/vload-pack-val:
      z; (CONST at i) (VLOAD V128 (SHAPE M X K _ sx) x ao) ~> (VCONST V128 c)
      -- (if $ibytes_(M, j) = $mem(z, x).BYTES[i + ao.OFFSET + k * M/8 : M/8])^(k<K)
      -- if c = $inv_lanes_(Jnn X K, $extend__(M, $jsizenn(Jnn), sx, j)^K)
         /\ $jsizenn(Jnn) = $(M * 2)`. -/
  -- core-exec: Step_read/vload-pack-val
  | vloadPackVal {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz} {k : Nat}
      {sx : Sx} {x : MemIdx} {ao : MemArg} {mi : MemInst} {sh : Shape}
      {js : List (IN sz.toNat)} {ls : List (Lane_ sh.lane)} {c : V128Lit} :
      z.memOf x = some mi →
      sh.lane.size = sz.toNat * 2 → sh.dim.toNat = k → js.length = k →
      (∀ m j, js[m]? = some j →
        Nm.ibytes_ sz.toNat j =
          slice mi.bytes (i.val + ao.offset.val + m * (sz.toNat / 8)) (sz.toNat / 8)) →
      js.mapM (fun j => inToLane sh.lane (Nm.extend__ sz.toNat sh.lane.size sx j)) =
        some ls →
      Nm.inv_lanes_ sh ls = c →
      Step_read Nm z .vloadPackVal
        [constAddr att i, .plain (.vload .v128 (some (.shape sz k sx)) x ao)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_read/vload-splat-oob:
      z; (CONST at i) (VLOAD V128 (SPLAT N) x ao) ~> TRAP
      -- if $(i + ao.OFFSET + N/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step_read/vload-splat-oob
  | vloadSplatOob {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      Step_read Nm z .vloadSplatOob
        [constAddr att i, .plain (.vload .v128 (some (.splat sz)) x ao)] [.trap]
  /-- `rule Step_read/vload-splat-val:
      z; (CONST at i) (VLOAD V128 (SPLAT N) x ao) ~> (VCONST V128 c)
      -- if $ibytes_(N, j) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]
      -- if N = $jsize(Jnn)  -- if M = $(128/N)
      -- if c = $inv_lanes_(Jnn X M, j^M)`. -/
  -- core-exec: Step_read/vload-splat-val
  | vloadSplatVal {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} {sh : Shape} {j : IN sh.lane.size}
      {lv : Lane_ sh.lane} {c : V128Lit} :
      z.memOf x = some mi →
      sh.lane.size = sz.toNat → sh.dim.toNat = 128 / sz.toNat →
      Nm.ibytes_ sh.lane.size j = slice mi.bytes (i.val + ao.offset.val) (sz.toNat / 8) →
      inToLane sh.lane j = some lv →
      Nm.inv_lanes_ sh (List.replicate sh.dim.toNat lv) = c →
      Step_read Nm z .vloadSplatVal
        [constAddr att i, .plain (.vload .v128 (some (.splat sz)) x ao)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_read/vload-zero-oob:
      z; (CONST at i) (VLOAD V128 (ZERO N) x ao) ~> TRAP
      -- if $(i + ao.OFFSET + N/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step_read/vload-zero-oob
  | vloadZeroOob {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      Step_read Nm z .vloadZeroOob
        [constAddr att i, .plain (.vload .v128 (some (.zero sz)) x ao)] [.trap]
  /-- `rule Step_read/vload-zero-val:
      z; (CONST at i) (VLOAD V128 (ZERO N) x ao) ~> (VCONST V128 c)
      -- if $ibytes_(N, j) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]
      -- if c = $extend__(N, 128, U, j)`. -/
  -- core-exec: Step_read/vload-zero-val
  | vloadZeroVal {z : State} {att : AddrType} {i : AddrLit att} {sz : Sz}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} {j : IN sz.toNat} {c : V128Lit} :
      z.memOf x = some mi →
      Nm.ibytes_ sz.toNat j = slice mi.bytes (i.val + ao.offset.val) (sz.toNat / 8) →
      Nm.extend__ sz.toNat 128 .u j = c →
      Step_read Nm z .vloadZeroVal
        [constAddr att i, .plain (.vload .v128 (some (.zero sz)) x ao)]
        [.plain (.vconst .v128 c)]
  /-- `rule Step_read/vload_lane-oob:
      z; (CONST at i) (VCONST V128 c_1) (VLOAD_LANE V128 N x ao j) ~> TRAP
      -- if $(i + ao.OFFSET + N/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step_read/vload_lane-oob
  | vloadLaneOob {z : State} {att : AddrType} {i : AddrLit att} {c₁ : V128Lit}
      {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      Step_read Nm z .vloadLaneOob
        [constAddr att i, .plain (.vconst .v128 c₁),
         .plain (.vloadLane .v128 sz x ao j)] [.trap]
  /-- `rule Step_read/vload_lane-val:
      z; (CONST at i) (VCONST V128 c_1) (VLOAD_LANE V128 N x ao j) ~> (VCONST V128 c)
      -- if $ibytes_(N, k) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]
      -- if N = $jsize(Jnn)  -- if M = $($vsize(V128)/N)
      -- if c = $inv_lanes_(Jnn X M, $lanes_(Jnn X M, c_1)[[j] = k])`. -/
  -- core-exec: Step_read/vload_lane-val
  | vloadLaneVal {z : State} {att : AddrType} {i : AddrLit att} {c₁ c : V128Lit}
      {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx} {mi : MemInst}
      {sh : Shape} {k : IN sh.lane.size} {lv : Lane_ sh.lane} {ls : List (Lane_ sh.lane)} :
      z.memOf x = some mi →
      sh.lane.size = sz.toNat → sh.dim.toNat = VecType.v128.size / sz.toNat →
      Nm.ibytes_ sh.lane.size k = slice mi.bytes (i.val + ao.offset.val) (sz.toNat / 8) →
      inToLane sh.lane k = some lv →
      setAt? (Nm.lanes_ sh c₁) j.val lv = some ls →
      Nm.inv_lanes_ sh ls = c →
      Step_read Nm z .vloadLaneVal
        [constAddr att i, .plain (.vconst .v128 c₁),
         .plain (.vloadLane .v128 sz x ao j)] [.plain (.vconst .v128 c)]
  /-- `rule Step_read/memory.size: z; (MEMORY.SIZE x) ~> (CONST at n)
      -- if $(n * $($(64 * $Ki))) = |$mem(z, x).BYTES|
      -- if $mem(z, x).TYPE = at lim PAGE`. -/
  -- core-exec: Step_read/memory.size
  | memorySize {z : State} {x : MemIdx} {mi : MemInst} {att : AddrType}
      {n : AddrLit att} :
      z.memOf x = some mi → n.val * (64 * Ki) = mi.bytes.length →
      mi.type.addr = att →
      Step_read Nm z .memorySize [.plain (.memorySize x)] [constAddr att n]
  /-- `rule Step_read/memory.fill-oob:
      z; (CONST at i) val (CONST at n) (MEMORY.FILL x) ~> TRAP
      -- if $(i + n) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step_read/memory.fill-oob
  | memoryFillOob {z : State} {att : AddrType} {i n : AddrLit att} {v : Val}
      {x : MemIdx} {mi : MemInst} :
      z.memOf x = some mi → i.val + n.val > mi.bytes.length →
      Step_read Nm z .memoryFillOob
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.memoryFill x)] [.trap]
  /-- `rule Step_read/memory.fill-zero:
      z; (CONST at i) val (CONST at n) (MEMORY.FILL x) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/memory.fill-zero
  | memoryFillZero {z : State} {att : AddrType} {i n : AddrLit att} {v : Val}
      {x : MemIdx} {mi : MemInst} :
      z.memOf x = some mi → ¬ (i.val + n.val > mi.bytes.length) → n.val = 0 →
      Step_read Nm z .memoryFillZero
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.memoryFill x)] []
  /-- `rule Step_read/memory.fill-succ:
      z; (CONST at i) val (CONST at n) (MEMORY.FILL x) ~>
        (CONST at i) val (STORE I32 `8 x $memarg0)
        (CONST at $(i+1)) val (CONST at $(n-1)) (MEMORY.FILL x)  -- otherwise`. -/
  -- core-exec: Step_read/memory.fill-succ
  | memoryFillSucc {z : State} {att : AddrType} {i n i' n' : AddrLit att} {v : Val}
      {x : MemIdx} {mi : MemInst} :
      z.memOf x = some mi → ¬ (i.val + n.val > mi.bytes.length) → n.val ≠ 0 →
      i'.val = i.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .memoryFillSucc
        [constAddr att i, v.toAdmin, constAddr att n, .plain (.memoryFill x)]
        [constAddr att i, v.toAdmin, .plain (.store .i32 (some ⟨.s8⟩) x MemArg.zero),
         constAddr att i', v.toAdmin, constAddr att n', .plain (.memoryFill x)]
  /-- `rule Step_read/memory.copy-oob:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (MEMORY.COPY x_1 x_2) ~> TRAP
      -- if $(i_1 + n) > |$mem(z, x_1).BYTES| \/ $(i_2 + n) > |$mem(z, x_2).BYTES|`. -/
  -- core-exec: Step_read/memory.copy-oob
  | memoryCopyOob {z : State} {att₁ att₂ att' : AddrType} {i₁ : AddrLit att₁}
      {i₂ : AddrLit att₂} {n : AddrLit att'} {x₁ x₂ : MemIdx} {mi₁ mi₂ : MemInst} :
      z.memOf x₁ = some mi₁ → z.memOf x₂ = some mi₂ →
      (i₁.val + n.val > mi₁.bytes.length ∨ i₂.val + n.val > mi₂.bytes.length) →
      Step_read Nm z .memoryCopyOob
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.memoryCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/memory.copy-zero:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (MEMORY.COPY x_1 x_2) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/memory.copy-zero
  | memoryCopyZero {z : State} {att₁ att₂ att' : AddrType} {i₁ : AddrLit att₁}
      {i₂ : AddrLit att₂} {n : AddrLit att'} {x₁ x₂ : MemIdx} {mi₁ mi₂ : MemInst} :
      z.memOf x₁ = some mi₁ → z.memOf x₂ = some mi₂ →
      ¬ (i₁.val + n.val > mi₁.bytes.length ∨ i₂.val + n.val > mi₂.bytes.length) →
      n.val = 0 →
      Step_read Nm z .memoryCopyZero
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.memoryCopy x₁ x₂)] []
  /-- `rule Step_read/memory.copy-le:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (MEMORY.COPY x_1 x_2) ~>
        (CONST at_1 i_1) (CONST at_2 i_2) (LOAD I32 (`8 _ U) x_2 $memarg0)
        (STORE I32 `8 x_1 $memarg0)
        (CONST at_1 $(i_1 + 1)) (CONST at_2 $(i_2 + 1)) (CONST at' $(n - 1))
        (MEMORY.COPY x_1 x_2)
      -- otherwise  -- if i_1 <= i_2`. -/
  -- core-exec: Step_read/memory.copy-le
  | memoryCopyLe {z : State} {att₁ att₂ att' : AddrType} {i₁ i₁' : AddrLit att₁}
      {i₂ i₂' : AddrLit att₂} {n n' : AddrLit att'} {x₁ x₂ : MemIdx}
      {mi₁ mi₂ : MemInst} :
      z.memOf x₁ = some mi₁ → z.memOf x₂ = some mi₂ →
      ¬ (i₁.val + n.val > mi₁.bytes.length ∨ i₂.val + n.val > mi₂.bytes.length) →
      n.val ≠ 0 → i₁.val ≤ i₂.val →
      i₁'.val = i₁.val + 1 → i₂'.val = i₂.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .memoryCopyLe
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.memoryCopy x₁ x₂)]
        [constAddr att₁ i₁, constAddr att₂ i₂,
         .plain (.load .i32 (some ⟨.s8, .u⟩) x₂ MemArg.zero),
         .plain (.store .i32 (some ⟨.s8⟩) x₁ MemArg.zero),
         constAddr att₁ i₁', constAddr att₂ i₂', constAddr att' n',
         .plain (.memoryCopy x₁ x₂)]
  /-- `rule Step_read/memory.copy-gt:
      z; (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' n) (MEMORY.COPY x_1 x_2) ~>
        (CONST at_1 $(i_1+n-1)) (CONST at_2 $(i_2+n-1)) (LOAD I32 (`8 _ U) x_2 $memarg0)
        (STORE I32 `8 x_1 $memarg0)
        (CONST at_1 i_1) (CONST at_2 i_2) (CONST at' $(n-1)) (MEMORY.COPY x_1 x_2)
      -- otherwise`. -/
  -- core-exec: Step_read/memory.copy-gt
  | memoryCopyGt {z : State} {att₁ att₂ att' : AddrType} {i₁ j₁ : AddrLit att₁}
      {i₂ j₂ : AddrLit att₂} {n n' : AddrLit att'} {x₁ x₂ : MemIdx}
      {mi₁ mi₂ : MemInst} :
      z.memOf x₁ = some mi₁ → z.memOf x₂ = some mi₂ →
      ¬ (i₁.val + n.val > mi₁.bytes.length ∨ i₂.val + n.val > mi₂.bytes.length) →
      n.val ≠ 0 → ¬ (i₁.val ≤ i₂.val) →
      j₁.val + 1 = i₁.val + n.val → j₂.val + 1 = i₂.val + n.val → n.val = n'.val + 1 →
      Step_read Nm z .memoryCopyGt
        [constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n,
         .plain (.memoryCopy x₁ x₂)]
        [constAddr att₁ j₁, constAddr att₂ j₂,
         .plain (.load .i32 (some ⟨.s8, .u⟩) x₂ MemArg.zero),
         .plain (.store .i32 (some ⟨.s8⟩) x₁ MemArg.zero),
         constAddr att₁ i₁, constAddr att₂ i₂, constAddr att' n',
         .plain (.memoryCopy x₁ x₂)]
  /-- `rule Step_read/memory.init-oob:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (MEMORY.INIT x y) ~> TRAP
      -- if $(i + n) > |$mem(z, x).BYTES| \/ $(j + n) > |$data(z, y).BYTES|`. -/
  -- core-exec: Step_read/memory.init-oob
  | memoryInitOob {z : State} {att : AddrType} {i : AddrLit att} {j n : U32}
      {x : MemIdx} {y : DataIdx} {mi : MemInst} {di : DataInst} :
      z.memOf x = some mi → z.dataOf y = some di →
      (i.val + n.val > mi.bytes.length ∨ j.val + n.val > di.bytes.length) →
      Step_read Nm z .memoryInitOob
        [constAddr att i, constI32 j, constI32 n, .plain (.memoryInit x y)] [.trap]
  /-- `rule Step_read/memory.init-zero:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (MEMORY.INIT x y) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/memory.init-zero
  | memoryInitZero {z : State} {att : AddrType} {i : AddrLit att} {j n : U32}
      {x : MemIdx} {y : DataIdx} {mi : MemInst} {di : DataInst} :
      z.memOf x = some mi → z.dataOf y = some di →
      ¬ (i.val + n.val > mi.bytes.length ∨ j.val + n.val > di.bytes.length) →
      n.val = 0 →
      Step_read Nm z .memoryInitZero
        [constAddr att i, constI32 j, constI32 n, .plain (.memoryInit x y)] []
  /-- `rule Step_read/memory.init-succ:
      z; (CONST at i) (CONST I32 j) (CONST I32 n) (MEMORY.INIT x y) ~>
        (CONST at i) (CONST I32 $data(z,y).BYTES[j]) (STORE I32 `8 x $memarg0)
        (CONST at $(i+1)) (CONST I32 $(j+1)) (CONST I32 $(n-1)) (MEMORY.INIT x y)
      -- otherwise`. -/
  -- core-exec: Step_read/memory.init-succ
  | memoryInitSucc {z : State} {att : AddrType} {i i' : AddrLit att}
      {j j' n n' : U32} {x : MemIdx} {y : DataIdx} {mi : MemInst} {di : DataInst}
      {b : Byte} {bc : U32} :
      z.memOf x = some mi → z.dataOf y = some di →
      ¬ (i.val + n.val > mi.bytes.length ∨ j.val + n.val > di.bytes.length) →
      n.val ≠ 0 → di.bytes[j.val]? = some b → bc.val = b.val →
      i'.val = i.val + 1 → j'.val = j.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .memoryInitSucc
        [constAddr att i, constI32 j, constI32 n, .plain (.memoryInit x y)]
        [constAddr att i, constI32 bc, .plain (.store .i32 (some ⟨.s8⟩) x MemArg.zero),
         constAddr att i', constI32 j', constI32 n', .plain (.memoryInit x y)]
  /-- `rule Step_read/ref.null-idx: z; (REF.NULL (_IDX x)) ~> (REF.NULL $type(z, x))`. -/
  -- core-exec: Step_read/ref.null-idx
  | refNullIdx {z : State} {x : TypeIdx} {dt : DefType} :
      z.typeOf x = some dt →
      Step_read Nm z .refNullIdx [.plain (.refNull (.use (.idx x)))]
        [Ref.toAdmin (.null (.use (.defd dt)))]
  /-- `rule Step_read/ref.func:
      z; (REF.FUNC x) ~> (REF.FUNC_ADDR $moduleinst(z).FUNCS[x])`. -/
  -- core-exec: Step_read/ref.func
  | refFunc {z : State} {x : FuncIdx} {a : FuncAddr} :
      (z.moduleinst).funcs[x.val]? = some a →
      Step_read Nm z .refFunc [.plain (.refFunc x)] [.addrref (.funcAddr a)]
  /-- `rule Step_read/ref.test-true: s; f; ref (REF.TEST rt) ~> (CONST I32 1)
      -- Ref_ok: s |- ref : rt'
      -- Reftype_sub: {} |- rt' <: $inst_reftype(f.MODULE, rt)`. -/
  -- core-exec: Step_read/ref.test-true
  | refTestTrue {z : State} {r : Ref} {rt rt' : RefType} {c : U32} :
      Ref_ok z.store r rt' →
      ReftypeSubFor Context.empty rt' (instRefType z.frame.mod rt) →
      c.val = 1 →
      Step_read Nm z .refTestTrue [r.toAdmin, .plain (.refTest rt)] [constI32 c]
  /-- `rule Step_read/ref.test-false: s; f; ref (REF.TEST rt) ~> (CONST I32 0)
      -- otherwise`. -/
  -- core-exec: Step_read/ref.test-false
  | refTestFalse {z : State} {r : Ref} {rt : RefType} {c : U32} :
      (¬ ∃ rt' : RefType, Ref_ok z.store r rt' ∧
          ReftypeSubFor Context.empty rt' (instRefType z.frame.mod rt)) →
      c.val = 0 →
      Step_read Nm z .refTestFalse [r.toAdmin, .plain (.refTest rt)] [constI32 c]
  /-- `rule Step_read/ref.cast-succeed: s; f; ref (REF.CAST rt) ~> ref
      -- Ref_ok: s |- ref : rt'
      -- Reftype_sub: {} |- rt' <: $inst_reftype(f.MODULE, rt)`. -/
  -- core-exec: Step_read/ref.cast-succeed
  | refCastSucceed {z : State} {r : Ref} {rt rt' : RefType} :
      Ref_ok z.store r rt' →
      ReftypeSubFor Context.empty rt' (instRefType z.frame.mod rt) →
      Step_read Nm z .refCastSucceed [r.toAdmin, .plain (.refCast rt)] [r.toAdmin]
  /-- `rule Step_read/ref.cast-fail: s; f; ref (REF.CAST rt) ~> TRAP  -- otherwise`. -/
  -- core-exec: Step_read/ref.cast-fail
  | refCastFail {z : State} {r : Ref} {rt : RefType} :
      (¬ ∃ rt' : RefType, Ref_ok z.store r rt' ∧
          ReftypeSubFor Context.empty rt' (instRefType z.frame.mod rt)) →
      Step_read Nm z .refCastFail [r.toAdmin, .plain (.refCast rt)] [.trap]
  /-- `rule Step_read/struct.new_default:
      z; (STRUCT.NEW_DEFAULT x) ~> val* (STRUCT.NEW x)
      -- Expand: $type(z, x) ~~ STRUCT (mut? zt)*
      -- (if $default_($unpack(zt)) = val)*`. -/
  -- core-exec: Step_read/struct.new_default
  | structNewDefault {z : State} {x : TypeIdx} {dt : DefType} {fts : FieldTypes}
      {vs : List Val} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      (fts.toList.mapM fun ft => default_ (fieldStorage ft).unpack) = some vs →
      Step_read Nm z .structNewDefault [.plain (.structNewDefault x)]
        (vals vs ++ [.plain (.structNew x)])
  /-- `rule Step_read/struct.get-null:
      z; (REF.NULL ht) (STRUCT.GET sx? x i) ~> TRAP`. -/
  -- core-exec: Step_read/struct.get-null
  | structGetNull {z : State} {ht : HeapType} {sx : Option Sx} {x : TypeIdx}
      {i : U32} :
      Step_read Nm z .structGetNull [Ref.toAdmin (.null ht), .plain (.structGet sx x i)] [.trap]
  /-- `rule Step_read/struct.get-struct:
      z; (REF.STRUCT_ADDR a) (STRUCT.GET sx? x i)
      ~> $unpackfield_(zt*[i], sx?, $structinst(z)[a].FIELDS[i])
      -- Expand: $type(z, x) ~~ STRUCT (mut? zt)*`. -/
  -- core-exec: Step_read/struct.get-struct
  | structGetStruct {z : State} {a : StructAddr} {sx : Option Sx} {x : TypeIdx}
      {i : U32} {dt : DefType} {fts : FieldTypes} {si : StructInst}
      {ft : FieldType} {fv : FieldVal} {v : Val} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      z.structinst[a]? = some si →
      fts.toList[i.val]? = some ft → si.fields[i.val]? = some fv →
      Nm.unpackfield_ (fieldStorage ft) sx fv = some v →
      Step_read Nm z .structGetStruct
        [.addrref (.structAddr a), .plain (.structGet sx x i)] [v.toAdmin]
  /-- `rule Step_read/array.new_default:
      z; (CONST I32 n) (ARRAY.NEW_DEFAULT x) ~> val^n (ARRAY.NEW_FIXED x n)
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if $default_($unpack(zt)) = val`. -/
  -- core-exec: Step_read/array.new_default
  | arrayNewDefault {z : State} {n : U32} {x : TypeIdx} {dt : DefType}
      {ft : FieldType} {v : Val} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      default_ (fieldStorage ft).unpack = some v →
      Step_read Nm z .arrayNewDefault [constI32 n, .plain (.arrayNewDefault x)]
        (vals (List.replicate n.val v) ++ [.plain (.arrayNewFixed x n)])
  /-- `rule Step_read/array.new_elem-oob:
      z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_ELEM x y) ~> TRAP
      -- if $(i + n > |$elem(z, y).REFS|)`. -/
  -- core-exec: Step_read/array.new_elem-oob
  | arrayNewElemOob {z : State} {i n : U32} {x : TypeIdx} {y : ElemIdx}
      {ei : ElemInst} :
      z.elemOf y = some ei → i.val + n.val > ei.refs.length →
      Step_read Nm z .arrayNewElemOob [constI32 i, constI32 n, .plain (.arrayNewElem x y)] [.trap]
  /-- `rule Step_read/array.new_elem-alloc:
      z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_ELEM x y) ~> ref^n (ARRAY.NEW_FIXED x n)
      -- if ref^n = $elem(z, y).REFS[i : n]`. -/
  -- core-exec: Step_read/array.new_elem-alloc
  | arrayNewElemAlloc {z : State} {i n : U32} {x : TypeIdx} {y : ElemIdx}
      {ei : ElemInst} {rs : List Ref} :
      z.elemOf y = some ei → rs = slice ei.refs i.val n.val → rs.length = n.val →
      Step_read Nm z .arrayNewElemAlloc [constI32 i, constI32 n, .plain (.arrayNewElem x y)]
        (vals (rs.map Val.ref) ++ [.plain (.arrayNewFixed x n)])
  /-- `rule Step_read/array.new_data-oob:
      z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_DATA x y) ~> TRAP
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if $(i + n * $zsize(zt)/8 > |$data(z, y).BYTES|)`. -/
  -- core-exec: Step_read/array.new_data-oob
  | arrayNewDataOob {z : State} {i n : U32} {x : TypeIdx} {y : DataIdx}
      {dt : DefType} {ft : FieldType} {di : DataInst} {zs : Nat} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      zsize (fieldStorage ft) = some zs → z.dataOf y = some di →
      i.val + n.val * zs / 8 > di.bytes.length →
      Step_read Nm z .arrayNewDataOob [constI32 i, constI32 n, .plain (.arrayNewData x y)] [.trap]
  /-- `rule Step_read/array.new_data-num:
      z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_DATA x y)
      ~> ($const($cunpack(zt), $cunpacknum_(zt, c)))^n (ARRAY.NEW_FIXED x n)
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if $concatn_(byte, $zbytes_(zt, c)^n, $($zsize(zt)/8))
         = $data(z, y).BYTES[i : n * $zsize(zt)/8]`. -/
  -- core-exec: Step_read/array.new_data-num
  | arrayNewDataNum {z : State} {i n : U32} {x : TypeIdx} {y : DataIdx}
      {dt : DefType} {ft : FieldType} {di : DataInst} {zs : Nat}
      {cs : List (Lit_ (fieldStorage ft))} {is : List Instr} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      zsize (fieldStorage ft) = some zs → z.dataOf y = some di →
      cs.length = n.val →
      (∀ c ∈ cs, (Nm.zbytes_ (fieldStorage ft) c).length = zs / 8) →
      (cs.map (fun c => Nm.zbytes_ (fieldStorage ft) c)).flatten =
        slice di.bytes i.val (n.val * zs / 8) →
      cs.mapM (Nm.cunpackConst (fieldStorage ft)) = some is →
      (∀ c ∈ cs, ByteSolvedLiteralWfFor (fieldStorage ft) c) →
      Step_read Nm z .arrayNewDataNum [constI32 i, constI32 n, .plain (.arrayNewData x y)]
        (plains is ++ [.plain (.arrayNewFixed x n)])
  /-- `rule Step_read/array.get-null:
      z; (REF.NULL ht) (CONST I32 i) (ARRAY.GET sx? x) ~> TRAP`. -/
  -- core-exec: Step_read/array.get-null
  | arrayGetNull {z : State} {ht : HeapType} {i : U32} {sx : Option Sx}
      {x : TypeIdx} :
      Step_read Nm z .arrayGetNull
        [Ref.toAdmin (.null ht), constI32 i, .plain (.arrayGet sx x)] [.trap]
  /-- `rule Step_read/array.get-oob:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) (ARRAY.GET sx? x) ~> TRAP
      -- if i >= |$arrayinst(z)[a].FIELDS|`. -/
  -- core-exec: Step_read/array.get-oob
  | arrayGetOob {z : State} {a : ArrayAddr} {i : U32} {sx : Option Sx}
      {x : TypeIdx} {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val ≥ ai.fields.length →
      Step_read Nm z .arrayGetOob
        [.addrref (.arrayAddr a), constI32 i, .plain (.arrayGet sx x)] [.trap]
  /-- `rule Step_read/array.get-array:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) (ARRAY.GET sx? x)
      ~> $unpackfield_(zt, sx?, $arrayinst(z)[a].FIELDS[i])
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)`. -/
  -- core-exec: Step_read/array.get-array
  | arrayGetArray {z : State} {a : ArrayAddr} {i : U32} {sx : Option Sx}
      {x : TypeIdx} {ai : ArrayInst} {dt : DefType} {ft : FieldType}
      {fv : FieldVal} {v : Val} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      z.arrayinst[a]? = some ai → ai.fields[i.val]? = some fv →
      Nm.unpackfield_ (fieldStorage ft) sx fv = some v →
      Step_read Nm z .arrayGetArray
        [.addrref (.arrayAddr a), constI32 i, .plain (.arrayGet sx x)] [v.toAdmin]
  /-- `rule Step_read/array.len-null: z; (REF.NULL ht) ARRAY.LEN ~> TRAP`. -/
  -- core-exec: Step_read/array.len-null
  | arrayLenNull {z : State} {ht : HeapType} :
      Step_read Nm z .arrayLenNull [Ref.toAdmin (.null ht), .plain .arrayLen] [.trap]
  /-- `rule Step_read/array.len-array:
      z; (REF.ARRAY_ADDR a) ARRAY.LEN ~> (CONST I32 $(|$arrayinst(z)[a].FIELDS|))`. -/
  -- core-exec: Step_read/array.len-array
  | arrayLenArray {z : State} {a : ArrayAddr} {ai : ArrayInst} {c : U32} :
      z.arrayinst[a]? = some ai → c.val = ai.fields.length →
      Step_read Nm z .arrayLenArray [.addrref (.arrayAddr a), .plain .arrayLen] [constI32 c]
  /-- `rule Step_read/array.fill-null:
      z; (REF.NULL ht) (CONST I32 i) val (CONST I32 n) (ARRAY.FILL x) ~> TRAP`. -/
  -- core-exec: Step_read/array.fill-null
  | arrayFillNull {z : State} {ht : HeapType} {i n : U32} {v : Val} {x : TypeIdx} :
      Step_read Nm z .arrayFillNull
        [Ref.toAdmin (.null ht), constI32 i, v.toAdmin, constI32 n,
         .plain (.arrayFill x)] [.trap]
  /-- `rule Step_read/array.fill-oob:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) val (CONST I32 n) (ARRAY.FILL x) ~> TRAP
      -- if $(i + n > |$arrayinst(z)[a].FIELDS|)`. -/
  -- core-exec: Step_read/array.fill-oob
  | arrayFillOob {z : State} {a : ArrayAddr} {i n : U32} {v : Val} {x : TypeIdx}
      {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val + n.val > ai.fields.length →
      Step_read Nm z .arrayFillOob
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, constI32 n,
         .plain (.arrayFill x)] [.trap]
  /-- `rule Step_read/array.fill-zero:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) val (CONST I32 n) (ARRAY.FILL x) ~> eps
      -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/array.fill-zero
  | arrayFillZero {z : State} {a : ArrayAddr} {i n : U32} {v : Val} {x : TypeIdx}
      {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → ¬ (i.val + n.val > ai.fields.length) → n.val = 0 →
      Step_read Nm z .arrayFillZero
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, constI32 n,
         .plain (.arrayFill x)] []
  /-- `rule Step_read/array.fill-succ:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) val (CONST I32 n) (ARRAY.FILL x) ~>
        (REF.ARRAY_ADDR a) (CONST I32 i) val (ARRAY.SET x)
        (REF.ARRAY_ADDR a) (CONST I32 $(i + 1)) val (CONST I32 $(n-1)) (ARRAY.FILL x)
      -- otherwise`. -/
  -- core-exec: Step_read/array.fill-succ
  | arrayFillSucc {z : State} {a : ArrayAddr} {i n i' n' : U32} {v : Val}
      {x : TypeIdx} {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → ¬ (i.val + n.val > ai.fields.length) → n.val ≠ 0 →
      i'.val = i.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .arrayFillSucc
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, constI32 n,
         .plain (.arrayFill x)]
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, .plain (.arraySet x),
         .addrref (.arrayAddr a), constI32 i', v.toAdmin, constI32 n',
         .plain (.arrayFill x)]
  /-- `rule Step_read/array.copy-null1:
      z; (REF.NULL ht_1) (CONST I32 i_1) ref (CONST I32 i_2) (CONST I32 n)
      (ARRAY.COPY x_1 x_2) ~> TRAP`. -/
  -- core-exec: Step_read/array.copy-null1
  | arrayCopyNull1 {z : State} {ht₁ : HeapType} {i₁ i₂ n : U32} {r : Ref}
      {x₁ x₂ : TypeIdx} :
      Step_read Nm z .arrayCopyNull1
        [Ref.toAdmin (.null ht₁), constI32 i₁, r.toAdmin, constI32 i₂, constI32 n,
         .plain (.arrayCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/array.copy-null2:
      z; ref (CONST I32 i_1) (REF.NULL ht_2) (CONST I32 i_2) (CONST I32 n)
      (ARRAY.COPY x_1 x_2) ~> TRAP`. -/
  -- core-exec: Step_read/array.copy-null2
  | arrayCopyNull2 {z : State} {ht₂ : HeapType} {i₁ i₂ n : U32} {r : Ref}
      {x₁ x₂ : TypeIdx} :
      Step_read Nm z .arrayCopyNull2
        [r.toAdmin, constI32 i₁, Ref.toAdmin (.null ht₂), constI32 i₂, constI32 n,
         .plain (.arrayCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/array.copy-oob1:
      z; (REF.ARRAY_ADDR a_1) (CONST I32 i_1) (REF.ARRAY_ADDR a_2) (CONST I32 i_2)
      (CONST I32 n) (ARRAY.COPY x_1 x_2) ~> TRAP
      -- if $(i_1 + n > |$arrayinst(z)[a_1].FIELDS|)`. -/
  -- core-exec: Step_read/array.copy-oob1
  | arrayCopyOob1 {z : State} {a₁ a₂ : ArrayAddr} {i₁ i₂ n : U32}
      {x₁ x₂ : TypeIdx} {ai₁ : ArrayInst} :
      z.arrayinst[a₁]? = some ai₁ → i₁.val + n.val > ai₁.fields.length →
      Step_read Nm z .arrayCopyOob1
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/array.copy-oob2:
      z; (REF.ARRAY_ADDR a_1) (CONST I32 i_1) (REF.ARRAY_ADDR a_2) (CONST I32 i_2)
      (CONST I32 n) (ARRAY.COPY x_1 x_2) ~> TRAP
      -- if $(i_2 + n > |$arrayinst(z)[a_2].FIELDS|)`. -/
  -- core-exec: Step_read/array.copy-oob2
  | arrayCopyOob2 {z : State} {a₁ a₂ : ArrayAddr} {i₁ i₂ n : U32}
      {x₁ x₂ : TypeIdx} {ai₂ : ArrayInst} :
      z.arrayinst[a₂]? = some ai₂ → i₂.val + n.val > ai₂.fields.length →
      Step_read Nm z .arrayCopyOob2
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)] [.trap]
  /-- `rule Step_read/array.copy-zero: ... ~> eps  -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/array.copy-zero
  | arrayCopyZero {z : State} {a₁ a₂ : ArrayAddr} {i₁ i₂ n : U32}
      {x₁ x₂ : TypeIdx} {ai₁ ai₂ : ArrayInst} :
      z.arrayinst[a₁]? = some ai₁ → z.arrayinst[a₂]? = some ai₂ →
      ¬ (i₁.val + n.val > ai₁.fields.length) →
      ¬ (i₂.val + n.val > ai₂.fields.length) → n.val = 0 →
      Step_read Nm z .arrayCopyZero
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)] []
  /-- `rule Step_read/array.copy-le: ... ~>
        (REF.ARRAY_ADDR a_1) (CONST I32 i_1) (REF.ARRAY_ADDR a_2) (CONST I32 i_2)
        (ARRAY.GET sx? x_2) (ARRAY.SET x_1)
        (REF.ARRAY_ADDR a_1) (CONST I32 $(i_1 + 1)) (REF.ARRAY_ADDR a_2)
        (CONST I32 $(i_2 + 1)) (CONST I32 $(n-1)) (ARRAY.COPY x_1 x_2)
      -- otherwise  -- Expand: $type(z, x_2) ~~ ARRAY (mut? zt_2)
      -- if i_1 <= i_2 /\ sx? = $sx(zt_2)`. -/
  -- core-exec: Step_read/array.copy-le
  | arrayCopyLe {z : State} {a₁ a₂ : ArrayAddr} {i₁ i₂ n i₁' i₂' n' : U32}
      {x₁ x₂ : TypeIdx} {ai₁ ai₂ : ArrayInst} {dt₂ : DefType} {ft₂ : FieldType}
      {sx : Option Sx} :
      z.arrayinst[a₁]? = some ai₁ → z.arrayinst[a₂]? = some ai₂ →
      ¬ (i₁.val + n.val > ai₁.fields.length) →
      ¬ (i₂.val + n.val > ai₂.fields.length) → n.val ≠ 0 →
      z.typeOf x₂ = some dt₂ → Expand dt₂ (.array ft₂) →
      i₁.val ≤ i₂.val → sx_ (fieldStorage ft₂) = some sx →
      i₁'.val = i₁.val + 1 → i₂'.val = i₂.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .arrayCopyLe
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, .plain (.arrayGet sx x₂), .plain (.arraySet x₁),
         .addrref (.arrayAddr a₁), constI32 i₁', .addrref (.arrayAddr a₂),
         constI32 i₂', constI32 n', .plain (.arrayCopy x₁ x₂)]
  /-- `rule Step_read/array.copy-gt: ... ~>
        (REF.ARRAY_ADDR a_1) (CONST I32 $(i_1 + n - 1)) (REF.ARRAY_ADDR a_2)
        (CONST I32 $(i_2 + n - 1)) (ARRAY.GET sx? x_2) (ARRAY.SET x_1)
        (REF.ARRAY_ADDR a_1) (CONST I32 i_1) (REF.ARRAY_ADDR a_2) (CONST I32 i_2)
        (CONST I32 $(n-1)) (ARRAY.COPY x_1 x_2)
      -- otherwise  -- Expand: $type(z, x_2) ~~ ARRAY (mut? zt_2)
      -- if sx? = $sx(zt_2)`. -/
  -- core-exec: Step_read/array.copy-gt
  | arrayCopyGt {z : State} {a₁ a₂ : ArrayAddr} {i₁ i₂ n j₁ j₂ n' : U32}
      {x₁ x₂ : TypeIdx} {ai₁ ai₂ : ArrayInst} {dt₂ : DefType} {ft₂ : FieldType}
      {sx : Option Sx} :
      z.arrayinst[a₁]? = some ai₁ → z.arrayinst[a₂]? = some ai₂ →
      ¬ (i₁.val + n.val > ai₁.fields.length) →
      ¬ (i₂.val + n.val > ai₂.fields.length) → n.val ≠ 0 → ¬ (i₁.val ≤ i₂.val) →
      z.typeOf x₂ = some dt₂ → Expand dt₂ (.array ft₂) →
      sx_ (fieldStorage ft₂) = some sx →
      j₁.val + 1 = i₁.val + n.val → j₂.val + 1 = i₂.val + n.val → n.val = n'.val + 1 →
      Step_read Nm z .arrayCopyGt
        [.addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]
        [.addrref (.arrayAddr a₁), constI32 j₁, .addrref (.arrayAddr a₂),
         constI32 j₂, .plain (.arrayGet sx x₂), .plain (.arraySet x₁),
         .addrref (.arrayAddr a₁), constI32 i₁, .addrref (.arrayAddr a₂),
         constI32 i₂, constI32 n', .plain (.arrayCopy x₁ x₂)]
  /-- `rule Step_read/array.init_elem-null:
      z; (REF.NULL ht) (CONST I32 i) (CONST I32 j) (CONST I32 n)
      (ARRAY.INIT_ELEM x y) ~> TRAP`. -/
  -- core-exec: Step_read/array.init_elem-null
  | arrayInitElemNull {z : State} {ht : HeapType} {i j n : U32} {x : TypeIdx}
      {y : ElemIdx} :
      Step_read Nm z .arrayInitElemNull
        [Ref.toAdmin (.null ht), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitElem x y)] [.trap]
  /-- `rule Step_read/array.init_elem-oob1: ... ~> TRAP
      -- if $(i + n > |$arrayinst(z)[a].FIELDS|)`. -/
  -- core-exec: Step_read/array.init_elem-oob1
  | arrayInitElemOob1 {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : ElemIdx} {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val + n.val > ai.fields.length →
      Step_read Nm z .arrayInitElemOob1
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitElem x y)] [.trap]
  /-- `rule Step_read/array.init_elem-oob2: ... ~> TRAP
      -- if $(j + n > |$elem(z, y).REFS|)`. -/
  -- core-exec: Step_read/array.init_elem-oob2
  | arrayInitElemOob2 {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : ElemIdx} {ei : ElemInst} :
      z.elemOf y = some ei → j.val + n.val > ei.refs.length →
      Step_read Nm z .arrayInitElemOob2
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitElem x y)] [.trap]
  /-- `rule Step_read/array.init_elem-zero: ... ~> eps  -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/array.init_elem-zero
  | arrayInitElemZero {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : ElemIdx} {ai : ArrayInst} {ei : ElemInst} :
      z.arrayinst[a]? = some ai → z.elemOf y = some ei →
      ¬ (i.val + n.val > ai.fields.length) → ¬ (j.val + n.val > ei.refs.length) →
      n.val = 0 →
      Step_read Nm z .arrayInitElemZero
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitElem x y)] []
  /-- `rule Step_read/array.init_elem-succ: ... ~>
        (REF.ARRAY_ADDR a) (CONST I32 i) ref (ARRAY.SET x)
        (REF.ARRAY_ADDR a) (CONST I32 $(i + 1)) (CONST I32 $(j + 1)) (CONST I32 $(n-1))
        (ARRAY.INIT_ELEM x y)
      -- otherwise  -- if ref = $elem(z, y).REFS[j]`. -/
  -- core-exec: Step_read/array.init_elem-succ
  | arrayInitElemSucc {z : State} {a : ArrayAddr} {i j n i' j' n' : U32}
      {x : TypeIdx} {y : ElemIdx} {ai : ArrayInst} {ei : ElemInst} {r : Ref} :
      z.arrayinst[a]? = some ai → z.elemOf y = some ei →
      ¬ (i.val + n.val > ai.fields.length) → ¬ (j.val + n.val > ei.refs.length) →
      n.val ≠ 0 → ei.refs[j.val]? = some r →
      i'.val = i.val + 1 → j'.val = j.val + 1 → n.val = n'.val + 1 →
      Step_read Nm z .arrayInitElemSucc
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitElem x y)]
        [.addrref (.arrayAddr a), constI32 i, r.toAdmin, .plain (.arraySet x),
         .addrref (.arrayAddr a), constI32 i', constI32 j', constI32 n',
         .plain (.arrayInitElem x y)]
  /-- `rule Step_read/array.init_data-null:
      z; (REF.NULL ht) (CONST I32 i) (CONST I32 j) (CONST I32 n)
      (ARRAY.INIT_DATA x y) ~> TRAP`. -/
  -- core-exec: Step_read/array.init_data-null
  | arrayInitDataNull {z : State} {ht : HeapType} {i j n : U32} {x : TypeIdx}
      {y : DataIdx} :
      Step_read Nm z .arrayInitDataNull
        [Ref.toAdmin (.null ht), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitData x y)] [.trap]
  /-- `rule Step_read/array.init_data-oob1: ... ~> TRAP
      -- if $(i + n > |$arrayinst(z)[a].FIELDS|)`. -/
  -- core-exec: Step_read/array.init_data-oob1
  | arrayInitDataOob1 {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : DataIdx} {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val + n.val > ai.fields.length →
      Step_read Nm z .arrayInitDataOob1
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitData x y)] [.trap]
  /-- `rule Step_read/array.init_data-oob2: ... ~> TRAP
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if $(j + n * $zsize(zt)/8 > |$data(z, y).BYTES|)`. -/
  -- core-exec: Step_read/array.init_data-oob2
  | arrayInitDataOob2 {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : DataIdx} {dt : DefType} {ft : FieldType} {di : DataInst} {zs : Nat} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      zsize (fieldStorage ft) = some zs → z.dataOf y = some di →
      j.val + n.val * zs / 8 > di.bytes.length →
      Step_read Nm z .arrayInitDataOob2
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitData x y)] [.trap]
  /-- `rule Step_read/array.init_data-zero: ... ~> eps  -- otherwise  -- if n = 0`. -/
  -- core-exec: Step_read/array.init_data-zero
  | arrayInitDataZero {z : State} {a : ArrayAddr} {i j n : U32} {x : TypeIdx}
      {y : DataIdx} {ai : ArrayInst} {dt : DefType} {ft : FieldType}
      {di : DataInst} {zs : Nat} :
      z.arrayinst[a]? = some ai → ¬ (i.val + n.val > ai.fields.length) →
      z.typeOf x = some dt → Expand dt (.array ft) →
      zsize (fieldStorage ft) = some zs → z.dataOf y = some di →
      ¬ (j.val + n.val * zs / 8 > di.bytes.length) → n.val = 0 →
      Step_read Nm z .arrayInitDataZero
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitData x y)] []
  /-- `rule Step_read/array.init_data-num: ... ~>
        (REF.ARRAY_ADDR a) (CONST I32 i) ($const($cunpack(zt), $cunpacknum_(zt, c)))
        (ARRAY.SET x)
        (REF.ARRAY_ADDR a) (CONST I32 $(i + 1)) (CONST I32 $(j + $zsize(zt)/8))
        (CONST I32 $(n-1)) (ARRAY.INIT_DATA x y)
      -- otherwise  -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if $zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]`. -/
  -- core-exec: Step_read/array.init_data-num
  | arrayInitDataNum {z : State} {a : ArrayAddr} {i j n i' j' n' : U32}
      {x : TypeIdx} {y : DataIdx} {ai : ArrayInst} {dt : DefType} {ft : FieldType}
      {di : DataInst} {zs : Nat} {c : Lit_ (fieldStorage ft)} {ci : Instr} :
      z.arrayinst[a]? = some ai → ¬ (i.val + n.val > ai.fields.length) →
      z.typeOf x = some dt → Expand dt (.array ft) →
      zsize (fieldStorage ft) = some zs → z.dataOf y = some di →
      ¬ (j.val + n.val * zs / 8 > di.bytes.length) → n.val ≠ 0 →
      Nm.zbytes_ (fieldStorage ft) c = slice di.bytes j.val (zs / 8) →
      Nm.cunpackConst (fieldStorage ft) c = some ci →
      ByteSolvedLiteralWfFor (fieldStorage ft) c →
      i'.val = i.val + 1 → j'.val = j.val + zs / 8 → n.val = n'.val + 1 →
      Step_read Nm z .arrayInitDataNum
        [.addrref (.arrayAddr a), constI32 i, constI32 j, constI32 n,
         .plain (.arrayInitData x y)]
        [.addrref (.arrayAddr a), constI32 i, .plain ci, .plain (.arraySet x),
         .addrref (.arrayAddr a), constI32 i', constI32 j', constI32 n',
         .plain (.arrayInitData x y)]

/-! ## `relation Step: config ~> config`

The structural rules, the context rules, and the reductions that write to the
store. -/

/-- `relation Step: config ~> config  hint(name "E")`. -/
inductive Step (Nm : Numerics) : State → List AdminInstr → State → List AdminInstr → Prop where
  /-- `rule Step/pure: z; instr* ~> z; instr'*  -- Step_pure: instr* ~> instr'*`. -/
  -- core-exec: Step/pure
  | pure {z : State} {is is' : List AdminInstr} :
      Step_pure Nm is is' → Step Nm z is z is'
  /-- `rule Step/read: z; instr* ~> z; instr'*  -- Step_read: z; instr* ~> instr'*`. -/
  -- core-exec: Step/read
  | read {z : State} {rule : ReadRule} {is is' : List AdminInstr} :
      Step_read Nm z rule is is' → Step Nm z is z is'
  /-- `rule Step/ctxt-instrs:
      z; val* instr* instr_1* ~> z'; val* instr'* instr_1*
      -- Step: z; instr* ~> z'; instr'*  -- if val* =/= eps \/ instr_1* =/= eps`. -/
  -- core-exec: Step/ctxt-instrs
  | ctxtInstrs {z z' : State} {vs : List Val} {is is' is₁ : List AdminInstr} :
      Step Nm z is z' is' → (vs ≠ [] ∨ is₁ ≠ []) →
      Step Nm z (vals vs ++ is ++ is₁) z' (vals vs ++ is' ++ is₁)
  /-- ``rule Step/ctxt-label:
      z; (LABEL_ n `{instr_0*} instr*) ~> z'; (LABEL_ n `{instr_0*} instr'*)
      -- Step: z; instr* ~> z'; instr'*``. -/
  -- core-exec: Step/ctxt-label
  | ctxtLabel {z z' : State} {n : Nat} {cont is is' : List AdminInstr} :
      Step Nm z is z' is' →
      Step Nm z [.label n cont is] z' [.label n cont is']
  /-- ``rule Step/ctxt-frame:
      s; f; (FRAME_ n `{f'} instr*) ~> s'; f; (FRAME_ n `{f''} instr'*)
      -- Step: s; f'; instr* ~> s'; f''; instr'*``. -/
  -- core-exec: Step/ctxt-frame
  | ctxtFrame {s s' : Store} {f f' f'' : Frame} {n : Nat} {is is' : List AdminInstr} :
      Step Nm ⟨s, f'⟩ is ⟨s', f''⟩ is' →
      Step Nm ⟨s, f⟩ [.frame n f' is] ⟨s', f⟩ [.frame n f'' is']
  /-- AMD-023 `Step/ctxt-handler`: the administrative handler evaluates its
  body while retaining its result arity and catch clauses. -/
  | ctxtHandler {z z' : State} {n : Nat} {cs : List Catch}
      {is is' : List AdminInstr} :
      HandlerAdministrativeRulesFor → Step Nm z is z' is' →
      Step Nm z [.handler n cs is] z' [.handler n cs is']
  /-- AMD-023 `Step_pure/trap-handler`: a completed trap escapes its
  administrative handler.  It is represented at this authority-selected
  layer so the byte-identical pinned `Step_pure` endpoint remains unchanged. -/
  | trapHandler {z : State} {n : Nat} {cs : List Catch} :
      HandlerAdministrativeRulesFor →
      Step Nm z [.handler n cs [.trap]] z [.trap]
  /-- `rule Step/throw:
      z; val^n (THROW x) ~> $add_exninst(z, exn); (REF.EXN_ADDR a) THROW_REF
      -- Expand: $as_deftype($tag(z, x).TYPE) ~~ FUNC t^n -> eps
      -- if a = |$exninst(z)|
      -- if exn = {TAG $tagaddr(z)[x], FIELDS val^n}`. -/
  -- core-exec: Step/throw
  | throw {z : State} {vs : List Val} {x : TagIdx} {ti : TagInst} {dt : DefType}
      {t : ValTypes} {n : Nat} {a : ExnAddr} {ta : TagAddr} {ex : ExnInst} :
      z.tagOf x = some ti → asDefType ti.type = some dt →
      Expand dt (.func t .nil) → t.length = n → vs.length = n →
      a = z.exninst.length → z.tagaddr[x.val]? = some ta →
      ex = { tag := ta, fields := vs } →
      Step Nm z (vals vs ++ [.plain (.throw x)]) (z.addExnInst [ex])
        [.addrref (.exnAddr a), .plain .throwRef]
  /-- `rule Step/local.set: z; val (LOCAL.SET x) ~> $with_local(z, x, val); eps`. -/
  -- core-exec: Step/local.set
  | localSet {z z' : State} {v : Val} {x : LocalIdx} :
      z.withLocal x v = some z' →
      Step Nm z [v.toAdmin, .plain (.localSet x)] z' []
  /-- `rule Step/global.set: z; val (GLOBAL.SET x) ~> $with_global(z, x, val); eps`. -/
  -- core-exec: Step/global.set
  | globalSet {z z' : State} {v : Val} {x : GlobalIdx} :
      z.withGlobal x v = some z' →
      Step Nm z [v.toAdmin, .plain (.globalSet x)] z' []
  /-- `rule Step/table.set-oob: z; (CONST at i) ref (TABLE.SET x) ~> z; TRAP
      -- if i >= |$table(z, x).REFS|`. -/
  -- core-exec: Step/table.set-oob
  | tableSetOob {z : State} {att : AddrType} {i : AddrLit att} {r : Ref}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → i.val ≥ ti.refs.length →
      Step Nm z [constAddr att i, r.toAdmin, .plain (.tableSet x)] z [.trap]
  /-- `rule Step/table.set-val:
      z; (CONST at i) ref (TABLE.SET x) ~> $with_table(z, x, i, ref); eps
      -- if i < |$table(z, x).REFS|`. -/
  -- core-exec: Step/table.set-val
  | tableSetVal {z z' : State} {att : AddrType} {i : AddrLit att} {r : Ref}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → i.val < ti.refs.length →
      z.withTable x i.val r = some z' →
      Step Nm z [constAddr att i, r.toAdmin, .plain (.tableSet x)] z' []
  /-- `rule Step/table.grow-succeed:
      z; ref (CONST at n) (TABLE.GROW x)
      ~> $with_tableinst(z, x, ti); (CONST at $(|$table(z, x).REFS|))
      -- if ti = $growtable($table(z, x), n, ref)`. -/
  -- core-exec: Step/table.grow-succeed
  | tableGrowSucceed {z z' : State} {att : AddrType} {n sz : AddrLit att} {r : Ref}
      {x : TableIdx} {ti ti' : TableInst} :
      z.tableOf x = some ti → growTable ti n.val r = some ti' →
      z.withTableInst x ti' = some z' → sz.val = ti.refs.length →
      Step Nm z [r.toAdmin, constAddr att n, .plain (.tableGrow x)] z'
        [constAddr att sz]
  /-- `rule Step/table.grow-fail:
      z; ref (CONST at n) (TABLE.GROW x) ~> z; (CONST at $inv_signed_($size(at), $(-1)))`.

  The source gives this rule no premise: an implementation may refuse to grow a
  table for any reason, so failure is a permitted successor of every
  `TABLE.GROW`. -/
  -- core-exec: Step/table.grow-fail
  | tableGrowFail {z : State} {att : AddrType} {n : AddrLit att} {r : Ref}
      {x : TableIdx} {e : AddrLit att} :
      e = Numerics.inv_signed_ (addrSize att) (-1) →
      Step Nm z [r.toAdmin, constAddr att n, .plain (.tableGrow x)] z
        [constAddr att e]
  /-- `rule Step/elem.drop: z; (ELEM.DROP x) ~> $with_elem(z, x, eps); eps`. -/
  -- core-exec: Step/elem.drop
  | elemDrop {z z' : State} {x : ElemIdx} :
      z.withElem x [] = some z' →
      Step Nm z [.plain (.elemDrop x)] z' []
  /-- `rule Step/store-num-oob:
      z; (CONST at i) (CONST nt c) (STORE nt x ao) ~> z; TRAP
      -- if $(i + ao.OFFSET + $size(nt)/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step/store-num-oob
  | storeNumOob {z : State} {att : AddrType} {i : AddrLit att} {nt : NumType}
      {c : Num_ nt} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + nt.size / 8 > mi.bytes.length →
      Step Nm z
        [constAddr att i, .plain (.const nt c), .plain (.store nt none x ao)] z [.trap]
  /-- `rule Step/store-num-val:
      z; (CONST at i) (CONST nt c) (STORE nt x ao)
      ~> $with_mem(z, x, $(i + ao.OFFSET), $($size(nt)/8), b*); eps
      -- if b* = $nbytes_(nt, c)`. -/
  -- core-exec: Step/store-num-val
  | storeNumVal {z z' : State} {att : AddrType} {i : AddrLit att} {nt : NumType}
      {c : Num_ nt} {x : MemIdx} {ao : MemArg} {bs : List Byte} :
      bs = Nm.nbytes_ nt c →
      z.withMem x (i.val + ao.offset.val) (nt.size / 8) bs = some z' →
      Step Nm z
        [constAddr att i, .plain (.const nt c), .plain (.store nt none x ao)] z' []
  /-- `rule Step/store-pack-oob:
      z; (CONST at i) (CONST Inn c) (STORE Inn n x ao) ~> z; TRAP
      -- if $(i + ao.OFFSET + n/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step/store-pack-oob
  | storePackOob {z : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {c : InnLit inn} {sz : Sz} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      Step Nm z
        [constAddr att i, constInn inn c,
         .plain (.store inn.toNumType (some ⟨sz⟩) x ao)] z [.trap]
  /-- `rule Step/store-pack-val:
      z; (CONST at i) (CONST Inn c) (STORE Inn n x ao)
      ~> $with_mem(z, x, $(i + ao.OFFSET), $(n/8), b*); eps
      -- if b* = $ibytes_(n, $wrap__($size(Inn), n, c))`. -/
  -- core-exec: Step/store-pack-val
  | storePackVal {z z' : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {c : InnLit inn} {sz : Sz} {x : MemIdx} {ao : MemArg} {bs : List Byte} :
      bs = Nm.ibytes_ sz.toNat (Nm.wrap__ inn.size sz.toNat c) →
      z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z' →
      Step Nm z
        [constAddr att i, constInn inn c,
         .plain (.store inn.toNumType (some ⟨sz⟩) x ao)] z' []
  /-- `rule Step/vstore-oob:
      z; (CONST at i) (VCONST V128 c) (VSTORE V128 x ao) ~> z; TRAP
      -- if $(i + ao.OFFSET + $vsize(V128)/8) > |$mem(z, x).BYTES|`. -/
  -- core-exec: Step/vstore-oob
  | vstoreOob {z : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + VecType.v128.size / 8 > mi.bytes.length →
      Step Nm z
        [constAddr att i, .plain (.vconst .v128 c), .plain (.vstore .v128 x ao)]
        z [.trap]
  /-- `rule Step/vstore-val:
      z; (CONST at i) (VCONST V128 c) (VSTORE V128 x ao)
      ~> $with_mem(z, x, $(i + ao.OFFSET), $($vsize(V128)/8), b*); eps
      -- if b* = $vbytes_(V128, c)`. -/
  -- core-exec: Step/vstore-val
  | vstoreVal {z z' : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {x : MemIdx} {ao : MemArg} {bs : List Byte} :
      bs = Nm.vbytes_ .v128 c →
      z.withMem x (i.val + ao.offset.val) (VecType.v128.size / 8) bs = some z' →
      Step Nm z
        [constAddr att i, .plain (.vconst .v128 c), .plain (.vstore .v128 x ao)]
        z' []
  /-- `rule Step/vstore_lane-oob:
      z; (CONST at i) (VCONST V128 c) (VSTORE_LANE V128 N x ao j) ~> z; TRAP
      -- if $(i + ao.OFFSET + N) > |$mem(z, x).BYTES|`.

  The source writes `N`, not `N/8`, in this side condition; transcribed as
  written. -/
  -- core-exec: Step/vstore_lane-oob
  | vstoreLaneOob {z : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat > mi.bytes.length →
      Step Nm z
        [constAddr att i, .plain (.vconst .v128 c),
         .plain (.vstoreLane .v128 sz x ao j)] z [.trap]
  /-- `rule Step/vstore_lane-val:
      z; (CONST at i) (VCONST V128 c) (VSTORE_LANE V128 N x ao j)
      ~> $with_mem(z, x, $(i + ao.OFFSET), $(N/8), b*); eps
      -- if N = $jsize(Jnn)  -- if M = $(128/N)
      -- if b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`. -/
  -- core-exec: Step/vstore_lane-val
  | vstoreLaneVal {z z' : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx} {sh : Shape}
      {lv : Lane_ sh.lane} {k : IN sh.lane.size} {bs : List Byte} :
      sh.lane.size = sz.toNat → sh.dim.toNat = 128 / sz.toNat →
      (Nm.lanes_ sh c)[j.val]? = some lv → laneToIN sh.lane lv = some k →
      bs = Nm.ibytes_ sh.lane.size k →
      z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z' →
      Step Nm z
        [constAddr att i, .plain (.vconst .v128 c),
         .plain (.vstoreLane .v128 sz x ao j)] z' []
  /-- `rule Step/memory.grow-succeed:
      z; (CONST at n) (MEMORY.GROW x)
      ~> $with_meminst(z, x, mi); (CONST at $(|$mem(z, x).BYTES| / $($(64 * $Ki))))
      -- if mi = $growmem($mem(z, x), n)`. -/
  -- core-exec: Step/memory.grow-succeed
  | memoryGrowSucceed {z z' : State} {att : AddrType} {n sz : AddrLit att}
      {x : MemIdx} {mi mi' : MemInst} :
      z.memOf x = some mi → growMem mi n.val = some mi' →
      z.withMemInst x mi' = some z' → sz.val = mi.bytes.length / (64 * Ki) →
      Step Nm z [constAddr att n, .plain (.memoryGrow x)] z' [constAddr att sz]
  /-- `rule Step/memory.grow-fail:
      z; (CONST at n) (MEMORY.GROW x) ~> z; (CONST at $inv_signed_($size(at), $(-1)))`.

  As with `table.grow-fail`, the source gives this rule no premise: refusing to
  grow is a permitted successor of every `MEMORY.GROW`, and that nondeterminism
  is part of the semantics rather than an implementation detail. -/
  -- core-exec: Step/memory.grow-fail
  | memoryGrowFail {z : State} {att : AddrType} {n : AddrLit att} {x : MemIdx}
      {e : AddrLit att} :
      e = Numerics.inv_signed_ (addrSize att) (-1) →
      Step Nm z [constAddr att n, .plain (.memoryGrow x)] z [constAddr att e]
  /-- `rule Step/data.drop: z; (DATA.DROP x) ~> $with_data(z, x, eps); eps`. -/
  -- core-exec: Step/data.drop
  | dataDrop {z z' : State} {x : DataIdx} :
      z.withData x [] = some z' →
      Step Nm z [.plain (.dataDrop x)] z' []
  /-- `rule Step/struct.new:
      z; val^n (STRUCT.NEW x) ~> $add_structinst(z, si); (REF.STRUCT_ADDR a)
      -- Expand: $type(z, x) ~~ STRUCT (mut? zt)^n
      -- if a = |$structinst(z)|
      -- if si = {TYPE $type(z, x), FIELDS ($packfield_(zt, val))^n}`. -/
  -- core-exec: Step/struct.new
  | structNew {z : State} {vs : List Val} {x : TypeIdx} {dt : DefType}
      {fts : FieldTypes} {n : Nat} {a : StructAddr} {fvs : List FieldVal}
      {si : StructInst} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      fts.toList.length = n → vs.length = n → a = z.structinst.length →
      (fts.toList.zip vs).mapM (fun p => Nm.packfield_ (fieldStorage p.1) p.2) =
        some fvs →
      si = { type := dt, fields := fvs } →
      Step Nm z (vals vs ++ [.plain (.structNew x)]) (z.addStructInst [si])
        [.addrref (.structAddr a)]
  /-- `rule Step/struct.set-null:
      z; (REF.NULL ht) val (STRUCT.SET x i) ~> z; TRAP`. -/
  -- core-exec: Step/struct.set-null
  | structSetNull {z : State} {ht : HeapType} {v : Val} {x : TypeIdx} {i : U32} :
      Step Nm z [Ref.toAdmin (.null ht), v.toAdmin, .plain (.structSet x i)] z [.trap]
  /-- `rule Step/struct.set-struct:
      z; (REF.STRUCT_ADDR a) val (STRUCT.SET x i)
      ~> $with_struct(z, a, i, $packfield_(zt*[i], val)); eps
      -- Expand: $type(z, x) ~~ STRUCT (mut? zt)*`. -/
  -- core-exec: Step/struct.set-struct
  | structSetStruct {z z' : State} {a : StructAddr} {v : Val} {x : TypeIdx}
      {i : U32} {dt : DefType} {fts : FieldTypes} {ft : FieldType} {fv : FieldVal} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      fts.toList[i.val]? = some ft →
      Nm.packfield_ (fieldStorage ft) v = some fv →
      z.withStruct a i.val fv = some z' →
      Step Nm z
        [.addrref (.structAddr a), v.toAdmin, .plain (.structSet x i)] z' []
  /-- `rule Step/array.new_fixed:
      z; val^n (ARRAY.NEW_FIXED x n) ~> $add_arrayinst(z, ai); (REF.ARRAY_ADDR a)
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)
      -- if a = |$arrayinst(z)|
         /\ ai = {TYPE $type(z, x), FIELDS ($packfield_(zt, val))^n}`. -/
  -- core-exec: Step/array.new_fixed
  | arrayNewFixed {z : State} {vs : List Val} {x : TypeIdx} {n : U32}
      {dt : DefType} {ft : FieldType} {a : ArrayAddr} {fvs : List FieldVal}
      {ai : ArrayInst} :
      z.typeOf x = some dt → Expand dt (.array ft) → vs.length = n.val →
      a = z.arrayinst.length →
      vs.mapM (fun v => Nm.packfield_ (fieldStorage ft) v) = some fvs →
      ai = { type := dt, fields := fvs } →
      Step Nm z (vals vs ++ [.plain (.arrayNewFixed x n)]) (z.addArrayInst [ai])
        [.addrref (.arrayAddr a)]
  /-- `rule Step/array.set-null:
      z; (REF.NULL ht) (CONST I32 i) val (ARRAY.SET x) ~> z; TRAP`. -/
  -- core-exec: Step/array.set-null
  | arraySetNull {z : State} {ht : HeapType} {i : U32} {v : Val} {x : TypeIdx} :
      Step Nm z
        [Ref.toAdmin (.null ht), constI32 i, v.toAdmin, .plain (.arraySet x)] z [.trap]
  /-- `rule Step/array.set-oob:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) val (ARRAY.SET x) ~> z; TRAP
      -- if i >= |$arrayinst(z)[a].FIELDS|`. -/
  -- core-exec: Step/array.set-oob
  | arraySetOob {z : State} {a : ArrayAddr} {i : U32} {v : Val} {x : TypeIdx}
      {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val ≥ ai.fields.length →
      Step Nm z
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, .plain (.arraySet x)]
        z [.trap]
  /-- `rule Step/array.set-array:
      z; (REF.ARRAY_ADDR a) (CONST I32 i) val (ARRAY.SET x)
      ~> $with_array(z, a, i, $packfield_(zt, val)); eps
      -- Expand: $type(z, x) ~~ ARRAY (mut? zt)`. -/
  -- core-exec: Step/array.set-array
  | arraySetArray {z z' : State} {a : ArrayAddr} {i : U32} {v : Val} {x : TypeIdx}
      {dt : DefType} {ft : FieldType} {fv : FieldVal} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      Nm.packfield_ (fieldStorage ft) v = some fv →
      z.withArray a i.val fv = some z' →
      Step Nm z
        [.addrref (.arrayAddr a), constI32 i, v.toAdmin, .plain (.arraySet x)] z' []

/-! ## `relation Steps: config ~>* config` -/

/-- `relation Steps: config ~>* config  hint(name "E")`. -/
inductive Steps (Nm : Numerics) : State → List AdminInstr → State → List AdminInstr → Prop where
  /-- `rule Steps/refl: z; instr* ~>* z; instr*`. -/
  -- core-exec: Steps/refl
  | refl {z : State} {is : List AdminInstr} : Steps Nm z is z is
  /-- `rule Steps/trans: z; instr* ~>* z''; instr''*
      -- Step: z; instr* ~> z'; instr'*  -- Steps: z'; instr'* ~>* z''; instr''*`. -/
  -- core-exec: Steps/trans
  | trans {z z' z'' : State} {is is' is'' : List AdminInstr} :
      Step Nm z is z' is' → Steps Nm z' is' z'' is'' → Steps Nm z is z'' is''

/-! ## `relation Eval_expr: state; expr ~>* state; val*` -/

/-- `relation Eval_expr: state; expr ~>* state; val*  hint(name "E-expr")`. -/
inductive Eval_expr (Nm : Numerics) : State → Expr → State → List Val → Prop where
  /-- `rule Eval_expr: z; instr* ~>* z'; val*  -- Steps: z; instr* ~>* z'; val*`. -/
  -- core-exec: Eval_expr
  | mk {z z' : State} {e : Expr} {vs : List Val} :
      Steps Nm z (exprAdmin e) z' (vals vs) → Eval_expr Nm z e z' vs

/-! ## Explicit authority endpoints -/

/-- The byte-identical pinned store-reading relation. -/
abbrev Step_readPinned := @Step_read pinnedExecutionAuthority

/-- AMD-011 store reading with an explicit numeric provider, for internal proofs. -/
abbrev Step_readAmendedFor := @Step_read amendedExecutionAuthority

/-- The sole public AMD-011 store-reading relation, bound to released numerics. -/
abbrev Step_readA := Step_readAmendedFor releasedNumerics

/-- Recognize the well-formedness bit of a singleton numeric-constant result.
This nondependent projection lets rule inversion transport a result across the
dependent `Num_` family without eliminating its type index by hand. -/
def singletonNumConstWf : List AdminInstr → Bool
  | [.plain (.const type value)] => Num_.wf type value
  | _ => false

/-- AMD-016 is operative on the public full-width load rule: every literal
solved from memory bytes inhabits the pinned side-conditioned numeric syntax
sort.  M29 makes the selector premise vacuous and requires this theorem to
stop elaborating. -/
theorem Step_readA.loadNumVal_result_wf {z : State} {att : AddrType}
    {i : AddrLit att} {nt : NumType} {x : MemIdx} {ao : MemArg}
    {c : Num_ nt}
    (step : Step_readA z .loadNumVal
      [constAddr att i, .plain (.load nt none x ao)]
      [.plain (.const nt c)]) :
    Num_.wf nt c = true := by
  generalize hsource :
      [constAddr att i, .plain (.load nt none x ao)] = source at step
  generalize htarget :
      ([AdminInstr.plain (.const nt c)] : List AdminInstr) = target at step
  cases step
  case loadNumVal hmem hbytes hwf =>
    change singletonNumConstWf [AdminInstr.plain (.const nt c)] = true
    rw [congrArg singletonNumConstWf htarget]
    simpa [singletonNumConstWf, ByteSolvedNumWfFor] using hwf

/-- The byte-identical pinned one-step relation. -/
abbrev StepPinned := @Step pinnedExecutionAuthority

/-- AMD-011 one-step execution with an explicit numeric provider, for internal proofs. -/
abbrev StepAmendedFor := @Step amendedExecutionAuthority

/-- Erasure target of the public event-labelled step relation. -/
abbrev StepEraseA := StepAmendedFor releasedNumerics

/-- The byte-identical pinned reflexive-transitive execution relation. -/
abbrev StepsPinned := @Steps pinnedExecutionAuthority

/-- AMD-011 reflexive-transitive execution with an explicit numeric provider. -/
abbrev StepsAmendedFor := @Steps amendedExecutionAuthority

/-- Erasure target of the public event-labelled run relation. -/
abbrev StepsEraseA := StepsAmendedFor releasedNumerics

/-- The byte-identical pinned expression-evaluation relation. -/
abbrev Eval_exprPinned := @Eval_expr pinnedExecutionAuthority

/-- AMD-011 expression evaluation with an explicit numeric provider. -/
abbrev Eval_exprAmendedFor := @Eval_expr amendedExecutionAuthority

/-- Erasure target of the public event-labelled expression evaluator. -/
abbrev Eval_exprEraseA := Eval_exprAmendedFor releasedNumerics

end WasmGemmGnaf.Wasm.Core.Exec
