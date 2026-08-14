/-
  Wasm/Core/Successors.lean --- the executable successor enumerator for
  `relation Step_pure` of the pinned WebAssembly Core 3.0 semantics.

  ## What this file proves

  `Wasm/Core/Execution.lean` transcribes the pinned execution semantics as five
  relations, 217 rules in all: `Step_pure` (78 rules), `Step_read` (105),
  `Step` (31), `Steps` (2) and `Eval_expr` (1).

  SPEC section 7.1 requires, for the whole machine, an executable
  `successors : Config -> List (Event x Config)` together with the anti-cheat
  property that the list is exactly the relation --- "a single evaluator path is
  not a replacement for this list".

  This file discharges that obligation for the FIRST of those five relations.
  `Step_pure` is a relation the pinned source states in its own right
  (`relation Step_pure: instr* ~> instr*`, the reductions that read neither the
  store nor the frame), so what is proved below is a complete statement about a
  complete pinned object, not a fragment of one:

      theorem mem_pureSuccessors_iff_step_pure (Nm : Numerics) (is is' : _) :
        (exists e, (e, is') in pureSuccessors Nm is) <-> Step_pure Nm is is'

      theorem pureSuccessors_nodup (Nm : Numerics) (is : _) :
        (pureSuccessors Nm is).Nodup

  That all 78 rules are covered is not a claim in prose: the `cases` in
  `step_pure_mem_pureSuccessors` has one branch per constructor and no
  catch-all, so Lean's own exhaustiveness check is what certifies that no rule
  was skipped, and `mem_pureOfInstr_step_pure` is what certifies that none was
  invented.

  ## What this file does NOT prove

  It does NOT discharge SPEC's `Wasm.mem_successors_iff_step`, and that name is
  NOT re-pointed at anything here; it still denotes the subset machine of
  `Wasm/Step.lean`.  Two obstructions remain, stated exactly so that nothing
  below is mistaken for more than it is.

  * `Step_read`'s 105 rules have premises that include `Expand`, `Ref_ok` and
    `Reftype_sub`.  `RuntimeDecision.lean` now supplies a sound executable
    principal reference type and proves its exact null case.  It also proves
    `refMatchesN_not_complete_on_raw`: malformed raw stores make an
    unconditional principal/checker converse false.  `RuntimeTypeOrigin.lean`
    additionally fixes the finite rank/fuel boundary for type vectors whose
    closed declared-super graph comes from module allocation.  Therefore the
    final enumerator belongs on the proof-carrying validated/typed public
    config carrier, whose invariant supplies allocation origin and validated
    subtype completeness; exposing the raw `(State × AdminInstr*)` pair as
    public `Config` could not satisfy SPEC's unconditional successor law.
  * `Step` closes the relation under `Step/ctxt-instrs`, which quantifies over
    EVERY split `val* instr* instr_1*` of the instruction sequence, and under
    `ctxt-label`, `ctxt-frame` and `ctxt-handler`.  `splitVals` below computes
    the ONE canonical decomposition each `Step_pure` rule needs; enumerating
    `Step` needs a recursion over all of them, with the resulting duplicate
    successors separated by the event.

  ## The event

  `PureEvent` names the pinned rule that fired and, for the rules whose result
  the source draws from a SET (`-- if c <- $op_(...)`), the index of the drawn
  element.  Recording the INDEX rather than the value drawn is what makes
  `pureSuccessors_nodup` true: `Numerics` is data a caller supplies, nothing
  here assumes its operators return duplicate-free sets, and an event that
  recorded only the value would not separate two entries drawn from a list with
  repeats.  `unop_two_choices` is the witness that the enumerator really lists
  every permitted result rather than choosing one.

  Every declaration in this file is proved.  Nothing is assumed.  The axiom
  closure of both headline theorems is `[propext, Quot.sound]` --- choice free.
-/
import WasmGemmGnaf.Wasm.Core.Execution
import WasmGemmGnaf.Wasm.Core.RuntimeDecision
import WasmGemmGnaf.Wasm.Core.RuntimeTypeOrigin

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Values inside an administrative instruction sequence

`Val.toAdmin` is the source's implicit coercion `val* <: instr*`.  Reading a
sequence back requires its partial inverse. -/

/-- The value an administrative instruction is, when it is one. -/
def adminToVal : AdminInstr → Option Val
  | .plain (.const nt c) => some (.num ⟨nt, c⟩)
  | .plain (.vconst vt c) => some (.vec ⟨vt, c⟩)
  | .plain (.refNull ht) => some (.ref (.null ht))
  | .addrref r => some (.ref (.addr r))
  | _ => none

@[simp] theorem adminToVal_toAdmin (v : Val) : adminToVal v.toAdmin = some v := by
  cases v with
  | num n => rfl
  | vec w => rfl
  | ref r => cases r <;> rfl

theorem toAdmin_of_adminToVal {a : AdminInstr} {v : Val}
    (h : adminToVal a = some v) : a = v.toAdmin := by
  cases a with
  | plain i =>
      cases i <;> simp [adminToVal] at h <;> subst h <;> rfl
  | addrref r => simp [adminToVal] at h; subst h; rfl
  | label n cont body => simp [adminToVal] at h
  | frame n f body => simp [adminToVal] at h
  | handler n cs body => simp [adminToVal] at h
  | trap => simp [adminToVal] at h

theorem adminToVal_eq_some_iff {a : AdminInstr} {v : Val} :
    adminToVal a = some v ↔ a = v.toAdmin :=
  ⟨toAdmin_of_adminToVal, fun h => by subst h; simp⟩

@[simp] theorem adminToVal_trap : adminToVal .trap = none := rfl

@[simp] theorem adminToVal_label (n : Nat) (cont body : List AdminInstr) :
    adminToVal (.label n cont body) = none := rfl

@[simp] theorem adminToVal_frame (n : Nat) (f : Frame) (body : List AdminInstr) :
    adminToVal (.frame n f body) = none := rfl

@[simp] theorem adminToVal_handler (n : Nat) (cs : List Catch)
    (body : List AdminInstr) : adminToVal (.handler n cs body) = none := rfl

@[simp] theorem vals_nil : vals [] = [] := rfl

@[simp] theorem vals_cons (v : Val) (vs : List Val) :
    vals (v :: vs) = v.toAdmin :: vals vs := rfl

@[simp] theorem vals_append (vs ws : List Val) :
    vals (vs ++ ws) = vals vs ++ vals ws := List.map_append

@[simp] theorem vals_length (vs : List Val) : (vals vs).length = vs.length :=
  List.length_map _

/-- `vals` is injective: the coercion loses nothing. -/
theorem vals_injective {vs ws : List Val} (h : vals vs = vals ws) : vs = ws := by
  induction vs generalizing ws with
  | nil => cases ws with
    | nil => rfl
    | cons w ws => simp [vals] at h
  | cons v vs ih =>
      cases ws with
      | nil => simp [vals] at h
      | cons w ws =>
          simp only [vals_cons, List.cons.injEq] at h
          have hv : v = w := by
            have := congrArg adminToVal h.1
            simpa using this
          exact by rw [hv, ih h.2]

/-! ## The canonical decomposition

Every rule of `Step_pure` whose left-hand side is a sequence writes it as
`val* ...`, with the tail starting at something that is not a value.  That
decomposition is unique, and `splitVals` computes it. -/

/-- The maximal value prefix of an instruction sequence, and what follows it. -/
def splitVals : List AdminInstr → List Val × List AdminInstr
  | [] => ([], [])
  | a :: rest =>
      match adminToVal a with
      | some v => (v :: (splitVals rest).1, (splitVals rest).2)
      | none => ([], a :: rest)

@[simp] theorem splitVals_nil : splitVals [] = ([], []) := rfl

theorem splitVals_cons_val (v : Val) (rest : List AdminInstr) :
    splitVals (v.toAdmin :: rest) =
      (v :: (splitVals rest).1, (splitVals rest).2) := by
  simp [splitVals]

theorem splitVals_cons_nonval {a : AdminInstr} (h : adminToVal a = none)
    (rest : List AdminInstr) : splitVals (a :: rest) = ([], a :: rest) := by
  simp [splitVals, h]

/-- `splitVals` really splits: the two components reassemble the input. -/
theorem splitVals_append (is : List AdminInstr) :
    vals (splitVals is).1 ++ (splitVals is).2 = is := by
  induction is with
  | nil => rfl
  | cons a rest ih =>
      cases h : adminToVal a with
      | none => simp [splitVals, h]
      | some v =>
          have ha : a = v.toAdmin := toAdmin_of_adminToVal h
          subst ha
          rw [splitVals_cons_val]
          simpa using ih

/-- What follows the maximal value prefix does not start with a value. -/
theorem splitVals_snd_head {is : List AdminInstr} {a : AdminInstr}
    {t : List AdminInstr} (h : (splitVals is).2 = a :: t) :
    adminToVal a = none := by
  induction is with
  | nil => simp at h
  | cons b rest ih =>
      cases hb : adminToVal b with
      | none =>
          rw [splitVals_cons_nonval hb] at h
          simp only [List.cons.injEq] at h
          rw [← h.1]; exact hb
      | some v =>
          have : b = v.toAdmin := toAdmin_of_adminToVal hb
          subst this
          rw [splitVals_cons_val] at h
          exact ih h

/-- **Canonicity.**  A decomposition whose tail does not start with a value IS
the one `splitVals` computes.  This is what lets a rule stated as
`val* ...` be recognized by an executable enumerator. -/
theorem splitVals_of_append (vs : List Val) (rest : List AdminInstr)
    (h : ∀ a t, rest = a :: t → adminToVal a = none) :
    splitVals (vals vs ++ rest) = (vs, rest) := by
  induction vs with
  | nil =>
      cases rest with
      | nil => rfl
      | cons a t => exact splitVals_cons_nonval (h a t rfl) t
  | cons v vs ih =>
      simp only [vals_cons, List.cons_append]
      rw [splitVals_cons_val, ih]

/-- The specialization used throughout: a tail that starts at an explicit
non-value. -/
theorem splitVals_vals_append_nonval (vs : List Val) {a : AdminInstr}
    (ha : adminToVal a = none) (t : List AdminInstr) :
    splitVals (vals vs ++ a :: t) = (vs, a :: t) :=
  splitVals_of_append vs (a :: t) (fun b u hb => by
    simp only [List.cons.injEq] at hb
    rw [← hb.1]; exact ha)

@[simp] theorem splitVals_vals (vs : List Val) : splitVals (vals vs) = (vs, []) := by
  have := splitVals_of_append vs [] (by intro a t h; simp at h)
  simpa using this

/-! ## The event

One constructor per rule of `relation Step_pure`, in the order
`Wasm/Core/Execution.lean` states them, plus a natural number that records
which element of a set-valued numeric result was drawn.  The rules whose
premise is written `c <- $op_(...)` in the source draw from a set; every other
rule uses index `0`. -/

/-- The name of a `Step_pure` rule. -/
inductive PureRule where
  | unreachable | nop | drop | selectTrue | selectFalse | ifTrue | ifFalse
  | labelVals | brLabelZero | brLabelSucc | brHandler | brIfTrue | brIfFalse
  | brTableLt | brTableGe | brOnNullNull | brOnNullAddr | brOnNonNullNull
  | brOnNonNullAddr | callIndirect | returnCallIndirect | frameVals
  | returnFrame | returnLabel | returnHandler | handlerVals | trapInstrs
  | trapLabel | trapFrame | localTee | refI31 | refIsNullTrue | refIsNullFalse
  | refAsNonNullNull | refAsNonNullAddr | refEqNull | refEqTrue | refEqFalse
  | i31GetNull | i31GetNum | arrayNew | externConvertAnyNull
  | externConvertAnyAddr | anyConvertExternNull | anyConvertExternAddr
  | unopVal | unopTrap | binopVal | binopTrap | testop | relop | cvtopVal
  | cvtopTrap | vvunop | vvbinop | vvternop | vvtestop | vunopVal | vunopTrap
  | vbinopVal | vbinopTrap | vternopVal | vternopTrap | vtestop | vrelop
  | vshiftop | vbitmask | vswizzlop | vshuffle | vsplat | vextractLaneNum
  | vextractLanePack | vreplaceLane | vextunop | vextbinop | vextternop
  | vnarrow | vcvtop
  deriving DecidableEq, Repr, Inhabited

/-- The label of one `Step_pure` reduction: the rule that fired, and which
permitted result it drew. -/
structure PureEvent where
  /-- The pinned rule this reduction is an instance of. -/
  rule : PureRule
  /-- The index of the drawn element, for a rule whose result the source takes
  from a set; `0` for every deterministic rule. -/
  choice : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-! ## Enumeration helpers -/

/-- A list paired with the position of each element. -/
def withIndex {α : Type} : List α → Nat → List (α × Nat)
  | [], _ => []
  | a :: l, i => (a, i) :: withIndex l (i + 1)

theorem mem_withIndex {α : Type} {l : List α} {a : α} {i k : Nat}
    (h : (a, i) ∈ withIndex l k) : a ∈ l := by
  induction l generalizing k with
  | nil => simp [withIndex] at h
  | cons b l ih =>
      simp only [withIndex, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨hb, _⟩ | h
      · exact hb ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem exists_mem_withIndex {α : Type} {l : List α} {a : α} (h : a ∈ l)
    (k : Nat) : ∃ i, (a, i) ∈ withIndex l k := by
  induction l generalizing k with
  | nil => simp at h
  | cons b l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨k, by simp [withIndex]⟩
      · obtain ⟨i, hi⟩ := ih h (k + 1)
        exact ⟨i, by simp [withIndex, hi]⟩

theorem withIndex_le {α : Type} {l : List α} {p : α × Nat} {k : Nat}
    (h : p ∈ withIndex l k) : k ≤ p.2 := by
  induction l generalizing k with
  | nil => simp [withIndex] at h
  | cons c l ih =>
      simp only [withIndex, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih h)

theorem withIndex_pairwise_snd {α : Type} (l : List α) (k : Nat) :
    (withIndex l k).Pairwise (fun p q => p.2 ≠ q.2) := by
  induction l generalizing k with
  | nil => simp [withIndex]
  | cons b l ih =>
      refine List.Pairwise.cons ?_ (ih (k + 1))
      intro q hq
      have := withIndex_le hq
      simp only
      omega

/-- Every entry a rule with a set-valued result contributes, tagged with the
index of the element drawn. -/
def choices {α : Type} (r : PureRule) (l : List α)
    (g : α → List AdminInstr) : List (PureEvent × List AdminInstr) :=
  (withIndex l 0).map (fun p => (⟨r, p.2⟩, g p.1))

/-- The single entry a deterministic rule contributes. -/
def single (r : PureRule) (is' : List AdminInstr) :
    List (PureEvent × List AdminInstr) := [(⟨r, 0⟩, is')]

@[simp] theorem exists_mem_single {r : PureRule} {is' x : List AdminInstr} :
    (∃ e, (e, is') ∈ single r x) ↔ is' = x := by
  simp [single]

theorem exists_mem_choices {α : Type} {r : PureRule} {l : List α}
    {g : α → List AdminInstr} {is' : List AdminInstr} :
    (∃ e, (e, is') ∈ choices r l g) ↔ ∃ a, a ∈ l ∧ is' = g a := by
  constructor
  · rintro ⟨e, he⟩
    simp only [choices, List.mem_map, Prod.mk.injEq] at he
    obtain ⟨p, hp, _, hg⟩ := he
    exact ⟨p.1, mem_withIndex hp, hg.symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := exists_mem_withIndex ha 0
    exact ⟨⟨r, i⟩, by
      simp only [choices, List.mem_map]
      exact ⟨(a, i), hi, rfl⟩⟩

theorem single_nodup (r : PureRule) (is' : List AdminInstr) :
    (single r is').Nodup := by simp [single]

theorem choices_nodup {α : Type} (r : PureRule) (l : List α)
    (g : α → List AdminInstr) : (choices r l g).Nodup := by
  refine List.Pairwise.map _ ?_ (withIndex_pairwise_snd l 0)
  intro p q hpq
  simp only [ne_eq, Prod.mk.injEq, not_and]
  intro he
  exact absurd (congrArg PureEvent.choice he) hpq

/-! ## Comparing a value's type with the type an operator names

The scalar operator rules require the operand's `numtype` to be the one the
instruction carries.  `numAt` decides that, and `numAt_val` states the
consequence as an equation between VALUES, so that no transport along a type
equation ever appears. -/

/-- A `num_(nt')` read at `nt`, when the two types agree. -/
def numAt : (nt' nt : NumType) → Num_ nt' → Option (Num_ nt)
  | .i32, .i32, c => some c
  | .i64, .i64, c => some c
  | .f32, .f32, c => some c
  | .f64, .f64, c => some c
  | _, _, _ => none

@[simp] theorem numAt_self (nt : NumType) (c : Num_ nt) : numAt nt nt c = some c := by
  cases nt <;> rfl

theorem numAt_val {nt' nt : NumType} {c₁ : Num_ nt'} {c : Num_ nt}
    (h : numAt nt' nt c₁ = some c) : Val.num ⟨nt', c₁⟩ = Val.num ⟨nt, c⟩ := by
  cases nt' <;> cases nt <;> simp [numAt] at h <;> subst h <;> rfl

/-! ## Null tests

Six rules are stated `-- if ref = (REF.NULL ht)` against an `-- otherwise`
sibling.  These decide that side condition. -/

/-- Whether a reference is a null reference. -/
def isNullRef : Ref → Bool
  | .null _ => true
  | .addr _ => false

/-- Whether a value is a null reference. -/
def isNullVal : Val → Bool
  | .ref r => isNullRef r
  | _ => false

theorem isNullVal_eq_true {v : Val} (h : isNullVal v = true) :
    ∃ ht, v = .ref (.null ht) := by
  cases v with
  | num _ => simp [isNullVal] at h
  | vec _ => simp [isNullVal] at h
  | ref r => cases r with
    | null ht => exact ⟨ht, rfl⟩
    | addr _ => simp [isNullVal, isNullRef] at h

theorem isNullVal_eq_false {v : Val} (h : isNullVal v = false) :
    ∀ ht, v ≠ .ref (.null ht) := by
  intro ht hv
  subst hv
  simp [isNullVal, isNullRef] at h

@[simp] theorem isNullVal_null (ht : HeapType) :
    isNullVal (.ref (.null ht)) = true := rfl

theorem isNullRef_eq_true {r : Ref} (h : isNullRef r = true) : ∃ ht, r = .null ht := by
  cases r with
  | null ht => exact ⟨ht, rfl⟩
  | addr _ => simp [isNullRef] at h

theorem isNullRef_eq_false {r : Ref} (h : isNullRef r = false) :
    ∀ ht, r ≠ .null ht := by
  intro ht hr; subst hr; simp [isNullRef] at h

/-! ## Literal constants the rules pin by an equation

`Step_pure/ref.is_null-true` concludes `(CONST I32 c)  -- if c = 1`; a subtype
of `Nat` is determined by its value, so the successor is unique. -/

/-- `0 : u32`. -/
def u32Zero : U32 := ⟨0, by decide⟩

/-- `1 : u32`. -/
def u32One : U32 := ⟨1, by decide⟩

/-- `0 : iN(128)`, the `$vsize(V128)`-wide zero `Step_pure/vvtestop` compares
against. -/
def v128Zero : IN 128 := ⟨0, by decide⟩

theorem u32_of_val_zero {c : U32} (h : c.val = 0) : c = u32Zero := Subtype.ext h

theorem u32_of_val_one {c : U32} (h : c.val = 1) : c = u32One := Subtype.ext h

theorem in128_of_val_zero {z : IN 128} (h : z.val = 0) : z = v128Zero := Subtype.ext h

/-! ## Operand patterns

Every `Step_pure` rule whose redex ends in a syntactic instruction fixes the
exact list of operands in front of it.  These read that list back.  Each comes
with two lemmas: one computing it on the shape the rule states, and one
recovering that shape from a successful read -- the second is where the
`numtype` transport of `numAt_val` is discharged, so no cast survives into a
proof. -/

/-- A value read as a `num_(nt)`. -/
def valNum (nt : NumType) : Val → Option (Num_ nt)
  | .num ⟨nt', c⟩ => numAt nt' nt c
  | _ => none

@[simp] theorem valNum_num (nt : NumType) (c : Num_ nt) :
    valNum nt (.num ⟨nt, c⟩) = some c := by simp [valNum]

theorem valNum_eq {nt : NumType} {v : Val} {c : Num_ nt}
    (h : valNum nt v = some c) : v = .num ⟨nt, c⟩ := by
  cases v with
  | num n => obtain ⟨nt', c'⟩ := n; exact numAt_val h
  | vec _ => simp [valNum] at h
  | ref _ => simp [valNum] at h

/-- A value read as a `vec_(V128)`. -/
def valVec : Val → Option V128Lit
  | .vec ⟨.v128, c⟩ => some c
  | _ => none

@[simp] theorem valVec_vec (c : V128Lit) : valVec (.vec ⟨.v128, c⟩) = some c := rfl

theorem valVec_eq {v : Val} {c : V128Lit} (h : valVec v = some c) :
    v = .vec ⟨.v128, c⟩ := by
  cases v with
  | vec w => obtain ⟨vt, c'⟩ := w; cases vt; simp [valVec] at h; subst h; rfl
  | num _ => simp [valVec] at h
  | ref _ => simp [valVec] at h

/-- A value read as a `ref`. -/
def valRef : Val → Option Ref
  | .ref r => some r
  | _ => none

@[simp] theorem valRef_ref (r : Ref) : valRef (.ref r) = some r := rfl

theorem valRef_eq {v : Val} {r : Ref} (h : valRef v = some r) : v = .ref r := by
  cases v with
  | ref r' => simp [valRef] at h; subst h; rfl
  | num _ => simp [valRef] at h
  | vec _ => simp [valRef] at h

/-- One operand of any sort. -/
def arg1 : List Val → Option Val
  | [v] => some v
  | _ => none

@[simp] theorem arg1_single (v : Val) : arg1 [v] = some v := rfl

theorem arg1_eq {vs : List Val} {v : Val} (h : arg1 vs = some v) : vs = [v] := by
  cases vs with
  | nil => simp [arg1] at h
  | cons a t => cases t with
    | nil => simp [arg1] at h; rw [h]
    | cons b u => simp [arg1] at h

/-- One numeric operand of type `nt`. -/
def arg1num (nt : NumType) : List Val → Option (Num_ nt)
  | [v] => valNum nt v
  | _ => none

@[simp] theorem arg1num_num (nt : NumType) (c : Num_ nt) :
    arg1num nt [Val.num ⟨nt, c⟩] = some c := by simp [arg1num]

theorem arg1num_eq {nt : NumType} {vs : List Val} {c : Num_ nt}
    (h : arg1num nt vs = some c) : vs = [Val.num ⟨nt, c⟩] := by
  cases vs with
  | nil => simp [arg1num] at h
  | cons a t => cases t with
    | nil => simp only [arg1num] at h; rw [valNum_eq h]
    | cons b u => simp [arg1num] at h

/-- Two numeric operands of type `nt`. -/
def arg2num (nt : NumType) : List Val → Option (Num_ nt × Num_ nt)
  | [v₁, v₂] =>
      match valNum nt v₁, valNum nt v₂ with
      | some c₁, some c₂ => some (c₁, c₂)
      | _, _ => none
  | _ => none

@[simp] theorem arg2num_num (nt : NumType) (c₁ c₂ : Num_ nt) :
    arg2num nt [Val.num ⟨nt, c₁⟩, Val.num ⟨nt, c₂⟩] = some (c₁, c₂) := by
  simp [arg2num]

theorem arg2num_eq {nt : NumType} {vs : List Val} {c₁ c₂ : Num_ nt}
    (h : arg2num nt vs = some (c₁, c₂)) :
    vs = [Val.num ⟨nt, c₁⟩, Val.num ⟨nt, c₂⟩] := by
  cases vs with
  | nil => simp [arg2num] at h
  | cons a t => cases t with
    | nil => simp [arg2num] at h
    | cons b u => cases u with
      | cons _ _ => simp [arg2num] at h
      | nil =>
          simp only [arg2num] at h
          cases h₁ : valNum nt a with
          | none => rw [h₁] at h; simp at h
          | some d₁ =>
              cases h₂ : valNum nt b with
              | none => rw [h₁, h₂] at h; simp at h
              | some d₂ =>
                  rw [h₁, h₂] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [valNum_eq h₁, valNum_eq h₂, h.1, h.2]

/-- One reference operand. -/
def arg1ref : List Val → Option Ref
  | [v] => valRef v
  | _ => none

@[simp] theorem arg1ref_ref (r : Ref) : arg1ref [Val.ref r] = some r := rfl

theorem arg1ref_eq {vs : List Val} {r : Ref} (h : arg1ref vs = some r) :
    vs = [Val.ref r] := by
  cases vs with
  | nil => simp [arg1ref] at h
  | cons a t => cases t with
    | nil => simp only [arg1ref] at h; rw [valRef_eq h]
    | cons b u => simp [arg1ref] at h

/-- Two reference operands. -/
def arg2ref : List Val → Option (Ref × Ref)
  | [v₁, v₂] =>
      match valRef v₁, valRef v₂ with
      | some r₁, some r₂ => some (r₁, r₂)
      | _, _ => none
  | _ => none

@[simp] theorem arg2ref_ref (r₁ r₂ : Ref) :
    arg2ref [Val.ref r₁, Val.ref r₂] = some (r₁, r₂) := by simp [arg2ref]

theorem arg2ref_eq {vs : List Val} {r₁ r₂ : Ref} (h : arg2ref vs = some (r₁, r₂)) :
    vs = [Val.ref r₁, Val.ref r₂] := by
  cases vs with
  | nil => simp [arg2ref] at h
  | cons a t => cases t with
    | nil => simp [arg2ref] at h
    | cons b u => cases u with
      | cons _ _ => simp [arg2ref] at h
      | nil =>
          simp only [arg2ref] at h
          cases h₁ : valRef a with
          | none => rw [h₁] at h; simp at h
          | some s₁ =>
              cases h₂ : valRef b with
              | none => rw [h₁, h₂] at h; simp at h
              | some s₂ =>
                  rw [h₁, h₂] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [valRef_eq h₁, valRef_eq h₂, h.1, h.2]

/-- One vector operand. -/
def arg1vec : List Val → Option V128Lit
  | [v] => valVec v
  | _ => none

@[simp] theorem arg1vec_vec (c : V128Lit) :
    arg1vec [Val.vec ⟨.v128, c⟩] = some c := rfl

theorem arg1vec_eq {vs : List Val} {c : V128Lit} (h : arg1vec vs = some c) :
    vs = [Val.vec ⟨.v128, c⟩] := by
  cases vs with
  | nil => simp [arg1vec] at h
  | cons a t => cases t with
    | nil => simp only [arg1vec] at h; rw [valVec_eq h]
    | cons b u => simp [arg1vec] at h

/-- Two vector operands. -/
def arg2vec : List Val → Option (V128Lit × V128Lit)
  | [v₁, v₂] =>
      match valVec v₁, valVec v₂ with
      | some c₁, some c₂ => some (c₁, c₂)
      | _, _ => none
  | _ => none

@[simp] theorem arg2vec_vec (c₁ c₂ : V128Lit) :
    arg2vec [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩] = some (c₁, c₂) := by
  simp [arg2vec]

theorem arg2vec_eq {vs : List Val} {c₁ c₂ : V128Lit}
    (h : arg2vec vs = some (c₁, c₂)) :
    vs = [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩] := by
  cases vs with
  | nil => simp [arg2vec] at h
  | cons a t => cases t with
    | nil => simp [arg2vec] at h
    | cons b u => cases u with
      | cons _ _ => simp [arg2vec] at h
      | nil =>
          simp only [arg2vec] at h
          cases h₁ : valVec a with
          | none => rw [h₁] at h; simp at h
          | some d₁ =>
              cases h₂ : valVec b with
              | none => rw [h₁, h₂] at h; simp at h
              | some d₂ =>
                  rw [h₁, h₂] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [valVec_eq h₁, valVec_eq h₂, h.1, h.2]

/-- Three vector operands. -/
def arg3vec : List Val → Option (V128Lit × V128Lit × V128Lit)
  | [v₁, v₂, v₃] =>
      match valVec v₁, valVec v₂, valVec v₃ with
      | some c₁, some c₂, some c₃ => some (c₁, c₂, c₃)
      | _, _, _ => none
  | _ => none

@[simp] theorem arg3vec_vec (c₁ c₂ c₃ : V128Lit) :
    arg3vec [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩] =
      some (c₁, c₂, c₃) := by simp [arg3vec]

theorem arg3vec_eq {vs : List Val} {c₁ c₂ c₃ : V128Lit}
    (h : arg3vec vs = some (c₁, c₂, c₃)) :
    vs = [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩] := by
  match vs with
  | [] => simp [arg3vec] at h
  | [_] => simp [arg3vec] at h
  | [_, _] => simp [arg3vec] at h
  | _ :: _ :: _ :: _ :: _ => simp [arg3vec] at h
  | [a, b, c] =>
      simp only [arg3vec] at h
      cases h₁ : valVec a with
      | none => rw [h₁] at h; simp at h
      | some d₁ =>
          cases h₂ : valVec b with
          | none => rw [h₁, h₂] at h; simp at h
          | some d₂ =>
              cases h₃ : valVec c with
              | none => rw [h₁, h₂, h₃] at h; simp at h
              | some d₃ =>
                  rw [h₁, h₂, h₃] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [valVec_eq h₁, valVec_eq h₂, valVec_eq h₃, h.1, h.2.1, h.2.2]

/-- A vector operand and a numeric operand of type `nt`. -/
def argVecNum (nt : NumType) : List Val → Option (V128Lit × Num_ nt)
  | [v₁, v₂] =>
      match valVec v₁, valNum nt v₂ with
      | some c₁, some c₂ => some (c₁, c₂)
      | _, _ => none
  | _ => none

@[simp] theorem argVecNum_vec (nt : NumType) (c₁ : V128Lit) (c₂ : Num_ nt) :
    argVecNum nt [Val.vec ⟨.v128, c₁⟩, Val.num ⟨nt, c₂⟩] = some (c₁, c₂) := by
  simp [argVecNum]

theorem argVecNum_eq {nt : NumType} {vs : List Val} {c₁ : V128Lit} {c₂ : Num_ nt}
    (h : argVecNum nt vs = some (c₁, c₂)) :
    vs = [Val.vec ⟨.v128, c₁⟩, Val.num ⟨nt, c₂⟩] := by
  cases vs with
  | nil => simp [argVecNum] at h
  | cons a t => cases t with
    | nil => simp [argVecNum] at h
    | cons b u => cases u with
      | cons _ _ => simp [argVecNum] at h
      | nil =>
          simp only [argVecNum] at h
          cases h₁ : valVec a with
          | none => rw [h₁] at h; simp at h
          | some d₁ =>
              cases h₂ : valNum nt b with
              | none => rw [h₁, h₂] at h; simp at h
              | some d₂ =>
                  rw [h₁, h₂] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [valVec_eq h₁, valNum_eq h₂, h.1, h.2]

/-- Any value and a numeric operand of type `nt`. -/
def argValNum (nt : NumType) : List Val → Option (Val × Num_ nt)
  | [v₁, v₂] =>
      match valNum nt v₂ with
      | some c => some (v₁, c)
      | none => none
  | _ => none

@[simp] theorem argValNum_val (nt : NumType) (v : Val) (c : Num_ nt) :
    argValNum nt [v, Val.num ⟨nt, c⟩] = some (v, c) := by simp [argValNum]

theorem argValNum_eq {nt : NumType} {vs : List Val} {v : Val} {c : Num_ nt}
    (h : argValNum nt vs = some (v, c)) : vs = [v, Val.num ⟨nt, c⟩] := by
  cases vs with
  | nil => simp [argValNum] at h
  | cons a t => cases t with
    | nil => simp [argValNum] at h
    | cons b u => cases u with
      | cons _ _ => simp [argValNum] at h
      | nil =>
          simp only [argValNum] at h
          cases h₂ : valNum nt b with
          | none => rw [h₂] at h; simp at h
          | some d =>
              rw [h₂] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [valNum_eq h₂, h.1, h.2]

/-- Two values and an `i32` selector: the operand list of `SELECT`. -/
def argSelect : List Val → Option (Val × Val × U32)
  | [v₁, v₂, v₃] =>
      match valNum .i32 v₃ with
      | some c => some (v₁, v₂, c)
      | none => none
  | _ => none

@[simp] theorem argSelect_val (v₁ v₂ : Val) (c : U32) :
    argSelect [v₁, v₂, Val.num ⟨.i32, c⟩] = some (v₁, v₂, c) := by simp [argSelect]

theorem argSelect_eq {vs : List Val} {v₁ v₂ : Val} {c : U32}
    (h : argSelect vs = some (v₁, v₂, c)) :
    vs = [v₁, v₂, Val.num ⟨.i32, c⟩] := by
  match vs with
  | [] => simp [argSelect] at h
  | [_] => simp [argSelect] at h
  | [_, _] => simp [argSelect] at h
  | _ :: _ :: _ :: _ :: _ => simp [argSelect] at h
  | [a, b, c'] =>
      simp only [argSelect] at h
      cases h₃ : valNum .i32 c' with
      | none => rw [h₃] at h; simp at h
      | some d =>
          rw [h₃] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [valNum_eq h₃, h.1, h.2.1, h.2.2]

/-! ## The enumerator, operator by operator

`pureOfInstr Nm vs i` enumerates the reductions of the sequence
`vals vs ++ [.plain i]`, which is the shape of every `Step_pure` rule whose
redex ends in a syntactic instruction. -/

/-- The successors of `vals vs ++ [.plain i]`. -/
def pureOfInstr (Nm : Numerics) (vs : List Val) :
    Instr → List (PureEvent × List AdminInstr)
  -- Step_pure/unreachable
  | .unreachable => match vs with
      | [] => single .unreachable [.trap]
      | _ => []
  -- Step_pure/nop
  | .nop => match vs with
      | [] => single .nop []
      | _ => []
  -- Step_pure/drop
  | .drop => match arg1 vs with
      | some _ => single .drop []
      | none => []
  -- Step_pure/select-true, Step_pure/select-false
  | .select _ => match argSelect vs with
      | some (v₁, v₂, c) =>
          if c.val = 0 then single .selectFalse [v₂.toAdmin]
          else single .selectTrue [v₁.toAdmin]
      | none => []
  -- Step_pure/if-true, Step_pure/if-false
  | .ifElse bt is₁ is₂ => match arg1num .i32 vs with
      | some c =>
          if c.val = 0 then single .ifFalse [.plain (.block bt is₂)]
          else single .ifTrue [.plain (.block bt is₁)]
      | none => []
  -- Step_pure/br_if-true, Step_pure/br_if-false
  | .brIf l => match arg1num .i32 vs with
      | some c =>
          if c.val = 0 then single .brIfFalse []
          else single .brIfTrue [.plain (.br l)]
      | none => []
  -- Step_pure/br_table-lt, Step_pure/br_table-ge
  | .brTable ls l' => match arg1num .i32 vs with
      | some i =>
          match ls[i.val]? with
          | some l => single .brTableLt [.plain (.br l)]
          | none => single .brTableGe [.plain (.br l')]
      | none => []
  -- Step_pure/br_on_null-null, Step_pure/br_on_null-addr
  | .brOnNull l => match arg1 vs with
      | some v =>
          if isNullVal v then single .brOnNullNull [.plain (.br l)]
          else single .brOnNullAddr [v.toAdmin]
      | none => []
  -- Step_pure/br_on_non_null-null, Step_pure/br_on_non_null-addr
  | .brOnNonNull l => match arg1 vs with
      | some v =>
          if isNullVal v then single .brOnNonNullNull []
          else single .brOnNonNullAddr [v.toAdmin, .plain (.br l)]
      | none => []
  -- Step_pure/call_indirect
  | .callIndirect x yy => match vs with
      | [] => single .callIndirect
          [.plain (.tableGet x), .plain (.refCast (.ref (some .null) (.use yy))),
           .plain (.callRef yy)]
      | _ => []
  -- Step_pure/return_call_indirect
  | .returnCallIndirect x yy => match vs with
      | [] => single .returnCallIndirect
          [.plain (.tableGet x), .plain (.refCast (.ref (some .null) (.use yy))),
           .plain (.returnCallRef yy)]
      | _ => []
  -- Step_pure/local.tee
  | .localTee x => match arg1 vs with
      | some v => single .localTee [v.toAdmin, v.toAdmin, .plain (.localSet x)]
      | none => []
  -- Step_pure/ref.i31
  | .refI31 => match arg1num .i32 vs with
      | some i => single .refI31 [.addrref (.i31 (Nm.wrap__ 32 31 i))]
      | none => []
  -- Step_pure/ref.is_null-true, Step_pure/ref.is_null-false
  | .refIsNull => match arg1ref vs with
      | some r =>
          if isNullRef r then single .refIsNullTrue [constI32 u32One]
          else single .refIsNullFalse [constI32 u32Zero]
      | none => []
  -- Step_pure/ref.as_non_null-null, Step_pure/ref.as_non_null-addr
  | .refAsNonNull => match arg1ref vs with
      | some r =>
          if isNullRef r then single .refAsNonNullNull [.trap]
          else single .refAsNonNullAddr [r.toAdmin]
      | none => []
  -- Step_pure/ref.eq-null, Step_pure/ref.eq-true, Step_pure/ref.eq-false
  | .refEq => match arg2ref vs with
      | some (r₁, r₂) =>
          if isNullRef r₁ && isNullRef r₂ then single .refEqNull [constI32 u32One]
          else if r₁ = r₂ then single .refEqTrue [constI32 u32One]
          else single .refEqFalse [constI32 u32Zero]
      | none => []
  -- Step_pure/i31.get-null, Step_pure/i31.get-num
  | .i31Get sx => match arg1ref vs with
      | some (.null _) => single .i31GetNull [.trap]
      | some (.addr (.i31 i)) =>
          single .i31GetNum [constI32 (Nm.extend__ 31 32 sx i)]
      | _ => []
  -- Step_pure/array.new
  | .arrayNew x => match argValNum .i32 vs with
      | some (v, n) =>
          single .arrayNew
            (vals (List.replicate n.val v) ++ [.plain (.arrayNewFixed x n)])
      | none => []
  -- Step_pure/extern.convert_any-null, Step_pure/extern.convert_any-addr
  | .externConvertAny => match arg1ref vs with
      | some (.null _) =>
          single .externConvertAnyNull [Ref.toAdmin (.null (.abs .extern))]
      | some (.addr r) => single .externConvertAnyAddr [.addrref (.extern r)]
      | none => []
  -- Step_pure/any.convert_extern-null, Step_pure/any.convert_extern-addr
  | .anyConvertExtern => match arg1ref vs with
      | some (.null _) =>
          single .anyConvertExternNull [Ref.toAdmin (.null (.abs .any))]
      | some (.addr (.extern r)) => single .anyConvertExternAddr [.addrref r]
      | _ => []
  -- Step_pure/unop-val, Step_pure/unop-trap
  | .unop nt op => match arg1num nt vs with
      | some c =>
          if Nm.unop_ nt op c = [] then single .unopTrap [.trap]
          else choices .unopVal (Nm.unop_ nt op c)
                 (fun r => [.plain (.const nt r)])
      | none => []
  -- Step_pure/binop-val, Step_pure/binop-trap
  | .binop nt op => match arg2num nt vs with
      | some (c₁, c₂) =>
          if Nm.binop_ nt op c₁ c₂ = [] then single .binopTrap [.trap]
          else choices .binopVal (Nm.binop_ nt op c₁ c₂)
                 (fun r => [.plain (.const nt r)])
      | none => []
  -- Step_pure/testop
  | .testop nt op => match arg1num nt vs with
      | some c =>
          match Numerics.testop_ nt op c with
          | some r => single .testop [constI32 r]
          | none => []
      | none => []
  -- Step_pure/relop
  | .relop nt op => match arg2num nt vs with
      | some (c₁, c₂) =>
          match Nm.relop_ nt op c₁ c₂ with
          | some r => single .relop [constI32 r]
          | none => []
      | none => []
  -- Step_pure/cvtop-val, Step_pure/cvtop-trap
  | .cvtop nt₂ nt₁ op => match arg1num nt₁ vs with
      | some c =>
          if Nm.cvtop__ nt₁ nt₂ op c = [] then single .cvtopTrap [.trap]
          else choices .cvtopVal (Nm.cvtop__ nt₁ nt₂ op c)
                 (fun r => [.plain (.const nt₂ r)])
      | none => []
  -- Step_pure/vvunop
  | .vvunop .v128 op => match arg1vec vs with
      | some c₁ =>
          choices .vvunop (Nm.vvunop_ .v128 op c₁)
            (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vvbinop
  | .vvbinop .v128 op => match arg2vec vs with
      | some (c₁, c₂) =>
          choices .vvbinop (Nm.vvbinop_ .v128 op c₁ c₂)
            (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vvternop
  | .vvternop .v128 op => match arg3vec vs with
      | some (c₁, c₂, c₃) =>
          choices .vvternop (Nm.vvternop_ .v128 op c₁ c₂ c₃)
            (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vvtestop
  | .vvtestop .v128 .anyTrue => match arg1vec vs with
      | some c₁ => single .vvtestop [constI32 (Numerics.ine_ 128 c₁ v128Zero)]
      | none => []
  -- Step_pure/vunop-val, Step_pure/vunop-trap
  | .vunop sh op => match arg1vec vs with
      | some c₁ =>
          if Nm.vunop_ sh op c₁ = [] then single .vunopTrap [.trap]
          else choices .vunopVal (Nm.vunop_ sh op c₁)
                 (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vbinop-val, Step_pure/vbinop-trap
  | .vbinop sh op => match arg2vec vs with
      | some (c₁, c₂) =>
          if Nm.vbinop_ sh op c₁ c₂ = [] then single .vbinopTrap [.trap]
          else choices .vbinopVal (Nm.vbinop_ sh op c₁ c₂)
                 (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vternop-val, Step_pure/vternop-trap
  | .vternop sh op => match arg3vec vs with
      | some (c₁, c₂, c₃) =>
          if Nm.vternop_ sh op c₁ c₂ c₃ = [] then single .vternopTrap [.trap]
          else choices .vternopVal (Nm.vternop_ sh op c₁ c₂ c₃)
                 (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- Step_pure/vtestop
  | .vtestop sh op => match arg1vec vs with
      | some c₁ =>
          match Nm.vtestop_ sh op c₁ with
          | some r => single .vtestop [constI32 r]
          | none => []
      | none => []
  -- Step_pure/vrelop
  | .vrelop sh op => match arg2vec vs with
      | some (c₁, c₂) =>
          match Nm.vrelop_ sh op c₁ c₂ with
          | some r => single .vrelop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vshiftop
  | .vshiftop sh op => match argVecNum .i32 vs with
      | some (c₁, i) =>
          match Nm.vshiftop_ sh op c₁ i with
          | some r => single .vshiftop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vbitmask
  | .vbitmask sh => match arg1vec vs with
      | some c₁ =>
          match Nm.vbitmaskop_ sh c₁ with
          | some r => single .vbitmask [constI32 r]
          | none => []
      | none => []
  -- Step_pure/vswizzlop
  | .vswizzlop sh op => match arg2vec vs with
      | some (c₁, c₂) =>
          match Nm.vswizzlop_ sh op c₁ c₂ with
          | some r => single .vswizzlop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vshuffle
  | .vshuffle sh is => match arg2vec vs with
      | some (c₁, c₂) =>
          match Nm.vshufflop_ sh is c₁ c₂ with
          | some r => single .vshuffle [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vsplat
  | .vsplat sh => match arg1num sh.lane.unpack vs with
      | some c =>
          single .vsplat
            [.plain (.vconst .v128
              (Nm.inv_lanes_ sh
                (List.replicate sh.dim.toNat (Nm.lpacknum_ sh.lane c))))]
      | none => []
  -- Step_pure/vextract_lane-num, Step_pure/vextract_lane-pack
  | .vextractLane sh sx i => match arg1vec vs with
      | some c₁ =>
          match sh, sx with
          | ⟨.num nt, m⟩, none =>
              match (Nm.lanes_ ⟨.num nt, m⟩ c₁)[i.val]? with
              | some c₂ => single .vextractLaneNum [.plain (.const nt c₂)]
              | none => []
          | ⟨.pack pt, m⟩, some sgn =>
              match (Nm.lanes_ ⟨.pack pt, m⟩ c₁)[i.val]? with
              | some l => single .vextractLanePack
                  [constI32 (Nm.extend__ pt.size 32 sgn l)]
              | none => []
          | _, _ => []
      | none => []
  -- Step_pure/vreplace_lane
  | .vreplaceLane sh i => match argVecNum sh.lane.unpack vs with
      | some (c₁, c₂) =>
          match setAt? (Nm.lanes_ sh c₁) i.val (Nm.lpacknum_ sh.lane c₂) with
          | some ls =>
              single .vreplaceLane [.plain (.vconst .v128 (Nm.inv_lanes_ sh ls))]
          | none => []
      | none => []
  -- Step_pure/vextunop
  | .vextunop sh₂ sh₁ op => match arg1vec vs with
      | some c₁ =>
          match Nm.vextunop__ sh₁ sh₂ op c₁ with
          | some r => single .vextunop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vextbinop
  | .vextbinop sh₂ sh₁ op => match arg2vec vs with
      | some (c₁, c₂) =>
          match Nm.vextbinop__ sh₁ sh₂ op c₁ c₂ with
          | some r => single .vextbinop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vextternop
  | .vextternop sh₂ sh₁ op => match arg3vec vs with
      | some (c₁, c₂, c₃) =>
          match Nm.vextternop__ sh₁ sh₂ op c₁ c₂ c₃ with
          | some r => single .vextternop [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vnarrow
  | .vnarrow sh₂ sh₁ sx => match arg2vec vs with
      | some (c₁, c₂) =>
          match Nm.vnarrowop__ sh₁ sh₂ sx c₁ c₂ with
          | some r => single .vnarrow [.plain (.vconst .v128 r)]
          | none => []
      | none => []
  -- Step_pure/vcvtop
  | .vcvtop sh₂ sh₁ op => match arg1vec vs with
      | some c₁ =>
          choices .vcvtop (Nm.vcvtop__ sh₁ sh₂ op c₁)
            (fun r => [.plain (.vconst .v128 r)])
      | none => []
  -- No `Step_pure` rule has any other syntactic instruction as its redex.
  | _ => []

/-! ## The enumerator, administrative form by administrative form -/

/-- ``The successors of `[LABEL_ n `{cont} body]``. -/
def pureOfLabel (n : Nat) (cont body : List AdminInstr) :
    List (PureEvent × List AdminInstr) :=
  match splitVals body with
  -- Step_pure/label-vals
  | (ws, []) => single .labelVals (vals ws)
  -- Step_pure/br-label-zero, Step_pure/br-label-succ
  | (ws, .plain (.br l) :: _) =>
      if l.val = 0 then
        (if n ≤ ws.length then
          single .brLabelZero (vals (ws.drop (ws.length - n)) ++ cont)
         else [])
      else
        single .brLabelSucc
          (vals ws ++
            [.plain (.br ⟨l.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.property⟩)])
  -- Step_pure/return-label
  | (ws, .plain .ret :: _) => single .returnLabel (vals ws ++ [.plain .ret])
  -- Step_pure/trap-label
  | ([], [.trap]) => single .trapLabel [.trap]
  | _ => []

/-- ``The successors of `[FRAME_ n `{f} body]``. -/
def pureOfFrame (n : Nat) (body : List AdminInstr) :
    List (PureEvent × List AdminInstr) :=
  match splitVals body with
  -- Step_pure/frame-vals
  | (ws, []) => if ws.length = n then single .frameVals (vals ws) else []
  -- Step_pure/return-frame
  | (ws, .plain .ret :: _) =>
      if n ≤ ws.length then
        single .returnFrame (vals (ws.drop (ws.length - n)))
      else []
  -- Step_pure/trap-frame
  | ([], [.trap]) => single .trapFrame [.trap]
  | _ => []

/-- ``The successors of `[HANDLER_ n `{cs} body]``.  `Step_pure` gives a handler
no trap rule; `Step_pure/trap-instrs` reaches inside it through
`Step/ctxt-handler` instead. -/
def pureOfHandler (body : List AdminInstr) : List (PureEvent × List AdminInstr) :=
  match splitVals body with
  -- Step_pure/handler-vals
  | (ws, []) => single .handlerVals (vals ws)
  -- Step_pure/br-handler
  | (ws, .plain (.br l) :: _) => single .brHandler (vals ws ++ [.plain (.br l)])
  -- Step_pure/return-handler
  | (ws, .plain .ret :: _) => single .returnHandler (vals ws ++ [.plain .ret])
  | _ => []

/-- The successors of `vals vs ++ rest`, for a `rest` that does not begin with a
value. -/
def pureOfSplit (Nm : Numerics) (vs : List Val) (rest : List AdminInstr) :
    List (PureEvent × List AdminInstr) :=
  match rest with
  | [.plain i] => pureOfInstr Nm vs i
  -- Step_pure/trap-instrs
  | .trap :: t =>
      match vs, t with
      | [], [] => []
      | _, _ => single .trapInstrs [.trap]
  | [.label n cont body] =>
      match vs with
      | [] => pureOfLabel n cont body
      | _ => []
  | [.frame n _ body] =>
      match vs with
      | [] => pureOfFrame n body
      | _ => []
  | [.handler _ _ body] =>
      match vs with
      | [] => pureOfHandler body
      | _ => []
  | _ => []

/-! ## Soundness: everything enumerated is a reduction -/

theorem not_both_null {r₁ r₂ : Ref} (h : (isNullRef r₁ && isNullRef r₂) = false) :
    ∀ ht₁ ht₂ : HeapType, ¬ (r₁ = .null ht₁ ∧ r₂ = .null ht₂) := by
  rintro ht₁ ht₂ ⟨h₁, h₂⟩
  subst h₁; subst h₂
  simp [isNullRef] at h

/-- Everything `pureOfInstr` lists is a `Step_pure` reduction of the sequence it
was computed from. -/
theorem mem_pureOfInstr_step_pure {Nm : Numerics} {vs : List Val} {i : Instr}
    {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureOfInstr Nm vs i) :
    Step_pure Nm (vals vs ++ [.plain i]) is' := by
  cases i
  case unreachable =>
    cases vs with
    | cons _ _ => simp [pureOfInstr] at h
    | nil => simp [pureOfInstr, single] at h; obtain ⟨-, rfl⟩ := h; exact .unreachable
  case nop =>
    cases vs with
    | cons _ _ => simp [pureOfInstr] at h
    | nil => simp [pureOfInstr, single] at h; obtain ⟨-, rfl⟩ := h; exact .nop
  case drop =>
    cases hA : arg1 vs with
    | none => simp [pureOfInstr, hA] at h
    | some v =>
        rw [arg1_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .drop
  case select ts =>
    cases hA : argSelect vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨v₁, v₂, c⟩ := p
        rw [argSelect_eq hA]
        by_cases hc : c.val = 0
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .selectFalse hc
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .selectTrue hc
  case ifElse bt is₁ is₂ =>
    cases hA : arg1num .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        by_cases hc : c.val = 0
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .ifFalse hc
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .ifTrue hc
  case brIf l =>
    cases hA : arg1num .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        by_cases hc : c.val = 0
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brIfFalse hc
        · simp [pureOfInstr, hA, hc, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brIfTrue hc
  case brTable ls l' =>
    cases hA : arg1num .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        cases hl : ls[c.val]? with
        | some l =>
            simp [pureOfInstr, hA, hl, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .brTableLt hl
        | none =>
            simp [pureOfInstr, hA, hl, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .brTableGe (List.getElem?_eq_none_iff.mp hl)
  case brOnNull l =>
    cases hA : arg1 vs with
    | none => simp [pureOfInstr, hA] at h
    | some v =>
        rw [arg1_eq hA]
        by_cases hn : isNullVal v = true
        · obtain ⟨ht, rfl⟩ := isNullVal_eq_true hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brOnNullNull
        · simp only [Bool.not_eq_true] at hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brOnNullAddr (isNullVal_eq_false hn)
  case brOnNonNull l =>
    cases hA : arg1 vs with
    | none => simp [pureOfInstr, hA] at h
    | some v =>
        rw [arg1_eq hA]
        by_cases hn : isNullVal v = true
        · obtain ⟨ht, rfl⟩ := isNullVal_eq_true hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brOnNonNullNull
        · simp only [Bool.not_eq_true] at hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .brOnNonNullAddr (isNullVal_eq_false hn)
  case callIndirect x yy =>
    cases vs with
    | cons _ _ => simp [pureOfInstr] at h
    | nil =>
        simp [pureOfInstr, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .callIndirect
  case returnCallIndirect x yy =>
    cases vs with
    | cons _ _ => simp [pureOfInstr] at h
    | nil =>
        simp [pureOfInstr, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .returnCallIndirect
  case localTee x =>
    cases hA : arg1 vs with
    | none => simp [pureOfInstr, hA] at h
    | some v =>
        rw [arg1_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .localTee
  case refI31 =>
    cases hA : arg1num .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .refI31 rfl
  case refIsNull =>
    cases hA : arg1ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some r =>
        rw [arg1ref_eq hA]
        by_cases hn : isNullRef r = true
        · obtain ⟨ht, rfl⟩ := isNullRef_eq_true hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .refIsNullTrue rfl
        · simp only [Bool.not_eq_true] at hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .refIsNullFalse (isNullRef_eq_false hn) rfl
  case refAsNonNull =>
    cases hA : arg1ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some r =>
        rw [arg1ref_eq hA]
        by_cases hn : isNullRef r = true
        · obtain ⟨ht, rfl⟩ := isNullRef_eq_true hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .refAsNonNullNull
        · simp only [Bool.not_eq_true] at hn
          simp [pureOfInstr, hA, hn, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .refAsNonNullAddr (isNullRef_eq_false hn)
  case refEq =>
    cases hA : arg2ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨r₁, r₂⟩ := p
        rw [arg2ref_eq hA]
        by_cases hb : (isNullRef r₁ && isNullRef r₂) = true
        · simp only [Bool.and_eq_true] at hb
          obtain ⟨ht₁, rfl⟩ := isNullRef_eq_true hb.1
          obtain ⟨ht₂, rfl⟩ := isNullRef_eq_true hb.2
          simp [pureOfInstr, hA, isNullRef, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .refEqNull rfl
        · simp only [Bool.not_eq_true] at hb
          have hbn : ¬ ((isNullRef r₁ && isNullRef r₂) = true) := by rw [hb]; simp
          by_cases hr : r₁ = r₂
          · have hdef : pureOfInstr Nm vs .refEq =
                single .refEqTrue [constI32 u32One] := by
              simp only [pureOfInstr, hA, if_neg hbn, if_pos hr]
            rw [hdef] at h
            simp [single] at h
            obtain ⟨-, rfl⟩ := h
            exact .refEqTrue (not_both_null hb) hr rfl
          · have hdef : pureOfInstr Nm vs .refEq =
                single .refEqFalse [constI32 u32Zero] := by
              simp only [pureOfInstr, hA, if_neg hbn, if_neg hr]
            rw [hdef] at h
            simp [single] at h
            obtain ⟨-, rfl⟩ := h
            exact .refEqFalse (not_both_null hb) hr rfl
  case i31Get sx =>
    cases hA : arg1ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some r =>
        rw [arg1ref_eq hA]
        cases r with
        | null ht =>
            simp [pureOfInstr, hA, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .i31GetNull
        | addr a =>
            cases a with
            | i31 j =>
                simp [pureOfInstr, hA, single] at h
                obtain ⟨-, rfl⟩ := h
                exact .i31GetNum rfl
            | structAddr _ => simp [pureOfInstr, hA] at h
            | arrayAddr _ => simp [pureOfInstr, hA] at h
            | funcAddr _ => simp [pureOfInstr, hA] at h
            | exnAddr _ => simp [pureOfInstr, hA] at h
            | hostAddr _ => simp [pureOfInstr, hA] at h
            | extern _ => simp [pureOfInstr, hA] at h
  case arrayNew x =>
    cases hA : argValNum .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨v, n⟩ := p
        rw [argValNum_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .arrayNew
  case externConvertAny =>
    cases hA : arg1ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some r =>
        rw [arg1ref_eq hA]
        cases r with
        | null ht =>
            simp [pureOfInstr, hA, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .externConvertAnyNull
        | addr a =>
            simp [pureOfInstr, hA, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .externConvertAnyAddr
  case anyConvertExtern =>
    cases hA : arg1ref vs with
    | none => simp [pureOfInstr, hA] at h
    | some r =>
        rw [arg1ref_eq hA]
        cases r with
        | null ht =>
            simp [pureOfInstr, hA, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .anyConvertExternNull
        | addr a =>
            cases a with
            | extern b =>
                simp [pureOfInstr, hA, single] at h
                obtain ⟨-, rfl⟩ := h
                exact .anyConvertExternAddr
            | i31 _ => simp [pureOfInstr, hA] at h
            | structAddr _ => simp [pureOfInstr, hA] at h
            | arrayAddr _ => simp [pureOfInstr, hA] at h
            | funcAddr _ => simp [pureOfInstr, hA] at h
            | exnAddr _ => simp [pureOfInstr, hA] at h
            | hostAddr _ => simp [pureOfInstr, hA] at h
  case unop nt op =>
    cases hA : arg1num nt vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        by_cases htr : Nm.unop_ nt op c = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .unopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .unopVal hr
  case binop nt op =>
    cases hA : arg2num nt vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2num_eq hA]
        by_cases htr : Nm.binop_ nt op c₁ c₂ = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .binopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .binopVal hr
  case testop nt op =>
    cases hA : arg1num nt vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        cases hr : Numerics.testop_ nt op c with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .testop hr
  case relop nt op =>
    cases hA : arg2num nt vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2num_eq hA]
        cases hr : Nm.relop_ nt op c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .relop hr
  case cvtop nt₂ nt₁ op =>
    cases hA : arg1num nt₁ vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        by_cases htr : Nm.cvtop__ nt₁ nt₂ op c = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .cvtopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .cvtopVal hr
  case vvunop vt op =>
    cases vt
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        simp only [pureOfInstr, hA] at h
        obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
        exact .vvunop hr
  case vvbinop vt op =>
    cases vt
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        simp only [pureOfInstr, hA] at h
        obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
        exact .vvbinop hr
  case vvternop vt op =>
    cases vt
    cases hA : arg3vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂, c₃⟩ := p
        rw [arg3vec_eq hA]
        simp only [pureOfInstr, hA] at h
        obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
        exact .vvternop hr
  case vvtestop vt op =>
    cases vt
    cases op
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .vvtestop rfl rfl
  case vunop sh op =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        by_cases htr : Nm.vunop_ sh op c₁ = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .vunopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .vunopVal hr
  case vbinop sh op =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        by_cases htr : Nm.vbinop_ sh op c₁ c₂ = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .vbinopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .vbinopVal hr
  case vternop sh op =>
    cases hA : arg3vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂, c₃⟩ := p
        rw [arg3vec_eq hA]
        by_cases htr : Nm.vternop_ sh op c₁ c₂ c₃ = []
        · simp [pureOfInstr, hA, htr, single] at h
          obtain ⟨-, rfl⟩ := h
          exact .vternopTrap htr
        · simp only [pureOfInstr, hA, if_neg htr] at h
          obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
          exact .vternopVal hr
  case vtestop sh op =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        cases hr : Nm.vtestop_ sh op c₁ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vtestop hr
  case vrelop sh op =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        cases hr : Nm.vrelop_ sh op c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vrelop hr
  case vshiftop sh op =>
    cases hA : argVecNum .i32 vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, j⟩ := p
        rw [argVecNum_eq hA]
        cases hr : Nm.vshiftop_ sh op c₁ j with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vshiftop hr
  case vbitmask sh =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        cases hr : Nm.vbitmaskop_ sh c₁ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vbitmask hr
  case vswizzlop sh op =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        cases hr : Nm.vswizzlop_ sh op c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vswizzlop hr
  case vshuffle sh js =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        cases hr : Nm.vshufflop_ sh js c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vshuffle hr
  case vsplat sh =>
    cases hA : arg1num sh.lane.unpack vs with
    | none => simp [pureOfInstr, hA] at h
    | some c =>
        rw [arg1num_eq hA]
        simp [pureOfInstr, hA, single] at h
        obtain ⟨-, rfl⟩ := h
        exact .vsplat rfl
  case vextractLane sh sx j =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        obtain ⟨lt, m⟩ := sh
        cases lt with
        | num nt =>
            cases sx with
            | some sgn => simp [pureOfInstr, hA] at h
            | none =>
                cases hl : (Nm.lanes_ ⟨.num nt, m⟩ c₁)[j.val]? with
                | none => simp [pureOfInstr, hA, hl] at h
                | some c₂ =>
                    simp [pureOfInstr, hA, hl, single] at h
                    obtain ⟨-, rfl⟩ := h
                    exact .vextractLaneNum hl
        | pack pt =>
            cases sx with
            | none => simp [pureOfInstr, hA] at h
            | some sgn =>
                cases hl : (Nm.lanes_ ⟨.pack pt, m⟩ c₁)[j.val]? with
                | none => simp [pureOfInstr, hA, hl] at h
                | some l =>
                    simp [pureOfInstr, hA, hl, single] at h
                    obtain ⟨-, rfl⟩ := h
                    exact .vextractLanePack hl rfl
  case vreplaceLane sh j =>
    cases hA : argVecNum sh.lane.unpack vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [argVecNum_eq hA]
        cases hr : setAt? (Nm.lanes_ sh c₁) j.val (Nm.lpacknum_ sh.lane c₂) with
        | none => simp [pureOfInstr, hA, hr] at h
        | some ls =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vreplaceLane hr rfl
  case vextunop sh₂ sh₁ op =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        cases hr : Nm.vextunop__ sh₁ sh₂ op c₁ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vextunop hr
  case vextbinop sh₂ sh₁ op =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        cases hr : Nm.vextbinop__ sh₁ sh₂ op c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vextbinop hr
  case vextternop sh₂ sh₁ op =>
    cases hA : arg3vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂, c₃⟩ := p
        rw [arg3vec_eq hA]
        cases hr : Nm.vextternop__ sh₁ sh₂ op c₁ c₂ c₃ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vextternop hr
  case vnarrow sh₂ sh₁ sx =>
    cases hA : arg2vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some p =>
        obtain ⟨c₁, c₂⟩ := p
        rw [arg2vec_eq hA]
        cases hr : Nm.vnarrowop__ sh₁ sh₂ sx c₁ c₂ with
        | none => simp [pureOfInstr, hA, hr] at h
        | some r =>
            simp [pureOfInstr, hA, hr, single] at h
            obtain ⟨-, rfl⟩ := h
            exact .vnarrow hr
  case vcvtop sh₂ sh₁ op =>
    cases hA : arg1vec vs with
    | none => simp [pureOfInstr, hA] at h
    | some c₁ =>
        rw [arg1vec_eq hA]
        simp only [pureOfInstr, hA] at h
        obtain ⟨r, hr, rfl⟩ := exists_mem_choices.mp ⟨e, h⟩
        exact .vcvtop hr
  all_goals simp [pureOfInstr] at h

/-- ``Everything `pureOfLabel` lists is a reduction of the label it came from.`` -/
theorem mem_pureOfLabel_step_pure {Nm : Numerics} {n : Nat}
    {cont body : List AdminInstr} {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureOfLabel n cont body) :
    Step_pure Nm [.label n cont body] is' := by
  have hb := splitVals_append body
  cases hs : splitVals body with
  | mk ws rest =>
    rw [hs] at hb
    subst hb
    cases rest with
    | nil =>
        simp only [pureOfLabel, hs, single, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hnil : vals ws ++ ([] : List AdminInstr) = vals ws := by simp
        rw [hnil]
        exact .labelVals
    | cons a t =>
        cases a with
        | plain ins =>
            cases ins with
            | br l =>
                by_cases hl : l.val = 0
                · by_cases hn : n ≤ ws.length
                  · simp only [pureOfLabel, hs, if_pos hl, if_pos hn, single,
                      List.mem_singleton, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    have hlen : (ws.drop (ws.length - n)).length = n := by
                      rw [List.length_drop]; omega
                    have hshape :
                        vals (ws.take (ws.length - n)) ++
                          vals (ws.drop (ws.length - n)) ++
                          [AdminInstr.plain (.br l)] ++ t =
                        vals ws ++ (AdminInstr.plain (.br l) :: t) := by
                      rw [← vals_append, List.take_append_drop]
                      simp
                    rw [← hshape]
                    exact .brLabelZero hlen hl
                  · simp only [pureOfLabel, hs, if_pos hl, if_neg hn] at h
                    simp at h
                · simp only [pureOfLabel, hs, if_neg hl, single,
                    List.mem_singleton, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  have hshape : vals ws ++ [AdminInstr.plain (.br l)] ++ t =
                      vals ws ++ (AdminInstr.plain (.br l) :: t) := by simp
                  rw [← hshape]
                  exact .brLabelSucc (by show l.val = l.val - 1 + 1; omega)
            | ret =>
                simp only [pureOfLabel, hs, single, List.mem_singleton,
                  Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                have hshape : vals ws ++ [AdminInstr.plain .ret] ++ t =
                    vals ws ++ (AdminInstr.plain .ret :: t) := by simp
                rw [← hshape]
                exact .returnLabel
            | _ => simp only [pureOfLabel, hs] at h <;> simp at h
        | trap =>
            cases ws with
            | cons _ _ => simp only [pureOfLabel, hs] at h; simp at h
            | nil =>
                cases t with
                | cons _ _ => simp only [pureOfLabel, hs] at h; simp at h
                | nil =>
                    simp only [pureOfLabel, hs, single, List.mem_singleton,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact .trapLabel
        | addrref _ => simp only [pureOfLabel, hs] at h; simp at h
        | label _ _ _ => simp only [pureOfLabel, hs] at h; simp at h
        | frame _ _ _ => simp only [pureOfLabel, hs] at h; simp at h
        | handler _ _ _ => simp only [pureOfLabel, hs] at h; simp at h

/-- ``Everything `pureOfFrame` lists is a reduction of the frame it came
from.`` -/
theorem mem_pureOfFrame_step_pure {Nm : Numerics} {n : Nat} {f : Frame}
    {body : List AdminInstr} {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureOfFrame n body) :
    Step_pure Nm [.frame n f body] is' := by
  have hb := splitVals_append body
  cases hs : splitVals body with
  | mk ws rest =>
    rw [hs] at hb
    subst hb
    cases rest with
    | nil =>
        by_cases hn : ws.length = n
        · simp only [pureOfFrame, hs, if_pos hn, single, List.mem_singleton,
            Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have hnil : vals ws ++ ([] : List AdminInstr) = vals ws := by simp
          rw [hnil]
          exact .frameVals hn
        · simp only [pureOfFrame, hs, if_neg hn] at h; simp at h
    | cons a t =>
        cases a with
        | plain ins =>
            cases ins with
            | ret =>
                by_cases hn : n ≤ ws.length
                · simp only [pureOfFrame, hs, if_pos hn, single,
                    List.mem_singleton, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  have hlen : (ws.drop (ws.length - n)).length = n := by
                    rw [List.length_drop]; omega
                  have hshape :
                      vals (ws.take (ws.length - n)) ++
                        vals (ws.drop (ws.length - n)) ++
                        [AdminInstr.plain .ret] ++ t =
                      vals ws ++ (AdminInstr.plain .ret :: t) := by
                    rw [← vals_append, List.take_append_drop]
                    simp
                  rw [← hshape]
                  exact .returnFrame hlen
                · simp only [pureOfFrame, hs, if_neg hn] at h; simp at h
            | _ => simp only [pureOfFrame, hs] at h <;> simp at h
        | trap =>
            cases ws with
            | cons _ _ => simp only [pureOfFrame, hs] at h; simp at h
            | nil =>
                cases t with
                | cons _ _ => simp only [pureOfFrame, hs] at h; simp at h
                | nil =>
                    simp only [pureOfFrame, hs, single, List.mem_singleton,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact .trapFrame
        | addrref _ => simp only [pureOfFrame, hs] at h; simp at h
        | label _ _ _ => simp only [pureOfFrame, hs] at h; simp at h
        | frame _ _ _ => simp only [pureOfFrame, hs] at h; simp at h
        | handler _ _ _ => simp only [pureOfFrame, hs] at h; simp at h

/-- ``Everything `pureOfHandler` lists is a reduction of the handler it came
from.`` -/
theorem mem_pureOfHandler_step_pure {Nm : Numerics} {n : Nat} {cs : List Catch}
    {body : List AdminInstr} {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureOfHandler body) :
    Step_pure Nm [.handler n cs body] is' := by
  have hb := splitVals_append body
  cases hs : splitVals body with
  | mk ws rest =>
    rw [hs] at hb
    subst hb
    cases rest with
    | nil =>
        simp only [pureOfHandler, hs, single, List.mem_singleton,
          Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hnil : vals ws ++ ([] : List AdminInstr) = vals ws := by simp
        rw [hnil]
        exact .handlerVals
    | cons a t =>
        cases a with
        | plain ins =>
            cases ins with
            | br l =>
                simp only [pureOfHandler, hs, single, List.mem_singleton,
                  Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                have hshape : vals ws ++ [AdminInstr.plain (.br l)] ++ t =
                    vals ws ++ (AdminInstr.plain (.br l) :: t) := by simp
                rw [← hshape]
                exact .brHandler
            | ret =>
                simp only [pureOfHandler, hs, single, List.mem_singleton,
                  Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                have hshape : vals ws ++ [AdminInstr.plain .ret] ++ t =
                    vals ws ++ (AdminInstr.plain .ret :: t) := by simp
                rw [← hshape]
                exact .returnHandler
            | _ => simp only [pureOfHandler, hs] at h <;> simp at h
        | trap => simp only [pureOfHandler, hs] at h; simp at h
        | addrref _ => simp only [pureOfHandler, hs] at h; simp at h
        | label _ _ _ => simp only [pureOfHandler, hs] at h; simp at h
        | frame _ _ _ => simp only [pureOfHandler, hs] at h; simp at h
        | handler _ _ _ => simp only [pureOfHandler, hs] at h; simp at h

/-- Everything the enumerator lists for a canonical decomposition is a
reduction of the sequence that decomposition came from. -/
theorem mem_pureOfSplit_step_pure {Nm : Numerics} {vs : List Val}
    {rest : List AdminInstr} {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureOfSplit Nm vs rest) :
    Step_pure Nm (vals vs ++ rest) is' := by
  cases rest with
  | nil => simp [pureOfSplit] at h
  | cons a t =>
      cases a with
      | plain ins =>
          cases t with
          | cons _ _ => simp [pureOfSplit] at h
          | nil =>
              simp only [pureOfSplit] at h
              exact mem_pureOfInstr_step_pure h
      | trap =>
          have hgen : ∀ (hc : vs ≠ [] ∨ t ≠ []),
              Step_pure Nm (vals vs ++ AdminInstr.trap :: t) [.trap] := by
            intro hc
            have hst : Step_pure Nm (vals vs ++ [AdminInstr.trap] ++ t) [.trap] :=
              .trapInstrs hc
            simpa using hst
          cases vs with
          | cons v vs' =>
              simp only [pureOfSplit, single, List.mem_singleton,
                Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact hgen (Or.inl (by simp))
          | nil =>
              cases t with
              | nil => simp [pureOfSplit] at h
              | cons b u =>
                  simp only [pureOfSplit, single, List.mem_singleton,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact hgen (Or.inr (by simp))
      | label m cont body =>
          cases t with
          | cons _ _ => simp [pureOfSplit] at h
          | nil =>
              cases vs with
              | cons _ _ => simp [pureOfSplit] at h
              | nil =>
                  simp only [pureOfSplit] at h
                  have := mem_pureOfLabel_step_pure (Nm := Nm) h
                  simpa using this
      | frame m f body =>
          cases t with
          | cons _ _ => simp [pureOfSplit] at h
          | nil =>
              cases vs with
              | cons _ _ => simp [pureOfSplit] at h
              | nil =>
                  simp only [pureOfSplit] at h
                  have := mem_pureOfFrame_step_pure (Nm := Nm) (f := f) h
                  simpa using this
      | handler m cs body =>
          cases t with
          | cons _ _ => simp [pureOfSplit] at h
          | nil =>
              cases vs with
              | cons _ _ => simp [pureOfSplit] at h
              | nil =>
                  simp only [pureOfSplit] at h
                  have := mem_pureOfHandler_step_pure (Nm := Nm) (n := m) (cs := cs) h
                  simpa using this
      | addrref r =>
          have : adminToVal (AdminInstr.addrref r) = some (.ref (.addr r)) := rfl
          cases t with
          | nil => simp [pureOfSplit] at h
          | cons _ _ => simp [pureOfSplit] at h

/-- **The executable successor enumerator of `relation Step_pure`.**  Total,
structurally recursive through `splitVals`, and free of any evaluator choice:
where the source permits several results the list carries all of them. -/
def pureSuccessors (Nm : Numerics) (is : List AdminInstr) :
    List (PureEvent × List AdminInstr) :=
  pureOfSplit Nm (splitVals is).1 (splitVals is).2

/-! ## Completeness: every rule is enumerated

Each lemma below computes the enumerator on the exact shape one family of rules
states its redex in, so the 78 cases of the induction reduce to an equation
between two explicit lists. -/

theorem pureSuccessors_ofInstr {Nm : Numerics} (vs : List Val) (i : Instr)
    (hi : adminToVal (.plain i) = none) :
    pureSuccessors Nm (vals vs ++ [.plain i]) = pureOfInstr Nm vs i := by
  show pureOfSplit Nm (splitVals (vals vs ++ [AdminInstr.plain i])).1
        (splitVals (vals vs ++ [AdminInstr.plain i])).2 = _
  rw [splitVals_vals_append_nonval vs hi []]
  rfl

theorem exists_mem_pureSuccessors_ofInstr {Nm : Numerics} {vs : List Val}
    {i : Instr} {is' : List AdminInstr} (hi : adminToVal (.plain i) = none)
    (h : ∃ e, (e, is') ∈ pureOfInstr Nm vs i) :
    ∃ e, (e, is') ∈ pureSuccessors Nm (vals vs ++ [.plain i]) := by
  rw [pureSuccessors_ofInstr vs i hi]; exact h

theorem pureSuccessors_label {Nm : Numerics} (n : Nat) (cont body : List AdminInstr) :
    pureSuccessors Nm [.label n cont body] = pureOfLabel n cont body := by
  show pureOfSplit Nm (splitVals [AdminInstr.label n cont body]).1
        (splitVals [AdminInstr.label n cont body]).2 = _
  rw [splitVals_cons_nonval (a := AdminInstr.label n cont body) rfl []]
  rfl

theorem pureSuccessors_frame {Nm : Numerics} (n : Nat) (f : Frame)
    (body : List AdminInstr) :
    pureSuccessors Nm [.frame n f body] = pureOfFrame n body := by
  show pureOfSplit Nm (splitVals [AdminInstr.frame n f body]).1
        (splitVals [AdminInstr.frame n f body]).2 = _
  rw [splitVals_cons_nonval (a := AdminInstr.frame n f body) rfl []]
  rfl

theorem pureSuccessors_handler {Nm : Numerics} (n : Nat) (cs : List Catch)
    (body : List AdminInstr) :
    pureSuccessors Nm [.handler n cs body] = pureOfHandler body := by
  show pureOfSplit Nm (splitVals [AdminInstr.handler n cs body]).1
        (splitVals [AdminInstr.handler n cs body]).2 = _
  rw [splitVals_cons_nonval (a := AdminInstr.handler n cs body) rfl []]
  rfl

theorem pureSuccessors_trap {Nm : Numerics} (vs : List Val) (t : List AdminInstr) :
    pureSuccessors Nm (vals vs ++ AdminInstr.trap :: t) =
      pureOfSplit Nm vs (.trap :: t) := by
  show pureOfSplit Nm (splitVals (vals vs ++ AdminInstr.trap :: t)).1
        (splitVals (vals vs ++ AdminInstr.trap :: t)).2 = _
  rw [splitVals_vals_append_nonval vs (a := AdminInstr.trap) rfl t]

theorem pureOfLabel_vals (n : Nat) (cont : List AdminInstr) (ws : List Val) :
    pureOfLabel n cont (vals ws) = single .labelVals (vals ws) := by
  simp only [pureOfLabel, splitVals_vals]

theorem pureOfLabel_br (n : Nat) (cont : List AdminInstr) (ws : List Val)
    (l : LabelIdx) (t : List AdminInstr) :
    pureOfLabel n cont (vals ws ++ AdminInstr.plain (.br l) :: t) =
      (if l.val = 0 then
        (if n ≤ ws.length then
          single .brLabelZero (vals (ws.drop (ws.length - n)) ++ cont)
         else [])
       else
        single .brLabelSucc
          (vals ws ++
            [.plain (.br ⟨l.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.property⟩)])) := by
  simp only [pureOfLabel,
    splitVals_vals_append_nonval ws (a := AdminInstr.plain (.br l)) rfl t]

theorem pureOfLabel_ret (n : Nat) (cont : List AdminInstr) (ws : List Val)
    (t : List AdminInstr) :
    pureOfLabel n cont (vals ws ++ AdminInstr.plain .ret :: t) =
      single .returnLabel (vals ws ++ [.plain .ret]) := by
  simp only [pureOfLabel,
    splitVals_vals_append_nonval ws (a := AdminInstr.plain .ret) rfl t]

theorem pureOfLabel_trap (n : Nat) (cont : List AdminInstr) :
    pureOfLabel n cont [.trap] = single .trapLabel [.trap] := rfl

theorem pureOfFrame_vals (n : Nat) (ws : List Val) :
    pureOfFrame n (vals ws) =
      (if ws.length = n then single .frameVals (vals ws) else []) := by
  simp only [pureOfFrame, splitVals_vals]

theorem pureOfFrame_ret (n : Nat) (ws : List Val) (t : List AdminInstr) :
    pureOfFrame n (vals ws ++ AdminInstr.plain .ret :: t) =
      (if n ≤ ws.length then
        single .returnFrame (vals (ws.drop (ws.length - n)))
       else []) := by
  simp only [pureOfFrame,
    splitVals_vals_append_nonval ws (a := AdminInstr.plain .ret) rfl t]

theorem pureOfFrame_trap (n : Nat) : pureOfFrame n [.trap] = single .trapFrame [.trap] :=
  rfl

theorem pureOfHandler_vals (ws : List Val) :
    pureOfHandler (vals ws) = single .handlerVals (vals ws) := by
  simp only [pureOfHandler, splitVals_vals]

theorem pureOfHandler_br (ws : List Val) (l : LabelIdx) (t : List AdminInstr) :
    pureOfHandler (vals ws ++ AdminInstr.plain (.br l) :: t) =
      single .brHandler (vals ws ++ [.plain (.br l)]) := by
  simp only [pureOfHandler,
    splitVals_vals_append_nonval ws (a := AdminInstr.plain (.br l)) rfl t]

theorem pureOfHandler_ret (ws : List Val) (t : List AdminInstr) :
    pureOfHandler (vals ws ++ AdminInstr.plain .ret :: t) =
      single .returnHandler (vals ws ++ [.plain .ret]) := by
  simp only [pureOfHandler,
    splitVals_vals_append_nonval ws (a := AdminInstr.plain .ret) rfl t]

/-- Every `Step_pure` reduction is enumerated. -/
theorem step_pure_mem_pureSuccessors {Nm : Numerics} {is is' : List AdminInstr}
    (h : Step_pure Nm is is') : ∃ e, (e, is') ∈ pureSuccessors Nm is := by
  cases h with
  | unreachable =>
      exact exists_mem_pureSuccessors_ofInstr (vs := []) rfl (exists_mem_single.mpr rfl)
  | nop =>
      exact exists_mem_pureSuccessors_ofInstr (vs := []) rfl (exists_mem_single.mpr rfl)
  | @drop v =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [v]) rfl
        (exists_mem_single.mpr rfl)
  | @selectTrue v₁ v₂ c ts hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [v₁, v₂, Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, argSelect_val, if_neg hc]
      exact exists_mem_single.mpr rfl
  | @selectFalse v₁ v₂ c ts hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [v₁, v₂, Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, argSelect_val, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @ifTrue c bt is₁ is₂ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_neg hc]
      exact exists_mem_single.mpr rfl
  | @ifFalse c bt is₁ is₂ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @labelVals n cont vs =>
      rw [pureSuccessors_label, pureOfLabel_vals]
      exact exists_mem_single.mpr rfl
  | @brLabelZero n cont vs' vs l is hlen hl =>
      rw [pureSuccessors_label,
        show vals vs' ++ vals vs ++ [AdminInstr.plain (.br l)] ++ is
           = vals (vs' ++ vs) ++ (AdminInstr.plain (.br l) :: is) from by simp,
        pureOfLabel_br]
      have hn : n ≤ (vs' ++ vs).length := by simp; omega
      have hd : (vs' ++ vs).drop ((vs' ++ vs).length - n) = vs := by
        have he : (vs' ++ vs).length - n = vs'.length := by simp; omega
        rw [he]; simp
      rw [if_pos hl, if_pos hn, hd]
      exact exists_mem_single.mpr rfl
  | @brLabelSucc n cont vs l l' is hl =>
      rw [pureSuccessors_label,
        show vals vs ++ [AdminInstr.plain (.br l)] ++ is
           = vals vs ++ (AdminInstr.plain (.br l) :: is) from by simp,
        pureOfLabel_br, if_neg (show ¬ l.val = 0 by omega)]
      have hl' : l' =
          (⟨l.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.property⟩ : LabelIdx) :=
        Subtype.ext (by show l'.val = l.val - 1; omega)
      rw [hl']
      exact exists_mem_single.mpr rfl
  | @brHandler n cs vs l is =>
      rw [pureSuccessors_handler,
        show vals vs ++ [AdminInstr.plain (.br l)] ++ is
           = vals vs ++ (AdminInstr.plain (.br l) :: is) from by simp,
        pureOfHandler_br]
      exact exists_mem_single.mpr rfl
  | @brIfTrue c l hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_neg hc]
      exact exists_mem_single.mpr rfl
  | @brIfFalse c l hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, c⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @brTableLt i ls l' l hl =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, i⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, hl]
      exact exists_mem_single.mpr rfl
  | @brTableGe i ls l' hl =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, i⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num,
        List.getElem?_eq_none_iff.mpr hl]
      exact exists_mem_single.mpr rfl
  | @brOnNullNull ht l =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl ?_
      simp only [pureOfInstr, arg1_single, isNullVal_null, if_pos]
      exact exists_mem_single.mpr rfl
  | @brOnNullAddr v l hv =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [v]) rfl ?_
      have hn : isNullVal v = false := by
        cases hb : isNullVal v with
        | false => rfl
        | true => obtain ⟨ht, rfl⟩ := isNullVal_eq_true hb; exact absurd rfl (hv ht)
      simp only [pureOfInstr, arg1_single, hn, if_neg (Bool.false_ne_true)]
      exact exists_mem_single.mpr rfl
  | @brOnNonNullNull ht l =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl ?_
      simp only [pureOfInstr, arg1_single, isNullVal_null, if_pos]
      exact exists_mem_single.mpr rfl
  | @brOnNonNullAddr v l hv =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [v]) rfl ?_
      have hn : isNullVal v = false := by
        cases hb : isNullVal v with
        | false => rfl
        | true => obtain ⟨ht, rfl⟩ := isNullVal_eq_true hb; exact absurd rfl (hv ht)
      simp only [pureOfInstr, arg1_single, hn, if_neg (Bool.false_ne_true)]
      exact exists_mem_single.mpr rfl
  | @callIndirect x yy =>
      exact exists_mem_pureSuccessors_ofInstr (vs := []) rfl
        (exists_mem_single.mpr rfl)
  | @returnCallIndirect x yy =>
      exact exists_mem_pureSuccessors_ofInstr (vs := []) rfl
        (exists_mem_single.mpr rfl)
  | @frameVals n f vs hlen =>
      rw [pureSuccessors_frame, pureOfFrame_vals, if_pos hlen]
      exact exists_mem_single.mpr rfl
  | @returnFrame n f vs' vs is hlen =>
      rw [pureSuccessors_frame,
        show vals vs' ++ vals vs ++ [AdminInstr.plain .ret] ++ is
           = vals (vs' ++ vs) ++ (AdminInstr.plain .ret :: is) from by simp,
        pureOfFrame_ret]
      have hn : n ≤ (vs' ++ vs).length := by simp; omega
      have hd : (vs' ++ vs).drop ((vs' ++ vs).length - n) = vs := by
        have he : (vs' ++ vs).length - n = vs'.length := by simp; omega
        rw [he]; simp
      rw [if_pos hn, hd]
      exact exists_mem_single.mpr rfl
  | @returnLabel n cont vs is =>
      rw [pureSuccessors_label,
        show vals vs ++ [AdminInstr.plain .ret] ++ is
           = vals vs ++ (AdminInstr.plain .ret :: is) from by simp,
        pureOfLabel_ret]
      exact exists_mem_single.mpr rfl
  | @returnHandler n cs vs is =>
      rw [pureSuccessors_handler,
        show vals vs ++ [AdminInstr.plain .ret] ++ is
           = vals vs ++ (AdminInstr.plain .ret :: is) from by simp,
        pureOfHandler_ret]
      exact exists_mem_single.mpr rfl
  | @handlerVals n cs vs =>
      rw [pureSuccessors_handler, pureOfHandler_vals]
      exact exists_mem_single.mpr rfl
  | @trapInstrs vs is hc =>
      rw [show vals vs ++ [AdminInstr.trap] ++ is = vals vs ++ AdminInstr.trap :: is
            from by simp, pureSuccessors_trap]
      rcases hc with hv | hi
      · cases vs with
        | nil => exact absurd rfl hv
        | cons v vs' => exact exists_mem_single.mpr rfl
      · cases is with
        | nil => exact absurd rfl hi
        | cons a t =>
            cases vs with
            | nil => exact exists_mem_single.mpr rfl
            | cons v vs' => exact exists_mem_single.mpr rfl
  | @trapLabel n cont =>
      rw [pureSuccessors_label, pureOfLabel_trap]
      exact exists_mem_single.mpr rfl
  | @trapFrame n f =>
      rw [pureSuccessors_frame, pureOfFrame_trap]
      exact exists_mem_single.mpr rfl
  | @localTee v x =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [v]) rfl
        (exists_mem_single.mpr rfl)
  | @refI31 i j hj =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨.i32, i⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, hj]
      exact exists_mem_single.mpr rfl
  | @refIsNullTrue ht c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl ?_
      rw [u32_of_val_one hc]
      exact exists_mem_single.mpr rfl
  | @refIsNullFalse r c hr hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref r]) rfl ?_
      have hn : isNullRef r = false := by
        cases hb : isNullRef r with
        | false => rfl
        | true => obtain ⟨ht, rfl⟩ := isNullRef_eq_true hb; exact absurd rfl (hr ht)
      rw [u32_of_val_zero hc]
      simp only [pureOfInstr, arg1ref_ref, hn, if_neg (Bool.false_ne_true)]
      exact exists_mem_single.mpr rfl
  | @refAsNonNullNull ht =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl
        (exists_mem_single.mpr rfl)
  | @refAsNonNullAddr r hr =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref r]) rfl ?_
      have hn : isNullRef r = false := by
        cases hb : isNullRef r with
        | false => rfl
        | true => obtain ⟨ht, rfl⟩ := isNullRef_eq_true hb; exact absurd rfl (hr ht)
      simp only [pureOfInstr, arg1ref_ref, hn, if_neg (Bool.false_ne_true)]
      exact exists_mem_single.mpr rfl
  | @refEqNull ht₁ ht₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.ref (.null ht₁), Val.ref (.null ht₂)]) rfl ?_
      rw [u32_of_val_one hc]
      exact exists_mem_single.mpr rfl
  | @refEqTrue r₁ r₂ c hn hr hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref r₁, Val.ref r₂]) rfl ?_
      have hb : (isNullRef r₁ && isNullRef r₂) = false := by
        cases h₁ : isNullRef r₁ with
        | false => simp
        | true =>
            cases h₂ : isNullRef r₂ with
            | false => simp
            | true =>
                obtain ⟨t₁, e₁⟩ := isNullRef_eq_true h₁
                obtain ⟨t₂, e₂⟩ := isNullRef_eq_true h₂
                exact absurd ⟨e₁, e₂⟩ (hn t₁ t₂)
      rw [u32_of_val_one hc]
      simp only [pureOfInstr, arg2ref_ref, hb, if_neg (Bool.false_ne_true), if_pos hr]
      exact exists_mem_single.mpr rfl
  | @refEqFalse r₁ r₂ c hn hr hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref r₁, Val.ref r₂]) rfl ?_
      have hb : (isNullRef r₁ && isNullRef r₂) = false := by
        cases h₁ : isNullRef r₁ with
        | false => simp
        | true =>
            cases h₂ : isNullRef r₂ with
            | false => simp
            | true =>
                obtain ⟨t₁, e₁⟩ := isNullRef_eq_true h₁
                obtain ⟨t₂, e₂⟩ := isNullRef_eq_true h₂
                exact absurd ⟨e₁, e₂⟩ (hn t₁ t₂)
      rw [u32_of_val_zero hc]
      simp only [pureOfInstr, arg2ref_ref, hb, if_neg (Bool.false_ne_true), if_neg hr]
      exact exists_mem_single.mpr rfl
  | @i31GetNull ht sx =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl
        (exists_mem_single.mpr rfl)
  | @i31GetNum i sx c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.addr (.i31 i))]) rfl ?_
      simp only [pureOfInstr, arg1ref_ref, hc]
      exact exists_mem_single.mpr rfl
  | @arrayNew v n x =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [v, Val.num ⟨.i32, n⟩]) rfl
        (exists_mem_single.mpr rfl)
  | @externConvertAnyNull ht =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl
        (exists_mem_single.mpr rfl)
  | @externConvertAnyAddr r =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.addr r)]) rfl
        (exists_mem_single.mpr rfl)
  | @anyConvertExternNull ht =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.null ht)]) rfl
        (exists_mem_single.mpr rfl)
  | @anyConvertExternAddr r =>
      exact exists_mem_pureSuccessors_ofInstr (vs := [Val.ref (.addr (.extern r))]) rfl
        (exists_mem_single.mpr rfl)
  | @unopVal nt op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨nt, c₁⟩]) rfl ?_
      have hne : ¬ (Nm.unop_ nt op c₁ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg1num_num, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @unopTrap nt op c₁ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨nt, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @binopVal nt op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.num ⟨nt, c₁⟩, Val.num ⟨nt, c₂⟩]) rfl ?_
      have hne : ¬ (Nm.binop_ nt op c₁ c₂ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg2num_num, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @binopTrap nt op c₁ c₂ hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.num ⟨nt, c₁⟩, Val.num ⟨nt, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2num_num, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @testop nt op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨nt, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, hc]
      exact exists_mem_single.mpr rfl
  | @relop nt op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.num ⟨nt, c₁⟩, Val.num ⟨nt, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2num_num, hc]
      exact exists_mem_single.mpr rfl
  | @cvtopVal nt₁ nt₂ op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨nt₁, c₁⟩]) rfl ?_
      have hne : ¬ (Nm.cvtop__ nt₁ nt₂ op c₁ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg1num_num, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @cvtopTrap nt₁ nt₂ op c₁ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.num ⟨nt₁, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @vvunop op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vvbinop op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vvternop op c₁ c₂ c₃ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩]) rfl ?_
      simp only [pureOfInstr, arg3vec_vec]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vvtestop c₁ c z hz hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      rw [in128_of_val_zero hz] at hc
      simp only [pureOfInstr, arg1vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vunopVal sh op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      have hne : ¬ (Nm.vunop_ sh op c₁ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg1vec_vec, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vunopTrap sh op c₁ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @vbinopVal sh op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      have hne : ¬ (Nm.vbinop_ sh op c₁ c₂ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg2vec_vec, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vbinopTrap sh op c₁ c₂ hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @vternopVal sh op c₁ c₂ c₃ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩]) rfl ?_
      have hne : ¬ (Nm.vternop_ sh op c₁ c₂ c₃ = []) := by
        intro he; rw [he] at hc; simp at hc
      simp only [pureOfInstr, arg3vec_vec, if_neg hne]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩
  | @vternopTrap sh op c₁ c₂ c₃ hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩]) rfl ?_
      simp only [pureOfInstr, arg3vec_vec, if_pos hc]
      exact exists_mem_single.mpr rfl
  | @vtestop sh op c₁ i hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vrelop sh op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vshiftop sh op c₁ c i hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.num ⟨.i32, i⟩]) rfl ?_
      simp only [pureOfInstr, argVecNum_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vbitmask sh c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vswizzlop sh op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vshuffle sh js c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vsplat lt m c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.num ⟨lt.unpack, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1num_num, hc]
      exact exists_mem_single.mpr rfl
  | @vextractLaneNum nt m i c₁ c₂ hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vextractLanePack pt m sx i c₁ l c₂ hl hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, hl, hc]
      exact exists_mem_single.mpr rfl
  | @vreplaceLane lt m i c₁ c c₂ ls hls hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.num ⟨lt.unpack, c₂⟩]) rfl ?_
      simp only [pureOfInstr, argVecNum_vec, hls, hc]
      exact exists_mem_single.mpr rfl
  | @vextunop sh₁ sh₂ op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vextbinop sh₁ sh₂ op c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vextternop sh₁ sh₂ op c₁ c₂ c₃ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩, Val.vec ⟨.v128, c₃⟩]) rfl ?_
      simp only [pureOfInstr, arg3vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vnarrow sh₁ sh₂ sx c₁ c₂ c hc =>
      refine exists_mem_pureSuccessors_ofInstr
        (vs := [Val.vec ⟨.v128, c₁⟩, Val.vec ⟨.v128, c₂⟩]) rfl ?_
      simp only [pureOfInstr, arg2vec_vec, hc]
      exact exists_mem_single.mpr rfl
  | @vcvtop sh₁ sh₂ op c₁ c hc =>
      refine exists_mem_pureSuccessors_ofInstr (vs := [Val.vec ⟨.v128, c₁⟩]) rfl ?_
      simp only [pureOfInstr, arg1vec_vec]
      exact exists_mem_choices.mpr ⟨c, hc, rfl⟩

/-! ## The enumerator is exactly the relation -/

theorem mem_pureSuccessors_step_pure {Nm : Numerics} {is : List AdminInstr}
    {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureSuccessors Nm is) : Step_pure Nm is is' := by
  have hb := splitVals_append is
  have hstep := mem_pureOfSplit_step_pure (Nm := Nm) (vs := (splitVals is).1)
    (rest := (splitVals is).2) h
  rwa [hb] at hstep

/-- **SPEC section 7.1, the anti-cheat property, for `relation Step_pure`.**
The executable enumeration of `pureSuccessors` is exactly the pinned relation
`Step_pure`: no permitted reduction is missing from the list, and the list
invents none.

The pinned source labels no `Step_pure` rule, so the relation it is compared
against is the unlabelled one the source states; the labels `pureSuccessors`
attaches are proved to separate the entries by `pureSuccessors_nodup`. -/
theorem mem_pureSuccessors_iff_step_pure (Nm : Numerics) (is is' : List AdminInstr) :
    (∃ e, (e, is') ∈ pureSuccessors Nm is) ↔ Step_pure Nm is is' :=
  ⟨fun h => h.elim (fun _ hm => mem_pureSuccessors_step_pure hm),
    step_pure_mem_pureSuccessors⟩

/-! ## The enumeration is duplicate free -/

theorem pureOfInstr_nodup (Nm : Numerics) (vs : List Val) (i : Instr) :
    (pureOfInstr Nm vs i).Nodup := by
  unfold pureOfInstr
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_nodup _ _
    | exact choices_nodup _ _ _

theorem pureOfLabel_nodup (n : Nat) (cont body : List AdminInstr) :
    (pureOfLabel n cont body).Nodup := by
  unfold pureOfLabel
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_nodup _ _

theorem pureOfFrame_nodup (n : Nat) (body : List AdminInstr) :
    (pureOfFrame n body).Nodup := by
  unfold pureOfFrame
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_nodup _ _

theorem pureOfHandler_nodup (body : List AdminInstr) :
    (pureOfHandler body).Nodup := by
  unfold pureOfHandler
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_nodup _ _

theorem pureOfSplit_nodup (Nm : Numerics) (vs : List Val) (rest : List AdminInstr) :
    (pureOfSplit Nm vs rest).Nodup := by
  unfold pureOfSplit
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_nodup _ _
    | exact pureOfInstr_nodup _ _ _
    | exact pureOfLabel_nodup _ _ _
    | exact pureOfFrame_nodup _ _
    | exact pureOfHandler_nodup _

/-- **SPEC section 7.1.**  The successor enumeration is duplicate free. -/
theorem pureSuccessors_nodup (Nm : Numerics) (is : List AdminInstr) :
    (pureSuccessors Nm is).Nodup :=
  pureOfSplit_nodup Nm _ _

/-- **The pure successors are `Step` successors.**  `rule Step/pure` embeds
`Step_pure` in the top-level relation without touching the state, so every entry
this file enumerates is a permitted successor of the full machine at every
state.  The converse is what is still missing: `Step` has 31 further rules and
closes the relation under four context rules. -/
theorem mem_pureSuccessors_step [authority : ExecutionAuthority]
    {Nm : Numerics} {z : State} {is : List AdminInstr}
    {e : PureEvent} {is' : List AdminInstr}
    (h : (e, is') ∈ pureSuccessors Nm is) : Step Nm z is z is' :=
  .pure (mem_pureSuccessors_step_pure h)

/-! ## Non-vacuity

The two theorems above would be worthless if `Step_pure` held of everything or
of nothing, or if the enumerator collapsed the source's set-valued results into
one entry.  All three facts below are kernel-checked closed terms. -/

/-- The relation is not everything: an empty sequence has no reduction. -/
theorem not_step_pure_nil {Nm : Numerics} {is' : List AdminInstr} :
    ¬ Step_pure Nm [] is' := by
  intro h
  obtain ⟨e, he⟩ := step_pure_mem_pureSuccessors h
  simp [pureSuccessors, pureOfSplit] at he

/-- The relation is not empty, and the enumerator finds the reduction. -/
theorem pureSuccessors_nop (Nm : Numerics) :
    pureSuccessors Nm [.plain .nop] = single .nop [] := rfl

/-- **The set-valued results are not collapsed.**  Where the pinned numerics
permit two results, the enumerator lists two entries, and they carry distinct
labels even when the two results happen to be equal -- which is exactly why the
event records the index and not only the value drawn. -/
theorem unop_two_choices {Nm : Numerics} {nt : NumType} {op : Unop}
    {c₁ r₁ r₂ : Num_ nt} (h : Nm.unop_ nt op c₁ = [r₁, r₂]) :
    pureSuccessors Nm (vals [Val.num ⟨nt, c₁⟩] ++ [.plain (.unop nt op)]) =
      [(⟨.unopVal, 0⟩, [.plain (.const nt r₁)]),
       (⟨.unopVal, 1⟩, [.plain (.const nt r₂)])] := by
  rw [pureSuccessors_ofInstr _ _ rfl]
  simp only [pureOfInstr, arg1num_num, h]
  rfl

end WasmGemmGnaf.Wasm.Core.Exec
