/-
  Wasm/Core/ValidateStack.lean --- the operand-stack machine of the validation
  ALGORITHM of `vendor/wasm-spec/document/core/appendix/algorithm.rst`.

  NORMATIVE SOURCE.  The appendix's `val_stack`, `push_val`, `pop_val`,
  `push_vals`, `pop_vals`, `unreachable()` and the `Bot` value type, transcribed
  as a pure state rather than as global variables.  The appendix is a sketch of
  a SOUND AND COMPLETE algorithm for the declarative judgment of
  `2.3-validation.instructions.spectec`; this file is its data structure, and
  `Core/ValidateInstr.lean` is the opcode dispatch plus the two directions of
  the equivalence.

  TWO DEPARTURES FROM THE APPENDIX'S PRESENTATION, BOTH FORCED AND NEITHER
  SEMANTIC:

  * The appendix keeps a CONTROL stack whose frames carry `start_types`,
    `end_types`, `val_height` and `unreachable`.  The declarative judgment keeps
    the same information in `C.LABELS` (pushed by `Instr_ok/block`, `/loop` and
    `/if`, with `/loop` pushing its ARGUMENT types --- exactly the appendix's
    `label_types`).  So the control stack here is `Context.pushLabel` plus, per
    frame, a FRESH `St`: `val_height` is the bottom of that state's `vals`, and
    the frame's `unreachable` flag is its `poly`.  Nothing is lost; the two
    representations carry the same three components.

  * The appendix's `vals` is indexed from the top (`stack[i]` is the last
    pushed).  `St.vals` is therefore stored TOP FIRST, while every `resulttype`
    in the pinned rules is written bottom first.  `pushs` and `pops` mediate:
    `pops st (t_1 ... t_n)` pops `t_n` first, which is what `pop_vals` does.

  `St.le` is the ordering that makes the algorithm's single pass work: `st_1`
  is at least as general as `st_2` when every stack `st_2` accepts, `st_1`
  accepts.  A polymorphic frame with fewer tracked operands is more general
  than a concrete one, which is exactly the `Bot`-generating case of `pop_val`.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeSound

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core
namespace Validate

/-! ## The value types the algorithm tracks

The appendix's `val_type` is Core's `valtype` plus `Bot`, and `Core/Types.lean`
already has `BOT` as a case of `valtype` (`Valtype_ok/bot` is a rule of the
pinned source).  So no new type is needed --- but two predicates are, because
the equivalence proved in `Core/ValidateInstr.lean` is closed over the
fragment of `valtype` this checker decides: `numtype`s and `vectype`s, plus
`BOT` where the algorithm generates it. -/

/-- A `numtype` or a `vectype`: the value types of the decided fragment. -/
def ValType.nv : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref _ => false
  | .bot => false

/-- A `numtype`, a `vectype`, or `BOT`: what may occur on the operand stack of
a run of this checker. -/
def ValType.nvb : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref _ => false
  | .bot => true

theorem ValType.nvb_of_nv {t : ValType} (h : ValType.nv t = true) :
    ValType.nvb t = true := by
  cases t <;> simp_all [ValType.nv, ValType.nvb]

/-- Every `numtype`/`vectype`/`BOT` is a well-formed value type in EVERY
context: `Valtype_ok/num`, `/vec` and `/bot` have no premises. -/
theorem valtype_ok_of_nvb {C : Context} {t : ValType} (h : ValType.nvb t = true) :
    Valtype_ok C t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref _ => simp [ValType.nvb] at h
  | bot => exact .bot

/-- `Resulttype_ok` for a sequence of such types. -/
theorem resulttype_ok_of_nvb {C : Context} {ts : List ValType}
    (h : ts.all ValType.nvb = true) : Resulttype_ok C ts :=
  .mk (fun t ht => valtype_ok_of_nvb (List.all_eq_true.mp h t ht))

/-- Corrected-hierarchy form of `valtype_ok_of_nvb`. -/
theorem valtype_okA_of_nvb {C : Context} {t : ValType} (h : ValType.nvb t = true) :
    Valtype_okA C t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref _ => simp [ValType.nvb] at h
  | bot => exact .bot

/-- Corrected-hierarchy form of `resulttype_ok_of_nvb`. -/
theorem resulttype_okA_of_nvb {C : Context} {ts : List ValType}
    (h : ts.all ValType.nvb = true) : Resulttype_okA C ts :=
  .mk (fun t ht => valtype_okA_of_nvb (List.all_eq_true.mp h t ht))

/-! ## `matches_val`

The appendix assumes a subtyping check on value types.  On the decided fragment
`Valtype_sub` is exactly "`BOT`, or the same type": the `/num` and `/vec` rules
are reflexivity (`Numtype_sub` and `Vectype_sub` relate a type only to itself),
`/bot` relates `BOT` to everything, and `/ref` cannot conclude at a `numtype`
or `vectype`.  `subOf` is that check, and it is sound in EVERY context and at
EVERY value type --- only completeness is fragment-scoped. -/

/-- `matches_val(t_1, t_2)` on the decided fragment. -/
def subOf (t₁ t₂ : ValType) : Bool := (t₁ == .bot) || (t₁ == t₂)

@[simp] theorem subOf_bot (t : ValType) : subOf .bot t = true := by simp [subOf]

@[simp] theorem subOf_refl (t : ValType) : subOf t t = true := by simp [subOf]

theorem subOf_trans {a b c : ValType} (h₁ : subOf a b = true) (h₂ : subOf b c = true) :
    subOf a c = true := by
  simp only [subOf, Bool.or_eq_true, beq_iff_eq] at h₁ h₂ ⊢
  rcases h₁ with h₁ | h₁
  · exact Or.inl h₁
  · subst h₁; exact h₂

/-- Reflexivity of `Valtype_sub`, which the pinned rules give at every case:
`/num` and `/vec` through the reflexive `Numtype_sub` / `Vectype_sub`, `/ref`
through `Reftype_sub` and `Heaptype_sub/refl`, and `/bot` outright. -/
theorem valtype_sub_refl {C : Context} (t : ValType) : Valtype_sub C t t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref rt =>
      refine .ref ?_
      cases rt with
      | ref nul ht =>
          cases nul with
          | none => exact .nonnull .refl
          | some n => cases n; exact .null .refl
  | bot => exact .bot

/-- Reflexivity in the corrected value-type relation. -/
theorem valtype_subA_refl {C : Context} (t : ValType) : Valtype_subA C t t := by
  cases t with
  | num _ => exact .num .mk
  | vec _ => exact .vec .mk
  | ref rt =>
      refine .ref ?_
      cases rt with
      | ref nul ht =>
          cases nul with
          | none => exact .nonnull .refl
          | some n => cases n; exact .null .refl
  | bot => exact .bot

/-- `subOf` is SOUND at every value type and in every context. -/
theorem valtype_sub_of_subOf {C : Context} {t₁ t₂ : ValType} (h : subOf t₁ t₂ = true) :
    Valtype_sub C t₁ t₂ := by
  simp only [subOf, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; exact .bot
  · subst h; exact valtype_sub_refl t₁

/-- `subOf` is sound for the corrected relation as well. -/
theorem valtype_subA_of_subOf {C : Context} {t₁ t₂ : ValType}
    (h : subOf t₁ t₂ = true) : Valtype_subA C t₁ t₂ := by
  simp only [subOf, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; exact .bot
  · subst h; exact valtype_subA_refl t₁

/-- `subOf` is COMPLETE whenever the SUPERtype is in the decided fragment: a
`numtype`, a `vectype` or `BOT` can be a supertype only of itself or of `BOT`. -/
theorem subOf_of_valtype_sub {C : Context} {t₁ t₂ : ValType}
    (h : Valtype_sub C t₁ t₂) (h₂ : ValType.nvb t₂ = true) : subOf t₁ t₂ = true := by
  cases h with
  | num hn => cases hn; simp
  | vec hv => cases hv; simp
  | ref _ => simp [ValType.nvb] at h₂
  | bot => simp

/-- Fragment completeness of `subOf` for the corrected relation. -/
theorem subOf_of_valtype_subA {C : Context} {t₁ t₂ : ValType}
    (h : Valtype_subA C t₁ t₂) (h₂ : ValType.nvb t₂ = true) : subOf t₁ t₂ = true := by
  cases h with
  | num hn => cases hn; simp
  | vec hv => cases hv; simp
  | ref _ => simp [ValType.nvb] at h₂
  | bot => simp

/-! ## `matches_val` lifted to result types -/

/-- Pointwise `matches_val` over two `resulttype`s of equal length. -/
def subs : List ValType → List ValType → Bool
  | [], [] => true
  | t₁ :: ts₁, t₂ :: ts₂ => subOf t₁ t₂ && subs ts₁ ts₂
  | _, _ => false

/-- Full corrected `matches_val`, including reference subtyping. -/
def subOfA (C : Context) (t₁ t₂ : ValType) : Bool :=
  decValtypeSubN C C.subtypeFuel t₁ t₂

/-- Full corrected pointwise result-type matching. -/
def subsA (C : Context) (ts₁ ts₂ : List ValType) : Bool :=
  decResulttypeSubN C C.subtypeFuel ts₁ ts₂

theorem valtype_subA_of_subOfA {C : Context} {t₁ t₂ : ValType}
    (h : subOfA C t₁ t₂ = true) : Valtype_subA C t₁ t₂ :=
  decValtypeSubN_sound h

theorem resulttype_subA_of_subsA {C : Context} {ts₁ ts₂ : List ValType}
    (h : subsA C ts₁ ts₂ = true) : Resulttype_subA C ts₁ ts₂ :=
  decResulttypeSubN_sound h

@[simp] theorem subs_nil : subs [] [] = true := rfl

@[simp] theorem subs_cons (a b : ValType) (as bs : List ValType) :
    subs (a :: as) (b :: bs) = (subOf a b && subs as bs) := rfl

@[simp] theorem subs_cons_nil (a : ValType) (as : List ValType) :
    subs (a :: as) [] = false := rfl

@[simp] theorem subs_nil_cons (b : ValType) (bs : List ValType) :
    subs [] (b :: bs) = false := rfl

theorem subs_refl : ∀ ts : List ValType, subs ts ts = true
  | [] => rfl
  | t :: ts => by simp [subs_refl ts]

theorem subs_length : ∀ {as bs : List ValType}, subs as bs = true → as.length = bs.length
  | [], [] => fun _ => rfl
  | _ :: _, [] => fun h => by simp at h
  | [], _ :: _ => fun h => by simp at h
  | _ :: as, _ :: bs => fun h => by
      simp only [subs_cons, Bool.and_eq_true] at h
      simp [subs_length h.2]

theorem subs_trans : ∀ {as bs cs : List ValType},
    subs as bs = true → subs bs cs = true → subs as cs = true
  | [], [], [] => fun _ _ => rfl
  | a :: as, b :: bs, c :: cs => fun h₁ h₂ => by
      simp only [subs_cons, Bool.and_eq_true] at h₁ h₂ ⊢
      exact ⟨subOf_trans h₁.1 h₂.1, subs_trans h₁.2 h₂.2⟩
  | [], [], _ :: _ => fun _ h₂ => by simp at h₂
  | [], _ :: _, _ => fun h₁ _ => by simp at h₁
  | _ :: _, [], _ => fun h₁ _ => by simp at h₁
  | _ :: _, _ :: _, [] => fun _ h₂ => by simp at h₂

theorem subs_append : ∀ {as bs cs ds : List ValType},
    subs as bs = true → subs cs ds = true → subs (as ++ cs) (bs ++ ds) = true
  | [], [], _, _ => fun _ h => by simpa using h
  | a :: as, b :: bs, cs, ds => fun h₁ h₂ => by
      simp only [subs_cons, Bool.and_eq_true] at h₁
      simp only [List.cons_append, subs_cons, Bool.and_eq_true]
      exact ⟨h₁.1, subs_append h₁.2 h₂⟩
  | [], _ :: _, _, _ => fun h₁ _ => by simp at h₁
  | _ :: _, [], _, _ => fun h₁ _ => by simp at h₁

/-- A match against a concatenation splits: this is what lets a polymorphic
frame be compared with a longer concrete one. -/
theorem subs_split : ∀ {as bs cs : List ValType}, subs (as ++ bs) cs = true →
    ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ subs as cs₁ = true ∧ subs bs cs₂ = true
  | [], bs, cs => fun h => ⟨[], cs, rfl, rfl, h⟩
  | a :: as, bs, cs => fun h => by
      cases cs with
      | nil => simp at h
      | cons c cs =>
          simp only [List.cons_append, subs_cons, Bool.and_eq_true] at h
          obtain ⟨cs₁, cs₂, he, h₁, h₂⟩ := subs_split h.2
          exact ⟨c :: cs₁, cs₂, by rw [he]; rfl, by simp [h.1, h₁], h₂⟩

/-- The pointwise reading of `subs`, in the indexed form `SeqAll₂` uses. -/
theorem subs_getElem : ∀ {as bs : List ValType} {i : Nat} {a b : ValType},
    subs as bs = true → as[i]? = some a → bs[i]? = some b → subOf a b = true
  | [], _, _, _, _ => fun _ ha _ => by simp at ha
  | _ :: _, [], _, _, _ => fun h _ _ => by simp at h
  | a' :: as, b' :: bs, 0, a, b => fun h ha hb => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha; subst hb
      simp only [subs_cons, Bool.and_eq_true] at h
      exact h.1
  | a' :: as, b' :: bs, i + 1, a, b => fun h ha hb => by
      simp only [List.getElem?_cons_succ] at ha hb
      simp only [subs_cons, Bool.and_eq_true] at h
      exact subs_getElem h.2 ha hb

/-- ... and back. -/
theorem subs_of_getElem : ∀ {as bs : List ValType}, as.length = bs.length →
    (∀ (i : Nat) (a b : ValType), as[i]? = some a → bs[i]? = some b → subOf a b = true) →
    subs as bs = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, hlen, hall => by
      simp only [subs_cons, Bool.and_eq_true]
      refine ⟨hall 0 a b (by simp) (by simp), subs_of_getElem (by simpa using hlen) ?_⟩
      intro i x y hx hy
      exact hall (i + 1) x y (by simpa using hx) (by simpa using hy)

/-- `Resulttype_sub` from the pointwise check: `Resulttype_sub` is exactly
`SeqLen₂` plus `SeqAll₂ Valtype_sub`. -/
theorem resulttype_sub_of_subs {C : Context} {as bs : List ValType}
    (h : subs as bs = true) : Resulttype_sub C as bs :=
  .mk (subs_length h) (fun _ _ _ ha hb => valtype_sub_of_subOf (subs_getElem h ha hb))

/-- Corrected-hierarchy form of `resulttype_sub_of_subs`. -/
theorem resulttype_subA_of_subs {C : Context} {as bs : List ValType}
    (h : subs as bs = true) : Resulttype_subA C as bs :=
  .mk (subs_length h) (fun _ _ _ ha hb => valtype_subA_of_subOf (subs_getElem h ha hb))

/-- ... and back, when the supertypes are in the decided fragment. -/
theorem subs_of_resulttype_sub {C : Context} {as bs : List ValType}
    (h : Resulttype_sub C as bs) (hb : bs.all ValType.nvb = true) : subs as bs = true := by
  cases h with
  | mk hlen hall =>
      refine subs_of_getElem hlen (fun i a b ha hbb => ?_)
      refine subOf_of_valtype_sub (hall i a b ha hbb) ?_
      exact List.all_eq_true.mp hb b (List.mem_of_getElem? hbb)

/-- Fragment completeness of `subs` for the corrected relation. -/
theorem subs_of_resulttype_subA {C : Context} {as bs : List ValType}
    (h : Resulttype_subA C as bs) (hb : bs.all ValType.nvb = true) : subs as bs = true := by
  cases h with
  | mk hlen hall =>
      refine subs_of_getElem hlen (fun i a b ha hbb => ?_)
      refine subOf_of_valtype_subA (hall i a b ha hbb) ?_
      exact List.all_eq_true.mp hb b (List.mem_of_getElem? hbb)

/-! ## The operand stack

`St` is one control frame's operand stack: `poly` is the frame's `unreachable`
flag and `vals` is everything the frame has pushed above its `val_height`, TOP
FIRST. -/

/-- One control frame's operand stack. -/
structure St where
  /-- The frame's `unreachable` flag. -/
  poly : Bool
  /-- The operand types above the frame's `val_height`, top first. -/
  vals : List ValType
  deriving DecidableEq, Repr, Inhabited

namespace St

/-- `push_val(type)`. -/
def push (st : St) (t : ValType) : St := ⟨st.poly, t :: st.vals⟩

/-- `push_vals(types)`: the LAST type of the sequence ends up on top. -/
def pushs (st : St) : List ValType → St
  | [] => st
  | t :: ts => (st.push t).pushs ts

/-- `pop_val(expect)`: on an empty polymorphic frame this is `Bot`, which
`matches_val` accepts unconditionally, so the frame is left unchanged. -/
def popE (st : St) (t : ValType) : Option St :=
  match st.vals with
  | a :: rest => if subOf a t then some ⟨st.poly, rest⟩ else none
  | [] => if st.poly then some st else none

/-- `pop_val()` with no expectation: the appendix's untyped `pop_val`, which
returns the popped type as well as the shrunken stack. -/
def pop (st : St) : Option (ValType × St) :=
  match st.vals with
  | a :: rest => some (a, ⟨st.poly, rest⟩)
  | [] => if st.poly then some (.bot, st) else none

/-- `pop_vals(types)`: pops the LAST type of the sequence first. -/
def pops (st : St) : List ValType → Option St
  | [] => some st
  | t :: ts => match st.pops ts with
      | some st' => st'.popE t
      | none => none

/-- Full `pop_val(expect)` using corrected reference subtyping. -/
def popEA (C : Context) (st : St) (t : ValType) : Option St :=
  match st.vals with
  | a :: rest => if subOfA C a t then some ⟨st.poly, rest⟩ else none
  | [] => if st.poly then some st else none

/-- Full `pop_vals`, using `popEA` for every expected type. -/
def popsA (C : Context) (st : St) : List ValType → Option St
  | [] => some st
  | t :: ts => match popsA C st ts with
      | some st' => popEA C st' t
      | none => none

/-- `unreachable()`: purge the frame's operands and set its flag. -/
def unreach (_st : St) : St := ⟨true, []⟩

/-- The frame's operands are exactly a stack of type `ts`: `pop_vals(ts)`
succeeds and leaves the frame at its `val_height`.  This is `pop_ctrl`'s check,
and it is also what it means for a state to be readable AS the `resulttype`
`ts`. -/
def Sat (st : St) (ts : List ValType) : Prop :=
  ∃ st', st.pops ts = some st' ∧ st'.vals = []

/-- `Sat` as a decision. -/
def finish (st : St) (ts : List ValType) : Bool :=
  match st.pops ts with
  | some st' => st'.vals.isEmpty
  | none => false

theorem popE_cons {st : St} {a : ValType} {rest : List ValType} (h : st.vals = a :: rest)
    (t : ValType) : st.popE t = if subOf a t then some ⟨st.poly, rest⟩ else none := by
  unfold popE; rw [h]

theorem popE_nil {st : St} (h : st.vals = []) (t : ValType) :
    st.popE t = if st.poly then some st else none := by
  unfold popE; rw [h]

@[simp] theorem pops_nil (st : St) : st.pops [] = some st := rfl

@[simp] theorem pops_cons (st : St) (t : ValType) (ts : List ValType) :
    st.pops (t :: ts) =
      match st.pops ts with
      | some st' => st'.popE t
      | none => none := rfl

theorem finish_iff_sat {st : St} {ts : List ValType} : st.finish ts = true ↔ st.Sat ts := by
  unfold finish Sat
  cases hp : st.pops ts with
  | none =>
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨st', hp', _⟩; exact absurd hp' (by simp)
  | some st' =>
      constructor
      · intro h
        replace h : st'.vals.isEmpty = true := h
        refine ⟨st', rfl, ?_⟩
        cases hv : st'.vals with
        | nil => rfl
        | cons a as => rw [hv] at h; exact absurd h (by simp)
      · rintro ⟨st'', hp'', hv⟩
        cases hp''
        show st'.vals.isEmpty = true
        rw [hv]; rfl

/-! ### Arithmetic of `push_vals` and `pop_vals` -/

theorem pushs_eq (st : St) : ∀ ts : List ValType, st.pushs ts = ⟨st.poly, ts.reverse ++ st.vals⟩
  | [] => rfl
  | t :: ts => by
      show (st.push t).pushs ts = _
      rw [pushs_eq (st.push t) ts]
      simp [push]

@[simp] theorem pushs_poly (st : St) (ts : List ValType) : (st.pushs ts).poly = st.poly := by
  rw [pushs_eq]

theorem pushs_append (st : St) (ts₁ ts₂ : List ValType) :
    st.pushs (ts₁ ++ ts₂) = (st.pushs ts₁).pushs ts₂ := by
  simp [pushs_eq]

theorem popE_poly {st st' : St} {t : ValType} (h : st.popE t = some st') :
    st'.poly = st.poly := by
  cases hv : st.vals with
  | nil =>
      rw [popE_nil hv] at h
      cases hb : st.poly with
      | false => rw [hb] at h; exact absurd h (by simp)
      | true => rw [hb] at h; simp at h; rw [← h]; exact hb
  | cons a rest =>
      rw [popE_cons hv] at h
      by_cases hs : subOf a t
      · rw [if_pos hs] at h; cases h; rfl
      · rw [if_neg hs] at h; exact absurd h (by simp)

theorem pops_poly {st st' : St} : ∀ {ts : List ValType},
    st.pops ts = some st' → st'.poly = st.poly := by
  intro ts
  induction ts generalizing st' with
  | nil => intro h; cases h; rfl
  | cons t ts ih =>
      intro h
      rw [pops_cons] at h
      cases hp : st.pops ts with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some st'' =>
          rw [hp] at h
          rw [popE_poly h, ih hp]

theorem pops_append (st : St) (ts₁ ts₂ : List ValType) :
    st.pops (ts₁ ++ ts₂) =
      match st.pops ts₂ with
      | some st' => st'.pops ts₁
      | none => none := by
  induction ts₁ generalizing st with
  | nil =>
      show st.pops ts₂ = _
      cases st.pops ts₂ <;> rfl
  | cons t ts₁ ih =>
      show (match st.pops (ts₁ ++ ts₂) with
            | some st' => st'.popE t
            | none => none) = _
      rw [ih]
      cases st.pops ts₂ with
      | none => rfl
      | some st' => rfl

theorem popE_of_subOf {st : St} {t t' : ValType} {st' : St}
    (h : st.popE t = some st') (hsub : subOf t t' = true) : st.popE t' = some st' := by
  cases hv : st.vals with
  | nil => rw [popE_nil hv] at h ⊢; exact h
  | cons a rest =>
      rw [popE_cons hv] at h ⊢
      by_cases hs : subOf a t
      · rw [if_pos hs] at h
        rw [if_pos (subOf_trans hs hsub)]
        exact h
      · rw [if_neg hs] at h; exact absurd h (by simp)

/-- Weakening the EXPECTED types: if `pop_vals` succeeds against `ts` then it
succeeds, with the same remaining frame, against any `ts'` that `ts` matches. -/
theorem pops_weaken {st st' : St} : ∀ {ts ts' : List ValType},
    st.pops ts = some st' → subs ts ts' = true → st.pops ts' = some st' := by
  intro ts
  induction ts generalizing st' with
  | nil =>
      intro ts' h hs
      cases ts' with
      | nil => exact h
      | cons _ _ => simp at hs
  | cons t ts ih =>
      intro ts' h hs
      cases ts' with
      | nil => simp at hs
      | cons t' ts' =>
          simp only [subs_cons, Bool.and_eq_true] at hs
          rw [pops_cons] at h ⊢
          cases hp : st.pops ts with
          | none => rw [hp] at h; exact absurd h (by simp)
          | some st'' =>
              rw [hp] at h
              rw [ih hp hs.2]
              exact popE_of_subOf h hs.1

theorem pushs_pops (st : St) : ∀ ts : List ValType, (st.pushs ts).pops ts = some st := by
  intro ts
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih =>
      show (match ((st.push t).pushs ts).pops ts with
            | some st' => st'.popE t
            | none => none) = some st
      rw [ih (st.push t)]
      show (st.push t).popE t = some st
      have hv : (st.push t).vals = t :: st.vals := rfl
      rw [popE_cons hv, if_pos (subOf_refl t)]
      rfl

theorem pushs_pops_weaken (st : St) {ts ts' : List ValType} (h : subs ts ts' = true) :
    (st.pushs ts).pops ts' = some st :=
  pops_weaken (pushs_pops st ts) h


/-! ### Generality of frames

`le st₁ st₂` says `st₁` is at least as general as `st₂`.  The polymorphic case
is the appendix's note that a polymorphic stack "cannot underflow, but instead
generates `Bot` types as needed": a polymorphic frame tracking FEWER operands
accepts everything a longer or concrete frame accepts. -/

/-- `st₁` is at least as general as `st₂`. -/
def le (st₁ st₂ : St) : Prop :=
  (st₁.poly = true ∧ ∃ hd tl, st₂.vals = hd ++ tl ∧ subs st₁.vals hd = true) ∨
  (st₁.poly = false ∧ st₂.poly = false ∧ subs st₁.vals st₂.vals = true)

theorem le_refl (st : St) : le st st := by
  cases hb : st.poly with
  | true => exact Or.inl ⟨hb, st.vals, [], by simp, subs_refl _⟩
  | false => exact Or.inr ⟨hb, hb, subs_refl _⟩

/-- The common shape of both cases of `le`: the more general frame's operands
match a top segment of the less general one's. -/
theorem le_split {st₁ st₂ : St} (h : le st₁ st₂) :
    ∃ hd tl, st₂.vals = hd ++ tl ∧ subs st₁.vals hd = true := by
  rcases h with ⟨_, hd, tl, he, hs⟩ | ⟨_, _, hs⟩
  · exact ⟨hd, tl, he, hs⟩
  · exact ⟨st₂.vals, [], by simp, hs⟩

theorem le_trans {st₁ st₂ st₃ : St} (h₁ : le st₁ st₂) (h₂ : le st₂ st₃) : le st₁ st₃ := by
  rcases h₁ with ⟨hp₁, hd₁, tl₁, he₁, hs₁⟩ | ⟨hp₁, hp₂, hs₁⟩
  · obtain ⟨hd₂, tl₂, he₂, hs₂⟩ := le_split h₂
    rw [he₁] at hs₂
    obtain ⟨c₁, c₂, hc, hc₁, _⟩ := subs_split hs₂
    refine Or.inl ⟨hp₁, c₁, c₂ ++ tl₂, ?_, subs_trans hs₁ hc₁⟩
    rw [he₂, hc, List.append_assoc]
  · rcases h₂ with ⟨hp₂', _, _, _, _⟩ | ⟨_, hp₃, hs₂⟩
    · rw [hp₂] at hp₂'; exact absurd hp₂' (by simp)
    · exact Or.inr ⟨hp₁, hp₃, subs_trans hs₁ hs₂⟩

/-- `pop_val` from a more general frame succeeds wherever it succeeds from a
less general one, and the results stay ordered.  This is the step that makes
the single pass of the appendix algorithm principal. -/
theorem popE_mono {st₁ st₂ st₂' : St} {t : ValType}
    (hle : le st₁ st₂) (h : st₂.popE t = some st₂') :
    ∃ st₁', st₁.popE t = some st₁' ∧ le st₁' st₂' := by
  rcases hle with ⟨hp₁, hd, tl, he, hs⟩ | ⟨hp₁, hp₂, hs⟩
  · -- `st₁` is polymorphic; its operands match a top segment `hd` of `st₂`'s
    cases hv₁ : st₁.vals with
    | nil =>
        refine ⟨st₁, ?_, ?_⟩
        · rw [popE_nil hv₁, hp₁]; rfl
        · exact Or.inl ⟨hp₁, [], st₂'.vals, by simp, by rw [hv₁]; rfl⟩
    | cons a rest =>
        cases hd with
        | nil => rw [hv₁] at hs; exact absurd hs (by simp)
        | cons b hd' =>
            rw [hv₁] at hs
            simp only [subs_cons, Bool.and_eq_true] at hs
            have hv₂ : st₂.vals = b :: (hd' ++ tl) := by rw [he]; rfl
            rw [popE_cons hv₂] at h
            by_cases hb : subOf b t
            · rw [if_pos hb] at h
              cases h
              refine ⟨⟨st₁.poly, rest⟩, ?_, ?_⟩
              · rw [popE_cons hv₁, if_pos (subOf_trans hs.1 hb)]
              · exact Or.inl ⟨hp₁, hd', tl, rfl, hs.2⟩
            · rw [if_neg hb] at h; exact absurd h (by simp)
  · -- both frames are concrete and pointwise ordered
    cases hv₂ : st₂.vals with
    | nil =>
        rw [popE_nil hv₂, hp₂] at h
        exact absurd h (by simp)
    | cons b rest₂ =>
        cases hv₁ : st₁.vals with
        | nil => rw [hv₁, hv₂] at hs; exact absurd hs (by simp)
        | cons a rest₁ =>
            rw [hv₁, hv₂] at hs
            simp only [subs_cons, Bool.and_eq_true] at hs
            rw [popE_cons hv₂] at h
            by_cases hb : subOf b t
            · rw [if_pos hb] at h
              cases h
              refine ⟨⟨st₁.poly, rest₁⟩, ?_, ?_⟩
              · rw [popE_cons hv₁, if_pos (subOf_trans hs.1 hb)]
              · exact Or.inr ⟨hp₁, hp₂, hs.2⟩
            · rw [if_neg hb] at h; exact absurd h (by simp)

theorem pops_mono {st₁ st₂ st₂' : St} : ∀ {ts : List ValType},
    le st₁ st₂ → st₂.pops ts = some st₂' → ∃ st₁', st₁.pops ts = some st₁' ∧ le st₁' st₂' := by
  intro ts
  induction ts generalizing st₁ st₂ st₂' with
  | nil => intro hle h; cases h; exact ⟨st₁, rfl, hle⟩
  | cons t ts ih =>
      intro hle h
      rw [pops_cons] at h
      cases hp : st₂.pops ts with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some st₂'' =>
          rw [hp] at h
          obtain ⟨st₁'', hp₁, hle''⟩ := ih hle hp
          obtain ⟨st₁', hpop, hle'⟩ := popE_mono hle'' h
          exact ⟨st₁', by rw [pops_cons, hp₁]; exact hpop, hle'⟩

theorem sat_mono {st₁ st₂ : St} {ts : List ValType} (hle : le st₁ st₂) (h : st₂.Sat ts) :
    st₁.Sat ts := by
  obtain ⟨st₂', hp, hv⟩ := h
  obtain ⟨st₁', hp₁, hle'⟩ := pops_mono hle hp
  refine ⟨st₁', hp₁, ?_⟩
  obtain ⟨hd, tl, he, hs⟩ := le_split hle'
  rw [hv] at he
  have : hd = [] := by
    cases hd with
    | nil => rfl
    | cons a as => exact absurd he.symm (by simp)
  rw [this] at hs
  cases hv₁ : st₁'.vals with
  | nil => rfl
  | cons a as => rw [hv₁] at hs; exact absurd hs (by simp)

theorem pushs_mono {st₁ st₂ : St} (hle : le st₁ st₂) (ts : List ValType) :
    le (st₁.pushs ts) (st₂.pushs ts) := by
  rcases hle with ⟨hp₁, hd, tl, he, hs⟩ | ⟨hp₁, hp₂, hs⟩
  · refine Or.inl ⟨by rw [pushs_poly]; exact hp₁, ts.reverse ++ hd, tl, ?_, ?_⟩
    · rw [pushs_eq, he, List.append_assoc]
    · rw [pushs_eq]
      exact subs_append (subs_refl _) hs
  · refine Or.inr ⟨by rw [pushs_poly]; exact hp₁, by rw [pushs_poly]; exact hp₂, ?_⟩
    rw [pushs_eq, pushs_eq]
    exact subs_append (subs_refl _) hs

/-- `unreachable()` produces the most general frame there is. -/
theorem le_unreach (st₁ st₂ : St) (h : st₁.poly = true) (hv : st₁.vals = []) :
    le st₁ st₂ := Or.inl ⟨h, [], st₂.vals, by simp, by rw [hv]; rfl⟩


/-! ### Reading a frame back as a concrete stack type

These are the lemmas the soundness direction needs: what a successful run of
`pop_vals` says about the operand types that were actually there. -/

/-- Every non-empty list ends somewhere. -/
theorem list_snoc {α : Type} : ∀ l : List α, l = [] ∨ ∃ l' a, l = l' ++ [a]
  | [] => Or.inl rfl
  | a :: l =>
      Or.inr (match list_snoc l with
        | Or.inl h => ⟨[], a, by rw [h]; rfl⟩
        | Or.inr ⟨l', b, h⟩ => ⟨a :: l', b, by rw [h]; rfl⟩)

/-- A frame with one operand pushed produces `ts` only if `ts` ends with a
supertype of that operand. -/
theorem push_sat {st : St} {t : ValType} {rs : List ValType} (h : (st.push t).Sat rs) :
    ∃ rs' u, rs = rs' ++ [u] ∧ subOf t u = true ∧ st.Sat rs' := by
  rcases list_snoc rs with rfl | ⟨rs', u, rfl⟩
  · obtain ⟨st', hp, hv⟩ := h
    rw [pops_nil] at hp
    cases hp
    exact absurd hv (by simp [push])
  · obtain ⟨st', hp, hv⟩ := h
    rw [pops_append] at hp
    have hpu : (st.push t).pops [u] = (st.push t).popE u := rfl
    refine ⟨rs', u, rfl, ?_, ?_⟩
    · rw [hpu] at hp
      have hvv : (st.push t).vals = t :: st.vals := rfl
      rw [popE_cons hvv] at hp
      by_cases hb : subOf t u
      · exact hb
      · rw [if_neg hb] at hp; exact absurd hp (by simp)
    · rw [hpu] at hp
      have hvv : (st.push t).vals = t :: st.vals := rfl
      rw [popE_cons hvv] at hp
      by_cases hb : subOf t u
      · rw [if_pos hb] at hp
        exact ⟨st', hp, hv⟩
      · rw [if_neg hb] at hp; exact absurd hp (by simp)

/-- A frame with `ts` pushed produces `ts'` exactly when `ts'` splits into what
the frame below produces and a supertype sequence of `ts`. -/
theorem pops_split_sat : ∀ (ts : List ValType) {st : St} {ts' : List ValType},
    (st.pushs ts).Sat ts' → ∃ rs cs, ts' = rs ++ cs ∧ subs ts cs = true ∧ st.Sat rs
  | [], st, ts', h => ⟨ts', [], by simp, rfl, h⟩
  | t :: ts, st, ts', h => by
      obtain ⟨rs, cs, he, hs, hsat⟩ := pops_split_sat ts (st := st.push t) h
      obtain ⟨rs', u, he', hu, hsat'⟩ := push_sat hsat
      refine ⟨rs', u :: cs, ?_, ?_, hsat'⟩
      · rw [he, he', List.append_assoc]; rfl
      · simp [hu, hs]

/-- A frame produces the type of its own operands. -/
theorem sat_own (st : St) : st.Sat st.vals.reverse := by
  refine ⟨⟨st.poly, []⟩, ?_, rfl⟩
  suffices h : ∀ (vs : List ValType) (p : Bool),
      (St.mk p vs).pops vs.reverse = some ⟨p, []⟩ by
    have := h st.vals st.poly
    simpa using this
  intro vs
  induction vs with
  | nil => intro p; rfl
  | cons a vs ih =>
      intro p
      rw [List.reverse_cons, pops_append]
      have h1 : (St.mk p (a :: vs)).pops [a] = some ⟨p, vs⟩ := by
        show (St.mk p (a :: vs)).popE a = _
        rw [popE_cons (show (St.mk p (a :: vs)).vals = a :: vs from rfl), if_pos (subOf_refl a)]
      rw [h1]
      exact ih p

/-- An empty concrete frame produces only the empty type. -/
theorem sat_empty_false {rs : List ValType} (h : (St.mk false []).Sat rs) : rs = [] := by
  rcases list_snoc rs with rfl | ⟨rs', u, rfl⟩
  · rfl
  · obtain ⟨st', hp, hv⟩ := h
    rw [pops_append] at hp
    have : (St.mk false []).pops [u] = none := by
      show (St.mk false []).popE u = none
      rw [popE_nil (show (St.mk false []).vals = [] from rfl)]
      rfl
    rw [this] at hp
    exact absurd hp (by simp)

/-- The untyped `pop_val` and the checking one agree. -/
theorem pop_popE {st : St} {t : ValType} {st' : St} (h : st.pop = some (t, st')) :
    st.popE t = some st' := by
  unfold pop at h
  cases hv : st.vals with
  | nil =>
      rw [hv] at h
      cases hb : st.poly with
      | false => rw [hb] at h; exact absurd h (by simp)
      | true =>
          rw [hb] at h
          simp only [if_pos, Option.some.injEq, Prod.mk.injEq] at h
          rw [popE_nil hv, hb, if_pos rfl, h.2]
  | cons a rest =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [popE_cons hv, ← h.1, if_pos (subOf_refl a), h.2]

/-- ... and popping with a weaker expectation succeeds too. -/
theorem pop_popE_of_subOf {st : St} {t : ValType} {st' : St} {u : ValType}
    (h : st.pop = some (t, st')) (hs : subOf t u = true) : st.popE u = some st' :=
  popE_of_subOf (pop_popE h) hs

/-- The operand type an untyped `pop_val` returns is one the frame carried, or
`Bot`. -/
theorem pop_nvb {st : St} {t : ValType} {st' : St} (h : st.pop = some (t, st'))
    (hst : st.vals.all ValType.nvb = true) :
    ValType.nvb t = true ∧ st'.vals.all ValType.nvb = true := by
  unfold pop at h
  cases hv : st.vals with
  | nil =>
      rw [hv] at h
      cases hb : st.poly with
      | false => rw [hb] at h; exact absurd h (by simp)
      | true =>
          rw [hb] at h
          simp only [if_pos, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, ← h.2, hv]
          exact ⟨rfl, rfl⟩
  | cons a rest =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [hv] at hst
      simp only [List.all_cons, Bool.and_eq_true] at hst
      rw [← h.1, ← h.2]
      exact ⟨hst.1, hst.2⟩

theorem popE_nvb {st st' : St} {t : ValType} (h : st.popE t = some st')
    (hst : st.vals.all ValType.nvb = true) : st'.vals.all ValType.nvb = true := by
  cases hv : st.vals with
  | nil => rw [popE_nil hv] at h
           cases hb : st.poly with
           | false => rw [hb] at h; exact absurd h (by simp)
           | true => rw [hb] at h; simp at h; rw [← h]; exact hst
  | cons a rest =>
      rw [popE_cons hv] at h
      by_cases hb : subOf a t
      · rw [if_pos hb] at h
        cases h
        rw [hv] at hst
        simp only [List.all_cons, Bool.and_eq_true] at hst
        exact hst.2
      · rw [if_neg hb] at h; exact absurd h (by simp)

theorem pops_nvb {st st' : St} : ∀ {ts : List ValType}, st.pops ts = some st' →
    st.vals.all ValType.nvb = true → st'.vals.all ValType.nvb = true := by
  intro ts
  induction ts generalizing st' with
  | nil => intro h _; cases h; assumption
  | cons t ts ih =>
      intro h hst
      rw [pops_cons] at h
      cases hp : st.pops ts with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some st'' => rw [hp] at h; exact popE_nvb h (ih hp hst)

theorem pushs_nvb {st : St} {ts : List ValType} (hst : st.vals.all ValType.nvb = true)
    (h : ts.all ValType.nvb = true) : (st.pushs ts).vals.all ValType.nvb = true := by
  rw [pushs_eq]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨by simpa using h, hst⟩

/-- On the decided fragment `matches_val` is equality: a `numtype` or
`vectype` is a subtype only of itself. -/
theorem subs_eq_of_nv : ∀ {as bs : List ValType}, subs as bs = true →
    as.all ValType.nv = true → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hn => by
      simp only [subs_cons, Bool.and_eq_true] at h
      simp only [List.all_cons, Bool.and_eq_true] at hn
      have : a = b := by
        simp only [subOf, Bool.or_eq_true, beq_iff_eq] at h
        rcases h.1 with h1 | h1
        · rw [h1] at hn; exact absurd hn.1 (by simp [ValType.nv])
        · exact h1
      rw [this, subs_eq_of_nv h.2 hn.2]

/-! ### `pop_val()` with no expectation, repeated

`Instr_ok/br_table` leaves the operand type `t*` FREE and only requires it to be
below every label's type, so the algorithm cannot pop against a fixed
expectation: `appendix/algorithm.rst` writes the `br_table` case as
`push_vals(pop_vals(label_types(ctrls[n])))`, i.e. it reads the operands the
frame actually supplies and compares them afterwards.  `popN` is that read: the
appendix's untyped `pop_val()` iterated `n` times, in `pop_vals` order.

It is PRINCIPAL, and that is the whole reason a single pass decides `br_table`:
`popN_pops` says the frame can pop what `popN` returns, and `popN_principal`
says every sequence the frame can pop is above it, so checking `popN`'s answer
against the labels decides the existential the rule quantifies over. -/

/-- `pop_val()` repeated `n` times: the operand types the frame supplies at its
top, deepest first, `BOT` where a polymorphic frame has nothing left. -/
def popN (st : St) : Nat → Option (List ValType × St)
  | 0 => some ([], st)
  | n + 1 =>
      match st.popN n with
      | some (ts, st') =>
          match st'.pop with
          | some (t, st'') => some (t :: ts, st'')
          | none => none
      | none => none

/-- `pop_val()` against the type it just returned succeeds. -/
theorem popE_of_pop {st st' : St} {t : ValType} (h : st.pop = some (t, st')) :
    st.popE t = some st' := by
  unfold pop at h
  cases hv : st.vals with
  | nil =>
      rw [hv] at h
      cases hb : st.poly with
      | false => rw [hb] at h; exact absurd h (by simp)
      | true =>
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq, if_pos] at h
          rw [popE_nil hv, hb, ← h.2]
          simp
  | cons a rest =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [popE_cons hv, ← h.1, if_pos (subOf_refl a), ← h.2]

theorem popN_zero (st : St) : st.popN 0 = some ([], st) := rfl

theorem popN_succ (st : St) (n : Nat) :
    st.popN (n + 1) =
      (match st.popN n with
       | some (ts, st') =>
           (match st'.pop with
            | some (t, st'') => some (t :: ts, st'')
            | none => none)
       | none => none) := rfl

theorem popN_length : ∀ {n : Nat} {st : St} {ts : List ValType} {st' : St},
    st.popN n = some (ts, st') → ts.length = n
  | 0, st, _, _, h => by
      rw [popN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
  | n + 1, st, _, _, h => by
      rw [popN_succ] at h
      cases hp : st.popN n with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨us, s⟩ := p
          simp only [hp] at h
          cases hq : s.pop with
          | none => simp only [hq] at h; exact absurd h (by simp)
          | some q =>
              obtain ⟨u, s'⟩ := q
              simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1]
              simp [popN_length hp]

theorem popN_pops : ∀ {n : Nat} {st : St} {ts : List ValType} {st' : St},
    st.popN n = some (ts, st') → st.pops ts = some st'
  | 0, st, _, _, h => by
      rw [popN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]; rfl
  | n + 1, st, _, _, h => by
      rw [popN_succ] at h
      cases hp : st.popN n with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨us, s⟩ := p
          simp only [hp] at h
          cases hq : s.pop with
          | none => simp only [hq] at h; exact absurd h (by simp)
          | some q =>
              obtain ⟨u, s'⟩ := q
              simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1, pops_cons, popN_pops hp, ← h.2]
              exact popE_of_pop hq

theorem popN_nvb : ∀ {n : Nat} {st : St} {ts : List ValType} {st' : St},
    st.popN n = some (ts, st') → st.vals.all ValType.nvb = true →
    ts.all ValType.nvb = true ∧ st'.vals.all ValType.nvb = true
  | 0, st, _, _, h, hst => by
      rw [popN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]; exact ⟨rfl, hst⟩
  | n + 1, st, _, _, h, hst => by
      rw [popN_succ] at h
      cases hp : st.popN n with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨us, s⟩ := p
          simp only [hp] at h
          cases hq : s.pop with
          | none => simp only [hq] at h; exact absurd h (by simp)
          | some q =>
              obtain ⟨u, s'⟩ := q
              simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hus, hs⟩ := popN_nvb hp hst
              obtain ⟨hu, hs'⟩ := pop_nvb hq hs
              rw [← h.1, ← h.2]
              exact ⟨by simp [hu, hus], hs'⟩

/-- `pop_vals` consumes exactly `|ts|` operands, whatever the expectations
were: the frame it leaves is determined by the LENGTH of its argument.  This is
what makes `popN`'s answer comparable with any other successful pop. -/
theorem pops_vals : ∀ {ts : List ValType} {st st' : St},
    st.pops ts = some st' → st'.vals = st.vals.drop ts.length := by
  intro ts
  induction ts with
  | nil => intro st st' h; cases h; simp
  | cons t ts ih =>
      intro st st' h
      rw [pops_cons] at h
      cases hp : st.pops ts with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some s =>
          simp only [hp] at h
          have hs : s.vals = st.vals.drop ts.length := ih hp
          have hd : st.vals.drop (t :: ts).length = (st.vals.drop ts.length).drop 1 := by
            rw [List.drop_drop]; rfl
          cases hv : s.vals with
          | nil =>
              rw [popE_nil hv] at h
              cases hb : s.poly with
              | false => rw [hb] at h; exact absurd h (by simp)
              | true =>
                  rw [hb] at h
                  simp only [if_true, Option.some.injEq] at h
                  rw [← h, hv, hd, ← hs, hv]
                  rfl
          | cons a rest =>
              rw [popE_cons hv] at h
              by_cases hsub : subOf a t
              · rw [if_pos hsub] at h
                cases h
                rw [hd, ← hs, hv]
                rfl
              · rw [if_neg hsub] at h; exact absurd h (by simp)

theorem popN_vals {n : Nat} {st st' : St} {ts : List ValType}
    (h : st.popN n = some (ts, st')) : st'.vals = st.vals.drop n := by
  rw [pops_vals (popN_pops h), popN_length h]

theorem popN_poly {n : Nat} {st st' : St} {ts : List ValType}
    (h : st.popN n = some (ts, st')) : st'.poly = st.poly :=
  pops_poly (popN_pops h)

/-- Two frames with the same flag and the same operands are the same frame. -/
theorem eq_of {st₁ st₂ : St} (hp : st₁.poly = st₂.poly) (hv : st₁.vals = st₂.vals) :
    st₁ = st₂ := by
  cases st₁; cases st₂; simp_all

/-! ## Full corrected-reference stack facts -/

@[simp] theorem subOfA_refl (C : Context) (t : ValType) :
    subOfA C t t = true := decValtypeSub_refl C t

def SatA (C : Context) (st : St) (ts : List ValType) : Prop :=
  ∃ st', popsA C st ts = some st' ∧ st'.vals = []

theorem popsA_append (C : Context) (st : St) (ts₁ ts₂ : List ValType) :
    popsA C st (ts₁ ++ ts₂) =
      match popsA C st ts₂ with
      | some st' => popsA C st' ts₁
      | none => none := by
  induction ts₁ generalizing st with
  | nil =>
      cases h : popsA C st ts₂ <;> simp [h, popsA]
  | cons t ts₁ ih =>
      show (match popsA C st (ts₁ ++ ts₂) with
            | some st' => popEA C st' t
            | none => none) = _
      rw [ih]
      cases popsA C st ts₂ <;> rfl

theorem pushs_popsA (C : Context) (st : St) : ∀ ts : List ValType,
    popsA C (st.pushs ts) ts = some st := by
  intro ts
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih =>
      show (match popsA C ((st.push t).pushs ts) ts with
            | some st' => popEA C st' t
            | none => none) = some st
      rw [ih (st.push t)]
      simp [popEA, push, subOfA_refl]

theorem popsA_unreach (C : Context) : ∀ ts : List ValType,
    popsA C (St.mk true []) ts = some (St.mk true [])
  | [] => rfl
  | t :: ts => by
      rw [popsA, popsA_unreach C ts]
      rfl

theorem satA_unreach (C : Context) (ts : List ValType) :
    SatA C (St.mk true []) ts := ⟨_, popsA_unreach C ts, rfl⟩

theorem satA_own (C : Context) (st : St) : SatA C st st.vals.reverse := by
  refine ⟨St.mk st.poly [], ?_, rfl⟩
  simpa [pushs_eq] using pushs_popsA C (St.mk st.poly []) st.vals.reverse

theorem satA_append {C : Context} {st st₀ : St} {ts rs : List ValType}
    (h : popsA C st ts = some st₀) (hsat : SatA C st₀ rs) :
    SatA C st (rs ++ ts) := by
  obtain ⟨st', hp, hv⟩ := hsat
  exact ⟨st', by rw [popsA_append, h]; exact hp, hv⟩

theorem push_satA {C : Context} {st : St} {t : ValType} {rs : List ValType}
    (h : SatA C (st.push t) rs) :
    ∃ rs' u, rs = rs' ++ [u] ∧ subOfA C t u = true ∧ SatA C st rs' := by
  rcases list_snoc rs with rfl | ⟨rs', u, rfl⟩
  · obtain ⟨st', hp, hv⟩ := h
    simp only [popsA] at hp
    cases hp
    exact absurd hv (by simp [push])
  · obtain ⟨st', hp, hv⟩ := h
    rw [popsA_append] at hp
    by_cases hb : subOfA C t u = true
    · have hpop : popsA C (st.push t) [u] = some st := by
        simp [popsA, popEA, push, hb]
      rw [hpop] at hp
      exact ⟨rs', u, rfl, hb, ⟨st', hp, hv⟩⟩
    · have hpop : popsA C (st.push t) [u] = none := by
        simp [popsA, popEA, push, hb]
      rw [hpop] at hp
      contradiction

theorem pops_split_satA (C : Context) : ∀ (ts : List ValType) {st : St}
    {ts' : List ValType}, SatA C (st.pushs ts) ts' →
      ∃ rs cs, ts' = rs ++ cs ∧ subsA C ts cs = true ∧ SatA C st rs
  | [], st, ts', h => ⟨ts', [], by simp, rfl, h⟩
  | t :: ts, st, ts', h => by
      obtain ⟨rs, cs, he, hs, hsat⟩ := pops_split_satA C ts (st := st.push t) h
      obtain ⟨rs', u, he', hu, hsat'⟩ := push_satA hsat
      refine ⟨rs', u :: cs, ?_, ?_, hsat'⟩
      · rw [he, he', List.append_assoc]
        rfl
      · simp only [subsA, decResulttypeSubN, decSeq₂, Bool.and_eq_true]
        exact ⟨hu, hs⟩

theorem satA_empty_false {C : Context} {rs : List ValType}
    (h : SatA C (St.mk false []) rs) : rs = [] := by
  rcases list_snoc rs with rfl | ⟨rs', u, rfl⟩
  · rfl
  · obtain ⟨st', hp, _⟩ := h
    rw [popsA_append] at hp
    have : popsA C (St.mk false []) [u] = none := by rfl
    rw [this] at hp
    contradiction

theorem popEA_of_pop {C : Context} {st st' : St} {t : ValType}
    (h : st.pop = some (t, st')) : popEA C st t = some st' := by
  cases st with
  | mk poly vals =>
    cases vals with
    | nil =>
        cases poly with
        | false => simp [pop] at h
        | true =>
            simp [pop] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
    | cons a rest =>
        simp [pop] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [popEA, subOfA_refl]

theorem popN_popsA {C : Context} : ∀ {n : Nat} {st : St} {ts : List ValType}
    {st' : St}, st.popN n = some (ts, st') → popsA C st ts = some st'
  | 0, st, _, _, h => by
      rw [popN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      rfl
  | n + 1, st, _, _, h => by
      rw [popN_succ] at h
      cases hp : st.popN n with
      | none => simp only [hp] at h; contradiction
      | some p =>
          obtain ⟨us, s⟩ := p
          simp only [hp] at h
          cases hq : s.pop with
          | none => simp only [hq] at h; contradiction
          | some q =>
              obtain ⟨u, s'⟩ := q
              simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1, popsA, popN_popsA hp, ← h.2]
              exact popEA_of_pop hq

theorem finishA_iff_satA {C : Context} {st : St} {ts : List ValType} :
    (match popsA C st ts with
     | some st' => st'.vals.isEmpty
     | none => false) = true ↔ SatA C st ts := by
  unfold SatA
  cases hp : popsA C st ts with
  | none => simp
  | some st' => simp [List.isEmpty_iff]

end St
end Validate
end WasmGemmGnaf.Wasm.Core
