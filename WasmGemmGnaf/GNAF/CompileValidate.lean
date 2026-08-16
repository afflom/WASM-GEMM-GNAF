import WasmGemmGnaf.GNAF.CompileModule
import WasmGemmGnaf.Wasm.Core.Validate

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Direct amended-Core validation of compiled GNAF plans

This file checks the direct compiler against the executable Core validator.
Its stack proof is structural over `HasType`; unsupported source constructors
remain syntactically valid Core because `unreachable` is stack-polymorphic,
while `CheckedPlan.coreSupported` independently prevents those constructors
from entering the semantic compiler contract.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectValidation
namespace DirectTyping

abbrev St := Wasm.Core.Validate.St

def checkList (C : Wasm.Core.Context) (st : St)
    (xs : List Wasm.Core.Instr) : Option St :=
  Wasm.Core.Validate.checkSeq C st (Wasm.Core.InstrSeq.ofList xs)

@[simp] theorem checkList_nil (C : Wasm.Core.Context) (st : St) :
    checkList C st [] = some st := rfl

@[simp] theorem checkList_cons (C : Wasm.Core.Context) (st : St)
    (i : Wasm.Core.Instr) (is : List Wasm.Core.Instr) :
    checkList C st (i :: is) =
      (Wasm.Core.Validate.checkInstr C st i).bind
        (fun st' => checkList C st' is) := by
  unfold checkList
  rw [Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq]
  cases Wasm.Core.Validate.checkInstr C st i <;> rfl

theorem checkList_append (C : Wasm.Core.Context) (st : St) :
    ∀ (a b : List Wasm.Core.Instr),
      checkList C st (a ++ b) =
        (checkList C st a).bind (fun st' => checkList C st' b) := by
  intro a
  induction a generalizing st with
  | nil => intro b; rfl
  | cons i rest ih =>
      intro b
      rw [List.cons_append, checkList_cons, checkList_cons]
      cases h : Wasm.Core.Validate.checkInstr C st i <;> simp [ih]

def Neutral (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st ∨
    checkList C st xs = some st.unreach

def Preserves (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st

theorem neutral_nil (C : Wasm.Core.Context) : Neutral C [] := by
  intro st
  exact Or.inl rfl

theorem neutral_append {C : Wasm.Core.Context} {a b : List Wasm.Core.Instr}
    (ha : Neutral C a) (hb : Neutral C b) : Neutral C (a ++ b) := by
  intro st
  rw [checkList_append]
  rcases ha st with ha | ha
  · rw [ha]
    exact hb st
  · rw [ha]
    rcases hb st.unreach with hb | hb
    · exact Or.inr hb
    · exact Or.inr (by simpa [Wasm.Core.Validate.St.unreach] using hb)

theorem neutral_of_preserves {C : Wasm.Core.Context}
    {xs : List Wasm.Core.Instr} (h : Preserves C xs) : Neutral C xs := by
  intro st
  exact Or.inl (h st)

def numLocal (nt : Wasm.Core.NumType) : Wasm.Core.LocalType :=
  { init := .set, valtype := .num nt }

def HasNumLocal (C : Wasm.Core.Context) (i : Nat)
    (nt : Wasm.Core.NumType) : Prop :=
  C.locals[(coreU32 i).val]? = some (numLocal nt)

abbrev HasI32Local (C : Wasm.Core.Context) (i : Nat) : Prop :=
  HasNumLocal C i .i32

abbrev HasI64Local (C : Wasm.Core.Context) (i : Nat) : Prop :=
  HasNumLocal C i .i64

theorem checkList_constL (C : Wasm.Core.Context) (st : St) (n : Nat) :
    checkList C st [constL n] = some (st.push (.num .i64)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, constL,
    Wasm.Core.Num_.wf, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.pushs]

theorem checkList_localGet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (nt : Wasm.Core.NumType) (hi : HasNumLocal C i nt) :
    checkList C st [localGet i] = some (st.push (.num nt)) := by
  unfold HasNumLocal numLocal at hi
  rw [show checkList C st [localGet i] =
      (Wasm.Core.Validate.checkInstr C st (localGet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localGet, hi,
    Wasm.Core.Validate.ValType.nv, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.pushs]

theorem checkList_localSet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (nt : Wasm.Core.NumType) (hi : HasNumLocal C i nt) :
    checkList C (st.push (.num nt)) [localSet i] = some st := by
  unfold HasNumLocal numLocal at hi
  rw [show checkList C (st.push (.num nt)) [localSet i] =
      (Wasm.Core.Validate.checkInstr C (st.push (.num nt)) (localSet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localSet, hi,
    Wasm.Core.Validate.ValType.nv, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
    Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.subOf]

theorem checkList_app2 {C : Wasm.Core.Context} {st mid out : St}
    {a b : List Wasm.Core.Instr}
    (ha : checkList C st a = some mid)
    (hb : checkList C mid b = some out) :
    checkList C st (a ++ b) = some out := by
  rw [checkList_append, ha]
  exact hb

theorem checkList_setConstL (C : Wasm.Core.Context) (st : St) (i n : Nat)
    (hi : HasI64Local C i) :
    checkList C st [constL n, localSet i] = some st := by
  refine checkList_app2 (a := [constL n]) (b := [localSet i])
    (checkList_constL C st n) ?_
  exact checkList_localSet C st i .i64 hi

theorem preserves_setConstL {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI64Local C i) (n : Nat) :
    Preserves C [constL n, localSet i] := by
  intro st
  exact checkList_setConstL C st i n hi

theorem checkList_i64Binop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.BinopI) :
    checkList C ((st.push (.num .i64)).push (.num .i64))
      [.binop .i64 (.int op)] = some (st.push (.num .i64)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf,
    Wasm.Core.Binop.wf, Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_i64Relop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.RelopI) :
    checkList C ((st.push (.num .i64)).push (.num .i64))
      [.relop .i64 (.int op)] = some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf,
    Wasm.Core.Relop.wf, Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_wrapI64 (C : Wasm.Core.Context) (st : St) :
    checkList C (st.push (.num .i64)) [wrapI64] =
      some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, wrapI64,
    Wasm.Core.Cvtop.wf, Wasm.Core.Inn.size, Wasm.Core.Inn.toNumType,
    Wasm.Core.NumType.size,
    Wasm.Core.NumType.toInn?, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
    Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.subOf]

abbrev pushLabel (C : Wasm.Core.Context) : Wasm.Core.Context :=
  Wasm.Core.Context.pushLabel [] C

def freshSt : St := { poly := false, vals := [] }

@[simp] theorem pushLabel_locals (C : Wasm.Core.Context) :
    (pushLabel C).locals = C.locals := rfl

theorem HasNumLocal.pushLabel {C : Wasm.Core.Context} {i : Nat}
    {nt : Wasm.Core.NumType} (h : HasNumLocal C i nt) :
    HasNumLocal (pushLabel C) i nt := by
  exact h

theorem checkList_ifE (C : Wasm.Core.Context) (st : St)
    (a b : List Wasm.Core.Instr)
    (ha : Neutral (pushLabel C) a) (hb : Neutral (pushLabel C) b) :
    checkList C (st.push (.num .i32)) [ifE a b] = some st := by
  rcases ha freshSt with ha | ha <;>
    rcases hb freshSt with hb | hb <;>
    unfold checkList at ha hb <;>
    simp only [pushLabel, freshSt] at ha hb <;>
    simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
      Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.blockType, ifE,
      ha, hb, Wasm.Core.Validate.St.pops,
      Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
      Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.St.finish,
      Wasm.Core.Validate.St.unreach, Wasm.Core.Validate.subOf]

def PushesI32 (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some (st.push (.num .i32))

def PushesI64 (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some (st.push (.num .i64))

theorem pushes_localGetL {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI64Local C i) : PushesI64 C [localGet i] := by
  intro st
  exact checkList_localGet C st i .i64 hi

theorem preserves_copyLocalL {C : Wasm.Core.Context} {src dst : Nat}
    (hsrc : HasI64Local C src) (hdst : HasI64Local C dst) :
    Preserves C [localGet src, localSet dst] := by
  intro st
  refine checkList_app2 (a := [localGet src]) (b := [localSet dst])
    (checkList_localGet C st src .i64 hsrc) ?_
  exact checkList_localSet C st dst .i64 hdst

theorem preserves_append_if {C : Wasm.Core.Context}
    {condition yes no : List Wasm.Core.Instr}
    (hc : PushesI32 C condition)
    (hy : Neutral (pushLabel C) yes) (hn : Neutral (pushLabel C) no) :
    Preserves C (condition ++ [ifE yes no]) := by
  intro st
  refine checkList_app2 (hc st) ?_
  exact checkList_ifE C st yes no hy hn

theorem pushes_i64Relop {C : Wasm.Core.Context} {lhs rhs : Nat}
    (hlhs : HasI64Local C lhs) (hrhs : HasI64Local C rhs)
    (op : Wasm.Core.RelopI) :
    PushesI32 C [localGet lhs, localGet rhs, .relop .i64 (.int op)] := by
  intro st
  refine checkList_app2 (a := [localGet lhs])
    (b := [localGet rhs, .relop .i64 (.int op)])
    (checkList_localGet C st lhs .i64 hlhs) ?_
  refine checkList_app2 (a := [localGet rhs])
    (b := [.relop .i64 (.int op)])
    (checkList_localGet C (st.push (.num .i64)) rhs .i64 hrhs) ?_
  exact checkList_i64Relop C st op

theorem preserves_i64BinopSet {C : Wasm.Core.Context}
    {lhs rhs dst : Nat} (hlhs : HasI64Local C lhs)
    (hrhs : HasI64Local C rhs) (hdst : HasI64Local C dst)
    (op : Wasm.Core.BinopI) :
    Preserves C
      [localGet lhs, localGet rhs, .binop .i64 (.int op), localSet dst] := by
  intro st
  refine checkList_app2 (a := [localGet lhs])
    (b := [localGet rhs, .binop .i64 (.int op), localSet dst])
    (checkList_localGet C st lhs .i64 hlhs) ?_
  refine checkList_app2 (a := [localGet rhs])
    (b := [.binop .i64 (.int op), localSet dst])
    (checkList_localGet C (st.push (.num .i64)) rhs .i64 hrhs) ?_
  refine checkList_app2 (a := [.binop .i64 (.int op)])
    (b := [localSet dst]) (checkList_i64Binop C st op) ?_
  exact checkList_localSet C st dst .i64 hdst

def Locals64Through (C : Wasm.Core.Context) (n : Nat) : Prop :=
  ∀ i, 2 ≤ i → i < n → HasI64Local C i

theorem Locals64Through.mono {C : Wasm.Core.Context} {m n : Nat}
    (h : Locals64Through C n) (hm : m ≤ n) : Locals64Through C m := by
  intro i hlo hi
  exact h i hlo (Nat.lt_of_lt_of_le hi hm)

theorem Locals64Through.pushLabel {C : Wasm.Core.Context} {n : Nat}
    (h : Locals64Through C n) : Locals64Through (pushLabel C) n := by
  intro i hlo hi
  exact (h i hlo hi).pushLabel

theorem coreSupported_sig_eq {P : Wasm.Profile} {G : Gemm.Problem P}
    (p : Plan) (s₁ s₂ : Sig) :
    p.coreSupported P G s₁ = p.coreSupported P G s₂ := by
  induction p <;> simp [Plan.coreSupported, *]

theorem code_neutral_supported {P : Wasm.Profile} {G : Gemm.Problem P}
    {s : Sig} {p : Plan} {t : Sig} (hp : HasType s p t) :
    ∀ (e : CompileEnv) (d scr : Nat) (C : Wasm.Core.Context),
      e.regs = s.regs →
      Locals64Through C (2 + e.regs + d + p.depth + 2) →
      p.coreSupported P G s = true → Neutral C (code e d scr p) := by
  induction hp with
  | nop s =>
      intro e d scr C hreg hloc hs
      exact neutral_nil C
  | @seq s u t a b ha hb iha ihb =>
      intro e d scr C hreg hloc hs
      have hs' : a.coreSupported P G s = true ∧
          b.coreSupported P G s = true := by
        simpa [Plan.coreSupported] using hs
      have hu : u.regs = s.regs := (hasType_fixed_resources ha).1
      have hda : a.depth ≤ Nat.max a.depth b.depth := Nat.le_max_left _ _
      have hdb : b.depth ≤ Nat.max a.depth b.depth := Nat.le_max_right _ _
      have hla : Locals64Through C (2 + e.regs + d + a.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      have hlb : Locals64Through C (2 + e.regs + d + b.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact neutral_append (iha e d scr C hreg hla hs'.1)
        (ihb e d scr C (by omega) hlb (by
          rw [← coreSupported_sig_eq b s u]
          exact hs'.2))
  | classifyRaw =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | dispatchLayout =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | branch =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | pack =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | unpack =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | storeReg =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | loadReg =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | loopNest =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | loopReg =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | tiled =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | reduce =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | @allocScratch s t bytes body hbody ih =>
      intro e d scr C hreg hloc hs
      have hbodyLoc : Locals64Through C
          (2 + e.regs + d + body.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact ih e d (scr + bytes) C hreg hbodyLoc (by
        rw [← coreSupported_sig_eq body s
          { s with scratch := s.scratch + bytes }]
        simpa [Plan.coreSupported] using hs)
  | @setReg s dst value hdst =>
      intro e d scr C hreg hloc hs
      exact neutral_nil C
  | @scalarOp s op dst lhs rhs hdst hlhs hrhs =>
      intro e d scr C hreg hloc hs
      cases op with
      | add => simp [Plan.coreSupported, Plan.coreScalarOpSupported] at hs
      | mul => simp [Plan.coreSupported, Plan.coreScalarOpSupported] at hs
      | sub => exact neutral_nil C
      | max => exact neutral_nil C
      | min => exact neutral_nil C
  | vectorOp =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | emitTable =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | tableLoad =>
      intro e d scr C hreg hloc hs
      simp [Plan.coreSupported] at hs
  | setStatus s status =>
      intro e d scr C hreg hloc hs
      have hstatus : HasI64Local C e.statusLocal := by
        apply hloc
        · unfold CompileEnv.statusLocal
          omega
        · unfold CompileEnv.statusLocal
          simp only [Plan.depth]
          omega
      simp only [code]
      exact neutral_of_preserves (preserves_setConstL hstatus status.code)
  | @buildOutput s src hstatus hsrc =>
      intro e d scr C hreg hloc hs
      simp only [code]
      exact neutral_nil C
  | @opaqueProcess s t spec body hsteps hbytes hbody ih =>
      intro e d scr C hreg hloc hs
      have hbodyLoc : Locals64Through C
          (2 + e.regs + d + body.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact ih e d scr C hreg hbodyLoc (by
        simpa [Plan.coreSupported] using hs)

end DirectTyping
end DirectValidation
end WasmGemmGnaf.GNAF

/- Obsolete duplicate of the mixed-local helper kernel; retained inside the
historical block with the former all-i32 proof below. -/
/-
namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectValidation
namespace DirectTyping

abbrev St := Wasm.Core.Validate.St

def checkList (C : Wasm.Core.Context) (st : St)
    (xs : List Wasm.Core.Instr) : Option St :=
  Wasm.Core.Validate.checkSeq C st (Wasm.Core.InstrSeq.ofList xs)

@[simp] theorem checkList_nil (C : Wasm.Core.Context) (st : St) :
    checkList C st [] = some st := rfl

@[simp] theorem checkList_cons (C : Wasm.Core.Context) (st : St)
    (i : Wasm.Core.Instr) (is : List Wasm.Core.Instr) :
    checkList C st (i :: is) =
      (Wasm.Core.Validate.checkInstr C st i).bind
        (fun st' => checkList C st' is) := by
  unfold checkList
  rw [Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq]
  cases Wasm.Core.Validate.checkInstr C st i <;> rfl

theorem checkList_append (C : Wasm.Core.Context) (st : St) :
    ∀ (a b : List Wasm.Core.Instr),
      checkList C st (a ++ b) =
        (checkList C st a).bind (fun st' => checkList C st' b) := by
  intro a
  induction a generalizing st with
  | nil => intro b; rfl
  | cons i rest ih =>
      intro b
      rw [List.cons_append, checkList_cons, checkList_cons]
      cases h : Wasm.Core.Validate.checkInstr C st i <;> simp [ih]

def Neutral (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st ∨
    checkList C st xs = some st.unreach

def Preserves (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st

theorem neutral_nil (C : Wasm.Core.Context) : Neutral C [] := by
  intro st
  exact Or.inl rfl

theorem neutral_append {C : Wasm.Core.Context} {a b : List Wasm.Core.Instr}
    (ha : Neutral C a) (hb : Neutral C b) : Neutral C (a ++ b) := by
  intro st
  rw [checkList_append]
  rcases ha st with ha | ha
  · rw [ha]
    exact hb st
  · rw [ha]
    rcases hb st.unreach with hb | hb
    · exact Or.inr hb
    · exact Or.inr (by simpa [Wasm.Core.Validate.St.unreach] using hb)

theorem neutral_of_preserves {C : Wasm.Core.Context}
    {xs : List Wasm.Core.Instr} (h : Preserves C xs) : Neutral C xs := by
  intro st
  exact Or.inl (h st)

def numLocal (nt : Wasm.Core.NumType) : Wasm.Core.LocalType :=
  { init := .set, valtype := .num nt }

def HasNumLocal (C : Wasm.Core.Context) (i : Nat)
    (nt : Wasm.Core.NumType) : Prop :=
  C.locals[(coreU32 i).val]? = some (numLocal nt)

abbrev HasI32Local (C : Wasm.Core.Context) (i : Nat) : Prop :=
  HasNumLocal C i .i32

abbrev HasI64Local (C : Wasm.Core.Context) (i : Nat) : Prop :=
  HasNumLocal C i .i64

theorem checkList_constL (C : Wasm.Core.Context) (st : St) (n : Nat) :
    checkList C st [constL n] = some (st.push (.num .i64)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, constL,
    Wasm.Core.Num_.wf, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.pushs]

theorem checkList_localGet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (nt : Wasm.Core.NumType) (hi : HasNumLocal C i nt) :
    checkList C st [localGet i] = some (st.push (.num nt)) := by
  unfold HasNumLocal numLocal at hi
  rw [show checkList C st [localGet i] =
      (Wasm.Core.Validate.checkInstr C st (localGet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localGet, hi,
    Wasm.Core.Validate.ValType.nv, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.pushs]

theorem checkList_localSet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (nt : Wasm.Core.NumType) (hi : HasNumLocal C i nt) :
    checkList C (st.push (.num nt)) [localSet i] = some st := by
  unfold HasNumLocal numLocal at hi
  rw [show checkList C (st.push (.num nt)) [localSet i] =
      (Wasm.Core.Validate.checkInstr C (st.push (.num nt)) (localSet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localSet, hi,
    Wasm.Core.Validate.ValType.nv, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
    Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.subOf]

theorem checkList_app2 {C : Wasm.Core.Context} {st mid out : St}
    {a b : List Wasm.Core.Instr}
    (ha : checkList C st a = some mid)
    (hb : checkList C mid b = some out) :
    checkList C st (a ++ b) = some out := by
  rw [checkList_append, ha]
  exact hb

theorem checkList_setConstL (C : Wasm.Core.Context) (st : St) (i n : Nat)
    (hi : HasI64Local C i) :
    checkList C st [constL n, localSet i] = some st := by
  refine checkList_app2 (a := [constL n]) (b := [localSet i])
    (checkList_constL C st n) ?_
  exact checkList_localSet C st i .i64 hi

theorem preserves_setConstL {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI64Local C i) (n : Nat) :
    Preserves C [constL n, localSet i] := by
  intro st
  exact checkList_setConstL C st i n hi

theorem checkList_i64Binop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.BinopI) :
    checkList C ((st.push (.num .i64)).push (.num .i64))
      [.binop .i64 (.int op)] = some (st.push (.num .i64)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf,
    Wasm.Core.Binop.wf, Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_i64Relop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.RelopI) :
    checkList C ((st.push (.num .i64)).push (.num .i64))
      [.relop .i64 (.int op)] = some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf,
    Wasm.Core.Relop.wf, Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_wrapI64 (C : Wasm.Core.Context) (st : St) :
    checkList C (st.push (.num .i64)) [wrapI64] =
      some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, wrapI64,
    Wasm.Core.Cvtop.wf, Wasm.Core.NumType.size,
    Wasm.Core.NumType.toInn?, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
    Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.subOf]

end DirectTyping
end DirectValidation
end WasmGemmGnaf.GNAF
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectValidation

def gemmDefType : Wasm.Core.DefType :=
  .defd Wasm.Core.gemmTypeDef.rectype 0

def preContext : Wasm.Core.Context :=
  { types := [gemmDefType]
    funcs := [gemmDefType] }

def moduleContext (e : CompileEnv) : Wasm.Core.Context :=
  { preContext with
    mems :=
      [{ addr := .i32,
         lim := { min := coreU64 e.pages, max := some (coreU64 e.maxPages) } }] }

def funcContext (e : CompileEnv) : Wasm.Core.Context :=
  Wasm.Core.Context.append (moduleContext e)
    { locals :=
        [{ init := .set, valtype := .num .i32 },
         { init := .set, valtype := .num .i32 }] ++
          List.replicate e.declaredLocals
            { init := .set, valtype := .num .i64 }
      labels := [[.num .i32]]
      ret := some [.num .i32] }

theorem moduleOf_validate_probe (e : CompileEnv) (body : List Wasm.Core.Instr)
    (h : Wasm.Core.Validate.validate (moduleOf e body) = true) :
    Wasm.Core.validate (moduleOf e body) = true := h

theorem moduleOf_validate_reduce (e : CompileEnv) (body : List Wasm.Core.Instr) :
    Wasm.Core.validate (moduleOf e body) =
      Wasm.Core.Validate.validate (moduleOf e body) := rfl

theorem rollTypes_gemm :
    Wasm.Core.Validate.rollTypes [] [Wasm.Core.gemmTypeDef] = [gemmDefType] := by
  decide

theorem empty_extern_globals : Wasm.Core.ExternType.globals [] = [] := rfl
theorem empty_extern_tags : Wasm.Core.ExternType.tags [] = [] := rfl
theorem empty_extern_mems : Wasm.Core.ExternType.mems [] = [] := rfl
theorem empty_extern_tables : Wasm.Core.ExternType.tables [] = [] := rfl

theorem free_nonfuncs_memory (mem : Wasm.Core.Mem) :
    Wasm.Core.funcidxNonfuncs' [] [mem] [] [] = [] := by
  rfl

theorem contexts_moduleOf (e : CompileEnv) (body : List Wasm.Core.Instr) :
    Wasm.Core.Validate.Module.contexts (moduleOf e body) =
      some (preContext, moduleContext e) := by
  simp [Wasm.Core.Validate.Module.contexts, moduleOf,
    Wasm.Core.Validate.Module.importTypes, Wasm.Core.Validate.Module.typeContext,
    rollTypes_gemm, Wasm.Core.funcsXt, free_nonfuncs_memory,
    empty_extern_globals, empty_extern_tags, empty_extern_mems,
    empty_extern_tables,
    Wasm.Core.Validate.checkGlobals, Wasm.Core.Context.append,
    gemmDefType, preContext, moduleContext, coreU32]

theorem checkTypes_gemm :
    Wasm.Core.Validate.checkTypesOkA Wasm.Core.Context.empty
      [Wasm.Core.gemmTypeDef] = true := by
  decide

theorem checkLimits_pages (e : CompileEnv)
    (hpages : (coreU64 e.pages).val ≤ 2 ^ 16) :
    Wasm.Core.Validate.checkLimits
      { min := coreU64 e.pages, max := some (coreU64 e.maxPages) } (2 ^ 16) = true := by
  have hpages' : e.pages % 18446744073709551616 ≤ 65536 := by
    simpa [coreU64] using hpages
  simp [Wasm.Core.Validate.checkLimits, CompileEnv.maxPages, coreU64, hpages']

theorem funcTypeOf_gemmDefType :
    Wasm.Core.Validate.funcTypeOf gemmDefType =
      some ([.num .i32, .num .i32], [.num .i32]) := by
  decide

theorem checkFunc_moduleOf (e : CompileEnv) (body : List Wasm.Core.Instr) :
    Wasm.Core.Validate.checkFunc (moduleContext e)
      { typeidx := coreU32 0
        locals := List.replicate e.declaredLocals { valtype := .num .i64 }
        body := Wasm.Core.InstrSeq.ofList body } =
      Wasm.Core.Validate.checkExpr (funcContext e)
        (Wasm.Core.InstrSeq.ofList body) [.num .i32] := by
  simp [Wasm.Core.Validate.checkFunc, moduleContext, preContext, funcContext,
    funcTypeOf_gemmDefType, Wasm.Core.Validate.ValType.nv,
    Wasm.Core.Context.append, coreU32]

theorem memoryExportName_ne_gemmExportName :
    Wasm.Core.memoryExportName ≠ Wasm.Core.gemmExportName := by
  decide

theorem moduleOf_validate_goal (e : CompileEnv) (body : List Wasm.Core.Instr)
    (hwf : (moduleOf e body).wf = true)
    (hpages : (coreU64 e.pages).val ≤ 2 ^ 16)
    (hbody : Wasm.Core.Validate.checkExpr (funcContext e)
      (Wasm.Core.InstrSeq.ofList body) [.num .i32] = true) :
    Wasm.Core.validate (moduleOf e body) = true := by
  rw [Wasm.Core.validate, Wasm.Core.Validate.validate, hwf]
  simp only [Bool.true_and]
  rw [show (moduleOf e body).types = [Wasm.Core.gemmTypeDef] by rfl,
    checkTypes_gemm]
  simp only [Bool.true_and]
  rw [contexts_moduleOf]
  simp [moduleOf, checkLimits_pages e hpages,
    Wasm.Core.Validate.checkExternIdx, Wasm.Core.disjoint]
  rw [checkFunc_moduleOf e body, hbody]
  exact ⟨⟨by simp [moduleContext, preContext, coreU32],
      by simp [moduleContext, preContext, coreU32]⟩,
    memoryExportName_ne_gemmExportName⟩

namespace DirectTyping

/- The original all-i32 structural derivation is retained here as historical
text while the compiler uses mixed ABI/compiler locals.  The active proof
below is rebuilt over the exact source-checker support predicate. -/
/-

abbrev St := Wasm.Core.Validate.St

def checkList (C : Wasm.Core.Context) (st : St)
    (xs : List Wasm.Core.Instr) : Option St :=
  Wasm.Core.Validate.checkSeq C st (Wasm.Core.InstrSeq.ofList xs)

@[simp] theorem checkList_nil (C : Wasm.Core.Context) (st : St) :
    checkList C st [] = some st := rfl

@[simp] theorem checkList_cons (C : Wasm.Core.Context) (st : St)
    (i : Wasm.Core.Instr) (is : List Wasm.Core.Instr) :
    checkList C st (i :: is) =
      (Wasm.Core.Validate.checkInstr C st i).bind
        (fun st' => checkList C st' is) := by
  unfold checkList
  rw [Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq]
  cases Wasm.Core.Validate.checkInstr C st i <;> rfl

theorem checkList_append (C : Wasm.Core.Context) (st : St) :
    ∀ (a b : List Wasm.Core.Instr),
      checkList C st (a ++ b) =
        (checkList C st a).bind (fun st' => checkList C st' b) := by
  intro a
  induction a generalizing st with
  | nil => intro b; rfl
  | cons i rest ih =>
      intro b
      rw [List.cons_append, checkList_cons, checkList_cons]
      cases h : Wasm.Core.Validate.checkInstr C st i <;> simp [h, ih]

def Neutral (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st ∨
    checkList C st xs = some st.unreach

def Preserves (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some st

theorem neutral_nil (C : Wasm.Core.Context) : Neutral C [] := by
  intro st
  exact Or.inl rfl

theorem neutral_append {C : Wasm.Core.Context} {a b : List Wasm.Core.Instr}
    (ha : Neutral C a) (hb : Neutral C b) : Neutral C (a ++ b) := by
  intro st
  rw [checkList_append]
  rcases ha st with ha | ha
  · rw [ha]
    exact hb st
  · rw [ha]
    rcases hb st.unreach with hb | hb
    · exact Or.inr hb
    · exact Or.inr (by simpa [Wasm.Core.Validate.St.unreach] using hb)

theorem neutral_of_preserves {C : Wasm.Core.Context}
    {xs : List Wasm.Core.Instr}
    (h : Preserves C xs) : Neutral C xs := by
  intro st
  exact Or.inl (h st)

theorem preserves_nil (C : Wasm.Core.Context) : Preserves C [] := by
  intro st
  rfl

theorem preserves_append {C : Wasm.Core.Context} {a b : List Wasm.Core.Instr}
    (ha : Preserves C a) (hb : Preserves C b) : Preserves C (a ++ b) := by
  intro st
  rw [checkList_append, ha st]
  exact hb st

theorem preserves_assoc_of_left_right {C : Wasm.Core.Context}
    {a b c : List Wasm.Core.Instr} (ha : Preserves C a)
    (hbc : Preserves C (b ++ c)) : Preserves C ((a ++ b) ++ c) := by
  intro st
  rw [List.append_assoc, checkList_append, ha st]
  exact hbc st

def i32Local : Wasm.Core.LocalType :=
  { init := .set, valtype := .num .i32 }

def HasI32Local (C : Wasm.Core.Context) (i : Nat) : Prop :=
  C.locals[(coreU32 i).val]? = some i32Local

def HasWasm32MemoryZero (C : Wasm.Core.Context) : Prop :=
  ∃ limits, C.mems[(coreU32 0).val]? = some { addr := .i32, lim := limits }

def HasEmptyLabel (C : Wasm.Core.Context) (i : Nat) : Prop :=
  C.labels[(coreU32 i).val]? = some []

theorem checkList_constI (C : Wasm.Core.Context) (st : St) (n : Nat) :
    checkList C st [constI n] = some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, constI,
    Wasm.Core.Num_.wf,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.pushs]

theorem checkList_localGet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (hi : HasI32Local C i) :
    checkList C st [localGet i] = some (st.push (.num .i32)) := by
  unfold HasI32Local i32Local at hi
  rw [show checkList C st [localGet i] =
      (Wasm.Core.Validate.checkInstr C st (localGet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localGet, hi,
    Wasm.Core.Validate.ValType.nv,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.pushs]

theorem checkList_localSet (C : Wasm.Core.Context) (st : St) (i : Nat)
    (hi : HasI32Local C i) :
    checkList C (st.push (.num .i32)) [localSet i] = some st := by
  unfold HasI32Local i32Local at hi
  rw [show checkList C (st.push (.num .i32)) [localSet i] =
      (Wasm.Core.Validate.checkInstr C (st.push (.num .i32)) (localSet i)).bind
        (fun st' => checkList C st' []) by rw [checkList_cons]]
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, localSet, hi,
    Wasm.Core.Validate.ValType.nv,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_app2 {C : Wasm.Core.Context} {st mid out : St}
    {a b : List Wasm.Core.Instr}
    (ha : checkList C st a = some mid)
    (hb : checkList C mid b = some out) :
    checkList C st (a ++ b) = some out := by
  rw [checkList_append, ha]
  exact hb

theorem checkList_setConst (C : Wasm.Core.Context) (st : St) (i n : Nat)
    (hi : HasI32Local C i) :
    checkList C st [constI n, localSet i] = some st := by
  refine checkList_app2 (a := [constI n]) (b := [localSet i])
    (checkList_constI C st n) ?_
  exact checkList_localSet C st i hi

theorem checkList_unreachable (C : Wasm.Core.Context) (st : St) :
    checkList C st [Wasm.Core.Instr.unreachable] = some st.unreach := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr]

theorem checkList_i32Binop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.BinopI) :
    checkList C ((st.push (.num .i32)).push (.num .i32))
      [.binop .i32 (.int op)] = some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, Wasm.Core.Binop.wf,
    Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_i32Relop (C : Wasm.Core.Context) (st : St)
    (op : Wasm.Core.RelopI) :
    checkList C ((st.push (.num .i32)).push (.num .i32))
      [.relop .i32 (.int op)] = some (st.push (.num .i32)) := by
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, Wasm.Core.Relop.wf,
    Wasm.Core.NumType.toInn?,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf]

theorem checkList_loadW (C : Wasm.Core.Context) (st : St)
    (hmem : HasWasm32MemoryZero C) :
    checkList C (st.push (.num .i32)) [loadW] =
      some (st.push (.num .i32)) := by
  obtain ⟨limits, hmem⟩ := hmem
  have hmem0 : C.mems[0]? = some { addr := .i32, lim := limits } := by
    simpa [coreU32] using hmem
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, loadW, memArg,
    hmem0, Wasm.Core.NumType.size,
    Wasm.Core.AddrType.toValType, Wasm.Core.AddrType.toNumType,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf, coreU32]

theorem checkList_load8U (C : Wasm.Core.Context) (st : St)
    (hmem : HasWasm32MemoryZero C) :
    checkList C (st.push (.num .i32)) [load8U] =
      some (st.push (.num .i32)) := by
  obtain ⟨limits, hmem⟩ := hmem
  have hmem0 : C.mems[0]? = some { addr := .i32, lim := limits } := by
    simpa [coreU32] using hmem
  have hwf : Wasm.Core.LoadOp.wf .i32 { sz := .s8, sx := .u } = true := by
    decide
  have halign : 2 ^ (coreU32 0).val ≤ Wasm.Core.Sz.s8.toNat / 8 := by
    decide
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, load8U, byteMemArg,
    hmem0, hwf, halign, Wasm.Core.NumType.size, Wasm.Core.Sz.toNat,
    Wasm.Core.AddrType.toValType, Wasm.Core.AddrType.toNumType,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf, coreU32]

theorem checkList_storeW (C : Wasm.Core.Context) (st : St)
    (hmem : HasWasm32MemoryZero C) :
    checkList C ((st.push (.num .i32)).push (.num .i32)) [storeW] = some st := by
  obtain ⟨limits, hmem⟩ := hmem
  have hmem0 : C.mems[0]? = some { addr := .i32, lim := limits } := by
    simpa [coreU32] using hmem
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, storeW, memArg,
    hmem0, Wasm.Core.NumType.size,
    Wasm.Core.AddrType.toValType, Wasm.Core.AddrType.toNumType,
    Wasm.Core.Validate.St.pops, Wasm.Core.Validate.St.popE,
    Wasm.Core.Validate.St.push, Wasm.Core.Validate.St.pushs,
    Wasm.Core.Validate.subOf, coreU32]

theorem checkList_brIf (C : Wasm.Core.Context) (st : St) (i : Nat)
    (hi : HasEmptyLabel C i) :
    checkList C (st.push (.num .i32)) [brIf i] = some st := by
  unfold HasEmptyLabel at hi
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.instrType,
    Wasm.Core.Validate.instrTypeRaw, Wasm.Core.Instr.wf, brIf, hi,
    Wasm.Core.Validate.nvs, Wasm.Core.Validate.St.pops,
    Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
    Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.subOf]

theorem checkList_br (C : Wasm.Core.Context) (st : St) (i : Nat)
    (hi : HasEmptyLabel C i) :
    checkList C st [br i] = some st.unreach := by
  unfold HasEmptyLabel at hi
  simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
    Wasm.Core.Validate.checkInstr, br, hi, Wasm.Core.Validate.nvs,
    Wasm.Core.Validate.St.pops]

theorem neutral_br (C : Wasm.Core.Context) (i : Nat)
    (hi : HasEmptyLabel C i) : Neutral C [br i] := by
  intro st
  exact Or.inr (checkList_br C st i hi)

abbrev pushLabel (C : Wasm.Core.Context) : Wasm.Core.Context :=
  Wasm.Core.Context.pushLabel [] C

def freshSt : St := { poly := false, vals := [] }

theorem checkList_ifE (C : Wasm.Core.Context) (st : St)
    (a b : List Wasm.Core.Instr)
    (ha : Neutral (pushLabel C) a) (hb : Neutral (pushLabel C) b) :
    checkList C (st.push (.num .i32)) [ifE a b] = some st := by
  rcases ha freshSt with ha | ha <;>
    rcases hb freshSt with hb | hb <;>
    unfold checkList at ha hb <;>
    simp only [pushLabel, freshSt] at ha hb <;>
    simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
      Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.blockType, ifE,
      pushLabel, freshSt, ha, hb, Wasm.Core.Validate.St.pops,
      Wasm.Core.Validate.St.popE, Wasm.Core.Validate.St.push,
      Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.St.finish,
      Wasm.Core.Validate.St.unreach, Wasm.Core.Validate.subOf]

theorem checkList_blockE (C : Wasm.Core.Context) (st : St)
    (body : List Wasm.Core.Instr) (hbody : Neutral (pushLabel C) body) :
    checkList C st [blockE body] = some st := by
  rcases hbody freshSt with hbody | hbody <;>
    unfold checkList at hbody <;>
    simp only [pushLabel, freshSt] at hbody <;>
    simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
      Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.blockType, blockE,
      pushLabel, freshSt, hbody, Wasm.Core.Validate.St.pops,
      Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.St.finish,
      Wasm.Core.Validate.St.unreach]

theorem checkList_loopE (C : Wasm.Core.Context) (st : St)
    (body : List Wasm.Core.Instr) (hbody : Neutral (pushLabel C) body) :
    checkList C st [loopE body] = some st := by
  rcases hbody freshSt with hbody | hbody <;>
    unfold checkList at hbody <;>
    simp only [pushLabel, freshSt] at hbody <;>
    simp [checkList, Wasm.Core.InstrSeq.ofList, Wasm.Core.Validate.checkSeq,
      Wasm.Core.Validate.checkInstr, Wasm.Core.Validate.blockType, loopE,
      pushLabel, freshSt, hbody, Wasm.Core.Validate.St.pops,
      Wasm.Core.Validate.St.pushs, Wasm.Core.Validate.St.finish,
      Wasm.Core.Validate.St.unreach]

@[simp] theorem pushLabel_locals (C : Wasm.Core.Context) :
    (pushLabel C).locals = C.locals := rfl

@[simp] theorem pushLabel_mems (C : Wasm.Core.Context) :
    (pushLabel C).mems = C.mems := rfl

theorem HasI32Local.pushLabel {C : Wasm.Core.Context} {i : Nat}
    (h : HasI32Local C i) : HasI32Local (pushLabel C) i := by
  exact h

theorem HasWasm32MemoryZero.pushLabel {C : Wasm.Core.Context}
    (h : HasWasm32MemoryZero C) : HasWasm32MemoryZero (pushLabel C) := by
  exact h

theorem hasEmptyLabel_zero_pushLabel (C : Wasm.Core.Context) :
    HasEmptyLabel (pushLabel C) 0 := by
  simp [HasEmptyLabel, pushLabel, coreU32, Wasm.Core.Context.pushLabel]

theorem hasEmptyLabel_one_pushLabel_pushLabel (C : Wasm.Core.Context) :
    HasEmptyLabel (pushLabel (pushLabel C)) 1 := by
  simp [HasEmptyLabel, pushLabel, coreU32, Wasm.Core.Context.pushLabel]

def PushesI32 (C : Wasm.Core.Context) (xs : List Wasm.Core.Instr) : Prop :=
  ∀ st, checkList C st xs = some (st.push (.num .i32))

theorem pushes_constI (C : Wasm.Core.Context) (n : Nat) :
    PushesI32 C [constI n] := by
  intro st
  exact checkList_constI C st n

theorem pushes_localGet {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI32Local C i) : PushesI32 C [localGet i] := by
  intro st
  exact checkList_localGet C st i hi

theorem pushes_loadAt (C : Wasm.Core.Context) (hmem : HasWasm32MemoryZero C)
    (a : Nat) : PushesI32 C (loadAt a) := by
  intro st
  unfold loadAt
  refine checkList_app2 (checkList_constI C st a) ?_
  exact checkList_loadW C st hmem

theorem pushes_loadCellAt (C : Wasm.Core.Context)
    (hmem : HasWasm32MemoryZero C) (a : Nat) : PushesI32 C (loadCellAt a) := by
  intro st
  unfold loadCellAt
  refine checkList_app2 (checkList_constI C st a) ?_
  exact checkList_load8U C st hmem

theorem pushes_inputAddr {C : Wasm.Core.Context}
    (hptr : HasI32Local C 0) (offset : Nat) : PushesI32 C (inputAddr offset) := by
  intro st
  unfold inputAddr
  refine checkList_app2 (a := [localGet 0]) (b := [constI offset, addI])
    (checkList_localGet C st 0 hptr) ?_
  refine checkList_app2 (a := [constI offset]) (b := [addI])
    (checkList_constI C (st.push (.num .i32)) offset) ?_
  exact checkList_i32Binop C st .add

theorem pushes_loadInputCell {C : Wasm.Core.Context}
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) (offset : Nat) :
    PushesI32 C (loadInputCell offset) := by
  intro st
  unfold loadInputCell
  refine checkList_app2 (pushes_inputAddr hptr offset st) ?_
  exact checkList_load8U C st hmem

theorem pushes_cellCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) (i : Nat) :
    PushesI32 C (cellCode e i) := by
  exact pushes_loadInputCell hptr hmem (e.memAddr i)

theorem pushes_eqConst (C : Wasm.Core.Context) (n : Nat) :
    ∀ st : St, checkList C (st.push (.num .i32)) (eqConst n) =
      some (st.push (.num .i32)) := by
  intro st
  unfold eqConst
  refine checkList_app2 (checkList_constI C (st.push (.num .i32)) n) ?_
  exact checkList_i32Relop C st .eq

theorem preserves_setConst {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI32Local C i) (n : Nat) : Preserves C [constI n, localSet i] := by
  intro st
  exact checkList_setConst C st i n hi

theorem preserves_storeConst (C : Wasm.Core.Context)
    (hmem : HasWasm32MemoryZero C) (a v : Nat) :
    Preserves C [constI a, constI v, storeW] := by
  intro st
  refine checkList_app2 (a := [constI a]) (b := [constI v, storeW])
    (checkList_constI C st a) ?_
  refine checkList_app2 (a := [constI v]) (b := [storeW])
    (checkList_constI C (st.push (.num .i32)) v) ?_
  exact checkList_storeW C st hmem

theorem neutral_unreachable (C : Wasm.Core.Context) :
    Neutral C [Wasm.Core.Instr.unreachable] := by
  intro st
  exact Or.inr (checkList_unreachable C st)

theorem pushes_append_binop {C : Wasm.Core.Context}
    {a b : List Wasm.Core.Instr} (ha : PushesI32 C a) (hb : PushesI32 C b)
    (op : Wasm.Core.BinopI) :
    PushesI32 C (a ++ b ++ [.binop .i32 (.int op)]) := by
  intro st
  rw [List.append_assoc]
  refine checkList_app2 (a := a) (b := b ++ [.binop .i32 (.int op)])
    (ha st) ?_
  refine checkList_app2 (a := b) (b := [.binop .i32 (.int op)])
    (hb (st.push (.num .i32))) ?_
  exact checkList_i32Binop C st op

theorem pushes_append_relop {C : Wasm.Core.Context}
    {a b : List Wasm.Core.Instr} (ha : PushesI32 C a) (hb : PushesI32 C b)
    (op : Wasm.Core.RelopI) :
    PushesI32 C (a ++ b ++ [.relop .i32 (.int op)]) := by
  intro st
  rw [List.append_assoc]
  refine checkList_app2 (a := a) (b := b ++ [.relop .i32 (.int op)])
    (ha st) ?_
  refine checkList_app2 (a := b) (b := [.relop .i32 (.int op)])
    (hb (st.push (.num .i32))) ?_
  exact checkList_i32Relop C st op

theorem preserves_append_if {C : Wasm.Core.Context}
    {condition yes no : List Wasm.Core.Instr}
    (hc : PushesI32 C condition)
    (hy : Neutral (pushLabel C) yes) (hn : Neutral (pushLabel C) no) :
    Preserves C (condition ++ [ifE yes no]) := by
  intro st
  refine checkList_app2 (hc st) ?_
  exact checkList_ifE C st yes no hy hn

theorem pushes_u16Code (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) (i : Nat) :
    PushesI32 C (u16Code e i) := by
  unfold u16Code
  intro st
  refine checkList_app2 (a := cellCode e i)
    (b := [constI 256] ++ cellCode e (i + 1) ++ [mulI, addI])
    (pushes_cellCode e C hptr hmem i st) ?_
  refine checkList_app2 (a := [constI 256])
    (b := cellCode e (i + 1) ++ [mulI, addI])
    (checkList_constI C (st.push (.num .i32)) 256) ?_
  refine checkList_app2 (a := cellCode e (i + 1)) (b := [mulI, addI])
    (pushes_cellCode e C hptr hmem (i + 1)
      ((st.push (.num .i32)).push (.num .i32))) ?_
  refine checkList_app2 (a := [mulI]) (b := [addI])
    (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
  exact checkList_i32Binop C st .add

theorem pushes_headerOkCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    PushesI32 C (headerOkCode e) := by
  unfold headerOkCode
  let one (i n : Nat) : List Wasm.Core.Instr := cellCode e i ++ eqConst n
  have hone (i n : Nat) : PushesI32 C (one i n) := by
    intro st
    unfold one
    refine checkList_app2 (pushes_cellCode e C hptr hmem i st) ?_
    exact pushes_eqConst C n st
  have hcombine (a b : List Wasm.Core.Instr)
      (ha : PushesI32 C a) (hb : PushesI32 C b) :
      PushesI32 C (a ++ b ++ [andI]) :=
    pushes_append_binop ha hb .and
  have h01 := hcombine (one 0 87) (one 1 71) (hone 0 87) (hone 1 71)
  have h012 := hcombine ((one 0 87) ++ (one 1 71) ++ [andI]) (one 2 78)
    h01 (hone 2 78)
  have h0123 := hcombine
    (((one 0 87) ++ (one 1 71) ++ [andI]) ++ (one 2 78) ++ [andI])
    (one 3 71) h012 (hone 3 71)
  have hv : PushesI32 C (u16Code e 4 ++ eqConst 1) := by
    intro st
    refine checkList_app2 (pushes_u16Code e C hptr hmem 4 st) ?_
    exact pushes_eqConst C 1 st
  have hh : PushesI32 C (u16Code e 6 ++ eqConst headerSize) := by
    intro st
    refine checkList_app2 (pushes_u16Code e C hptr hmem 6 st) ?_
    exact pushes_eqConst C headerSize st
  have h0123v := hcombine
    ((((one 0 87) ++ (one 1 71) ++ [andI]) ++ (one 2 78) ++ [andI]) ++
      (one 3 71) ++ [andI])
    (u16Code e 4 ++ eqConst 1) h0123 hv
  have hall := hcombine
    (((((one 0 87) ++ (one 1 71) ++ [andI]) ++ (one 2 78) ++ [andI]) ++
      (one 3 71) ++ [andI]) ++ (u16Code e 4 ++ eqConst 1) ++ [andI])
    (u16Code e 6 ++ eqConst headerSize) h0123v hh
  simpa [one, List.append_assoc] using hall

theorem preserves_loopExitFixed {C : Wasm.Core.Context} {c n : Nat}
    (hc : HasI32Local C c) (hlabel : HasEmptyLabel C 1) :
    Preserves C [localGet c, constI n, geUI, brIf 1] := by
  intro st
  refine checkList_app2 (a := [localGet c])
    (b := [constI n, geUI, brIf 1]) (checkList_localGet C st c hc) ?_
  refine checkList_app2 (a := [constI n]) (b := [geUI, brIf 1])
    (checkList_constI C (st.push (.num .i32)) n) ?_
  refine checkList_app2 (a := [geUI]) (b := [brIf 1])
    (checkList_i32Relop C st (.ge .u)) ?_
  exact checkList_brIf C st 1 hlabel

theorem preserves_loopExitVar {C : Wasm.Core.Context} {c ext : Nat}
    (hc : HasI32Local C c) (hext : HasI32Local C ext)
    (hlabel : HasEmptyLabel C 1) :
    Preserves C [localGet c, localGet ext, geUI, brIf 1] := by
  intro st
  refine checkList_app2 (a := [localGet c])
    (b := [localGet ext, geUI, brIf 1]) (checkList_localGet C st c hc) ?_
  refine checkList_app2 (a := [localGet ext]) (b := [geUI, brIf 1])
    (checkList_localGet C (st.push (.num .i32)) ext hext) ?_
  refine checkList_app2 (a := [geUI]) (b := [brIf 1])
    (checkList_i32Relop C st (.ge .u)) ?_
  exact checkList_brIf C st 1 hlabel

theorem neutral_loopIncrementBreak {C : Wasm.Core.Context} {c : Nat}
    (hc : HasI32Local C c) (hlabel : HasEmptyLabel C 0) :
    Neutral C [localGet c, constI 1, addI, localSet c, br 0] := by
  have hprefix : Preserves C [localGet c, constI 1, addI, localSet c] := by
    intro st
    refine checkList_app2 (a := [localGet c])
      (b := [constI 1, addI, localSet c]) (checkList_localGet C st c hc) ?_
    refine checkList_app2 (a := [constI 1]) (b := [addI, localSet c])
      (checkList_constI C (st.push (.num .i32)) 1) ?_
    refine checkList_app2 (a := [addI]) (b := [localSet c])
      (checkList_i32Binop C st .add) ?_
    exact checkList_localSet C st c hc
  exact neutral_append (a := [localGet c, constI 1, addI, localSet c])
    (b := [br 0]) (neutral_of_preserves hprefix) (neutral_br C 0 hlabel)

theorem preserves_countLoop {C : Wasm.Core.Context} {c n : Nat}
    (hc : HasI32Local C c) {body : List Wasm.Core.Instr}
    (hbody : Neutral (pushLabel (pushLabel C)) body) :
    Preserves C (countLoop c n body) := by
  have hc2 : HasI32Local (pushLabel (pushLabel C)) c := hc.pushLabel.pushLabel
  have hexit : Preserves (pushLabel (pushLabel C))
      [localGet c, constI n, geUI, brIf 1] :=
    preserves_loopExitFixed hc2 (hasEmptyLabel_one_pushLabel_pushLabel C)
  have htail : Neutral (pushLabel (pushLabel C))
      [localGet c, constI 1, addI, localSet c, br 0] :=
    neutral_loopIncrementBreak hc2
      (hasEmptyLabel_zero_pushLabel (pushLabel C))
  have hloopBody : Neutral (pushLabel (pushLabel C))
      ([localGet c, constI n, geUI, brIf 1] ++ body ++
        [localGet c, constI 1, addI, localSet c, br 0]) :=
    neutral_append
      (neutral_append (neutral_of_preserves hexit) hbody) htail
  intro st
  unfold countLoop
  refine checkList_app2 (a := [constI 0, localSet c])
    (b := [blockE [loopE
      ([localGet c, constI n, geUI, brIf 1] ++ body ++
       [localGet c, constI 1, addI, localSet c, br 0])]])
    (checkList_setConst C st c 0 hc) ?_
  exact checkList_blockE C st _
    (neutral_of_preserves (fun inner =>
      checkList_loopE (pushLabel C) inner _ hloopBody))

theorem preserves_countLoopVar {C : Wasm.Core.Context} {c ext : Nat}
    (hc : HasI32Local C c) (hext : HasI32Local C ext)
    {body : List Wasm.Core.Instr}
    (hbody : Neutral (pushLabel (pushLabel C)) body) :
    Preserves C (countLoopVar c ext body) := by
  have hc2 : HasI32Local (pushLabel (pushLabel C)) c := hc.pushLabel.pushLabel
  have hext2 : HasI32Local (pushLabel (pushLabel C)) ext :=
    hext.pushLabel.pushLabel
  have hexit : Preserves (pushLabel (pushLabel C))
      [localGet c, localGet ext, geUI, brIf 1] :=
    preserves_loopExitVar hc2 hext2 (hasEmptyLabel_one_pushLabel_pushLabel C)
  have htail : Neutral (pushLabel (pushLabel C))
      [localGet c, constI 1, addI, localSet c, br 0] :=
    neutral_loopIncrementBreak hc2
      (hasEmptyLabel_zero_pushLabel (pushLabel C))
  have hloopBody : Neutral (pushLabel (pushLabel C))
      ([localGet c, localGet ext, geUI, brIf 1] ++ body ++
        [localGet c, constI 1, addI, localSet c, br 0]) :=
    neutral_append
      (neutral_append (neutral_of_preserves hexit) hbody) htail
  intro st
  unfold countLoopVar
  refine checkList_app2 (a := [constI 0, localSet c])
    (b := [blockE [loopE
      ([localGet c, localGet ext, geUI, brIf 1] ++ body ++
       [localGet c, constI 1, addI, localSet c, br 0])]])
    (checkList_setConst C st c 0 hc) ?_
  exact checkList_blockE C st _
    (neutral_of_preserves (fun inner =>
      checkList_loopE (pushLabel C) inner _ hloopBody))

theorem pushes_tagsKnownCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    PushesI32 C (tagsKnownCode e) := by
  unfold tagsKnownCode
  have hlt (i n : Nat) :
      PushesI32 C (cellCode e i ++ [constI n, ltUI]) := by
    intro st
    refine checkList_app2 (pushes_cellCode e C hptr hmem i st) ?_
    refine checkList_app2 (a := [constI n]) (b := [ltUI])
      (checkList_constI C (st.push (.num .i32)) n) ?_
    exact checkList_i32Relop C st (.lt .u)
  have h01 := pushes_append_binop (hlt 8 13) (hlt 11 13) .and
  have hall := pushes_append_binop h01 (hlt 12 4) .and
  simpa [List.append_assoc] using hall

theorem pushes_keyCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    PushesI32 C (keyCode e) := by
  unfold keyCode
  have hmul (i n : Nat) :
      PushesI32 C (cellCode e i ++ [constI n, mulI]) := by
    intro st
    refine checkList_app2 (pushes_cellCode e C hptr hmem i st) ?_
    refine checkList_app2 (a := [constI n]) (b := [mulI])
      (checkList_constI C (st.push (.num .i32)) n) ?_
    exact checkList_i32Binop C st .mul
  have hsum := pushes_append_binop (hmul 12 169) (hmul 8 13) .add
  have hall := pushes_append_binop hsum (pushes_cellCode e C hptr hmem 11) .add
  simpa [List.append_assoc] using hall

theorem preserves_keyChain (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) : ∀ ks : List Nat,
    ∀ st : St, checkList C (st.push (.num .i32)) (keyChain e ks) =
      some (st.push (.num .i32)) := by
  intro ks
  induction ks with
  | nil => intro st; rfl
  | cons k ks ih =>
      intro st
      rw [keyChain, List.append_assoc]
      refine checkList_app2 (a := keyCode e)
        (b := [constI k, eqI, orI] ++ keyChain e ks)
        (pushes_keyCode e C hptr hmem (st.push (.num .i32))) ?_
      refine checkList_app2 (a := [constI k])
        (b := [eqI, orI] ++ keyChain e ks)
        (checkList_constI C
          ((st.push (.num .i32)).push (.num .i32)) k) ?_
      refine checkList_app2 (a := [eqI]) (b := [orI] ++ keyChain e ks)
        (checkList_i32Relop C (st.push (.num .i32)) .eq) ?_
      refine checkList_app2 (a := [orI]) (b := keyChain e ks)
        (checkList_i32Binop C st .or) ?_
      exact ih st

theorem pushes_compatCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    PushesI32 C (compatCode e) := by
  intro st
  unfold compatCode
  refine checkList_app2 (checkList_constI C st 0) ?_
  exact preserves_keyChain e C hptr hmem compatibleKeys st

theorem preserves_dispatchOn {C : Wasm.Core.Context} {t k : Nat}
    (ht : HasI32Local C t) {a b : List Wasm.Core.Instr}
    (ha : Neutral (pushLabel C) a) (hb : Neutral (pushLabel C) b) :
    Preserves C (dispatchOn t k a b) := by
  have hcondition : PushesI32 C [localGet t, constI k, eqI] := by
    intro st
    refine checkList_app2 (a := [localGet t]) (b := [constI k, eqI])
      (checkList_localGet C st t ht) ?_
    refine checkList_app2 (a := [constI k]) (b := [eqI])
      (checkList_constI C (st.push (.num .i32)) k) ?_
    exact checkList_i32Relop C st .eq
  simpa [dispatchOn] using preserves_append_if hcondition ha hb

theorem preserves_classifyCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C)
    (t : Nat) (ht : HasI32Local C t) :
    Preserves C (classifyCode e t) := by
  unfold classifyCode
  split
  · exact preserves_setConst ht 1
  · have ht1 := ht.pushLabel
    have hm1 := hmem.pushLabel
    have hcompatIf : Preserves (pushLabel (pushLabel C))
        (compatCode e ++ [ifE [] [constI 1, localSet t]]) := by
      exact preserves_append_if
        (pushes_compatCode e _ hptr.pushLabel.pushLabel hm1.pushLabel)
        (neutral_nil _) (neutral_of_preserves (preserves_setConst ht1.pushLabel 1))
    have htagsIf : Preserves (pushLabel C)
        (tagsKnownCode e ++
          [ifE (compatCode e ++ [ifE [] [constI 1, localSet t]])
            [constI 2, localSet t]]) := by
      exact preserves_append_if (pushes_tagsKnownCode e _ hptr.pushLabel hm1)
        (neutral_of_preserves hcompatIf)
        (neutral_of_preserves (preserves_setConst ht1.pushLabel 2))
    have hheaderIf : Preserves C
        (headerOkCode e ++
          [ifE
            (tagsKnownCode e ++
              [ifE (compatCode e ++ [ifE [] [constI 1, localSet t]])
                [constI 2, localSet t]])
            [constI 1, localSet t]]) := by
      exact preserves_append_if (pushes_headerOkCode e C hptr hmem)
        (neutral_of_preserves htagsIf)
        (neutral_of_preserves (preserves_setConst ht1 1))
    exact preserves_assoc_of_left_right
      (a := [constI (if e.memWords ≤ maxRawExtent then 0 else 3), localSet t])
      (b := headerOkCode e)
      (c := [ifE
        (tagsKnownCode e ++
          [ifE (compatCode e ++ [ifE [] [constI 1, localSet t]])
            [constI 2, localSet t]])
        [constI 1, localSet t]])
      (preserves_setConst ht
        (if e.memWords ≤ maxRawExtent then 0 else 3)) hheaderIf

theorem preserves_tableStores (C : Wasm.Core.Context)
    (hmem : HasWasm32MemoryZero C) (base : Nat) : ∀ (vs : List Nat) (j : Nat),
    Preserves C (tableStores base j vs) := by
  intro vs
  induction vs with
  | nil => intro j; exact preserves_nil C
  | cons v vs ih =>
      intro j
      exact preserves_append (preserves_storeConst C hmem (base + 4 * j) v)
        (ih (j + 1))

theorem preserves_widthChain (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    ∀ ks : List ScalarKind,
    ∀ st : St, checkList C (st.push (.num .i32)) (widthChain e ks) =
      some (st.push (.num .i32)) := by
  intro ks
  induction ks with
  | nil => intro st; rfl
  | cons k ks ih =>
      intro st
      rw [widthChain, List.append_assoc]
      refine checkList_app2 (a := cellCode e 8)
        (b := [constI k.tag, eqI, constI k.byteWidth, mulI, addI] ++
          widthChain e ks)
        (pushes_cellCode e C hptr hmem 8 (st.push (.num .i32))) ?_
      refine checkList_app2 (a := [constI k.tag])
        (b := [eqI, constI k.byteWidth, mulI, addI] ++ widthChain e ks)
        (checkList_constI C
          ((st.push (.num .i32)).push (.num .i32)) k.tag) ?_
      refine checkList_app2 (a := [eqI])
        (b := [constI k.byteWidth, mulI, addI] ++ widthChain e ks)
        (checkList_i32Relop C (st.push (.num .i32)) .eq) ?_
      refine checkList_app2 (a := [constI k.byteWidth])
        (b := [mulI, addI] ++ widthChain e ks)
        (checkList_constI C
          ((st.push (.num .i32)).push (.num .i32)) k.byteWidth) ?_
      refine checkList_app2 (a := [mulI])
        (b := [addI] ++ widthChain e ks)
        (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
      refine checkList_app2 (a := [addI]) (b := widthChain e ks)
        (checkList_i32Binop C st .add) ?_
      exact ih st

theorem pushes_widthCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) :
    PushesI32 C (widthCode e) := by
  intro st
  unfold widthCode
  refine checkList_app2 (checkList_constI C st 0) ?_
  exact preserves_widthChain e C hptr hmem ScalarKind.all st

theorem preserves_layoutTestCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C) (t field cls : Nat)
    (ht : HasI32Local C t) : Preserves C (layoutTestCode e t field cls) := by
  have hcondition : PushesI32 C
      (u16Code e field ++ (widthCode e ++ [eqI])) := by
    intro st
    refine checkList_app2 (pushes_u16Code e C hptr hmem field st) ?_
    refine checkList_app2 (a := widthCode e) (b := [eqI])
      (pushes_widthCode e C hptr hmem (st.push (.num .i32))) ?_
    exact checkList_i32Relop C st .eq
  have hif : Preserves C
      ((u16Code e field ++ (widthCode e ++ [eqI])) ++
        [ifE [constI cls, localSet t] []]) :=
    preserves_append_if hcondition
      (neutral_of_preserves (preserves_setConst ht.pushLabel cls))
      (neutral_nil _)
  simpa only [layoutTestCode, List.append_assoc] using hif

theorem preserves_layoutCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hptr : HasI32Local C 0) (hmem : HasWasm32MemoryZero C)
    (t : Nat) (ht : HasI32Local C t) :
    Preserves C (layoutCode e t) := by
  unfold layoutCode
  exact preserves_append (preserves_setConst ht 2)
    (preserves_append (preserves_layoutTestCode e C hptr hmem t 56 1 ht)
      (preserves_layoutTestCode e C hptr hmem t 64 0 ht))

theorem pushes_condCode (e : CompileEnv) (C : Wasm.Core.Context)
    (hmem : HasWasm32MemoryZero C) (hstatus : HasI32Local C e.statusLocal)
    (scr : Nat) (co : Cond)
    (hco : ∀ r, co.readsReg = some r → HasI32Local C (e.regLocal r)) :
    PushesI32 C (condCode e scr co) := by
  cases co with
  | statusIs status =>
      intro st
      unfold condCode
      refine checkList_app2 (pushes_localGet hstatus st) ?_
      exact pushes_eqConst C status.code st
  | regEq r value =>
      intro st
      unfold condCode
      refine checkList_app2 (a := [localGet (e.regLocal r)])
        (b := [constI value, eqI])
        (checkList_localGet C st _ (hco r rfl)) ?_
      refine checkList_app2 (a := [constI value]) (b := [eqI])
        (checkList_constI C (st.push (.num .i32)) value) ?_
      exact checkList_i32Relop C st .eq
  | regLt r value =>
      intro st
      unfold condCode
      refine checkList_app2 (a := [localGet (e.regLocal r)])
        (b := [constI value, ltUI])
        (checkList_localGet C st _ (hco r rfl)) ?_
      refine checkList_app2 (a := [constI value]) (b := [ltUI])
        (checkList_constI C (st.push (.num .i32)) value) ?_
      exact checkList_i32Relop C st (.lt .u)
  | scratchAtLeast bytes =>
      exact pushes_constI C (if bytes ≤ scr then 1 else 0)

theorem preserves_store_of_pushes {C : Wasm.Core.Context}
    (hmem : HasWasm32MemoryZero C) {address value : List Wasm.Core.Instr}
    (ha : PushesI32 C address) (hv : PushesI32 C value) :
    Preserves C (address ++ value ++ [storeW]) := by
  intro st
  rw [List.append_assoc]
  refine checkList_app2 (ha st) ?_
  refine checkList_app2 (hv (st.push (.num .i32))) ?_
  exact checkList_storeW C st hmem

theorem pushes_load_of_pushes {C : Wasm.Core.Context}
    (hmem : HasWasm32MemoryZero C) {address : List Wasm.Core.Instr}
    (ha : PushesI32 C address) : PushesI32 C (address ++ [loadW]) := by
  intro st
  refine checkList_app2 (ha st) ?_
  exact checkList_loadW C st hmem

theorem preserves_set_of_pushes {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI32Local C i) {value : List Wasm.Core.Instr}
    (hv : PushesI32 C value) : Preserves C (value ++ [localSet i]) := by
  intro st
  refine checkList_app2 (hv st) ?_
  exact checkList_localSet C st i hi

theorem preserves_copyLocal {C : Wasm.Core.Context} {src dst : Nat}
    (hsrc : HasI32Local C src) (hdst : HasI32Local C dst) :
    Preserves C [localGet src, localSet dst] := by
  intro st
  refine checkList_app2 (a := [localGet src]) (b := [localSet dst])
    (checkList_localGet C st src hsrc) ?_
  exact checkList_localSet C st dst hdst

theorem pushes_affine1 {C : Wasm.Core.Context} (base scale index : Nat)
    (hindex : HasI32Local C index) :
    PushesI32 C
      [constI base, localGet index, constI scale, mulI, addI] := by
  intro st
  refine checkList_app2 (a := [constI base])
    (b := [localGet index, constI scale, mulI, addI])
    (checkList_constI C st base) ?_
  refine checkList_app2 (a := [localGet index])
    (b := [constI scale, mulI, addI])
    (checkList_localGet C (st.push (.num .i32)) index hindex) ?_
  refine checkList_app2 (a := [constI scale]) (b := [mulI, addI])
    (checkList_constI C
      ((st.push (.num .i32)).push (.num .i32)) scale) ?_
  refine checkList_app2 (a := [mulI]) (b := [addI])
    (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
  exact checkList_i32Binop C st .add

/-- The ABI-relative variant of `pushes_affine1`: the base address is the
public pointer parameter plus a source-region offset. -/
theorem pushes_inputAffine1 {C : Wasm.Core.Context}
    (hptr : HasI32Local C 0) (base scale index : Nat)
    (hindex : HasI32Local C index) :
    PushesI32 C
      (inputAddr base ++ [localGet index, constI scale, mulI, addI]) := by
  intro st
  refine checkList_app2 (a := inputAddr base)
    (b := [localGet index, constI scale, mulI, addI])
    (pushes_inputAddr hptr base st) ?_
  refine checkList_app2 (a := [localGet index])
    (b := [constI scale, mulI, addI])
    (checkList_localGet C (st.push (.num .i32)) index hindex) ?_
  refine checkList_app2 (a := [constI scale]) (b := [mulI, addI])
    (checkList_constI C
      ((st.push (.num .i32)).push (.num .i32)) scale) ?_
  refine checkList_app2 (a := [mulI]) (b := [addI])
    (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
  exact checkList_i32Binop C st .add

theorem pushes_affine3 {C : Wasm.Core.Context}
    (base i0 s0 i1 s1 i2 s2 : Nat)
    (hi0 : HasI32Local C i0) (hi1 : HasI32Local C i1)
    (hi2 : HasI32Local C i2) :
    PushesI32 C
      [constI base,
       localGet i0, constI s0, mulI, addI,
       localGet i1, constI s1, mulI, addI,
       localGet i2, constI s2, mulI, addI] := by
  have h0 := pushes_affine1 base s0 i0 hi0
  have h1 : ∀ st : St,
      checkList C (st.push (.num .i32))
        [localGet i1, constI s1, mulI, addI] =
        some (st.push (.num .i32)) := by
    intro st
    refine checkList_app2 (a := [localGet i1])
      (b := [constI s1, mulI, addI])
      (checkList_localGet C (st.push (.num .i32)) i1 hi1) ?_
    refine checkList_app2 (a := [constI s1]) (b := [mulI, addI])
      (checkList_constI C
        ((st.push (.num .i32)).push (.num .i32)) s1) ?_
    refine checkList_app2 (a := [mulI]) (b := [addI])
      (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
    exact checkList_i32Binop C st .add
  have h2 : ∀ st : St,
      checkList C (st.push (.num .i32))
        [localGet i2, constI s2, mulI, addI] =
        some (st.push (.num .i32)) := by
    intro st
    refine checkList_app2 (a := [localGet i2])
      (b := [constI s2, mulI, addI])
      (checkList_localGet C (st.push (.num .i32)) i2 hi2) ?_
    refine checkList_app2 (a := [constI s2]) (b := [mulI, addI])
      (checkList_constI C
        ((st.push (.num .i32)).push (.num .i32)) s2) ?_
    refine checkList_app2 (a := [mulI]) (b := [addI])
      (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
    exact checkList_i32Binop C st .add
  intro st
  refine checkList_app2 (a :=
      [constI base, localGet i0, constI s0, mulI, addI])
    (b := [localGet i1, constI s1, mulI, addI,
      localGet i2, constI s2, mulI, addI]) (h0 st) ?_
  refine checkList_app2 (a := [localGet i1, constI s1, mulI, addI])
    (b := [localGet i2, constI s2, mulI, addI]) (h1 st) ?_
  exact h2 st

/-- The ABI-relative variant of `pushes_affine3`. -/
theorem pushes_inputAffine3 {C : Wasm.Core.Context}
    (hptr : HasI32Local C 0) (base i0 s0 i1 s1 i2 s2 : Nat)
    (hi0 : HasI32Local C i0) (hi1 : HasI32Local C i1)
    (hi2 : HasI32Local C i2) :
    PushesI32 C
      (inputAddr base ++
       [localGet i0, constI s0, mulI, addI,
        localGet i1, constI s1, mulI, addI,
        localGet i2, constI s2, mulI, addI]) := by
  have h0 := pushes_inputAffine1 hptr base s0 i0 hi0
  have h1 : ∀ st : St,
      checkList C (st.push (.num .i32))
        [localGet i1, constI s1, mulI, addI] =
        some (st.push (.num .i32)) := by
    intro st
    refine checkList_app2 (a := [localGet i1])
      (b := [constI s1, mulI, addI])
      (checkList_localGet C (st.push (.num .i32)) i1 hi1) ?_
    refine checkList_app2 (a := [constI s1]) (b := [mulI, addI])
      (checkList_constI C
        ((st.push (.num .i32)).push (.num .i32)) s1) ?_
    refine checkList_app2 (a := [mulI]) (b := [addI])
      (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
    exact checkList_i32Binop C st .add
  have h2 : ∀ st : St,
      checkList C (st.push (.num .i32))
        [localGet i2, constI s2, mulI, addI] =
        some (st.push (.num .i32)) := by
    intro st
    refine checkList_app2 (a := [localGet i2])
      (b := [constI s2, mulI, addI])
      (checkList_localGet C (st.push (.num .i32)) i2 hi2) ?_
    refine checkList_app2 (a := [constI s2]) (b := [mulI, addI])
      (checkList_constI C
        ((st.push (.num .i32)).push (.num .i32)) s2) ?_
    refine checkList_app2 (a := [mulI]) (b := [addI])
      (checkList_i32Binop C (st.push (.num .i32)) .mul) ?_
    exact checkList_i32Binop C st .add
  intro st
  refine checkList_app2
    (a := inputAddr base ++ [localGet i0, constI s0, mulI, addI])
    (b := [localGet i1, constI s1, mulI, addI,
      localGet i2, constI s2, mulI, addI]) (h0 st) ?_
  refine checkList_app2 (a := [localGet i1, constI s1, mulI, addI])
    (b := [localGet i2, constI s2, mulI, addI]) (h1 st) ?_
  exact h2 st

def LocalsThrough (C : Wasm.Core.Context) (n : Nat) : Prop :=
  ∀ i, i < n → HasI32Local C i

theorem LocalsThrough.mono {C : Wasm.Core.Context} {m n : Nat}
    (h : LocalsThrough C n) (hm : m ≤ n) : LocalsThrough C m := by
  intro i hi
  exact h i (Nat.lt_of_lt_of_le hi hm)

theorem LocalsThrough.pushLabel {C : Wasm.Core.Context} {n : Nat}
    (h : LocalsThrough C n) : LocalsThrough (pushLabel C) n := by
  intro i hi
  exact (h i hi).pushLabel

/-! ### Structural typing of every emitted plan body -/

theorem code_neutral {s : Sig} {p : Plan} {t : Sig} (hp : HasType s p t) :
    ∀ (e : CompileEnv) (d scr : Nat) (C : Wasm.Core.Context),
      e.regs = s.regs →
      LocalsThrough C (2 + e.regs + d + p.depth + 2) →
      HasWasm32MemoryZero C → Neutral C (code e d scr p) := by
  induction hp with
  | nop s =>
      intro e d scr C hreg hloc hmem
      exact neutral_nil C
  | @seq s u t a b ha hb iha ihb =>
      intro e d scr C hreg hloc hmem
      have hu : u.regs = s.regs := (hasType_fixed_resources ha).1
      have hda : a.depth ≤ Nat.max a.depth b.depth := Nat.le_max_left _ _
      have hdb : b.depth ≤ Nat.max a.depth b.depth := Nat.le_max_right _ _
      have hla : LocalsThrough C (2 + e.regs + d + a.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      have hlb : LocalsThrough C (2 + e.regs + d + b.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact neutral_append (iha e d scr C hreg hla hmem)
        (ihb e d scr C (by omega) hlb hmem)
  | @classifyRaw s t v i u x hv hi hu hx ihv ihi ihu ihx =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have branchLoc (q : Plan)
          (hq : q.depth ≤ Nat.max (Nat.max v.depth i.depth)
            (Nat.max u.depth x.depth)) :
          LocalsThrough (pushLabel C) (2 + e.regs + d + q.depth + 2) := by
        apply (hloc.mono ?_).pushLabel
        simp only [Plan.depth]
        omega
      have hvn := ihv e d scr (pushLabel C) hreg
        (branchLoc v (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)))
        hmem.pushLabel
      have hin := ihi e d scr (pushLabel (pushLabel C)) hreg
        ((branchLoc i
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))).pushLabel)
        hmem.pushLabel.pushLabel
      have hun := ihu e d scr (pushLabel (pushLabel (pushLabel C))) hreg
        (((branchLoc u
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))).pushLabel).pushLabel)
        hmem.pushLabel.pushLabel.pushLabel
      have hxn := ihx e d scr (pushLabel (pushLabel (pushLabel C))) hreg
        (((branchLoc x
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))).pushLabel).pushLabel)
        hmem.pushLabel.pushLabel.pushLabel
      have hthird : Preserves (pushLabel (pushLabel C))
          (dispatchOn (e.tempLocal d) 2 (code e d scr u) (code e d scr x)) :=
        preserves_dispatchOn hT.pushLabel.pushLabel hun hxn
      have hsecond : Preserves (pushLabel C)
          (dispatchOn (e.tempLocal d) 1 (code e d scr i)
            (dispatchOn (e.tempLocal d) 2 (code e d scr u) (code e d scr x))) :=
        preserves_dispatchOn hT.pushLabel hin (neutral_of_preserves hthird)
      have hfirst : Preserves C
          (dispatchOn (e.tempLocal d) 0 (code e d scr v)
            (dispatchOn (e.tempLocal d) 1 (code e d scr i)
              (dispatchOn (e.tempLocal d) 2 (code e d scr u) (code e d scr x)))) :=
        preserves_dispatchOn hT hvn (neutral_of_preserves hsecond)
      simp only [code]
      exact neutral_of_preserves
        (preserves_append
          (preserves_classifyCode e C (hloc 0 (by omega)) hmem _ hT) hfirst)
  | @dispatchLayout s t r c g hr hc hg ihr ihc ihg =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have branchLoc (q : Plan)
          (hq : q.depth ≤ Nat.max r.depth (Nat.max c.depth g.depth)) :
          LocalsThrough (pushLabel C) (2 + e.regs + d + q.depth + 2) := by
        apply (hloc.mono ?_).pushLabel
        simp only [Plan.depth]
        omega
      have hrn := ihr e d scr (pushLabel C) hreg
        (branchLoc r (Nat.le_max_left _ _)) hmem.pushLabel
      have hcn := ihc e d scr (pushLabel (pushLabel C)) hreg
        ((branchLoc c
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))).pushLabel)
        hmem.pushLabel.pushLabel
      have hgn := ihg e d scr (pushLabel (pushLabel C)) hreg
        ((branchLoc g
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))).pushLabel)
        hmem.pushLabel.pushLabel
      have hsecond : Preserves (pushLabel C)
          (dispatchOn (e.tempLocal d) 1 (code e d scr c) (code e d scr g)) :=
        preserves_dispatchOn hT.pushLabel hcn hgn
      have hfirst : Preserves C
          (dispatchOn (e.tempLocal d) 0 (code e d scr r)
            (dispatchOn (e.tempLocal d) 1 (code e d scr c) (code e d scr g))) :=
        preserves_dispatchOn hT hrn (neutral_of_preserves hsecond)
      simp only [code]
      exact neutral_of_preserves
        (preserves_append
          (preserves_layoutCode e C (hloc 0 (by omega)) hmem _ hT) hfirst)
  | @branch s t co yes no hco hy hn ihy ihn =>
      intro e d scr C hreg hloc hmem
      have hdy : yes.depth ≤ Nat.max yes.depth no.depth := Nat.le_max_left _ _
      have hdn : no.depth ≤ Nat.max yes.depth no.depth := Nat.le_max_right _ _
      have hyes : LocalsThrough (pushLabel C)
          (2 + e.regs + d + yes.depth + 2) := by
        apply (hloc.mono ?_).pushLabel
        simp only [Plan.depth]
        omega
      have hno : LocalsThrough (pushLabel C)
          (2 + e.regs + d + no.depth + 2) := by
        apply (hloc.mono ?_).pushLabel
        simp only [Plan.depth]
        omega
      have hcond : PushesI32 C (condCode e scr co) := by
        have hstatus : HasI32Local C e.statusLocal := by
          apply hloc
          unfold CompileEnv.statusLocal
          omega
        apply pushes_condCode e C hmem hstatus scr co
        intro r hr
        apply hloc
        unfold CompileEnv.regLocal
        have : r < s.regs := by
          cases co with
          | statusIs _ => simp [Cond.readsReg] at hr
          | regEq r' value => cases hr; exact of_decide_eq_true hco
          | regLt r' value => cases hr; exact of_decide_eq_true hco
          | scratchAtLeast _ => simp [Cond.readsReg] at hr
        omega
      simp only [code]
      exact neutral_of_preserves (preserves_append_if hcond
        (ihy e d scr (pushLabel C) hreg hyes hmem.pushLabel)
        (ihn e d scr (pushLabel C) hreg hno hmem.pushLabel))
  | @pack s src dst map width hsrc hdst hw =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      let D := pushLabel (pushLabel C)
      have hTd : HasI32Local D (e.tempLocal d) := hT.pushLabel.pushLabel
      have hptrd : HasI32Local D 0 :=
        (hloc 0 (by omega)).pushLabel.pushLabel
      have hmd : HasWasm32MemoryZero D := hmem.pushLabel.pushLabel
      have ha : PushesI32 D
          [constI (e.scratchAddr dst.base), localGet (e.tempLocal d),
            constI 4, mulI, addI] :=
        pushes_affine1 _ _ _ hTd
      have hv : PushesI32 D
          (inputAddr (e.memAddr (src.base + map.c0)) ++
            [localGet (e.tempLocal d), constI (4 * map.cb), mulI, addI,
              loadW]) := by
        exact pushes_load_of_pushes hmd
          (pushes_inputAffine1 hptrd _ _ _ hTd)
      have hbody : Preserves D
          ([constI (e.scratchAddr dst.base), localGet (e.tempLocal d),
            constI 4, mulI, addI] ++
           (inputAddr (e.memAddr (src.base + map.c0)) ++
            [localGet (e.tempLocal d), constI (4 * map.cb), mulI, addI,
              loadW]) ++ [storeW]) :=
        preserves_store_of_pushes hmd ha hv
      simp only [code]
      exact neutral_of_preserves (preserves_countLoop hT
        (neutral_of_preserves hbody))
  | @unpack s src dst map width hsrc hdst hw =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      let D := pushLabel (pushLabel C)
      have hTd : HasI32Local D (e.tempLocal d) := hT.pushLabel.pushLabel
      have hptrd : HasI32Local D 0 :=
        (hloc 0 (by omega)).pushLabel.pushLabel
      have hmd : HasWasm32MemoryZero D := hmem.pushLabel.pushLabel
      have ha : PushesI32 D
          (inputAddr (e.memAddr dst.base) ++
            [localGet (e.tempLocal d), constI 4, mulI, addI]) :=
        pushes_inputAffine1 hptrd _ _ _ hTd
      have hv : PushesI32 D
          [constI (e.scratchAddr (src.base + map.c0)), localGet (e.tempLocal d),
            constI (4 * map.cb), mulI, addI, loadW] := by
        exact pushes_load_of_pushes hmd
          (pushes_affine1 _ _ _ hTd)
      have hbody : Preserves D
          ((inputAddr (e.memAddr dst.base) ++
            [localGet (e.tempLocal d), constI 4, mulI, addI]) ++
           [constI (e.scratchAddr (src.base + map.c0)), localGet (e.tempLocal d),
            constI (4 * map.cb), mulI, addI, loadW] ++ [storeW]) :=
        preserves_store_of_pushes hmd ha hv
      simp only [code]
      exact neutral_of_preserves (preserves_countLoop hT
        (neutral_of_preserves hbody))
  | @storeReg s dst map width src hdst hw hsrc hregs =>
      intro e d scr C hreg hloc hmem
      have h0 : HasI32Local C (e.regLocal 0) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have h1 : HasI32Local C (e.regLocal 1) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have h2 : HasI32Local C (e.regLocal 2) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have hv : HasI32Local C (e.regLocal src) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have haddress := pushes_inputAffine3 (hloc 0 (by omega))
        (e.memAddr (dst.base + map.c0))
        (e.regLocal 0) map.cb
        (e.regLocal 1) map.ci
        (e.regLocal 2) map.cj h0 h1 h2
      have hstore := preserves_store_of_pushes hmem haddress
        (pushes_localGet hv)
      simp only [code]
      exact neutral_of_preserves hstore
  | @loadReg s dst src map width hsrc hw hdst hregs =>
      intro e d scr C hreg hloc hmem
      have h0 : HasI32Local C (e.regLocal 0) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have h1 : HasI32Local C (e.regLocal 1) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have h2 : HasI32Local C (e.regLocal 2) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have hd : HasI32Local C (e.regLocal dst) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have haddress := pushes_inputAffine3 (hloc 0 (by omega))
        (e.memAddr (src.base + map.c0))
        (e.regLocal 0) map.cb
        (e.regLocal 1) map.ci
        (e.regLocal 2) map.cj h0 h1 h2
      have hvalue := pushes_load_of_pushes hmem haddress
      have hset := preserves_set_of_pushes hd hvalue
      simp only [code]
      exact neutral_of_preserves hset
  | @loopNest s axis body hix hbody ih =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have hR : HasI32Local (pushLabel (pushLabel C))
          (e.regLocal axis.indexReg) := by
        apply (hloc.pushLabel.pushLabel)
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      have hbodyLoc : LocalsThrough (pushLabel (pushLabel C))
          (2 + e.regs + (d + 1) + body.depth + 2) := by
        apply (hloc.mono ?_).pushLabel.pushLabel
        simp only [Plan.depth]
        omega
      have hcompiled := ih e (d + 1) scr (pushLabel (pushLabel C)) hreg
        hbodyLoc hmem.pushLabel.pushLabel
      have hloopBody := neutral_append
        (neutral_of_preserves
          (preserves_copyLocal hT.pushLabel.pushLabel hR)) hcompiled
      simp only [code]
      exact neutral_of_preserves (preserves_countLoop hT hloopBody)
  | @loopReg s ir er map body hir her hbody ih =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have hE : HasI32Local C (e.regLocal er) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      have hI : HasI32Local (pushLabel (pushLabel C)) (e.regLocal ir) := by
        apply hloc.pushLabel.pushLabel
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      have hbodyLoc : LocalsThrough (pushLabel (pushLabel C))
          (2 + e.regs + (d + 1) + body.depth + 2) := by
        apply (hloc.mono ?_).pushLabel.pushLabel
        simp only [Plan.depth]
        omega
      have hcompiled := ih e (d + 1) scr (pushLabel (pushLabel C)) hreg
        hbodyLoc hmem.pushLabel.pushLabel
      have hloopBody := neutral_append
        (neutral_of_preserves
          (preserves_copyLocal hT.pushLabel.pushLabel hI)) hcompiled
      simp only [code]
      exact neutral_of_preserves (preserves_countLoopVar hT hE hloopBody)
  | @tiled s order tiling extents body hpos hbody ih =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have hbodyLoc : LocalsThrough (pushLabel (pushLabel C))
          (2 + e.regs + (d + 1) + body.depth + 2) := by
        apply (hloc.mono ?_).pushLabel.pushLabel
        simp only [Plan.depth]
        omega
      have hcompiled := ih e (d + 1) scr (pushLabel (pushLabel C)) hreg
        hbodyLoc hmem.pushLabel.pushLabel
      have hprefix : Neutral (pushLabel (pushLabel C))
          (if 0 < e.regs then
            [localGet (e.tempLocal d), localSet (e.regLocal 0)] else []) := by
        split
        · have hR : HasI32Local (pushLabel (pushLabel C))
              (e.regLocal 0) := by
            apply hloc.pushLabel.pushLabel
            unfold CompileEnv.regLocal
            simp only [Plan.depth]
            omega
          exact neutral_of_preserves
            (preserves_copyLocal hT.pushLabel.pushLabel hR)
        · exact neutral_nil _
      simp only [code]
      exact neutral_of_preserves (preserves_countLoop hT
        (neutral_append hprefix hcompiled))
  | @reduce s contract acc lhs rhs hacc hcompat hlhs hrhs =>
      intro e d scr C hreg hloc hmem
      have hT : HasI32Local C (e.tempLocal d) := by
        apply hloc
        unfold CompileEnv.tempLocal
        simp only [Plan.depth]
        omega
      have hA : HasI32Local (pushLabel (pushLabel C))
          (e.regLocal acc) := by
        apply hloc.pushLabel.pushLabel
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      have hTd := hT.pushLabel.pushLabel
      have hmd := hmem.pushLabel.pushLabel
      simp only [code]
      split
      · let D := pushLabel (pushLabel C)
        have hptrd : HasI32Local D 0 :=
          (hloc 0 (by omega)).pushLabel.pushLabel
        have hleft : PushesI32 D
            (inputAddr (e.memAddr lhs.base) ++
              [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) :=
          pushes_load_of_pushes hmd
            (pushes_inputAffine1 hptrd _ _ _ hTd)
        have hright : PushesI32 D
            (inputAddr (e.memAddr rhs.base) ++
              [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) :=
          pushes_load_of_pushes hmd
            (pushes_inputAffine1 hptrd _ _ _ hTd)
        have hreduceBody : Preserves D
            ([localGet (e.regLocal acc)] ++
             (inputAddr (e.memAddr lhs.base) ++
               [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) ++
             (inputAddr (e.memAddr rhs.base) ++
               [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) ++
             [mulI, addI, localSet (e.regLocal acc)]) := by
          intro st
          refine checkList_app2 (a := [localGet (e.regLocal acc)])
            (b :=
              (inputAddr (e.memAddr lhs.base) ++
                [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) ++
              (inputAddr (e.memAddr rhs.base) ++
                [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) ++
              [mulI, addI, localSet (e.regLocal acc)])
            (pushes_localGet hA st) ?_
          refine checkList_app2
            (a := inputAddr (e.memAddr lhs.base) ++
              [localGet (e.tempLocal d), constI 4, mulI, addI, loadW])
            (b :=
              (inputAddr (e.memAddr rhs.base) ++
                [localGet (e.tempLocal d), constI 4, mulI, addI, loadW]) ++
              [mulI, addI, localSet (e.regLocal acc)])
            (hleft (st.push (.num .i32))) ?_
          refine checkList_app2
            (a := inputAddr (e.memAddr rhs.base) ++
              [localGet (e.tempLocal d), constI 4, mulI, addI, loadW])
            (b := [mulI, addI, localSet (e.regLocal acc)])
            (hright ((st.push (.num .i32)).push (.num .i32))) ?_
          refine checkList_app2 (a := [mulI])
            (b := [addI, localSet (e.regLocal acc)])
            (checkList_i32Binop D (st.push (.num .i32)) .mul) ?_
          refine checkList_app2 (a := [addI])
            (b := [localSet (e.regLocal acc)])
            (checkList_i32Binop D st .add) ?_
          exact checkList_localSet D st _ hA
        exact neutral_of_preserves
          (preserves_countLoop hT (neutral_of_preserves hreduceBody))
      · exact neutral_unreachable C
  | @allocScratch s t bytes body hbody ih =>
      intro e d scr C hreg hloc hmem
      have hbodyLoc : LocalsThrough C
          (2 + e.regs + d + body.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact ih e d (scr + bytes) C hreg hbodyLoc hmem
  | @setReg s dst value hdst =>
      intro e d scr C hreg hloc hmem
      have hD : HasI32Local C (e.regLocal dst) := by
        apply hloc
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      simp only [code]
      exact neutral_of_preserves (preserves_setConst hD value)
  | @scalarOp s op dst lhs rhs hdst hlhs hrhs =>
      intro e d scr C hreg hloc hmem
      have hD : HasI32Local C (e.regLocal dst) := by
        apply hloc
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      have hL : HasI32Local C (e.regLocal lhs) := by
        apply hloc
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      have hR : HasI32Local C (e.regLocal rhs) := by
        apply hloc
        unfold CompileEnv.regLocal
        simp only [Plan.depth]
        omega
      simp only [code]
      cases op with
      | add =>
          apply neutral_of_preserves
          intro st
          refine checkList_app2 (a := [localGet (e.regLocal lhs)])
            (b := [localGet (e.regLocal rhs),
              addI,
              localSet (e.regLocal dst)])
            (checkList_localGet C st _ hL) ?_
          refine checkList_app2 (a := [localGet (e.regLocal rhs)])
            (checkList_localGet C (st.push (.num .i32)) _ hR) ?_
          refine checkList_app2 (a := [addI])
            (checkList_i32Binop C st .add) ?_
          exact checkList_localSet C st _ hD
      | mul =>
          apply neutral_of_preserves
          intro st
          refine checkList_app2 (a := [localGet (e.regLocal lhs)])
            (b := [localGet (e.regLocal rhs), mulI,
              localSet (e.regLocal dst)])
            (checkList_localGet C st _ hL) ?_
          refine checkList_app2 (a := [localGet (e.regLocal rhs)])
            (checkList_localGet C (st.push (.num .i32)) _ hR) ?_
          refine checkList_app2 (a := [mulI])
            (checkList_i32Binop C st .mul) ?_
          exact checkList_localSet C st _ hD
      | sub =>
          have hcondition : PushesI32 C
              [localGet (e.regLocal lhs), localGet (e.regLocal rhs), geUI] := by
            intro st
            refine checkList_app2 (checkList_localGet C st _ hL) ?_
            refine checkList_app2
              (checkList_localGet C (st.push (.num .i32)) _ hR) ?_
            exact checkList_i32Relop C st (.ge .u)
          have hyes : Neutral (pushLabel C)
              [localGet (e.regLocal lhs), localGet (e.regLocal rhs), subI,
                localSet (e.regLocal dst)] := by
            apply neutral_of_preserves
            intro st
            refine checkList_app2 (checkList_localGet _ st _ hL.pushLabel) ?_
            refine checkList_app2
              (checkList_localGet _ (st.push (.num .i32)) _ hR.pushLabel) ?_
            refine checkList_app2 (checkList_i32Binop _ st .sub) ?_
            exact checkList_localSet _ st _ hD.pushLabel
          have hno : Neutral (pushLabel C)
              [constI 0, localSet (e.regLocal dst)] :=
            neutral_of_preserves (preserves_setConst hD.pushLabel 0)
          exact neutral_of_preserves
            (preserves_append_if hcondition hyes hno)
      | max =>
          have hcondition : PushesI32 C
              [localGet (e.regLocal lhs), localGet (e.regLocal rhs),
                gtUI] := by
            intro st
            refine checkList_app2 (checkList_localGet C st _ hL) ?_
            refine checkList_app2
              (checkList_localGet C (st.push (.num .i32)) _ hR) ?_
            exact checkList_i32Relop C st (.gt .u)
          have hyes : Neutral (pushLabel C)
              [localGet (e.regLocal lhs), localSet (e.regLocal dst)] :=
            neutral_of_preserves (preserves_copyLocal hL.pushLabel hD.pushLabel)
          have hno : Neutral (pushLabel C)
              [localGet (e.regLocal rhs), localSet (e.regLocal dst)] :=
            neutral_of_preserves (preserves_copyLocal hR.pushLabel hD.pushLabel)
          exact neutral_of_preserves
            (preserves_append_if hcondition hyes hno)
      | min =>
          have hcondition : PushesI32 C
              [localGet (e.regLocal lhs), localGet (e.regLocal rhs),
                ltUI] := by
            intro st
            refine checkList_app2 (checkList_localGet C st _ hL) ?_
            refine checkList_app2
              (checkList_localGet C (st.push (.num .i32)) _ hR) ?_
            exact checkList_i32Relop C st (.lt .u)
          have hyes : Neutral (pushLabel C)
              [localGet (e.regLocal lhs), localSet (e.regLocal dst)] :=
            neutral_of_preserves (preserves_copyLocal hL.pushLabel hD.pushLabel)
          have hno : Neutral (pushLabel C)
              [localGet (e.regLocal rhs), localSet (e.regLocal dst)] :=
            neutral_of_preserves (preserves_copyLocal hR.pushLabel hD.pushLabel)
          exact neutral_of_preserves
            (preserves_append_if hcondition hyes hno)
  | @vectorOp s op lanes dst lhs rhs hlanes hmax hdst hlhs hrhs =>
      intro e d scr C hreg hloc hmem
      simp only [code]
      exact neutral_unreachable C
  | @emitTable s index data hindex =>
      intro e d scr C hreg hloc hmem
      simp only [code]
      exact neutral_of_preserves
        (preserves_tableStores C hmem _ data 0)
  | @tableLoad s table index dst htable hdst =>
      intro e d scr C hreg hloc hmem
      have hD : HasI32Local C (e.regLocal dst) := by
        apply hloc
        unfold CompileEnv.regLocal
        omega
      simp only [code]
      exact neutral_of_preserves
        (preserves_set_of_pushes hD (pushes_loadAt C hmem _))
  | setStatus s status =>
      intro e d scr C hreg hloc hmem
      have hstatus : HasI32Local C e.statusLocal := by
        apply hloc
        unfold CompileEnv.statusLocal
        omega
      simp only [code]
      exact neutral_of_preserves
        (preserves_setConst hstatus status.code)
  | @buildOutput s src hstatus hsrc =>
      intro e d scr C hreg hloc hmem
      simp only [code]
      exact neutral_nil C
  | @opaqueProcess s t spec body hsteps hbytes hbody ih =>
      intro e d scr C hreg hloc hmem
      have hbodyLoc : LocalsThrough C
          (2 + e.regs + d + body.depth + 2) := by
        apply hloc.mono
        simp only [Plan.depth]
        omega
      simp only [code]
      exact ih e d scr C hreg hbodyLoc hmem

theorem bodyCode_checkExpr {s : Sig} {p : Plan} {t : Sig}
    (hp : HasType s p t) (e : CompileEnv) (scr : Nat)
    (C : Wasm.Core.Context) (hreg : e.regs = s.regs)
    (hloc : LocalsThrough C (2 + e.regs + p.depth + 2))
    (hmem : HasWasm32MemoryZero C) :
    Wasm.Core.Validate.checkExpr C
      (Wasm.Core.InstrSeq.ofList (bodyCode e scr p)) [.num .i32] = true := by
  have hcode := code_neutral hp e 0 scr C hreg (by simpa using hloc) hmem
  have hstatus : HasI32Local C e.statusLocal := by
    apply hloc
    unfold CompileEnv.statusLocal
    omega
  have hload := pushes_localGet hstatus
  unfold Wasm.Core.Validate.checkExpr
  change (match checkList C (Wasm.Core.Validate.St.mk false [])
      (bodyCode e scr p) with
    | some st => st.finish [.num .i32]
    | none => false) = true
  unfold bodyCode
  rw [checkList_append]
  rcases hcode (Wasm.Core.Validate.St.mk false []) with hcode | hcode <;>
    rw [hcode] <;> simp only [Option.bind_some]
  · rw [hload (Wasm.Core.Validate.St.mk false [])]
    rfl
  · rw [hload (Wasm.Core.Validate.St.mk false []).unreach]
    rfl

theorem funcContext_localsThrough (e : CompileEnv)
    (hidx : 2 + e.declaredLocals ≤ 2 ^ 32) :
    LocalsThrough (DirectValidation.funcContext e) (2 + e.declaredLocals) := by
  intro i hi
  have hi32 : i < 2 ^ 32 := Nat.lt_of_lt_of_le hi hidx
  unfold HasI32Local
  rw [coreU32_exact i hi32]
  cases i with
  | zero =>
      simp [DirectValidation.funcContext, DirectValidation.moduleContext,
        DirectValidation.preContext, Wasm.Core.Context.append, i32Local]
  | succ i =>
      cases i with
      | zero =>
          simp [DirectValidation.funcContext, DirectValidation.moduleContext,
            DirectValidation.preContext, Wasm.Core.Context.append, i32Local]
      | succ i =>
          have hir : i < e.declaredLocals := by omega
          simp [DirectValidation.funcContext, DirectValidation.moduleContext,
            DirectValidation.preContext, Wasm.Core.Context.append, i32Local,
            List.getElem?_replicate, hir]

theorem funcContext_memory (e : CompileEnv) :
    HasWasm32MemoryZero (DirectValidation.funcContext e) := by
  refine ⟨{ min := coreU64 e.pages, max := some (coreU64 e.pages) }, ?_⟩
  simp [HasWasm32MemoryZero, DirectValidation.funcContext,
    DirectValidation.moduleContext, DirectValidation.preContext,
    Wasm.Core.Context.append, coreU32]

theorem envOf_pages (s : Sig) (p : Plan) :
    (envOf s p).pages = 65536 := rfl

theorem compileCore_validates {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.validate (compileCore checked) = true := by
  let e := envOf checked.inputSig checked.plan
  let body := bodyCode e checked.inputSig.scratch checked.plan
  have represented :
      max checked.plan.coreImmediateCeiling
          (max (3 + checked.inputSig.regs + checked.plan.depth)
            (checked.plan.coreLayoutBytes checked.inputSig)) < 2 ^ 32 ∧
        checked.plan.coreLayoutPages checked.inputSig ≤ P.body.maxPages ∧
        checked.plan.coreLayoutPages checked.inputSig ≤ G.body.resources.maxPages ∧
        checked.inputSig.regs + checked.plan.depth + 2 ≤
          P.body.limits.maxLocals ∧
        checked.plan.coreModuleByteBudget < 2 ^ 32 ∧
        checked.plan.coreModuleByteBudget ≤ P.body.limits.maxModuleBytes ∧
        checked.plan.charges.dataBytes ≤ G.body.resources.maxInvocationBytes ∧
        checked.inputSig.tables * checked.plan.tableWords ≤
          G.body.resources.maxTableElements := by
    exact of_decide_eq_true checked.coreRepresentable
  have hlocalMax :
      3 + checked.inputSig.regs + checked.plan.depth < 2 ^ 32 :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      represented.1
  have hlocalCount : 2 + e.declaredLocals ≤ 2 ^ 32 := by
    simp only [e, envOf, CompileEnv.declaredLocals]
    omega
  have hlocals : LocalsThrough (DirectValidation.funcContext e)
      (2 + e.regs + checked.plan.depth + 2) := by
    have h := funcContext_localsThrough e hlocalCount
    have heq : 2 + e.declaredLocals =
        2 + e.regs + checked.plan.depth + 2 := by
      simp only [e, envOf, CompileEnv.declaredLocals]
      omega
    rw [← heq]
    exact h
  have hbody : Wasm.Core.Validate.checkExpr (DirectValidation.funcContext e)
      (Wasm.Core.InstrSeq.ofList body) [.num .i32] = true := by
    exact bodyCode_checkExpr checked.typed e checked.inputSig.scratch
      (DirectValidation.funcContext e) (by rfl) hlocals
      (funcContext_memory e)
  have hePages : e.pages ≤ 2 ^ 16 := by
    simp only [e, envOf_pages]
    decide
  have hePages64 : e.pages < 2 ^ 64 := by omega
  have hpages : (coreU64 e.pages).val ≤ 2 ^ 16 := by
    simpa [coreU64, Nat.mod_eq_of_lt hePages64] using hePages
  have hwf : (compileCore checked).wf = true := by
    have h := Wasm.Module.core_wf (compile checked)
    simpa only [compile_core] using h
  unfold compileCore
  change Wasm.Core.validate (moduleOf e body) = true
  exact DirectValidation.moduleOf_validate_goal e body hwf hpages hbody

-/

theorem checkList_statusResult {C : Wasm.Core.Context} {i : Nat}
    (hi : HasI64Local C i) (st : St) :
    checkList C st [localGet i, wrapI64] =
      some (st.push (.num .i32)) := by
  refine checkList_app2 (a := [localGet i]) (b := [wrapI64])
    (checkList_localGet C st i .i64 hi) ?_
  exact checkList_wrapI64 C st

theorem bodyCode_checkExpr_supported
    {P : Wasm.Profile} {G : Gemm.Problem P}
    {s : Sig} {p : Plan} {t : Sig}
    (hp : HasType s p t) (hs : p.coreSupported P G s = true)
    (e : CompileEnv) (scr : Nat) (C : Wasm.Core.Context)
    (hreg : e.regs = s.regs)
    (hloc : Locals64Through C (2 + e.regs + p.depth + 2)) :
    Wasm.Core.Validate.checkExpr C
      (Wasm.Core.InstrSeq.ofList (bodyCode e scr p)) [.num .i32] = true := by
  have hcode := code_neutral_supported hp e 0 scr C hreg
    (by simpa using hloc) hs
  have hstatus : HasI64Local C e.statusLocal := by
    apply hloc
    · unfold CompileEnv.statusLocal
      omega
    · unfold CompileEnv.statusLocal
      omega
  unfold Wasm.Core.Validate.checkExpr
  change (match checkList C (Wasm.Core.Validate.St.mk false [])
      (bodyCode e scr p) with
    | some st => st.finish [.num .i32]
    | none => false) = true
  unfold bodyCode
  rw [checkList_append]
  rcases hcode (Wasm.Core.Validate.St.mk false []) with hcode | hcode <;>
    rw [hcode] <;> simp only [Option.bind_some]
  · rw [checkList_statusResult hstatus (Wasm.Core.Validate.St.mk false [])]
    rfl
  · rw [checkList_statusResult hstatus
      (Wasm.Core.Validate.St.mk false []).unreach]
    rfl

theorem funcContext_locals64Through (e : CompileEnv)
    (hidx : 2 + e.declaredLocals ≤ 2 ^ 32) :
    Locals64Through (DirectValidation.funcContext e)
      (2 + e.declaredLocals) := by
  intro i hlo hi
  have hi32 : i < 2 ^ 32 := Nat.lt_of_lt_of_le hi hidx
  unfold HasI64Local HasNumLocal
  rw [coreU32_exact i hi32]
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => omega
      | succ i =>
          have hir : i < e.declaredLocals := by omega
          simp [DirectValidation.funcContext, DirectValidation.moduleContext,
            DirectValidation.preContext, Wasm.Core.Context.append, numLocal,
            List.getElem?_replicate, hir]

theorem envOf_pages_eq (s : Sig) (p : Plan) :
    (envOf s p).pages = p.coreLayoutPages s := by
  unfold CompileEnv.pages Plan.coreLayoutPages Wasm.pagesFor
  congr 1
  simp [CompileEnv.byteSize, CompileEnv.outLenAddr, CompileEnv.statusAddr,
    CompileEnv.tableBase, CompileEnv.scratchBase, envOf,
    Plan.coreLayoutBytes]
  omega

theorem compileCore_validates {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) :
    Wasm.Core.validate (compileCore checked) = true := by
  let e := envOf checked.inputSig checked.plan
  let body := bodyCode e checked.inputSig.scratch checked.plan
  have represented :
      max checked.plan.coreImmediateCeiling
          (max (3 + checked.inputSig.regs + checked.plan.depth)
            (checked.plan.coreLayoutBytes checked.inputSig)) < 2 ^ 32 ∧
        checked.plan.coreLayoutPages checked.inputSig ≤ P.body.maxPages ∧
        checked.plan.coreLayoutPages checked.inputSig ≤
          G.body.resources.maxPages ∧
        checked.inputSig.regs + checked.plan.depth + 2 ≤
          P.body.limits.maxLocals ∧
        checked.plan.coreModuleByteBudget < 2 ^ 32 ∧
        checked.plan.coreModuleByteBudget ≤ P.body.limits.maxModuleBytes ∧
        checked.plan.charges.dataBytes ≤
          G.body.resources.maxInvocationBytes ∧
        checked.inputSig.tables * checked.plan.tableWords ≤
          G.body.resources.maxTableElements := by
    exact of_decide_eq_true checked.coreRepresentable
  have hlocalMax :
      3 + checked.inputSig.regs + checked.plan.depth < 2 ^ 32 :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      represented.1
  have hlocalCount : 2 + e.declaredLocals ≤ 2 ^ 32 := by
    simp only [e, envOf, CompileEnv.declaredLocals]
    omega
  have hlocals : Locals64Through (DirectValidation.funcContext e)
      (2 + e.regs + checked.plan.depth + 2) := by
    have h := funcContext_locals64Through e hlocalCount
    have heq : 2 + e.declaredLocals =
        2 + e.regs + checked.plan.depth + 2 := by
      simp only [e, envOf, CompileEnv.declaredLocals]
      omega
    rw [← heq]
    exact h
  have hbody : Wasm.Core.Validate.checkExpr (DirectValidation.funcContext e)
      (Wasm.Core.InstrSeq.ofList body) [.num .i32] = true := by
    exact bodyCode_checkExpr_supported checked.typed checked.coreSupported e
      checked.inputSig.scratch (DirectValidation.funcContext e) (by rfl) hlocals
  have hePages : e.pages ≤ 2 ^ 16 := by
    rw [show e.pages = checked.plan.coreLayoutPages checked.inputSig by
      exact envOf_pages_eq checked.inputSig checked.plan]
    rw [show 2 ^ 16 = P.body.maxPages by
      symm
      exact P.lawful.maxPages]
    exact represented.2.1
  have hePages64 : e.pages < 2 ^ 64 := by omega
  have hpages : (coreU64 e.pages).val ≤ 2 ^ 16 := by
    simpa [coreU64, Nat.mod_eq_of_lt hePages64] using hePages
  have hwf : (compileCore checked).wf = true := by
    have h := Wasm.Module.core_wf (compile checked)
    simpa only [compile_core] using h
  unfold compileCore
  change Wasm.Core.validate (moduleOf e body) = true
  exact DirectValidation.moduleOf_validate_goal e body hwf hpages hbody

end DirectTyping

end DirectValidation
end WasmGemmGnaf.GNAF
