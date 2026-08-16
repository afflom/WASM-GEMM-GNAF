import WasmGemmGnaf.Wasm.Core.RuntimePureProgress

set_option autoImplicit false

/-!
# Static head inversion for amended instruction sequences

Sequence subsumption and stack framing can hide the outermost `seq`
constructor.  These lemmas recover the genuine source `Instr_okA` judgment at
a nonempty head without changing the validation relation or assuming a runtime
transition.
-/

namespace WasmGemmGnaf.Wasm.Core

private theorem Instrs_okA.exists_head_typing_general {context : Context}
    {instructions : List Instr} {sequenceType : InstrType}
    (typed : Instrs_okA context instructions sequenceType) :
    ∀ {head : Instr} {tail : List Instr},
      instructions = head :: tail →
        ∃ headType, Instr_okA context head headType := by
  induction typed using Instrs_okA.rec
      (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case empty =>
    intro head tail heq
    simp at heq
  case seq =>
    intro head tail heq
    simp only [List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨_, by assumption⟩

/-- Every nonempty amended-typed sequence has an amended typing derivation for
its first source instruction. -/
theorem Instrs_okA.exists_head_typing {context : Context} {head : Instr}
    {tail : List Instr} {sequenceType : InstrType}
    (typed : Instrs_okA context (head :: tail) sequenceType) :
    ∃ headType, Instr_okA context head headType := by
  exact typed.exists_head_typing_general rfl

/-- Syntax well-formedness of the active instruction follows from the actual
head typing derivation, including through sequence subsumption/framing. -/
theorem Instrs_okA.head_wf {context : Context} {head : Instr}
    {tail : List Instr} {sequenceType : InstrType}
    (typed : Instrs_okA context (head :: tail) sequenceType) :
    head.wf = true := by
  obtain ⟨headType, headTyped⟩ := typed.exists_head_typing
  exact headTyped.wf_of

end WasmGemmGnaf.Wasm.Core
