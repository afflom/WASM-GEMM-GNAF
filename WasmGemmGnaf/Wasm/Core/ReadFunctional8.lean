import WasmGemmGnaf.Wasm.Core.ReadFunctional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem Step_readA.target_functional_group8
    {state : State} {rule : ReadRule} {source left right : List AdminInstr}
    (hgroup : rule.functionalGroup = 8)
    (hl : Step_readA state rule source left)
    (hr : Step_readA state rule source right) : left = right := by
  obtain ⟨leftSource, leftTarget, hleftSource, hleftTarget, leftProof⟩ :=
    hl.unindexSourceTarget
  obtain ⟨rightSource, rightTarget, hrightSource, hrightTarget, rightProof⟩ :=
    hr.unindexSourceTarget
  have sourcesEqual : leftSource = rightSource := hleftSource.trans hrightSource.symm
  rw [← hleftTarget, ← hrightTarget]
  clear hl hr hleftSource hrightSource hleftTarget hrightTarget source left right
  cases rule <;> simp [ReadRule.functionalGroup] at hgroup
  all_goals cases leftProof <;> cases rightProof
  all_goals have splitSourcesEqual := congrArg splitVals sourcesEqual
  all_goals snapshot_equalities
  all_goals simp_all [constI32_eq_iff, constAddr_eq_iff, Val.toAdmin_eq_iff,
    splitVals_append]
  all_goals restore_equalities
  all_goals simp_all [constI32_eq_iff, constAddr_eq_iff, Val.toAdmin_eq_iff]
  case loadNumVal.loadNumVal.loadNumVal =>
    have htype := sourcesEqual.2.1
    cases htype
    apply heq_of_eq
    apply nbytes_injective_of_wf <;> simp_all [ByteSolvedNumWfFor]
  case loadPackVal.loadPackVal.loadPackVal =>
    have hinn := Inn.toNumType_injective sourcesEqual.2.1
    cases hinn
    have hsize := sourcesEqual.2.2.1.1
    have hsigned := sourcesEqual.2.2.1.2
    cases hsize
    cases hsigned
    apply loadPack_output_injective <;> assumption
  all_goals try omega
  all_goals try (apply Subtype.ext; omega)

end WasmGemmGnaf.Wasm.Core.Exec
