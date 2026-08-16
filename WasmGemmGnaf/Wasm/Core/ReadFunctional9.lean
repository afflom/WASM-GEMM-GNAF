import WasmGemmGnaf.Wasm.Core.ReadFunctional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem Step_readA.target_functional_group9
    {state : State} {rule : ReadRule} {source left right : List AdminInstr}
    (hgroup : rule.functionalGroup = 9)
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
  case vloadVal.vloadVal.vloadVal =>
    apply vbytes_v128_injective
    solve_by_elim [Eq.trans, Eq.symm]
  case vloadPackVal.vloadPackVal.vloadPackVal =>
    have hsize := sourcesEqual.2.1.1
    have hcount := sourcesEqual.2.1.2.1
    have hsigned := sourcesEqual.2.1.2.2
    cases hsize
    cases hcount
    cases hsigned
    apply vloadPack_output_injective <;> assumption
  case vloadSplatVal.vloadSplatVal.vloadSplatVal =>
    have hsize := sourcesEqual.2.1
    cases hsize
    apply vloadSplat_output_injective <;> assumption
  all_goals try omega
  all_goals try (apply Subtype.ext; omega)

end WasmGemmGnaf.Wasm.Core.Exec
