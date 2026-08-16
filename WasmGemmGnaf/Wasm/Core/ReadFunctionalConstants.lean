import WasmGemmGnaf.Wasm.Core.ReadFunctional5
import WasmGemmGnaf.Wasm.Core.ReadFunctional14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem Step_readA.globalGet_target_functional
    {state : State} {source left right : List AdminInstr}
    (hl : Step_readA state .globalGet source left)
    (hr : Step_readA state .globalGet source right) : left = right :=
  Step_readA.target_functional_group5 rfl hl hr

theorem Step_readA.refFunc_target_functional
    {state : State} {source left right : List AdminInstr}
    (hl : Step_readA state .refFunc source left)
    (hr : Step_readA state .refFunc source right) : left = right := by
  obtain ⟨leftSource, leftTarget, hleftSource, hleftTarget, leftProof⟩ :=
    hl.unindexSourceTarget
  obtain ⟨rightSource, rightTarget, hrightSource, hrightTarget, rightProof⟩ :=
    hr.unindexSourceTarget
  have sourcesEqual : leftSource = rightSource := hleftSource.trans hrightSource.symm
  rw [← hleftTarget, ← hrightTarget]
  clear hl hr hleftSource hrightSource hleftTarget hrightTarget source left right
  cases leftProof <;> cases rightProof
  all_goals simp_all [constI32_eq_iff, constAddr_eq_iff, Val.toAdmin_eq_iff]

theorem Step_readA.structNewDefault_target_functional
    {state : State} {source left right : List AdminInstr}
    (hl : Step_readA state .structNewDefault source left)
    (hr : Step_readA state .structNewDefault source right) : left = right :=
  Step_readA.target_functional_group14 rfl hl hr

theorem Step_readA.arrayNewDefault_target_functional
    {state : State} {source left right : List AdminInstr}
    (hl : Step_readA state .arrayNewDefault source left)
    (hr : Step_readA state .arrayNewDefault source right) : left = right :=
  Step_readA.target_functional_group14 rfl hl hr

end WasmGemmGnaf.Wasm.Core.Exec
