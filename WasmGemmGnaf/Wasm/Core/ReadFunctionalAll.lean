import WasmGemmGnaf.Wasm.Core.ReadFunctional1
import WasmGemmGnaf.Wasm.Core.ReadFunctional2
import WasmGemmGnaf.Wasm.Core.ReadFunctional3
import WasmGemmGnaf.Wasm.Core.ReadFunctional4
import WasmGemmGnaf.Wasm.Core.ReadFunctional5
import WasmGemmGnaf.Wasm.Core.ReadFunctional6
import WasmGemmGnaf.Wasm.Core.ReadFunctional7
import WasmGemmGnaf.Wasm.Core.ReadFunctional8
import WasmGemmGnaf.Wasm.Core.ReadFunctional9
import WasmGemmGnaf.Wasm.Core.ReadFunctional10
import WasmGemmGnaf.Wasm.Core.ReadFunctional11
import WasmGemmGnaf.Wasm.Core.ReadFunctional12
import WasmGemmGnaf.Wasm.Core.ReadFunctional13
import WasmGemmGnaf.Wasm.Core.ReadFunctional14
import WasmGemmGnaf.Wasm.Core.ReadFunctional15
import WasmGemmGnaf.Wasm.Core.ReadFunctional16
import WasmGemmGnaf.Wasm.Core.ReadFunctional17
import WasmGemmGnaf.Wasm.Core.ReadFunctional18
import WasmGemmGnaf.Wasm.Core.ReadFunctional19
import WasmGemmGnaf.Wasm.Core.ReadFunctional20

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- For the amended authority, a fixed store-reading rule, source state, and
labelled source instruction sequence determine at most one target sequence. -/
theorem Step_readA.target_functional
    {state : State} {rule : ReadRule} {source left right : List AdminInstr}
    (hl : Step_readA state rule source left)
    (hr : Step_readA state rule source right) : left = right := by
  have hbound : rule.functionalGroup ≤ 20 := by
    cases rule <;> decide
  generalize hgroup : rule.functionalGroup = group at hbound
  have hcases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨
      group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 ∨
      group = 9 ∨ group = 10 ∨ group = 11 ∨ group = 12 ∨
      group = 13 ∨ group = 14 ∨ group = 15 ∨ group = 16 ∨
      group = 17 ∨ group = 18 ∨ group = 19 ∨ group = 20 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact hl.target_functional_group0 (hgroup.trans h) hr
  · exact hl.target_functional_group1 (hgroup.trans h) hr
  · exact hl.target_functional_group2 (hgroup.trans h) hr
  · exact hl.target_functional_group3 (hgroup.trans h) hr
  · exact hl.target_functional_group4 (hgroup.trans h) hr
  · exact hl.target_functional_group5 (hgroup.trans h) hr
  · exact hl.target_functional_group6 (hgroup.trans h) hr
  · exact hl.target_functional_group7 (hgroup.trans h) hr
  · exact hl.target_functional_group8 (hgroup.trans h) hr
  · exact hl.target_functional_group9 (hgroup.trans h) hr
  · exact hl.target_functional_group10 (hgroup.trans h) hr
  · exact hl.target_functional_group11 (hgroup.trans h) hr
  · exact hl.target_functional_group12 (hgroup.trans h) hr
  · exact hl.target_functional_group13 (hgroup.trans h) hr
  · exact hl.target_functional_group14 (hgroup.trans h) hr
  · exact hl.target_functional_group15 (hgroup.trans h) hr
  · exact hl.target_functional_group16 (hgroup.trans h) hr
  · exact hl.target_functional_group17 (hgroup.trans h) hr
  · exact hl.target_functional_group18 (hgroup.trans h) hr
  · exact hl.target_functional_group19 (hgroup.trans h) hr
  · exact hl.target_functional_group20 (hgroup.trans h) hr

end WasmGemmGnaf.Wasm.Core.Exec
