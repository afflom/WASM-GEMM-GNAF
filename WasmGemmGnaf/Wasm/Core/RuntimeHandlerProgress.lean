import WasmGemmGnaf.Wasm.Core.RuntimeAdminProgress

set_option autoImplicit false

/-!
# Handler administrative progress

These combinators expose the two genuine ways an administrative handler can
advance after AMD-023: a value body exits through `handler-vals`, while an
inner body step is lifted through the handler evaluation context.  A completed
trap uses the separate amended trap-propagation rule.

No typing or progress conclusion is stored in a runtime structure here; the
caller must supply the inner values-or-step fact.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- A handler advances whenever its body is already a value sequence or can
take one event-labelled Core step. -/
theorem handler_step_of_values_or_step
    {state : State} {arity : Nat} {catches : List Catch}
    {body : List AdminInstr}
    (bodyProgress :
      (∃ values, body = vals values) ∨
        ∃ event target, StepA (state, body) event target) :
    ∃ event target,
      StepA (state, [.handler arity catches body]) event target := by
  rcases bodyProgress with
    ⟨values, rfl⟩ | ⟨event, target, step⟩
  · exact handler_values_step state arity catches values
  · rcases target with ⟨nextState, nextBody⟩
    exact ⟨.ctxtHandler arity event,
      (nextState, [.handler arity catches nextBody]),
      .ctxtHandler step⟩

/-- A completed trap escapes its administrative handler by the exact
AMD-023 event-labelled propagation rule. -/
theorem handler_trap_step (state : State) (arity : Nat)
    (catches : List Catch) :
    ∃ event target,
      StepA (state, [.handler arity catches [.trap]]) event target := by
  exact ⟨.trapHandler arity, (state, [.trap]), .trapHandler⟩

end WasmGemmGnaf.Wasm.Core.Exec
