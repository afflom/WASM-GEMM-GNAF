import WasmGemmGnaf.Wasm.Core.EventExecution

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

local instance : ExecutionAuthority := amendedExecutionAuthority

private def indexedNullCounterType : DefType := default
private def indexedNullCounterIndex : TypeIdx := TypeIdx.ofNat 0
private def indexedNullCounterState : State :=
  { store := {},
    frame := { mod := { types := [indexedNullCounterType] } } }
private def indexedNullCounterExpr : Expr :=
  .cons (.refNull (.use (.idx indexedNullCounterIndex))) .nil
private def indexedNullRawValues : List Val :=
  [.ref (.null (.use (.idx indexedNullCounterIndex)))]
private def indexedNullClosedValues : List Val :=
  [.ref (.null (.use (.defd indexedNullCounterType)))]

private theorem indexedNullCounterType_lookup :
    indexedNullCounterState.typeOf indexedNullCounterIndex =
      some indexedNullCounterType := by
  rfl

private theorem indexedNullCounter_eval_raw :
    Eval_exprEraseA indexedNullCounterState indexedNullCounterExpr
      indexedNullCounterState indexedNullRawValues := by
  apply Eval_expr.mk
  exact Steps.refl

private theorem indexedNullCounter_eval_closed :
    Eval_exprEraseA indexedNullCounterState indexedNullCounterExpr
      indexedNullCounterState indexedNullClosedValues := by
  apply Eval_expr.mk
  apply Steps.trans
  · apply Step.read
    exact Step_read.refNullIdx indexedNullCounterType_lookup
  · exact Steps.refl

private theorem indexedNullCounter_values_ne :
    indexedNullRawValues ≠ indexedNullClosedValues := by
  intro h
  simp [indexedNullRawValues, indexedNullClosedValues] at h

/-- The raw expression relation is not target-functional: an indexed null is
both an administrative value and the source of `Step_read/ref.null-idx`.
AMD-019 excludes the reflexively terminal representation at the public Harness
initialization boundary while retaining the relational instantiation witness. -/
theorem eval_expr_indexed_ref_null_not_target_functional :
    ¬ (∀ {state : State} {expression : Expr}
      {leftState rightState : State} {leftValues rightValues : List Val},
      Eval_exprEraseA state expression leftState leftValues →
      Eval_exprEraseA state expression rightState rightValues →
      leftState = rightState ∧ leftValues = rightValues) := by
  intro h
  exact indexedNullCounter_values_ne
    (h indexedNullCounter_eval_raw indexedNullCounter_eval_closed).2

end WasmGemmGnaf.Wasm.Core.Exec
