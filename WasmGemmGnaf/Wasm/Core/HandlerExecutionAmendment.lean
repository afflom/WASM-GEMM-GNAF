import WasmGemmGnaf.Wasm.Core.Runtime

set_option autoImplicit false

/-!
# Administrative handler execution amendment

AMD-023 adds exactly the two handler-administrative rules absent from the
pinned Core 3.0 execution tree: body context closure and completed-trap
propagation.  This selector keeps the byte-identical pinned `Step` endpoint
available while the public amended endpoint enables those rules.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Whether AMD-023's two administrative handler rules are enabled at the
selected execution authority. -/
def HandlerAdministrativeRulesFor [authority : ExecutionAuthority] : Prop :=
  authority.revision = .amended

theorem handlerAdministrativeRules_amended :
    @HandlerAdministrativeRulesFor amendedExecutionAuthority := by
  rfl

theorem handlerAdministrativeRules_not_pinned :
    ¬ @HandlerAdministrativeRulesFor pinnedExecutionAuthority := by
  intro impossible
  cases impossible

end WasmGemmGnaf.Wasm.Core.Exec
