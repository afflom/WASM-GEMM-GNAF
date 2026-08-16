import WasmGemmGnaf.Wasm.Core.Execution

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- The public AMD-016 endpoint for numeric literals reconstructed from bytes. -/
def ByteSolvedNumWfA : (type : NumType) → Num_ type → Prop :=
  @ByteSolvedNumWfFor amendedExecutionAuthority

/-- The public AMD-016 endpoint for storage literals reconstructed from bytes. -/
def ByteSolvedLiteralWfA : (storage : StorageType) → Lit_ storage → Prop :=
  @ByteSolvedLiteralWfFor amendedExecutionAuthority

end WasmGemmGnaf.Wasm.Core.Exec
