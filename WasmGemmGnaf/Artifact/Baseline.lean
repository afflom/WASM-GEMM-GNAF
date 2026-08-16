/-
  Artifact/Baseline.lean --- compatibility import after the public-Core
  release-cone migration.

  The former declarations in this module described a legacy `Wasm.Subset`
  compiler output.  They were not release-applicable and cannot inhabit the
  public competitor/evaluator carrier.  They are intentionally absent.  The
  actual release artifact will be defined only from the emitted full-GEMM
  public-Core compilation.
-/
import WasmGemmGnaf.Artifact.Release

set_option autoImplicit false

namespace WasmGemmGnaf.Artifact

end WasmGemmGnaf.Artifact
