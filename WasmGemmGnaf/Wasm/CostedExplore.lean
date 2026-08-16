/-
  Compatibility module for the canonical public amended-Core costed explorer.

  The former contents implemented a parallel legacy `Wasm.Subset` explorer
  and imported `Universal.Competitor`, creating the wrong carrier and an import
  cycle at the release boundary.  The sole implementation now lives in the
  lower, Wasm-only module below.
-/
import WasmGemmGnaf.Wasm.PublicCostedExplore

set_option autoImplicit false
