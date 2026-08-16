import WasmGemmGnaf.Wasm.Core.SubtypeTransport
import WasmGemmGnaf.Wasm.Core.ValidateSeq
import WasmGemmGnaf.Wasm.Core.ValidateStoredCompOk

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-!
# Semantic validity of the final type-section context

The full instruction validator changes locals and control labels, but its
type environment is the final rolled output of `Types_okA`.  This file keeps
the one difficult invariant explicit: semantic validity of the raw and
closed stored defined types.  No checker or metatheoretic conclusion is
stored in that invariant.
-/

/-- Once the rolled raw and causal closed defined types have been rebuilt as
semantic `Deftype_okA` derivations, the exact final type-only context satisfies
the validator's ordinary semantic context invariant. -/
theorem Types_okA.finalContextValidA_of_storedDeftypes
    {tds : List TypeDef} {dts : List DefType}
    (hsyn : tds.all TypeDef.isSyn = true)
    (htypes : Types_okA Context.empty tds dts)
    (hstored : ({ Context.empty with types := dts } : Context).StoredDeftypesOkA) :
    Validate.Context.ValidA { Context.empty with types := dts } := by
  let C : Context := { Context.empty with types := dts }
  have hstoredC : C.StoredDeftypesOkA := by simpa [C] using hstored
  constructor
  · intro D hD x dt ct hlookup hexpand
    have hlookupDts : dts[x.val]? = some dt := by
      simpa [C] using hlookup
    have hct : Comptype_okA C ct := by
      simpa [C, Context.empty] using
        htypes.storedCompOkA_of_storedDeftypes hsyn hstoredC
          hlookupDts hexpand
    exact Comptype_okA.transport hD.1 hD.2 hct
  · intro D hD x dt ct hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x dt hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x jt dt dom hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x gt hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x tt hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x rt hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x lt hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD x ts hlookup
    simp [C, Context.empty] at hlookup
  · intro D hD ts hret
    simp [C, Context.empty] at hret

end WasmGemmGnaf.Wasm.Core
