import WasmGemmGnaf.Wasm.Core.RuntimeDefinedFunctionTyping
import WasmGemmGnaf.Wasm.Core.HarnessExecution

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Static typing of the released function activation

The public Harness invokes the resolved exported function with its checked
two-`i32`/one-`i32` ABI.  The theorem below connects that concrete invocation
to the source body's ordinary amended validation derivation through allocation
provenance.  It stores no transition or progress fact in a configuration.
-/

namespace WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Harness
namespace Exec

/-- The freshly instantiated released GEMM invocation takes its exact
`call_ref-func` step to a frame carrying the validated source-body and runtime
local typing witnesses. -/
theorem InstantiateA.gemm_callRefFunc_typed_activation
    {module : Module} {instantiated invocation : Config}
    {harness : Harness}
    (hsyntax : module.types.all TypeDef.isSyn = true)
    (hinst : InstantiateA ({} : Store) module [] instantiated)
    (hrequest : harness.request.module = module)
    (hresolves : ResolvesExports instantiated.1.frame.mod harness)
    (hready : GemmFunctionReady harness instantiated.1.store)
    (hinvoke : InvokeA instantiated.1.store harness.gemmAddr harness.args
      invocation) :
    ∃ (event : Event) (target : Config) (frame : Frame)
        (sourceFunction : Func) (context : Context)
        (localTypes : List LocalType),
      StepA invocation event target ∧
      target =
        (⟨instantiated.1.store, { mod := {} }⟩,
          [.frame 1 frame
            [.label 1 [] (plains sourceFunction.body.toList)]]) ∧
      FunctionActivationOkA instantiated.1.store frame 1
        [.label 1 [] (plains sourceFunction.body.toList)] := by
  obtain ⟨moduleType, hmodule⟩ := hinst.module_okA
  have haddress : harness.gemmAddr ∈ instantiated.1.frame.mod.funcs :=
    hinst.function_export_address_mem hresolves.2
  obtain ⟨index, allocatedFunction, sourceFunction, allocatedType, hindex,
      haddressEq, hsourceFunction, hsourceType, hallocatedLookup,
      hallocatedType, hallocatedCode, hallocatedModule⟩ :=
    hinst.defined_function_origin_of_mem haddress
  cases hinvoke with
  | @mk functionInstance runtimeDomain runtimeCodomain hfunctionLookup
      hruntimeExpand hargumentsLength harguments =>
      have hfunctionEq : functionInstance = allocatedFunction :=
        Option.some.inj (hfunctionLookup.symm.trans hallocatedLookup)
      subst functionInstance
      obtain ⟨context, rawType, sourceDomain, sourceCodomain, localTypes,
          htypeClosure, hclosedExpand, hlocalsLength, hlocals, hbody⟩ :=
        hmodule.defined_function_closed_typing hsyntax hsourceFunction
          hsourceType
      have hready' := hready
      unfold GemmFunctionReady at hready'
      rw [Option.bind_eq_some_iff] at hready'
      obtain ⟨readyFunction, hreadyLookup, hreadyExpand⟩ := hready'
      have hreadyFunctionEq : readyFunction = allocatedFunction :=
        Option.some.inj (hreadyLookup.symm.trans hallocatedLookup)
      subst readyFunction
      have habiExpand : Expand allocatedType
          (.func
            (ValTypes.ofList [.num .i32, .num .i32])
            (ValTypes.ofList [.num .i32])) := by
        apply Expand.mk
        simpa [hallocatedType] using hreadyExpand
      have habiAtFunction : Expand allocatedFunction.type
          (.func
            (ValTypes.ofList [.num .i32, .num .i32])
            (ValTypes.ofList [.num .i32])) := by
        simpa [hallocatedType] using habiExpand
      have hruntimeShape :
          CompType.func runtimeDomain runtimeCodomain =
            .func
              (ValTypes.ofList [.num .i32, .num .i32])
              (ValTypes.ofList [.num .i32]) := by
        cases hruntimeExpand with
        | mk hruntime =>
            cases habiAtFunction with
            | mk habi => exact Option.some.inj (hruntime.symm.trans habi)
      have hruntimeDomain : runtimeDomain =
          ValTypes.ofList [.num .i32, .num .i32] :=
        CompType.func.inj hruntimeShape |>.1
      have hruntimeCodomain : runtimeCodomain =
          ValTypes.ofList [.num .i32] :=
        CompType.func.inj hruntimeShape |>.2
      subst runtimeDomain
      subst runtimeCodomain
      have hclosedShape :
          CompType.func (context.closValTypes sourceDomain)
              (context.closValTypes sourceCodomain) =
            .func
              (ValTypes.ofList [.num .i32, .num .i32])
              (ValTypes.ofList [.num .i32]) := by
        cases hclosedExpand with
        | mk hclosed =>
            cases habiExpand with
            | mk habi => exact Option.some.inj (hclosed.symm.trans habi)
      have hsourceDomain : sourceDomain =
          ValTypes.ofList [.num .i32, .num .i32] :=
        context.closValTypes_eq_i32_i32 (CompType.func.inj hclosedShape |>.1)
      have hsourceCodomain : sourceCodomain =
          ValTypes.ofList [.num .i32] :=
        context.closValTypes_eq_i32 (CompType.func.inj hclosedShape |>.2)
      subst sourceDomain
      subst sourceCodomain
      have hargumentTyping : ValuesOkA instantiated.1.store harness.args
          (ValTypes.ofList [.num .i32, .num .i32]).toList :=
        ValuesOkA.iff_seq.mpr ⟨hargumentsLength, harguments⟩
      obtain ⟨frame, hstep, hactivation⟩ :=
        callRefFunc_step_to_typed_activation
          (state := ⟨instantiated.1.store, { mod := {} }⟩)
          (typeUse := .defd allocatedFunction.type)
          hallocatedLookup habiAtFunction hallocatedCode hargumentTyping
          hlocalsLength hlocals hbody
      refine ⟨
        .read .callRefFunc
          (sourcePlains (vals harness.args ++
            [.addrref (.funcAddr harness.gemmAddr),
              .plain (.callRef (.defd allocatedFunction.type))])),
        (⟨instantiated.1.store, { mod := {} }⟩,
          [.frame 1 frame
            [.label 1 [] (plains sourceFunction.body.toList)]]),
        frame, sourceFunction, context, localTypes, ?_, rfl, ?_⟩
      · simpa [hallocatedType] using hstep
      · simpa using hactivation

end Exec
end WasmGemmGnaf.Wasm.Core
