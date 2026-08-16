import WasmGemmGnaf.Wasm.Core.HarnessActivationTyping
import WasmGemmGnaf.Wasm.Core.InstantiationOrigins

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Source/runtime alignment of the released function activation

The ordinary activation theorem retains the validated source body and the
typing of its concrete local vector.  Runtime progress additionally needs the
exact relationship between the source type context and the closed type vector
installed in the active frame.  The theorem below retains that computational
equality while constructing the same genuine `call_ref-func` transition.  It
adds no progress or transition premise to a runtime invariant.
-/

namespace WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Harness
namespace Exec

/-- A freshly instantiated released GEMM invocation enters the exact validated
source function body with typed locals, and the active frame's runtime type
vector is precisely the closure of the source validation context. -/
theorem InstantiateA.gemm_callRefFunc_aligned_activation
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
        (sourceIndex : Nat) (sourceFunction : Func) (context : Context)
        (localTypes : List LocalType),
      StepA invocation event target ∧
      coreTrapCause? event = none ∧
      target =
        (⟨instantiated.1.store, { mod := {} }⟩,
          [.frame 1 frame
            [.label 1 [] (plains sourceFunction.body.toList)]]) ∧
      frame.mod = instantiated.1.frame.mod ∧
      frame.mod.types = closDefTypes context.types ∧
      Types_okA Context.empty module.types context.types ∧
      module.funcs[sourceIndex]? = some sourceFunction ∧
      LocalsOkA instantiated.1.store frame.locals
        ((ValTypes.ofList [.num .i32, .num .i32]).toList.map
          (fun type => ⟨Init.set, type⟩) ++ localTypes) ∧
      Expr_okA (Context.append context
        { locals :=
            (ValTypes.ofList [.num .i32, .num .i32]).toList.map
                (fun type => ⟨Init.set, type⟩) ++ localTypes,
          labels := [(ValTypes.ofList [.num .i32]).toList],
          ret := some (ValTypes.ofList [.num .i32]).toList })
        sourceFunction.body (ValTypes.ofList [.num .i32]).toList := by
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
      obtain ⟨context, rawTypes, functionType, hcontextTypes, htypes,
          hfunctionTyped⟩ :=
        hmodule.defined_function_context_types hsourceFunction
      cases hfunctionTyped with
      | @mk sourceDomain sourceCodomain localTypes htypeLookup hsourceExpand
          hlocalsLength hlocals hbody =>
          have hcausal := htypes.storedFreeBefore hsyntax
          have hbound := htypes.outputLength_le
          have hrawLookup :
              rawTypes[sourceFunction.typeidx.val]? = some functionType := by
            simpa [hcontextTypes] using htypeLookup
          have hclosedLookup := closDefTypes_get_full hcausal hbound hrawLookup
          have hallocTypes := htypes.allocTypes_eq_closure hsyntax
          rw [hallocTypes] at hsourceType
          have hallocatedEq : allocatedType =
              substAllDefType functionType
                ((closDefTypes rawTypes).map TypeUse.defd) :=
            Option.some.inj (hsourceType.symm.trans hclosedLookup)
          have hclosure :
              allocatedType = context.closDefType functionType := by
            rw [hallocatedEq]
            simp [Context.closDefType, Context.closTypes, hcontextTypes]
          have hclosedExpand : Expand allocatedType
              (.func (context.closValTypes sourceDomain)
                (context.closValTypes sourceCodomain)) := by
            rw [hclosure]
            exact hsourceExpand.close_func (context := context)
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
                | mk habi =>
                    exact Option.some.inj (hruntime.symm.trans habi)
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
            context.closValTypes_eq_i32_i32
              (CompType.func.inj hclosedShape |>.1)
          have hsourceCodomain : sourceCodomain =
              ValTypes.ofList [.num .i32] :=
            context.closValTypes_eq_i32
              (CompType.func.inj hclosedShape |>.2)
          subst sourceDomain
          subst sourceCodomain
          have hargumentTyping : ValuesOkA instantiated.1.store harness.args
              (ValTypes.ofList [.num .i32, .num .i32]).toList :=
            ValuesOkA.iff_seq.mpr ⟨hargumentsLength, harguments⟩
          let frame : Frame :=
            { locals := harness.args.map some ++
                sourceFunction.locals.map
                  (fun localDecl => default_ localDecl.valtype)
              mod := allocatedFunction.mod }
          have hread : Step_readA
              ⟨instantiated.1.store, { mod := {} }⟩ .callRefFunc
              (vals harness.args ++
                [.addrref (.funcAddr harness.gemmAddr),
                  .plain (.callRef (.defd allocatedFunction.type))])
              [.frame 1 frame
                [.label 1 [] (plains sourceFunction.body.toList)]] := by
            letI : ExecutionAuthority := amendedExecutionAuthority
            apply Step_read.callRefFunc
              (z := ⟨instantiated.1.store, { mod := {} }⟩)
              (yy := .defd allocatedFunction.type) (f := frame)
              hallocatedLookup habiAtFunction rfl rfl hargumentsLength
              hallocatedCode
            rfl
          have hframeTypes : frame.mod.types =
              closDefTypes context.types := by
            dsimp [frame]
            rw [hallocatedModule, hinst.frameTypes_eq_allocTypes,
              htypes.allocTypes_eq_closure hsyntax]
            exact congrArg closDefTypes hcontextTypes.symm
          have hframeModule : frame.mod = instantiated.1.frame.mod := by
            dsimp [frame]
            exact hallocatedModule
          have hframeLocals : LocalsOkA instantiated.1.store frame.locals
              ((ValTypes.ofList [.num .i32, .num .i32]).toList.map
                  (fun type => ⟨Init.set, type⟩) ++ localTypes) := by
            dsimp [frame]
            exact function_frame_locals_typed hargumentTyping hlocalsLength
              hlocals
          have hcontextTypesOk :
              Types_okA Context.empty module.types context.types := by
            simpa [hcontextTypes] using htypes
          refine ⟨
            .read .callRefFunc
              (sourcePlains (vals harness.args ++
                [.addrref (.funcAddr harness.gemmAddr),
                  .plain (.callRef (.defd allocatedFunction.type))])),
            (⟨instantiated.1.store, { mod := {} }⟩,
              [.frame 1 frame
                [.label 1 [] (plains sourceFunction.body.toList)]]),
            frame, index, sourceFunction, context, localTypes, ?_, rfl,
            rfl, hframeModule, hframeTypes, hcontextTypesOk,
            hsourceFunction, hframeLocals, hbody⟩
          simpa [hallocatedType] using StepA.read hread

end Exec
end WasmGemmGnaf.Wasm.Core
