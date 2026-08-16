import WasmGemmGnaf.Wasm.Core.HarnessSuccessors
import WasmGemmGnaf.Wasm.Core.TypedRuntimeMatch

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core

namespace Exec

private theorem State.withLocal_funcs {source target : State}
    {index : LocalIdx} {value : Val}
    (h : source.withLocal index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withLocal at h
  rw [Option.map_eq_some_iff] at h
  rcases h with ⟨_, _, rfl⟩
  rfl

private theorem State.withGlobal_funcs {source target : State}
    {index : GlobalIdx} {value : Val}
    (h : source.withGlobal index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withGlobal at h
  cases haddress : source.frame.mod.globals[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases hglobal : source.store.globals[address]? with
      | none => simp [haddress, hglobal] at h
      | some global =>
          cases hglobals : setAt? source.store.globals address
              { global with value := value } with
          | none => simp [haddress, hglobal, hglobals] at h
          | some globals =>
              simp [haddress, hglobal, hglobals] at h
              subst target
              rfl

private theorem State.withTable_funcs {source target : State}
    {index : TableIdx} {offset : Nat} {value : Ref}
    (h : source.withTable index offset value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withTable at h
  cases haddress : source.frame.mod.tables[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases htable : source.store.tables[address]? with
      | none => simp [haddress, htable] at h
      | some table =>
          cases hrefs : setAt? table.refs offset value with
          | none => simp [haddress, htable, hrefs] at h
          | some refs =>
              cases htables : setAt? source.store.tables address
                  { table with refs := refs } with
              | none => simp [haddress, htable, hrefs, htables] at h
              | some tables =>
                  simp [haddress, htable, hrefs, htables] at h
                  subst target
                  rfl

private theorem State.withTableInst_funcs {source target : State}
    {index : TableIdx} {value : TableInst}
    (h : source.withTableInst index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withTableInst at h
  cases haddress : source.frame.mod.tables[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases htables : setAt? source.store.tables address value with
      | none => simp [haddress, htables] at h
      | some tables =>
          simp [haddress, htables] at h
          subst target
          rfl

private theorem State.withMem_funcs {source target : State}
    {index : MemIdx} {offset width : Nat} {bytes : List Byte}
    (h : source.withMem index offset width bytes = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withMem at h
  cases haddress : source.frame.mod.mems[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases hmemory : source.store.mems[address]? with
      | none => simp [haddress, hmemory] at h
      | some memory =>
          cases hbytes : spliceAt? memory.bytes offset width bytes with
          | none => simp [haddress, hmemory, hbytes] at h
          | some resultBytes =>
              cases hmems : setAt? source.store.mems address
                  { memory with bytes := resultBytes } with
              | none => simp [haddress, hmemory, hbytes, hmems] at h
              | some mems =>
                  simp [haddress, hmemory, hbytes, hmems] at h
                  subst target
                  rfl

private theorem State.withMemInst_funcs {source target : State}
    {index : MemIdx} {value : MemInst}
    (h : source.withMemInst index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withMemInst at h
  cases haddress : source.frame.mod.mems[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases hmems : setAt? source.store.mems address value with
      | none => simp [haddress, hmems] at h
      | some mems =>
          simp [haddress, hmems] at h
          subst target
          rfl

private theorem State.withElem_funcs {source target : State}
    {index : ElemIdx} {values : List Ref}
    (h : source.withElem index values = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withElem at h
  cases haddress : source.frame.mod.elems[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases helem : source.store.elems[address]? with
      | none => simp [haddress, helem] at h
      | some elem =>
          cases helems : setAt? source.store.elems address
              { elem with refs := values } with
          | none => simp [haddress, helem, helems] at h
          | some elems =>
              simp [haddress, helem, helems] at h
              subst target
              rfl

private theorem State.withData_funcs {source target : State}
    {index : DataIdx} {bytes : List Byte}
    (h : source.withData index bytes = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withData at h
  cases haddress : source.frame.mod.datas[index.val]? with
  | none => simp [haddress] at h
  | some address =>
      cases hdata : source.store.datas[address]? with
      | none => simp [haddress, hdata] at h
      | some data =>
          cases hdatas : setAt? source.store.datas address
              { data with bytes := bytes } with
          | none => simp [haddress, hdata, hdatas] at h
          | some datas =>
              simp [haddress, hdata, hdatas] at h
              subst target
              rfl

private theorem State.withStruct_funcs {source target : State}
    {address : StructAddr} {index : Nat} {value : FieldVal}
    (h : source.withStruct address index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withStruct at h
  cases hstruct : source.store.structs[address]? with
  | none => simp [hstruct] at h
  | some struct =>
      cases hfields : setAt? struct.fields index value with
      | none => simp [hstruct, hfields] at h
      | some fields =>
          cases hstructs : setAt? source.store.structs address
              { struct with fields := fields } with
          | none => simp [hstruct, hfields, hstructs] at h
          | some structs =>
              simp [hstruct, hfields, hstructs] at h
              subst target
              rfl

private theorem State.withArray_funcs {source target : State}
    {address : ArrayAddr} {index : Nat} {value : FieldVal}
    (h : source.withArray address index value = some target) :
    target.store.funcs = source.store.funcs := by
  unfold State.withArray at h
  cases harray : source.store.arrays[address]? with
  | none => simp [harray] at h
  | some array =>
      cases hfields : setAt? array.fields index value with
      | none => simp [harray, hfields] at h
      | some fields =>
          cases harrays : setAt? source.store.arrays address
              { array with fields := fields } with
          | none => simp [harray, hfields, harrays] at h
          | some arrays =>
              simp [harray, hfields, harrays] at h
              subst target
              rfl

/-- Core reduction never mutates the function-instance component of the
runtime store.  Function allocation occurs only during module instantiation,
before the event-labelled execution relation begins. -/
theorem StepA.store_funcs_eq {source target : Config} {event : Event}
    (step : StepA source event target) :
    target.1.store.funcs = source.1.store.funcs := by
  induction step with
  | pure | read => rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | trapHandler => rfl
  | throw | tableSetOob | tableGrowFail | storeNumOob | storePackOob |
      vstoreOob | vstoreLaneOob | memoryGrowFail | structNew |
      structSetNull | arrayNewFixed | arraySetNull | arraySetOob => rfl
  | localSet hupdate =>
      exact State.withLocal_funcs hupdate
  | globalSet hupdate => exact State.withGlobal_funcs hupdate
  | tableSetVal _ _ hupdate =>
      exact State.withTable_funcs hupdate
  | tableGrowSucceed _ _ hupdate _ =>
      exact State.withTableInst_funcs hupdate
  | elemDrop hupdate => exact State.withElem_funcs hupdate
  | storeNumVal _ hupdate => exact State.withMem_funcs hupdate
  | storePackVal _ hupdate => exact State.withMem_funcs hupdate
  | vstoreVal _ hupdate => exact State.withMem_funcs hupdate
  | vstoreLaneVal _ _ _ _ _ hupdate =>
      exact State.withMem_funcs hupdate
  | memoryGrowSucceed _ _ hupdate _ =>
      exact State.withMemInst_funcs hupdate
  | dataDrop hupdate => exact State.withData_funcs hupdate
  | structSetStruct _ _ _ _ hupdate =>
      exact State.withStruct_funcs hupdate
  | arraySetArray _ _ _ hupdate =>
      exact State.withArray_funcs hupdate

end Exec

namespace Harness

/-- The released function-ABI lookup depends only on the function-instance
component of the store. -/
theorem GemmFunctionReady.of_funcs_eq {harness : Harness}
    {source target : Exec.Store} (ready : GemmFunctionReady harness source)
    (hfuncs : target.funcs = source.funcs) :
    GemmFunctionReady harness target := by
  unfold GemmFunctionReady at ready ⊢
  rw [hfuncs]
  exact ready

/-- Raw-memory growth and splicing preserve the function-instance store. -/
theorem installRaw?_store_funcs_eq {harness : Harness}
    {source target : Exec.State} {previousPages grownPages : Nat}
    (hinstall : installRaw? harness source =
      some (previousPages, grownPages, target)) :
    target.store.funcs = source.store.funcs := by
  unfold installRaw? at hinstall
  cases haddress : source.frame.mod.mems[0]? with
  | none => simp [haddress] at hinstall
  | some memoryAddress =>
      by_cases heq : memoryAddress = harness.memoryAddr
      · cases hmemory : source.store.mems[harness.memoryAddr]? with
        | none => simp [haddress, heq, hmemory] at hinstall
        | some memory =>
            cases hgrow : Exec.growMem memory
                (rawGrowthPages harness.request memory) with
            | none => simp [haddress, heq, hmemory, hgrow] at hinstall
            | some grownMemory =>
                cases hgrown : source.withMemInst idx0 grownMemory with
                | none =>
                    simp [haddress, heq, hmemory, hgrow, hgrown] at hinstall
                | some grownState =>
                    cases hbytes : grownState.withMem idx0
                        harness.request.rawPtr.val harness.request.rawLen.val
                        harness.request.rawBytes with
                    | none =>
                        simp [haddress, heq, hmemory, hgrow, hgrown, hbytes]
                          at hinstall
                    | some installedState =>
                        simp [haddress, heq, hmemory, hgrow, hgrown, hbytes]
                          at hinstall
                        rcases hinstall with ⟨rfl, rfl, rfl⟩
                        exact (Exec.State.withMem_funcs hbytes).trans
                          (Exec.State.withMemInst_funcs hgrown)
      · simp [haddress, heq] at hinstall

/-- Function-ABI readiness projected over every post-instantiation harness
phase.  The initial request has no runtime store and therefore no such
projection yet. -/
def Config.GemmReady : Config → Prop
  | .initializing _ => False
  | .beforeEntry harness core | .trappingBeforeEntry harness _ core |
      .afterEntry harness _ core | .trappingAfterEntry harness _ _ core =>
      GemmFunctionReady harness core.1.store
  | .readyToEnter harness state | .returned harness _ _ state |
      .trappedBeforeEntry harness _ state |
      .trappedAfterEntry harness _ _ state |
      .thrownBeforeEntry harness _ _ state |
      .thrownAfterEntry harness _ _ _ state =>
      GemmFunctionReady harness state.store

/-- Every post-instantiation Harness transition preserves the computed GEMM
function ABI lookup. -/
theorem StepA.preserveGemmReady {source target : Config} {event : Event}
    (step : StepA source event target) (ready : source.GemmReady) :
    target.GemmReady := by
  cases step with
  | instantiate => simp [Config.GemmReady] at ready
  | coreBefore coreStep _ _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreBeforeTrap coreStep _ _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreBeforeTrapFinal coreStep _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreTrappingBefore coreStep _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreTrappingBeforeFinal coreStep =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | installRaw hinstall =>
      exact ready.of_funcs_eq (installRaw?_store_funcs_eq hinstall)
  | enterGemm invoke =>
      cases invoke
      exact ready
  | coreAfter coreStep _ _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreAfterTrap coreStep _ _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreAfterTrapFinal coreStep _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreTrappingAfter coreStep _ =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | coreTrappingAfterFinal coreStep =>
      exact ready.of_funcs_eq coreStep.store_funcs_eq
  | returnAfter => exact ready
  | throwBefore => exact ready
  | throwAfter => exact ready

/-- Every finite post-instantiation Harness execution preserves the computed
GEMM function ABI lookup. -/
theorem StepsA.preserveGemmReady {source target : Config}
    {trace : List Event} (steps : StepsA source trace target)
    (ready : source.GemmReady) : target.GemmReady := by
  induction steps with
  | refl => exact ready
  | cons head _ ih => exact ih (head.preserveGemmReady ready)

end Harness

end WasmGemmGnaf.Wasm.Core
