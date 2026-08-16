import WasmGemmGnaf.Wasm.Core.InstantiationFunctionOrigin
import WasmGemmGnaf.Wasm.Core.RuntimeFunctionActivation
import WasmGemmGnaf.Wasm.Core.RuntimeTypeBridge
import WasmGemmGnaf.Wasm.Core.RuntimeTypeClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Validated source typing at an allocated defined function

Module validation types function bodies against the raw rolled type section,
whereas runtime allocation stores the corresponding closed type.  This module
retains their exact computational relationship.  It introduces no execution,
progress, or termination premise.
-/

namespace WasmGemmGnaf.Wasm.Core

private theorem seqAll₂_left_getElem?_with_right {A B : Type}
    {relation : A → B → Prop} {left : List A} {right : List B}
    (hlength : SeqLen₂ left right) (hall : SeqAll₂ relation left right)
    {index : Nat} {value : A} (hvalue : left[index]? = some value) :
    ∃ result, right[index]? = some result ∧ relation value result := by
  have hleft : index < left.length :=
    (List.getElem?_eq_some_iff.mp hvalue).1
  have hright : index < right.length := by
    simpa [SeqLen₂, hlength] using hleft
  let result := right[index]
  exact ⟨result, List.getElem?_eq_getElem hright,
    hall index value result hvalue (List.getElem?_eq_getElem hright)⟩

private theorem mapM_member_origin {A B : Type} {f : A → Option B}
    {source : List A} {target : List B}
    (hmap : source.mapM f = some target) {result : B}
    (hresult : result ∈ target) : ∃ value ∈ source, f value = some result := by
  induction source generalizing target with
  | nil =>
      simp at hmap
      subst target
      simp at hresult
  | cons head tail ih =>
      simp only [List.mapM_cons] at hmap
      cases hhead : f head with
      | none => simp [hhead] at hmap
      | some headResult =>
          cases htail : tail.mapM f with
          | none => simp [hhead, htail] at hmap
          | some tailResults =>
              simp [hhead, htail] at hmap
              subst target
              simp only [List.mem_cons] at hresult
              rcases hresult with rfl | htailResult
              · exact ⟨head, List.mem_cons_self, hhead⟩
              · obtain ⟨value, hvalue, hvalueResult⟩ :=
                  ih htail htailResult
                exact ⟨value, List.mem_cons_of_mem _ hvalue, hvalueResult⟩

/-- A function export installed by module allocation always selects an address
from that allocated module instance's function-address vector. -/
theorem Exec.AllocModule.function_export_address_mem
    {source target : Exec.Store} {module : Module}
    {externAddresses : List Exec.ExternAddr} {globalValues : List Exec.Val}
    {tableRefs : List Exec.Ref} {elemRefs : List (List Exec.Ref)}
    {moduleInst : Exec.ModuleInst}
    (halloc : Exec.AllocModule source module externAddresses globalValues
      tableRefs elemRefs target moduleInst)
    {name : Name} {address : Exec.FuncAddr}
    (hexport : ({ name := name, addr := .func address } : Exec.ExportInst) ∈
      moduleInst.exports) :
    address ∈ moduleInst.funcs := by
  cases halloc with
  | mk htypes htagsI hglobalsI hmemsI htablesI hfuncsI hdefinedFuncs
      htags hglobals hmems htables hdatas helems hfunctionTypes hfunctions
      haddressModule hexports hmoduleInst =>
      rw [hmoduleInst] at hexport ⊢
      simp only at hexport ⊢
      obtain ⟨sourceExport, _, hsourceExport⟩ :=
        mapM_member_origin hexports hexport
      cases sourceExport with
      | mk sourceName externIndex =>
          cases externIndex with
          | tag index => simp [Exec.allocExport] at hsourceExport
          | global index => simp [Exec.allocExport] at hsourceExport
          | mem index => simp [Exec.allocExport] at hsourceExport
          | table index => simp [Exec.allocExport] at hsourceExport
          | func index =>
              simp only [Exec.allocExport, Option.map_eq_some_iff] at hsourceExport
              obtain ⟨selectedAddress, hselected, heq⟩ := hsourceExport
              cases heq
              rw [haddressModule] at hselected
              exact List.mem_of_getElem? hselected

/-- Every function export of an import-free fresh instantiation belongs to the
allocated module instance's defined-function address vector. -/
theorem Exec.InstantiateA.function_export_address_mem
    {module : Module} {core : Exec.Config}
    (hinst : Exec.InstantiateA ({} : Exec.Store) module [] core)
    {name : Name} {address : Exec.FuncAddr}
    (hexport : ({ name := name, addr := .func address } : Exec.ExportInst) ∈
      core.1.frame.mod.exports) :
    address ∈ core.1.frame.mod.funcs := by
  cases hinst with
  | mk hmodule himportsLength himports hinitialModule hinitialState hglobals
      htables helems hheap halloc hdatas hdataInstructions helemMap
      helemInstructions hstart =>
      exact halloc.function_export_address_mem hexport

/-- Public amended instantiation retains the exact amended module-validation
derivation it consumed. -/
theorem Exec.InstantiateA.module_okA
    {source : Exec.Store} {module : Module}
    {externAddresses : List Exec.ExternAddr} {core : Exec.Config}
    (hinst : Exec.InstantiateA source module externAddresses core) :
    ∃ moduleType, Module_okA module moduleType := by
  cases hinst
  exact ⟨_, by assumption⟩

/-- The validation context used for every defined function has exactly the raw
rolled type vector produced by validation of the module's type section. -/
theorem Module_okA.defined_function_context_types
    {module : Module} {moduleType : ModuleType}
    (hmodule : Module_okA module moduleType)
    {index : Nat} {function : Func}
    (hfunction : module.funcs[index]? = some function) :
    ∃ context rawTypes functionType,
      context.types = rawTypes ∧
      Types_okA Context.empty module.types rawTypes ∧
      Func_okA context function functionType := by
  cases hmodule with
  | mk htypes himportsLength himports htagsLength htags hglobals hmemsLength
      hmems htablesLength htables hfuncsLength hfuncs hdatasLength hdatas
      helemsLength helems hstart hexportsLength hexports hdisjoint hcontext
      hbaseContext hrefs himportTags himportGlobals himportMems himportTables
      himportFuncs =>
      obtain ⟨functionType, _, hfunctionTyped⟩ :=
        seqAll₂_left_getElem?_with_right hfuncsLength hfuncs hfunction
      refine ⟨_, _, functionType, ?_, htypes, hfunctionTyped⟩
      simp [hcontext, hbaseContext, Context.append]

/-- A selected validated source function's allocated type is definitionally
the closure of its source type, and its runtime function expansion is the
pointwise closure of the source domain and codomain used to type its body. -/
theorem Module_okA.defined_function_closed_typing
    {module : Module} {moduleType : ModuleType}
    (hsyntax : module.types.all TypeDef.isSyn = true)
    (hmodule : Module_okA module moduleType)
    {index : Nat} {function : Func} {allocatedType : DefType}
    (hfunction : module.funcs[index]? = some function)
    (hallocated :
      (Exec.allocTypes module.types)[function.typeidx.val]? =
        some allocatedType) :
    ∃ context rawType sourceDomain sourceCodomain localTypes,
      allocatedType = context.closDefType rawType ∧
      Expand allocatedType
        (.func (context.closValTypes sourceDomain)
          (context.closValTypes sourceCodomain)) ∧
      SeqLen₂ function.locals localTypes ∧
      SeqAll₂ (Local_okA context) function.locals localTypes ∧
      Expr_okA (Context.append context
        { locals := sourceDomain.toList.map
              (fun type => ⟨Init.set, type⟩) ++ localTypes,
          labels := [sourceCodomain.toList],
          ret := some sourceCodomain.toList })
        function.body sourceCodomain.toList := by
  obtain ⟨context, rawTypes, functionType, hcontextTypes, htypes,
      hfunctionTyped⟩ :=
    hmodule.defined_function_context_types hfunction
  cases hfunctionTyped with
  | @mk sourceDomain sourceCodomain localTypes htypeLookup hsourceExpand
      hlocalsLength hlocals hbody =>
      have hcausal := htypes.storedFreeBefore hsyntax
      have hbound := htypes.outputLength_le
      have hrawLookup : rawTypes[function.typeidx.val]? = some functionType := by
        simpa [hcontextTypes] using htypeLookup
      have hclosedLookup := closDefTypes_get_full hcausal hbound hrawLookup
      have hallocTypes := htypes.allocTypes_eq_closure hsyntax
      rw [hallocTypes] at hallocated
      have hallocatedEq : allocatedType =
          substAllDefType functionType
            ((closDefTypes rawTypes).map TypeUse.defd) :=
        Option.some.inj (hallocated.symm.trans hclosedLookup)
      have hclosure : allocatedType = context.closDefType functionType := by
        rw [hallocatedEq]
        simp [Context.closDefType, Context.closTypes, hcontextTypes]
      refine ⟨context, functionType, sourceDomain, sourceCodomain, localTypes,
        hclosure, ?_, hlocalsLength, hlocals, hbody⟩
      rw [hclosure]
      exact hsourceExpand.close_func (context := context)

end WasmGemmGnaf.Wasm.Core
