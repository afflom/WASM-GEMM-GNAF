import WasmGemmGnaf.Wasm.Core.InstantiationAmended

set_option autoImplicit false

/-!
# Defined-function origin through public instantiation

The allocation relation appends one runtime function instance for each source
function.  These lemmas retain that exact pointwise correspondence so runtime
typing can invert an invoked defined function back to its validated source
body.
-/

namespace WasmGemmGnaf.Wasm.Core
namespace Exec

private theorem mapM_getElem?_origin {A B : Type} {f : A → Option B}
    {xs : List A} {ys : List B}
    (hmap : xs.mapM f = some ys) {index : Nat} {x : A}
    (hx : xs[index]? = some x) :
    ∃ y, f x = some y ∧ ys[index]? = some y := by
  induction xs generalizing ys index with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [List.mapM_cons] at hmap
      cases hhead : f head with
      | none => simp [hhead] at hmap
      | some headResult =>
          cases htail : tail.mapM f with
          | none => simp [hhead, htail] at hmap
          | some tailResults =>
              simp [hhead, htail] at hmap
              subst ys
              cases index with
              | zero =>
                  simp at hx
                  subst x
                  exact ⟨headResult, hhead, rfl⟩
              | succ index =>
                  simp only [List.getElem?_cons_succ] at hx
                  obtain ⟨result, hresult, hlookup⟩ := ih htail hx
                  exact ⟨result, hresult, by simpa using hlookup⟩

private theorem allocFuncs_preserves_func_lookup
    {source target : Store} {types : List DefType} {codes : List FuncCode}
    {modules : List ModuleInst} {addresses : List FuncAddr}
    (halloc : allocFuncs source types codes modules = some (target, addresses))
    {index : Nat} {function : FuncInst}
    (hlookup : source.funcs[index]? = some function) :
    target.funcs[index]? = some function := by
  induction types generalizing source target codes modules addresses with
  | nil =>
      cases codes <;> cases modules <;> simp [allocFuncs] at halloc
      rcases halloc with ⟨rfl, rfl⟩
      exact hlookup
  | cons type types ih =>
      cases codes with
      | nil => simp [allocFuncs] at halloc
      | cons code codes =>
          cases modules with
          | nil => simp [allocFuncs] at halloc
          | cons module modules =>
              simp only [allocFuncs] at halloc
              cases hrest : allocFuncs (allocFunc source type code module).1
                  types codes modules with
              | none => simp [hrest] at halloc
              | some result =>
                  rcases result with ⟨recursiveTarget, recursiveAddresses⟩
                  simp [hrest] at halloc
                  rcases halloc with ⟨rfl, rfl⟩
                  apply ih hrest
                  have hi : index < source.funcs.length :=
                    (List.getElem?_eq_some_iff.mp hlookup).1
                  rw [show (allocFunc source type code module).1.funcs =
                    source.funcs ++ [{ type := type, mod := module, code := code }]
                    by rfl]
                  rw [List.getElem?_append_left hi]
                  exact hlookup

private theorem allocFuncs_defined_lookup
    {source target : Store} {types : List DefType} {codes : List FuncCode}
    {modules : List ModuleInst} {addresses : List FuncAddr}
    (halloc : allocFuncs source types codes modules = some (target, addresses))
    {index : Nat} {type : DefType} {code : FuncCode} {module : ModuleInst}
    (htype : types[index]? = some type)
    (hcode : codes[index]? = some code)
    (hmodule : modules[index]? = some module) :
    addresses[index]? = some (source.funcs.length + index) ∧
      target.funcs[source.funcs.length + index]? =
        some { type := type, mod := module, code := code } := by
  induction types generalizing source target codes modules addresses index with
  | nil => simp at htype
  | cons headType types ih =>
      cases codes with
      | nil => simp at hcode
      | cons headCode codes =>
          cases modules with
          | nil => simp at hmodule
          | cons headModule modules =>
              simp only [allocFuncs] at halloc
              cases hrest : allocFuncs
                  (allocFunc source headType headCode headModule).1
                  types codes modules with
              | none => simp [hrest] at halloc
              | some result =>
                  rcases result with ⟨recursiveTarget, recursiveAddresses⟩
                  simp [hrest] at halloc
                  rcases halloc with ⟨rfl, rfl⟩
                  cases index with
                  | zero =>
                      simp at htype hcode hmodule
                      subst type
                      subst code
                      subst module
                      constructor
                      · rfl
                      · apply allocFuncs_preserves_func_lookup hrest
                        simp [allocFunc]
                  | succ index =>
                      simp only [List.getElem?_cons_succ] at htype hcode hmodule
                      have hrecursive := ih hrest htype hcode hmodule
                      constructor
                      · simpa [allocFunc, Nat.add_assoc, Nat.add_comm,
                          Nat.add_left_comm] using hrecursive.1
                      · simpa [allocFunc, Nat.add_assoc, Nat.add_comm,
                          Nat.add_left_comm] using hrecursive.2

/-- Every address in the defined-function range of a successful allocation
selects the exact source function closure installed at that index. -/
theorem AllocModule.defined_function_origin
    {source target : Store} {module : Module} {externAddresses : List ExternAddr}
    {globalValues : List Val} {tableRefs : List Ref}
    {elemRefs : List (List Ref)} {moduleInst : ModuleInst}
    (halloc : AllocModule source module externAddresses globalValues tableRefs
      elemRefs target moduleInst)
    {index : Nat} (hindex : index < module.funcs.length) :
    ∃ function sourceFunction sourceType,
      module.funcs[index]? = some sourceFunction ∧
      (allocTypes module.types)[sourceFunction.typeidx.val]? = some sourceType ∧
      target.funcs[source.funcs.length + index]? = some function ∧
      function.type = sourceType ∧
      function.code = .func sourceFunction ∧
      function.mod = moduleInst := by
  cases halloc with
  | mk htypes htagsI hglobalsI hmemsI htablesI hfuncsI hfa htags hglobals
      hmems htables hdatas helems hfunctionTypes hfunctions hmm₀ hexports hmm =>
      let sourceFunction := module.funcs[index]
      have hsourceFunction : module.funcs[index]? = some sourceFunction :=
        List.getElem?_eq_getElem hindex
      obtain ⟨sourceType, hsourceType, hfdts⟩ :=
        mapM_getElem?_origin hfunctionTypes hsourceFunction
      have hcode : (module.funcs.map FuncCode.func)[index]? =
          some (.func sourceFunction) := by
        simp [List.getElem?_map, hsourceFunction]
      have hmodule : (List.replicate module.funcs.length moduleInst)[index]? =
          some moduleInst := by simp [hindex]
      have horigin := allocFuncs_defined_lookup hfunctions hfdts hcode hmodule
      have hreturned := horigin.1
      rw [hfa] at hreturned
      simp [hindex] at hreturned
      have hlookup := horigin.2
      rw [← hreturned] at hlookup
      exact ⟨{ type := sourceType, mod := moduleInst, code := .func sourceFunction },
        sourceFunction, sourceType, hsourceFunction, by simpa [htypes] using hsourceType,
        hlookup,
        rfl, rfl, rfl⟩

theorem AllocModule.module_funcs_eq
    {source target : Store} {module : Module} {externAddresses : List ExternAddr}
    {globalValues : List Val} {tableRefs : List Ref}
    {elemRefs : List (List Ref)} {moduleInst : ModuleInst}
    (halloc : AllocModule source module externAddresses globalValues tableRefs
      elemRefs target moduleInst) :
    moduleInst.funcs = funcsxa externAddresses ++
      (List.range module.funcs.length).map
        (fun index => source.funcs.length + index) := by
  cases halloc with
  | mk htypes htagsI hglobalsI hmemsI htablesI hfuncsI hfa htags hglobals
      hmems htables hdatas helems hfunctionTypes hfunctions hmm₀ hexports hmm =>
      simp [hmm, hfuncsI, hfa]

/-- In the import-free public initialization used by the release harness,
every function address in the resulting module instance is a defined source
function and retains its exact source code and type. -/
theorem InstantiateA.defined_function_origin_of_mem
    {module : Module} {core : Config}
    (hinst : InstantiateA {} module [] core)
    {address : FuncAddr} (haddress : address ∈ core.1.frame.mod.funcs) :
    ∃ index function sourceFunction sourceType,
      index < module.funcs.length ∧
      address = index ∧
      module.funcs[index]? = some sourceFunction ∧
      (allocTypes module.types)[sourceFunction.typeidx.val]? = some sourceType ∧
      core.1.store.funcs[address]? = some function ∧
      function.type = sourceType ∧
      function.code = .func sourceFunction ∧
      function.mod = core.1.frame.mod := by
  cases hinst with
  | mk hmodule himportsLength himports hinitialModule hinitialState hglobals
      htables helems hheap halloc hdatas hdataInstructions helemMap
      helemInstructions hstart =>
      have hfuncs := halloc.module_funcs_eq
      rw [hheap] at hfuncs
      simp at hfuncs
      rw [hfuncs] at haddress
      have hindex : address < module.funcs.length := List.mem_range.mp haddress
      obtain ⟨function, sourceFunction, sourceType, hsource, htype, hlookup,
          hfunctionType, hcode, hmoduleInst⟩ :=
        halloc.defined_function_origin hindex
      refine ⟨address, function, sourceFunction, sourceType, hindex, rfl,
        hsource, htype, ?_, hfunctionType, hcode, hmoduleInst⟩
      simpa [hheap] using hlookup

end Exec
end WasmGemmGnaf.Wasm.Core
