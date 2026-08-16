import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false

/-!
# Function typing extracted from amended module validation

These inversion lemmas expose the declarative typing witness for a defined
function selected from a validated public Core module.  They add no runtime
assumption: the witnesses are exactly those carried by `Module_okA`.
-/

namespace WasmGemmGnaf.Wasm.Core

private theorem seqAll₂_left_getElem? {A B : Type} {R : A → B → Prop}
    {as : List A} {bs : List B} (hlen : SeqLen₂ as bs)
    (hall : SeqAll₂ R as bs) {index : Nat} {a : A}
    (ha : as[index]? = some a) : ∃ b, R a b := by
  have hiA : index < as.length := (List.getElem?_eq_some_iff.mp ha).1
  have hiB : index < bs.length := by simpa [SeqLen₂, hlen] using hiA
  let b := bs[index]
  exact ⟨b, hall index a b ha (List.getElem?_eq_getElem hiB)⟩

theorem Module_okA.func_ok_of_getElem? {module : Module}
    {moduleType : ModuleType} (hmodule : Module_okA module moduleType)
    {index : Nat} {func : Func} (hfunc : module.funcs[index]? = some func) :
    ∃ C dt, Func_okA C func dt := by
  cases hmodule with
  | mk htypes himportsLen himports htagsLen htags hglobals hmemsLen hmems
      htablesLen htables hfuncsLen hfuncs hdatasLen hdatas helemsLen helems
      hstart hexportsLen hexports hdisjoint hC hC' hxs hjtsI hgtsI hmtsI
      httsI hfuncsXt =>
      obtain ⟨dt, htyped⟩ :=
        seqAll₂_left_getElem? hfuncsLen hfuncs hfunc
      exact ⟨_, dt, htyped⟩

theorem Module_okA.func_body_typing_of_getElem? {module : Module}
    {moduleType : ModuleType} (hmodule : Module_okA module moduleType)
    {index : Nat} {func : Func} (hfunc : module.funcs[index]? = some func) :
    ∃ C dt dom cod lcts,
      C.types[func.typeidx.val]? = some dt ∧
      Expand dt (.func dom cod) ∧
      SeqLen₂ func.locals lcts ∧
      SeqAll₂ (Local_okA C) func.locals lcts ∧
      Expr_okA (Context.append C
        { locals := (ValTypes.toList dom).map (fun t => ⟨Init.set, t⟩) ++ lcts,
          labels := [ValTypes.toList cod],
          ret := some (ValTypes.toList cod) })
        func.body (ValTypes.toList cod) := by
  obtain ⟨C, dt, htyped⟩ := hmodule.func_ok_of_getElem? hfunc
  cases htyped with
  | @mk dom cod lcts hlookup hexpand hlen hall hbody =>
      exact ⟨C, dt, dom, cod, lcts, hlookup, hexpand, hlen, hall, hbody⟩

end WasmGemmGnaf.Wasm.Core
