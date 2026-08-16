import WasmGemmGnaf.Wasm.Core.RuntimeOrigin

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem StepsEraseA.preserveConfigTypeOriginsA {dts : List DefType}
    {z z' : State} {instructions instructions' : List AdminInstr}
    (h : StepsEraseA z instructions z' instructions')
    (horigin : ConfigTypeOriginsA dts (z, instructions)) :
    ConfigTypeOriginsA dts (z', instructions') := by
  induction h with
  | refl => exact horigin
  | @trans _ middle final source middleInstructions target hstep hsteps ih =>
      obtain ⟨event, hlabelled⟩ :=
        (stepA_iff_erased _ _ _ _).mpr hstep
      exact ih (hlabelled.preserveConfigTypeOriginsA horigin)

theorem Eval_exprEraseA.preserveTypeOriginsA {dts : List DefType}
    {z z' : State} {expression : Expr} {values : List Val}
    (h : Eval_exprEraseA z expression z' values)
    (hstore : StoreTypeOriginsA z.store dts)
    (hframe : z.frame.mod.types = dts) :
    StoreTypeOriginsA z'.store dts ∧ z'.frame.mod.types = dts := by
  cases h with
  | mk hsteps =>
      have hinitial : ConfigTypeOriginsA dts (z, exprAdmin expression) := by
        exact ⟨hstore, hframe, by simp [exprAdmin]⟩
      have hfinal :=
        StepsEraseA.preserveConfigTypeOriginsA hsteps hinitial
      exact ⟨hfinal.1, hfinal.2.1⟩

theorem EvalGlobalsA.preserveTypeOriginsA {dts : List DefType}
    {initial final : State} {globalTypes : List GlobalType}
    {expressions : List Expr} {values : List Val}
    (h : EvalGlobalsA initial globalTypes expressions final values)
    (hstore : StoreTypeOriginsA initial.store dts)
    (hframe : initial.frame.mod.types = dts) :
    StoreTypeOriginsA final.store dts ∧
      final.frame.mod.types = dts := by
  induction h with
  | nil => exact ⟨hstore, hframe⟩
  | @cons state evaluated final evaluatedStore allocatedStore frame address
      globalType globalTypes expression expressions value values
      heval hevaluated halloc hrest ih =>
      have hevaluatedOrigins :=
        heval.preserveTypeOriginsA hstore hframe
      subst evaluated
      simp only [allocGlobal, Prod.mk.injEq] at halloc
      rcases halloc with ⟨rfl, rfl⟩
      apply ih
      · exact hevaluatedOrigins.1.of_components rfl rfl rfl
      · simpa using hevaluatedOrigins.2

theorem EvalRefExprsA.preserveTypeOriginsA {dts : List DefType}
    {initial final : State} {expressions : List Expr} {references : List Ref}
    (h : EvalRefExprsA initial expressions final references)
    (hstore : StoreTypeOriginsA initial.store dts)
    (hframe : initial.frame.mod.types = dts) :
    StoreTypeOriginsA final.store dts ∧ final.frame.mod.types = dts := by
  induction h with
  | nil => exact ⟨hstore, hframe⟩
  | cons heval hrest ih =>
      obtain ⟨hevaluatedStore, hevaluatedFrame⟩ :=
        heval.preserveTypeOriginsA hstore hframe
      exact ih hevaluatedStore hevaluatedFrame

theorem EvalRefExprListsA.preserveTypeOriginsA {dts : List DefType}
    {initial final : State} {expressionLists : List (List Expr)}
    {referenceLists : List (List Ref)}
    (h : EvalRefExprListsA initial expressionLists final referenceLists)
    (hstore : StoreTypeOriginsA initial.store dts)
    (hframe : initial.frame.mod.types = dts) :
    StoreTypeOriginsA final.store dts ∧ final.frame.mod.types = dts := by
  induction h with
  | nil => exact ⟨hstore, hframe⟩
  | cons hhead htail ih =>
      obtain ⟨hheadStore, hheadFrame⟩ :=
        hhead.preserveTypeOriginsA hstore hframe
      exact ih hheadStore hheadFrame

private def SameOriginComponents (target source : Store) : Prop :=
  target.structs = source.structs ∧ target.arrays = source.arrays ∧
    target.funcs = source.funcs

private theorem SameOriginComponents.refl (store : Store) :
    SameOriginComponents store store := ⟨rfl, rfl, rfl⟩

private theorem SameOriginComponents.trans {first second third : Store}
    (h₁ : SameOriginComponents first second)
    (h₂ : SameOriginComponents second third) :
    SameOriginComponents first third :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    h₁.2.2.trans h₂.2.2⟩

private theorem allocTags_sameOriginComponents (source : Store)
    (types : List TagType) :
    SameOriginComponents (allocTags source types).1 source := by
  induction types generalizing source with
  | nil => exact SameOriginComponents.refl source
  | cons type types ih =>
      simpa [allocTags, allocTag] using
        ih ({ source with tags := source.tags ++ [{ type := type }] })

private theorem allocMems_sameOriginComponents (source : Store)
    (types : List MemType) :
    SameOriginComponents (allocMems source types).1 source := by
  induction types generalizing source with
  | nil => exact SameOriginComponents.refl source
  | cons type types ih =>
      simpa [allocMems, allocMem] using
        ih (allocMem source type).1

private theorem allocGlobals_sameOriginComponents {source target : Store}
    {types : List GlobalType} {values : List Val} {addresses : List GlobalAddr}
    (h : allocGlobals source types values = some (target, addresses)) :
    SameOriginComponents target source := by
  induction types generalizing source target values addresses with
  | nil =>
      cases values with
      | nil =>
          simp [allocGlobals] at h
          rcases h with ⟨rfl, rfl⟩
          exact SameOriginComponents.refl source
      | cons value values => simp [allocGlobals] at h
  | cons type types ih =>
      cases values with
      | nil => simp [allocGlobals] at h
      | cons value values =>
          simp only [allocGlobals] at h
          cases hrest : allocGlobals (allocGlobal source type value).1 types values with
          | none => simp [hrest] at h
          | some result =>
              rcases result with ⟨recursiveTarget, recursiveAddresses⟩
              simp [hrest] at h
              rcases h with ⟨rfl, rfl⟩
              have hrecursive := ih hrest
              exact hrecursive.trans (by
                simp [SameOriginComponents, allocGlobal])

private theorem allocTables_sameOriginComponents {source target : Store}
    {types : List TableType} {values : List Ref} {addresses : List TableAddr}
    (h : allocTables source types values = some (target, addresses)) :
    SameOriginComponents target source := by
  induction types generalizing source target values addresses with
  | nil =>
      cases values with
      | nil =>
          simp [allocTables] at h
          rcases h with ⟨rfl, rfl⟩
          exact SameOriginComponents.refl source
      | cons value values => simp [allocTables] at h
  | cons type types ih =>
      cases values with
      | nil => simp [allocTables] at h
      | cons value values =>
          simp only [allocTables] at h
          cases hrest : allocTables (allocTable source type value).1
              types values with
          | none => simp [hrest] at h
          | some result =>
              rcases result with ⟨recursiveTarget, recursiveAddresses⟩
              simp [hrest] at h
              rcases h with ⟨rfl, rfl⟩
              have hrecursive := ih hrest
              exact hrecursive.trans (by
                simp [SameOriginComponents, allocTable])

private theorem allocDatas_sameOriginComponents {source target : Store}
    {types : List DataType} {values : List (List Byte)}
    {addresses : List DataAddr}
    (h : allocDatas source types values = some (target, addresses)) :
    SameOriginComponents target source := by
  induction types generalizing source target values addresses with
  | nil =>
      cases values with
      | nil =>
          simp [allocDatas] at h
          rcases h with ⟨rfl, rfl⟩
          exact SameOriginComponents.refl source
      | cons value values => simp [allocDatas] at h
  | cons type types ih =>
      cases values with
      | nil => simp [allocDatas] at h
      | cons value values =>
          simp only [allocDatas] at h
          cases hrest : allocDatas (allocData source type value).1
              types values with
          | none => simp [hrest] at h
          | some result =>
              rcases result with ⟨recursiveTarget, recursiveAddresses⟩
              simp [hrest] at h
              rcases h with ⟨rfl, rfl⟩
              have hrecursive := ih hrest
              exact hrecursive.trans (by
                simp [SameOriginComponents, allocData])

private theorem allocElems_sameOriginComponents {source target : Store}
    {types : List ElemType} {values : List (List Ref)}
    {addresses : List ElemAddr}
    (h : allocElems source types values = some (target, addresses)) :
    SameOriginComponents target source := by
  induction types generalizing source target values addresses with
  | nil =>
      cases values with
      | nil =>
          simp [allocElems] at h
          rcases h with ⟨rfl, rfl⟩
          exact SameOriginComponents.refl source
      | cons value values => simp [allocElems] at h
  | cons type types ih =>
      cases values with
      | nil => simp [allocElems] at h
      | cons value values =>
          simp only [allocElems] at h
          cases hrest : allocElems (allocElem source type value).1
              types values with
          | none => simp [hrest] at h
          | some result =>
              rcases result with ⟨recursiveTarget, recursiveAddresses⟩
              simp [hrest] at h
              rcases h with ⟨rfl, rfl⟩
              have hrecursive := ih hrest
              exact hrecursive.trans (by
                simp [SameOriginComponents, allocElem])

private theorem allocFuncs_storeTypeOriginsA {dts : List DefType}
    {source target : Store} {types : List DefType} {codes : List FuncCode}
    {modules : List ModuleInst} {addresses : List FuncAddr}
    (hsource : StoreTypeOriginsA source dts)
    (htypes : ∀ type ∈ types, ∃ i : Nat, dts[i]? = some type)
    (hmodules : ∀ module ∈ modules, module.types = dts)
    (h : allocFuncs source types codes modules = some (target, addresses)) :
    StoreTypeOriginsA target dts := by
  induction types generalizing source target codes modules addresses with
  | nil =>
      cases codes <;> cases modules <;> simp [allocFuncs] at h
      rcases h with ⟨rfl, rfl⟩
      exact hsource
  | cons type types ih =>
      cases codes with
      | nil => simp [allocFuncs] at h
      | cons code codes =>
          cases modules with
          | nil => simp [allocFuncs] at h
          | cons module modules =>
              have htype : ∃ i : Nat, dts[i]? = some type :=
                htypes type (by simp)
              have htailTypes : ∀ tailType ∈ types,
                  ∃ i : Nat, dts[i]? = some tailType := by
                intro tailType hmember
                exact htypes tailType (by simp [hmember])
              have hmodule : module.types = dts :=
                hmodules module (by simp)
              have htailModules : ∀ tailModule ∈ modules,
                  tailModule.types = dts := by
                intro tailModule hmember
                exact hmodules tailModule (by simp [hmember])
              have hfirst : StoreTypeOriginsA
                  (allocFunc source type code module).1 dts := by
                rcases hsource with ⟨hstructs, harrays, hfuncs⟩
                refine ⟨?_, ?_, ?_⟩
                · intro struct hmember
                  exact hstructs hmember
                · intro array hmember
                  exact harrays hmember
                · intro candidate hmember
                  simp only [allocFunc, List.mem_append,
                    List.mem_singleton] at hmember
                  rcases hmember with hmember | rfl
                  · exact hfuncs hmember
                  · exact ⟨htype, hmodule⟩
              simp only [allocFuncs] at h
              cases hrest : allocFuncs (allocFunc source type code module).1
                  types codes modules with
              | none => simp [hrest] at h
              | some result =>
                  rcases result with ⟨recursiveTarget, recursiveAddresses⟩
                  simp [hrest] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact ih hfirst htailTypes htailModules hrest

private theorem functionTypes_origin {dts functionTypes : List DefType}
    {functions : List Func}
    (h : functions.mapM (fun function => dts[function.typeidx.val]?) =
      some functionTypes) :
    ∀ type ∈ functionTypes, ∃ i : Nat, dts[i]? = some type := by
  induction functions generalizing functionTypes with
  | nil =>
      simp at h
      subst functionTypes
      simp
  | cons function functions ih =>
      simp only [List.mapM_cons] at h
      cases htype : dts[function.typeidx.val]? with
      | none => simp [htype] at h
      | some type =>
          cases htail : functions.mapM
              (fun tailFunction => dts[tailFunction.typeidx.val]?) with
          | none => simp [htype, htail] at h
          | some tailTypes =>
              simp [htype, htail] at h
              subst functionTypes
              intro candidate hmember
              simp only [List.mem_cons] at hmember
              rcases hmember with rfl | htailMember
              · exact ⟨function.typeidx.val, htype⟩
              · exact ih htail candidate htailMember

theorem AllocModule.storeTypeOriginsA {source target : Store}
    {module : Module} {externAddresses : List ExternAddr}
    {globalValues : List Val} {tableRefs : List Ref}
    {elemRefs : List (List Ref)} {moduleInst : ModuleInst}
    (h : AllocModule source module externAddresses globalValues tableRefs
      elemRefs target moduleInst)
    (hsource : StoreTypeOriginsA source (allocTypes module.types)) :
    StoreTypeOriginsA target (allocTypes module.types) := by
  cases h with
  | @mk s₁ s₂ s₃ s₄ s₅ s₆ s₇ m xas valG refT refE
      dts fdts aaI gaI maI taI faI aa ga ma ta fa da ea xis mm mm₀
      hdts haaI hgaI hmaI htaI hfaI hfa htags hglobals hmems htables
      hdatas helems hfunctionTypes hfuncs hmm₀ hexports hmm =>
      subst dts
      have hs₁ : SameOriginComponents s₁ source := by
        have hs := allocTags_sameOriginComponents source
          (module.tags.map fun tag =>
            substAllTagType tag.tagtype
              ((allocTypes module.types).map TypeUse.defd))
        rw [htags] at hs
        exact hs
      have hs₂ : SameOriginComponents s₂ source :=
        (allocGlobals_sameOriginComponents hglobals).trans hs₁
      have hs₃ : SameOriginComponents s₃ source := by
        have hs := allocMems_sameOriginComponents s₂
          (module.mems.map fun mem =>
            substAllMemType mem.memtype
              ((allocTypes module.types).map TypeUse.defd))
        rw [hmems] at hs
        exact hs.trans hs₂
      have hs₄ : SameOriginComponents s₄ source :=
        (allocTables_sameOriginComponents htables).trans hs₃
      have hs₅ : SameOriginComponents s₅ source :=
        (allocDatas_sameOriginComponents hdatas).trans hs₄
      have hs₆ : SameOriginComponents s₆ source :=
        (allocElems_sameOriginComponents helems).trans hs₅
      have hsource₆ : StoreTypeOriginsA s₆ (allocTypes module.types) :=
        hsource.of_components hs₆.1 hs₆.2.1 hs₆.2.2
      have hmmTypes : moduleInst.types = allocTypes module.types := by
        rw [hmm]
      have hmodules : ∀ allocatedModule ∈
          List.replicate module.funcs.length moduleInst,
          allocatedModule.types = allocTypes module.types := by
        intro candidate hmember
        have : candidate = moduleInst := List.eq_of_mem_replicate hmember
        subst candidate
        exact hmmTypes
      exact allocFuncs_storeTypeOriginsA hsource₆
        (functionTypes_origin hfunctionTypes) hmodules hfuncs

theorem InstantiateA.frameTypes_eq_allocTypes
    {m : Module} {core : Config}
    (h : InstantiateA ({} : Store) m [] core) :
    core.1.frame.mod.types = allocTypes m.types := by
  exact h.allocatedTypesFrom

theorem InstantiateA.storeTypeOriginsA {m : Module} {core : Config}
    (h : InstantiateA ({} : Store) m [] core) :
    StoreTypeOriginsA core.1.store (allocTypes m.types) := by
  cases h with
  | @mk allocatedStore heapBase module externAddresses moduleType
      initialState globalsState tablesState elementsState initialModuleInst
      moduleInst globalValues tableRefs elemRefs dataInstructions
      elemInstructions dataInstructionLists elemInstructionLists
      startInstruction hmodule himportsLength himports hinitialModule
      hinitialState hglobals htables helems hheap halloc hdatas
      hdataInstructions helemLists helemInstructions hstart =>
      let dts := allocTypes m.types
      have hempty : StoreTypeOriginsA ({} : Store) dts := by
        simp [StoreTypeOriginsA]
      have hinitialStore : StoreTypeOriginsA initialState.store dts := by
        rw [hinitialState]
        exact hempty
      have hinitialFrame : initialState.frame.mod.types = dts := by
        rw [hinitialState, hinitialModule]
      obtain ⟨hglobalsStore, hglobalsFrame⟩ :=
        hglobals.preserveTypeOriginsA hinitialStore hinitialFrame
      obtain ⟨htablesStore, htablesFrame⟩ :=
        htables.preserveTypeOriginsA hglobalsStore hglobalsFrame
      obtain ⟨helementsStore, helementsFrame⟩ :=
        helems.preserveTypeOriginsA htablesStore htablesFrame
      have hheapOrigin : StoreTypeOriginsA heapBase dts := by
        rw [hheap]
        rcases helementsStore with ⟨hstructs, harrays, hfuncs⟩
        refine ⟨?_, ?_, ?_⟩
        · intro struct hmember
          exact hstructs hmember
        · intro array hmember
          exact harrays hmember
        · simp
      simpa [dts] using halloc.storeTypeOriginsA hheapOrigin

end WasmGemmGnaf.Wasm.Core.Exec
