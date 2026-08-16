/-
  The sole public amended Core instantiation relation.

  The pinned `4.4-execution.modules.spectec` relation is retained in
  `Instantiation.lean` as an authority reference.  Its initializer expressions
  are required to return to their source state, which excludes the managed-heap
  allocation instructions admitted by `Expr_const`.  AMD-014 repairs exactly
  that mismatch: post-expression states are threaded in source order, temporary
  globals remain available to later `global.get` instructions, and the resulting
  structure and array heaps are carried into canonical module allocation.
-/
import WasmGemmGnaf.Wasm.Core.ConstEval
import WasmGemmGnaf.Wasm.Core.Instantiation
import WasmGemmGnaf.Wasm.Core.Validation.ModulesCombinedAmended

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

namespace Store

/-- Preserve the source store's ordinary components while retaining every
managed structure and array allocated during constant-expression evaluation.
The AMD-014 constant grammar has no other state-writing instruction. -/
def carryConstHeap (base evaluated : Store) : Store :=
  { base with structs := evaluated.structs, arrays := evaluated.arrays }

@[simp] theorem carryConstHeap_structs (base evaluated : Store) :
    (carryConstHeap base evaluated).structs = evaluated.structs := rfl

@[simp] theorem carryConstHeap_arrays (base evaluated : Store) :
    (carryConstHeap base evaluated).arrays = evaluated.arrays := rfl

@[simp] theorem carryConstHeap_globals (base evaluated : Store) :
    (carryConstHeap base evaluated).globals = base.globals := rfl

@[simp] theorem carryConstHeap_funcs (base evaluated : Store) :
    (carryConstHeap base evaluated).funcs = base.funcs := rfl

end Store

/-- AMD-014 global initialization.  The evaluated state, rather than the source
state, supplies the store in which the temporary global is allocated; this both
threads GC allocation and makes the new global available to later expressions. -/
inductive EvalGlobalsA :
    State → List GlobalType → List Expr → State → List Val → Prop where
  | nil {state : State} : EvalGlobalsA state [] [] state []
  | cons {state evaluated final : State} {evaluatedStore allocatedStore : Store}
      {frame : Frame} {address : GlobalAddr} {globalType : GlobalType}
      {globalTypes : List GlobalType} {expression : Expr}
      {expressions : List Expr} {value : Val} {values : List Val} :
      Eval_exprEraseA state expression evaluated [value] →
      evaluated = ⟨evaluatedStore, frame⟩ →
      allocGlobal evaluatedStore globalType value = (allocatedStore, address) →
      EvalGlobalsA
        ⟨allocatedStore,
          { frame with mod :=
              { frame.mod with globals := frame.mod.globals ++ [address] } }⟩
        globalTypes expressions final values →
      EvalGlobalsA state (globalType :: globalTypes)
        (expression :: expressions) final (value :: values)

/-- Evaluate a source-ordered list of reference-producing constant expressions,
threading every post-expression state. -/
inductive EvalRefExprsA : State → List Expr → State → List Ref → Prop where
  | nil {state : State} : EvalRefExprsA state [] state []
  | cons {state evaluated final : State} {expression : Expr}
      {expressions : List Expr} {reference : Ref} {references : List Ref} :
      Eval_exprEraseA state expression evaluated [.ref reference] →
      EvalRefExprsA evaluated expressions final references →
      EvalRefExprsA state (expression :: expressions) final
        (reference :: references)

/-- Evaluate element-segment expression lists in module order and each segment's
expressions in source order. -/
inductive EvalRefExprListsA :
    State → List (List Expr) → State → List (List Ref) → Prop where
  | nil {state : State} : EvalRefExprListsA state [] state []
  | cons {state afterHead final : State} {expressions : List Expr}
      {expressionLists : List (List Expr)} {references : List Ref}
      {referenceLists : List (List Ref)} :
      EvalRefExprsA state expressions afterHead references →
      EvalRefExprListsA afterHead expressionLists final referenceLists →
      EvalRefExprListsA state (expressions :: expressionLists) final
        (references :: referenceLists)

/-! ## Executable amended constant-initializer layer -/

/-- Execute and temporarily allocate a source-ordered global list. -/
def evalGlobals : State → List GlobalType → List Expr →
    Option (State × List Val)
  | state, [], [] => some (state, [])
  | state, globalType :: globalTypes, expression :: expressions => do
      let (evaluated, produced) ← evalConstExpr state expression
      let value ← exactlyOne produced
      let (allocatedStore, address) :=
        allocGlobal evaluated.store globalType value
      let next : State :=
        ⟨allocatedStore,
          { evaluated.frame with mod :=
              { evaluated.frame.mod with
                globals := evaluated.frame.mod.globals ++ [address] } }⟩
      let (final, values) ← evalGlobals next globalTypes expressions
      pure (final, value :: values)
  | _, _, _ => none

/-- Execute a source-ordered reference-initializer list. -/
def evalRefExprs : State → List Expr → Option (State × List Ref)
  | state, [] => some (state, [])
  | state, expression :: expressions => do
      let (evaluated, produced) ← evalConstExpr state expression
      let value ← exactlyOne produced
      let .ref reference := value | none
      let (final, references) ← evalRefExprs evaluated expressions
      pure (final, reference :: references)

/-- Execute element-segment initializer lists in module order. -/
def evalRefExprLists : State → List (List Expr) →
    Option (State × List (List Ref))
  | state, [] => some (state, [])
  | state, expressions :: expressionLists => do
      let (afterHead, references) ← evalRefExprs state expressions
      let (final, referenceLists) ←
        evalRefExprLists afterHead expressionLists
      pure (final, references :: referenceLists)

/-- The executable global evaluator constructs exactly the AMD-014 relation.
This theorem is the kernel-facing target of mutation M24. -/
theorem evalGlobals_sound {state final : State}
    {globalTypes : List GlobalType} {expressions : List Expr}
    {values : List Val}
    (hconst : ∀ expression ∈ expressions,
      ∃ context, Expr_const context expression)
    (h : evalGlobals state globalTypes expressions = some (final, values)) :
    EvalGlobalsA state globalTypes expressions final values := by
  induction globalTypes generalizing state expressions final values with
  | nil =>
      cases expressions with
      | nil =>
          simp [evalGlobals] at h
          rcases h with ⟨rfl, rfl⟩
          exact .nil
      | cons expression expressions => simp [evalGlobals] at h
  | cons globalType globalTypes ih =>
      cases expressions with
      | nil => simp [evalGlobals] at h
      | cons expression expressions =>
          obtain ⟨context, hexpression⟩ := hconst expression (by simp)
          have hrest : ∀ next ∈ expressions,
              ∃ context, Expr_const context next := by
            intro next hmember
            exact hconst next (by simp [hmember])
          cases heval : evalConstExpr state expression with
          | none => simp [evalGlobals, heval] at h
          | some evaluatedResult =>
              rcases evaluatedResult with ⟨evaluated, produced⟩
              cases hone : exactlyOne produced with
              | none => simp [evalGlobals, heval, hone] at h
              | some value =>
                  have hproduced := exactlyOne_eq_some hone
                  rw [hproduced] at heval
                  let allocated := allocGlobal evaluated.store globalType value
                  let next : State :=
                    ⟨allocated.1,
                      { evaluated.frame with mod :=
                          { evaluated.frame.mod with globals :=
                              evaluated.frame.mod.globals ++ [allocated.2] } }⟩
                  cases hrec : evalGlobals next globalTypes expressions with
                  | none =>
                      simp [evalGlobals, heval, exactlyOne, next, allocated,
                        hrec] at h
                  | some recursiveResult =>
                      rcases recursiveResult with ⟨recursiveFinal, recursiveValues⟩
                      simp [evalGlobals, heval, exactlyOne, next, allocated,
                        hrec] at h
                      rcases h with ⟨rfl, rfl⟩
                      apply EvalGlobalsA.cons
                        (evalConstExpr_sound hexpression heval) rfl rfl
                      exact ih hrest hrec

/-- The executable flat reference evaluator constructs the amended relation. -/
theorem evalRefExprs_sound {state final : State}
    {expressions : List Expr} {references : List Ref}
    (hconst : ∀ expression ∈ expressions,
      ∃ context, Expr_const context expression)
    (h : evalRefExprs state expressions = some (final, references)) :
    EvalRefExprsA state expressions final references := by
  induction expressions generalizing state final references with
  | nil =>
      simp [evalRefExprs] at h
      rcases h with ⟨rfl, rfl⟩
      exact .nil
  | cons expression expressions ih =>
      obtain ⟨context, hexpression⟩ := hconst expression (by simp)
      have hrest : ∀ next ∈ expressions,
          ∃ context, Expr_const context next := by
        intro next hmember
        exact hconst next (by simp [hmember])
      cases heval : evalConstExpr state expression with
      | none => simp [evalRefExprs, heval] at h
      | some evaluatedResult =>
          rcases evaluatedResult with ⟨evaluated, produced⟩
          cases hone : exactlyOne produced with
          | none => simp [evalRefExprs, heval, hone] at h
          | some value =>
              have hproduced := exactlyOne_eq_some hone
              rw [hproduced] at heval
              cases value with
              | num numeric =>
                  simp [evalRefExprs, heval, exactlyOne] at h
              | vec vector =>
                  simp [evalRefExprs, heval, exactlyOne] at h
              | ref reference =>
                  cases hrec : evalRefExprs evaluated expressions with
                  | none =>
                      simp [evalRefExprs, heval, exactlyOne, hrec] at h
                  | some recursiveResult =>
                      rcases recursiveResult with
                        ⟨recursiveFinal, recursiveReferences⟩
                      simp [evalRefExprs, heval, exactlyOne, hrec] at h
                      rcases h with ⟨rfl, rfl⟩
                      exact .cons (evalConstExpr_sound hexpression heval)
                        (ih hrest hrec)

/-- The executable nested evaluator constructs the amended element relation. -/
theorem evalRefExprLists_sound {state final : State}
    {expressionLists : List (List Expr)} {referenceLists : List (List Ref)}
    (hconst : ∀ expressions ∈ expressionLists,
      ∀ expression ∈ expressions, ∃ context, Expr_const context expression)
    (h : evalRefExprLists state expressionLists =
      some (final, referenceLists)) :
    EvalRefExprListsA state expressionLists final referenceLists := by
  induction expressionLists generalizing state final referenceLists with
  | nil =>
      simp [evalRefExprLists] at h
      rcases h with ⟨rfl, rfl⟩
      exact .nil
  | cons expressions expressionLists ih =>
      have hhead := hconst expressions (by simp)
      have hrest : ∀ next ∈ expressionLists,
          ∀ expression ∈ next, ∃ context, Expr_const context expression := by
        intro next hmember
        exact hconst next (by simp [hmember])
      cases hheadEval : evalRefExprs state expressions with
      | none => simp [evalRefExprLists, hheadEval] at h
      | some headResult =>
          rcases headResult with ⟨afterHead, references⟩
          cases htailEval : evalRefExprLists afterHead expressionLists with
          | none => simp [evalRefExprLists, hheadEval, htailEval] at h
          | some tailResult =>
              rcases tailResult with ⟨recursiveFinal, recursiveReferences⟩
              simp [evalRefExprLists, hheadEval, htailEval] at h
              rcases h with ⟨rfl, rfl⟩
              exact .cons (evalRefExprs_sound hhead hheadEval)
                (ih hrest htailEval)

/-! ## Executable canonical module allocation -/

/-- Compute the source `allocmodule` fixed point.  Function addresses are known
before function instances are installed, so the final module instance can be
constructed first and copied into each function closure; the returned address
list is checked against those predicted addresses. -/
def allocModuleA? (sourceStore : Store) (module : Module)
    (externAddresses : List ExternAddr) (globalValues : List Val)
    (tableRefs : List Ref) (elemRefs : List (List Ref)) :
    Option (Store × ModuleInst) := do
  let closedTypes := allocTypes module.types
  let importedTags := tagsxa externAddresses
  let importedGlobals := globalsxa externAddresses
  let importedMems := memsxa externAddresses
  let importedTables := tablesxa externAddresses
  let importedFuncs := funcsxa externAddresses
  let predictedFuncs :=
    (List.range module.funcs.length).map
      (fun index => sourceStore.funcs.length + index)
  let (afterTags, tagAddresses) :=
    allocTags sourceStore
      (module.tags.map fun tag =>
        substAllTagType tag.tagtype (closedTypes.map TypeUse.defd))
  let (afterGlobals, globalAddresses) ←
    allocGlobals afterTags
      (module.globals.map fun global =>
        substAllGlobalType global.globaltype
          (closedTypes.map TypeUse.defd)) globalValues
  let (afterMems, memAddresses) :=
    allocMems afterGlobals
      (module.mems.map fun memory =>
        substAllMemType memory.memtype (closedTypes.map TypeUse.defd))
  let (afterTables, tableAddresses) ←
    allocTables afterMems
      (module.tables.map fun table =>
        substAllTableType table.tabletype
          (closedTypes.map TypeUse.defd)) tableRefs
  let (afterDatas, dataAddresses) ←
    allocDatas afterTables (module.datas.map fun _ => DataType.ok)
      (module.datas.map Data.bytes)
  let (afterElems, elemAddresses) ←
    allocElems afterDatas
      (module.elems.map fun elem =>
        substAllRefType elem.reftype (closedTypes.map TypeUse.defd)) elemRefs
  let functionTypes ←
    module.funcs.mapM fun function => closedTypes[function.typeidx.val]?
  let addressModule : ModuleInst :=
    { tags := importedTags ++ tagAddresses,
      globals := importedGlobals ++ globalAddresses,
      mems := importedMems ++ memAddresses,
      tables := importedTables ++ tableAddresses,
      funcs := importedFuncs ++ predictedFuncs }
  let exportInstances ← allocExports addressModule module.exports
  let moduleInst : ModuleInst :=
    { types := closedTypes,
      tags := importedTags ++ tagAddresses,
      globals := importedGlobals ++ globalAddresses,
      mems := importedMems ++ memAddresses,
      tables := importedTables ++ tableAddresses,
      funcs := importedFuncs ++ predictedFuncs,
      datas := dataAddresses,
      elems := elemAddresses,
      exports := exportInstances }
  let (allocatedStore, allocatedFuncs) ←
    allocFuncs afterElems functionTypes (module.funcs.map FuncCode.func)
      (List.replicate module.funcs.length moduleInst)
  if allocatedFuncs = predictedFuncs then
    some (allocatedStore, moduleInst)
  else none

/-- The executable allocator returns only witnesses of the pinned allocation
relation (with AMD-014's heap-carried source store). -/
theorem allocModuleA?_sound {sourceStore allocatedStore : Store}
    {module : Module} {externAddresses : List ExternAddr}
    {globalValues : List Val} {tableRefs : List Ref}
    {elemRefs : List (List Ref)} {moduleInst : ModuleInst}
    (h : allocModuleA? sourceStore module externAddresses globalValues
      tableRefs elemRefs = some (allocatedStore, moduleInst)) :
    AllocModule sourceStore module externAddresses globalValues tableRefs
      elemRefs allocatedStore moduleInst := by
  unfold allocModuleA? at h
  let closedTypes := allocTypes module.types
  let importedTags := tagsxa externAddresses
  let importedGlobals := globalsxa externAddresses
  let importedMems := memsxa externAddresses
  let importedTables := tablesxa externAddresses
  let importedFuncs := funcsxa externAddresses
  let predictedFuncs := (List.range module.funcs.length).map
    (fun index => sourceStore.funcs.length + index)
  let tagsResult := allocTags sourceStore
    (module.tags.map fun tag =>
      substAllTagType tag.tagtype (closedTypes.map TypeUse.defd))
  rcases htags : tagsResult with ⟨afterTags, tagAddresses⟩
  cases hglobals : allocGlobals afterTags
      (module.globals.map fun global =>
        substAllGlobalType global.globaltype
          (closedTypes.map TypeUse.defd)) globalValues with
  | none =>
      simp [closedTypes, importedTags, importedGlobals, importedMems,
        importedTables, importedFuncs, predictedFuncs, tagsResult, htags,
        hglobals] at h
  | some globalsResult =>
      rcases globalsResult with ⟨afterGlobals, globalAddresses⟩
      let memsResult := allocMems afterGlobals
        (module.mems.map fun memory =>
          substAllMemType memory.memtype (closedTypes.map TypeUse.defd))
      rcases hmems : memsResult with ⟨afterMems, memAddresses⟩
      cases htables : allocTables afterMems
          (module.tables.map fun table =>
            substAllTableType table.tabletype
              (closedTypes.map TypeUse.defd)) tableRefs with
      | none =>
          simp [closedTypes, importedTags, importedGlobals, importedMems,
            importedTables, importedFuncs, predictedFuncs, tagsResult, htags,
            hglobals, memsResult, hmems, htables] at h
      | some tablesResult =>
          rcases tablesResult with ⟨afterTables, tableAddresses⟩
          cases hdatas : allocDatas afterTables
              (module.datas.map fun _ => DataType.ok)
              (module.datas.map Data.bytes) with
          | none =>
              simp [closedTypes, importedTags, importedGlobals, importedMems,
                importedTables, importedFuncs, predictedFuncs, tagsResult,
                htags, hglobals, memsResult, hmems, htables, hdatas] at h
          | some datasResult =>
              rcases datasResult with ⟨afterDatas, dataAddresses⟩
              cases helems : allocElems afterDatas
                  (module.elems.map fun elem =>
                    substAllRefType elem.reftype
                      (closedTypes.map TypeUse.defd)) elemRefs with
              | none =>
                  simp [closedTypes, importedTags, importedGlobals,
                    importedMems, importedTables, importedFuncs,
                    predictedFuncs, tagsResult, htags, hglobals, memsResult,
                    hmems, htables, hdatas, helems] at h
              | some elemsResult =>
                  rcases elemsResult with ⟨afterElems, elemAddresses⟩
                  cases hfunctionTypes : module.funcs.mapM
                      (fun function => closedTypes[function.typeidx.val]?) with
                  | none =>
                      simp [closedTypes, importedTags, importedGlobals,
                        importedMems, importedTables, importedFuncs,
                        predictedFuncs, tagsResult, htags, hglobals,
                        memsResult, hmems, htables, hdatas, helems,
                        hfunctionTypes] at h
                  | some functionTypes =>
                      let addressModule : ModuleInst :=
                        { tags := importedTags ++ tagAddresses,
                          globals := importedGlobals ++ globalAddresses,
                          mems := importedMems ++ memAddresses,
                          tables := importedTables ++ tableAddresses,
                          funcs := importedFuncs ++ predictedFuncs }
                      cases hexports : allocExports addressModule module.exports with
                      | none =>
                          simp [closedTypes, importedTags, importedGlobals,
                            importedMems, importedTables, importedFuncs,
                            predictedFuncs, tagsResult, htags, hglobals,
                            memsResult, hmems, htables, hdatas, helems,
                            hfunctionTypes, addressModule, hexports] at h
                      | some exportInstances =>
                          let computedModule : ModuleInst :=
                            { types := closedTypes,
                              tags := importedTags ++ tagAddresses,
                              globals := importedGlobals ++ globalAddresses,
                              mems := importedMems ++ memAddresses,
                              tables := importedTables ++ tableAddresses,
                              funcs := importedFuncs ++ predictedFuncs,
                              datas := dataAddresses,
                              elems := elemAddresses,
                              exports := exportInstances }
                          cases hfuncs : allocFuncs afterElems functionTypes
                              (module.funcs.map FuncCode.func)
                              (List.replicate module.funcs.length computedModule) with
                          | none =>
                              simp [closedTypes, importedTags, importedGlobals,
                                importedMems, importedTables, importedFuncs,
                                predictedFuncs, tagsResult, htags, hglobals,
                                memsResult, hmems, htables, hdatas, helems,
                                hfunctionTypes, addressModule, hexports,
                                computedModule, hfuncs] at h
                          | some funcsResult =>
                              rcases funcsResult with
                                ⟨computedStore, allocatedFuncs⟩
                              by_cases haddresses :
                                  allocatedFuncs = predictedFuncs
                              · simp [closedTypes, importedTags, importedGlobals,
                                  importedMems, importedTables, importedFuncs,
                                  predictedFuncs, tagsResult, htags, hglobals,
                                  memsResult, hmems, htables, hdatas, helems,
                                  hfunctionTypes, addressModule, hexports,
                                  computedModule, hfuncs, haddresses] at h
                                rcases h with ⟨rfl, rfl⟩
                                exact .mk rfl rfl rfl rfl rfl rfl rfl
                                  (by simpa [tagsResult] using htags)
                                  hglobals
                                  (by simpa [memsResult] using hmems)
                                  htables hdatas helems
                                  (by simpa [closedTypes] using hfunctionTypes)
                                  (by simpa [haddresses, computedModule] using hfuncs)
                                  rfl hexports rfl
                              · simp [closedTypes, importedTags, importedGlobals,
                                  importedMems, importedTables, importedFuncs,
                                  predictedFuncs, tagsResult, htags, hglobals,
                                  memsResult, hmems, htables, hdatas, helems,
                                  hfunctionTypes, addressModule, hexports,
                                  computedModule, hfuncs, haddresses] at h

/-- Execute all deterministic phases of AMD-014 instantiation.  Validation is
checked by the caller and reflected into `InstantiateA` by the soundness theorem
below; this function contains no proof or conclusion parameter. -/
def instantiateA? (sourceStore : Store) (module : Module)
    (externAddresses : List ExternAddr) : Option Config := do
  let initialModuleInst : ModuleInst :=
    { types := allocTypes module.types,
      globals := globalsxa externAddresses,
      funcs := funcsxa externAddresses ++
        (List.range module.funcs.length).map
          (fun index => sourceStore.funcs.length + index) }
  let initialState : State := ⟨sourceStore, { mod := initialModuleInst }⟩
  let (globalsState, globalValues) ←
    evalGlobals initialState
      (module.globals.map Global.globaltype)
      (module.globals.map Global.init)
  let (tablesState, tableRefs) ←
    evalRefExprs globalsState (module.tables.map Table.init)
  let (elementsState, elemRefs) ←
    evalRefExprLists tablesState (module.elems.map Elem.init)
  let heapBase := Store.carryConstHeap sourceStore elementsState.store
  let (allocatedStore, moduleInst) ←
    allocModuleA? heapBase module externAddresses globalValues tableRefs elemRefs
  let dataInstructionLists ← module.datas.zipIdx.mapM fun pair =>
    runData_ (TypeIdx.ofNat pair.2) pair.1
  let elemInstructionLists ← module.elems.zipIdx.mapM fun pair =>
    runElem_ (TypeIdx.ofNat pair.2) pair.1
  let dataInstructions := dataInstructionLists.flatten
  let elemInstructions := elemInstructionLists.flatten
  let startInstruction := module.start.map fun start => Instr.call start.funcidx
  pure
    (⟨allocatedStore, { mod := moduleInst }⟩,
      plains elemInstructions ++ plains dataInstructions ++
        plains startInstruction.toList)

/-- AMD-014 public instantiation.  Validation uses the combined amended module
judgment, initializer evaluation is state-threaded, and `AllocModule` starts from
the original store with exactly the constant-expression GC heaps carried over.
The pinned `Instantiate` remains available only as an authority reference. -/
inductive InstantiateA : Store → Module → List ExternAddr → Config → Prop where
  | mk {sourceStore allocatedStore heapBase : Store} {module : Module}
      {externAddresses : List ExternAddr} {moduleType : ModuleType}
      {initialState globalsState tablesState elementsState : State}
      {initialModuleInst moduleInst : ModuleInst} {globalValues : List Val}
      {tableRefs : List Ref} {elemRefs : List (List Ref)}
      {dataInstructions elemInstructions : List Instr}
      {dataInstructionLists elemInstructionLists : List (List Instr)}
      {startInstruction : Option Instr} :
      Module_okA module moduleType →
      SeqLen₂ externAddresses moduleType.imports →
      SeqAll₂ (fun address externType =>
        Externaddr_ok sourceStore address externType)
        externAddresses moduleType.imports →
      initialModuleInst =
        { types := allocTypes module.types,
          globals := globalsxa externAddresses,
          funcs := funcsxa externAddresses ++
            (List.range module.funcs.length).map
              (fun index => sourceStore.funcs.length + index) } →
      initialState = ⟨sourceStore, { mod := initialModuleInst }⟩ →
      EvalGlobalsA initialState
        (module.globals.map Global.globaltype)
        (module.globals.map Global.init) globalsState globalValues →
      EvalRefExprsA globalsState (module.tables.map Table.init)
        tablesState tableRefs →
      EvalRefExprListsA tablesState (module.elems.map Elem.init)
        elementsState elemRefs →
      heapBase = Store.carryConstHeap sourceStore elementsState.store →
      AllocModule heapBase module externAddresses globalValues tableRefs elemRefs
        allocatedStore moduleInst →
      (module.datas.zipIdx.mapM fun pair =>
        runData_ (TypeIdx.ofNat pair.2) pair.1) = some dataInstructionLists →
      dataInstructions = dataInstructionLists.flatten →
      (module.elems.zipIdx.mapM fun pair =>
        runElem_ (TypeIdx.ofNat pair.2) pair.1) = some elemInstructionLists →
      elemInstructions = elemInstructionLists.flatten →
      startInstruction = module.start.map (fun start => Instr.call start.funcidx) →
      InstantiateA sourceStore module externAddresses
        (⟨allocatedStore, { mod := moduleInst }⟩,
          plains elemInstructions ++ plains dataInstructions ++
            plains startInstruction.toList)

/-- Successful executable initialization is a derivation of the sole public
AMD-014 relation.  Constant-expression grammar proofs are explicit inputs here;
`Module_okA` supplies them in the validator-to-initializer theorem. -/
theorem instantiateA?_sound {sourceStore : Store} {module : Module}
    {externAddresses : List ExternAddr} {moduleType : ModuleType}
    {core : Config}
    (hmodule : Module_okA module moduleType)
    (himportsLength : SeqLen₂ externAddresses moduleType.imports)
    (himports : SeqAll₂ (fun address externType =>
      Externaddr_ok sourceStore address externType)
      externAddresses moduleType.imports)
    (hglobalConst : ∀ global ∈ module.globals,
      ∃ context, Expr_const context global.init)
    (htableConst : ∀ table ∈ module.tables,
      ∃ context, Expr_const context table.init)
    (helemConst : ∀ elem ∈ module.elems, ∀ expression ∈ elem.init,
      ∃ context, Expr_const context expression)
    (h : instantiateA? sourceStore module externAddresses = some core) :
    InstantiateA sourceStore module externAddresses core := by
  have hglobalExprs : ∀ expression ∈ module.globals.map Global.init,
      ∃ context, Expr_const context expression := by
    intro expression hmember
    obtain ⟨global, hglobal, rfl⟩ := List.mem_map.mp hmember
    exact hglobalConst global hglobal
  have htableExprs : ∀ expression ∈ module.tables.map Table.init,
      ∃ context, Expr_const context expression := by
    intro expression hmember
    obtain ⟨table, htable, rfl⟩ := List.mem_map.mp hmember
    exact htableConst table htable
  have helemExprs : ∀ expressions ∈ module.elems.map Elem.init,
      ∀ expression ∈ expressions,
        ∃ context, Expr_const context expression := by
    intro expressions hmember expression hexpression
    obtain ⟨elem, helem, rfl⟩ := List.mem_map.mp hmember
    exact helemConst elem helem expression hexpression
  unfold instantiateA? at h
  let initialModuleInst : ModuleInst :=
    { types := allocTypes module.types,
      globals := globalsxa externAddresses,
      funcs := funcsxa externAddresses ++
        (List.range module.funcs.length).map
          (fun index => sourceStore.funcs.length + index) }
  let initialState : State := ⟨sourceStore, { mod := initialModuleInst }⟩
  cases hglobals : evalGlobals initialState
      (module.globals.map Global.globaltype)
      (module.globals.map Global.init) with
  | none => simp [initialModuleInst, initialState, hglobals] at h
  | some globalsResult =>
      rcases globalsResult with ⟨globalsState, globalValues⟩
      cases htables : evalRefExprs globalsState
          (module.tables.map Table.init) with
      | none =>
          simp [initialModuleInst, initialState, hglobals, htables] at h
      | some tablesResult =>
          rcases tablesResult with ⟨tablesState, tableRefs⟩
          cases helems : evalRefExprLists tablesState
              (module.elems.map Elem.init) with
          | none =>
              simp [initialModuleInst, initialState, hglobals, htables,
                helems] at h
          | some elemsResult =>
              rcases elemsResult with ⟨elementsState, elemRefs⟩
              let heapBase :=
                Store.carryConstHeap sourceStore elementsState.store
              cases halloc : allocModuleA? heapBase module externAddresses
                  globalValues tableRefs elemRefs with
              | none =>
                  simp [initialModuleInst, initialState, hglobals, htables,
                    helems, heapBase, halloc] at h
              | some allocationResult =>
                  rcases allocationResult with ⟨allocatedStore, moduleInst⟩
                  cases hdatas : module.datas.zipIdx.mapM (fun pair =>
                      runData_ (TypeIdx.ofNat pair.2) pair.1) with
                  | none =>
                      simp [initialModuleInst, initialState, hglobals, htables,
                        helems, heapBase, halloc, hdatas] at h
                  | some dataInstructionLists =>
                      cases helemInstructions : module.elems.zipIdx.mapM
                          (fun pair =>
                            runElem_ (TypeIdx.ofNat pair.2) pair.1) with
                      | none =>
                          simp [initialModuleInst, initialState, hglobals,
                            htables, helems, heapBase, halloc, hdatas,
                            helemInstructions] at h
                      | some elemInstructionLists =>
                          simp [initialModuleInst, initialState, hglobals,
                            htables, helems, heapBase, halloc, hdatas,
                            helemInstructions] at h
                          subst core
                          rw [← List.append_assoc]
                          apply InstantiateA.mk hmodule himportsLength himports
                            (initialModuleInst := initialModuleInst)
                            (initialState := initialState)
                            (globalsState := globalsState)
                            (tablesState := tablesState)
                            (elementsState := elementsState)
                            (heapBase := heapBase)
                            (globalValues := globalValues)
                            (tableRefs := tableRefs) (elemRefs := elemRefs)
                            (allocatedStore := allocatedStore)
                            (moduleInst := moduleInst)
                            (dataInstructionLists := dataInstructionLists)
                            (elemInstructionLists := elemInstructionLists)
                            (dataInstructions := dataInstructionLists.flatten)
                            (elemInstructions := elemInstructionLists.flatten)
                            (startInstruction := module.start.map
                              (fun start => Instr.call start.funcidx))
                          · rfl
                          · rfl
                          · exact evalGlobals_sound hglobalExprs hglobals
                          · exact evalRefExprs_sound htableExprs htables
                          · exact evalRefExprLists_sound (by
                              intro expressions hmem expression hexpression
                              exact helemExprs expressions hmem expression
                                hexpression) helems
                          · rfl
                          · exact allocModuleA?_sound halloc
                          · exact hdatas
                          · rfl
                          · exact helemInstructions
                          · rfl
                          · rfl

/-! ## Validation supplies the constant-expression grammar -/

theorem seqAll₂_left_exists {alpha beta : Type} {relation : alpha → beta → Prop}
    {left : List alpha} {right : List beta} (hlength : SeqLen₂ left right)
    (hall : SeqAll₂ relation left right) :
    ∀ value ∈ left, ∃ paired, relation value paired := by
  intro value hmember
  rcases List.mem_iff_getElem.mp hmember with ⟨index, hindex, rfl⟩
  have hright : index < right.length := by omega
  exact ⟨right[index], hall index _ _
    (List.getElem?_eq_getElem hindex) (List.getElem?_eq_getElem hright)⟩

theorem Globals_okA.constInitializers {context : Context}
    {globals : List Global} {globalTypes : List GlobalType}
    (h : Globals_okA context globals globalTypes) :
    ∀ global ∈ globals, ∃ expressionContext,
      Expr_const expressionContext global.init := by
  induction h with
  | empty => simp
  | cons hglobal _ ih =>
      intro global hmember
      simp only [List.mem_cons] at hmember
      rcases hmember with rfl | htail
      · cases hglobal with
        | mk _ hexpression =>
            cases hexpression with
            | mk _ hconst => exact ⟨_, hconst⟩
      · exact ih global htail

/-- Amended module validation exposes the constant grammar for every global,
table, and element initializer consumed by `instantiateA?`. -/
theorem Module_okA.constInitializers {module : Module} {moduleType : ModuleType}
    (h : Module_okA module moduleType) :
    (∀ global ∈ module.globals,
      ∃ context, Expr_const context global.init) ∧
    (∀ table ∈ module.tables,
      ∃ context, Expr_const context table.init) ∧
    (∀ elem ∈ module.elems, ∀ expression ∈ elem.init,
      ∃ context, Expr_const context expression) := by
  cases h with
  | mk _ _ _ _ _ hglobals _ _ htablesLength htables _ _ _ _
      helemsLength helems _ _ _ _ _ _ _ _ _ _ _ _ =>
      constructor
      · exact Exec.Globals_okA.constInitializers hglobals
      constructor
      · intro table hmember
        obtain ⟨tableType, htable⟩ :=
          seqAll₂_left_exists htablesLength htables table hmember
        cases htable with
        | mk _ hexpression =>
            cases hexpression with
            | mk _ hconst => exact ⟨_, hconst⟩
      · intro elem hmember expression hexpressionMember
        obtain ⟨elemType, helem⟩ :=
          seqAll₂_left_exists helemsLength helems elem hmember
        cases helem with
        | mk _ hinit _ =>
            cases hinit expression hexpressionMember with
            | mk _ hconst => exact ⟨_, hconst⟩

/-- Validator-to-initializer soundness with no separately supplied constant
grammar evidence. -/
theorem instantiateA?_sound_of_module {sourceStore : Store} {module : Module}
    {externAddresses : List ExternAddr} {moduleType : ModuleType}
    {core : Config}
    (hmodule : Module_okA module moduleType)
    (himportsLength : SeqLen₂ externAddresses moduleType.imports)
    (himports : SeqAll₂ (fun address externType =>
      Externaddr_ok sourceStore address externType)
      externAddresses moduleType.imports)
    (h : instantiateA? sourceStore module externAddresses = some core) :
    InstantiateA sourceStore module externAddresses core := by
  obtain ⟨hglobals, htables, helems⟩ :=
    Exec.Module_okA.constInitializers hmodule
  exact instantiateA?_sound hmodule himportsLength himports hglobals htables
    helems h

/-- Every public amended instantiation carries the allocation-derived closed
type section used by runtime subtype enumeration. -/
theorem InstantiateA.allocatedTypesFrom {sourceStore allocatedStore : Store}
    {module : Module} {externAddresses : List ExternAddr} {instructions : List AdminInstr}
    {frame : Frame}
    (h : InstantiateA sourceStore module externAddresses
      (⟨allocatedStore, frame⟩, instructions)) :
    frame.mod.AllocatedTypesFrom module := by
  cases h
  apply AllocModule.allocatedTypesFrom
  assumption

end WasmGemmGnaf.Wasm.Core.Exec
