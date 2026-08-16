import WasmGemmGnaf.Wasm.Core.InstantiationAmended

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Functionality of the amended instantiation tail

These lemmas isolate expression evaluation as the only relational component of
fresh instantiation.  Once evaluations from a fixed state and expression agree,
every subsequent allocation and emitted instruction list agrees as well. -/

theorem AllocModule.target_functional {store : Store} {module : Module}
    {addresses : List ExternAddr} {values : List Val} {tableRefs : List Ref}
    {elemRefs : List (List Ref)} {leftStore rightStore : Store}
    {leftModule rightModule : ModuleInst}
    (hl : AllocModule store module addresses values tableRefs elemRefs
      leftStore leftModule)
    (hr : AllocModule store module addresses values tableRefs elemRefs
      rightStore rightModule) :
    leftStore = rightStore ∧ leftModule = rightModule := by
  cases hl
  cases hr
  simp_all

theorem EvalGlobalsA.target_functional_of_eval
    (evalFunctional : ∀ {state : State} {expression : Expr}
      {leftState rightState : State} {leftValues rightValues : List Val},
      Eval_exprEraseA state expression leftState leftValues →
      Eval_exprEraseA state expression rightState rightValues →
      leftState = rightState ∧ leftValues = rightValues)
    {state leftState rightState : State} {types : List GlobalType}
    {expressions : List Expr} {leftValues rightValues : List Val}
    (hl : EvalGlobalsA state types expressions leftState leftValues)
    (hr : EvalGlobalsA state types expressions rightState rightValues) :
    leftState = rightState ∧ leftValues = rightValues := by
  induction hl generalizing rightState rightValues with
  | nil =>
      cases hr
      exact ⟨rfl, rfl⟩
  | @cons state evaluated leftState evaluatedStore allocatedStore frame address
      globalType types expression expressions value leftValues
      heval hevaluated halloc hrest ih =>
      cases hr with
      | @cons _ rightEvaluated _ rightEvaluatedStore rightAllocatedStore
          rightFrame rightAddress _ _ _ _ rightValue rightValues
          rightEval rightEvaluatedEq rightAlloc rightRest =>
          obtain ⟨rfl, hvalues⟩ := evalFunctional heval rightEval
          have hvalue : value = rightValue := List.cons.inj hvalues |>.1
          subst rightValue
          have hshape := hevaluated.symm.trans rightEvaluatedEq
          cases hshape
          rw [halloc] at rightAlloc
          cases rightAlloc
          obtain ⟨rfl, rfl⟩ := ih rightRest
          exact ⟨rfl, rfl⟩

theorem EvalRefExprsA.target_functional_of_eval
    (evalFunctional : ∀ {state : State} {expression : Expr}
      {leftState rightState : State} {leftValues rightValues : List Val},
      Eval_exprEraseA state expression leftState leftValues →
      Eval_exprEraseA state expression rightState rightValues →
      leftState = rightState ∧ leftValues = rightValues)
    {state leftState rightState : State} {expressions : List Expr}
    {leftRefs rightRefs : List Ref}
    (hl : EvalRefExprsA state expressions leftState leftRefs)
    (hr : EvalRefExprsA state expressions rightState rightRefs) :
    leftState = rightState ∧ leftRefs = rightRefs := by
  induction hl generalizing rightState rightRefs with
  | nil =>
      cases hr
      exact ⟨rfl, rfl⟩
  | @cons state evaluated leftState expression expressions reference leftRefs
      heval hrest ih =>
      cases hr with
      | @cons _ rightEvaluated _ _ _ rightReference rightRefs rightEval rightRest =>
          obtain ⟨rfl, hvalues⟩ := evalFunctional heval rightEval
          have hreference : reference = rightReference := by
            have : Val.ref reference = .ref rightReference :=
              List.cons.inj hvalues |>.1
            injection this
          subst rightReference
          obtain ⟨rfl, rfl⟩ := ih rightRest
          exact ⟨rfl, rfl⟩

theorem EvalRefExprListsA.target_functional_of_eval
    (evalFunctional : ∀ {state : State} {expression : Expr}
      {leftState rightState : State} {leftValues rightValues : List Val},
      Eval_exprEraseA state expression leftState leftValues →
      Eval_exprEraseA state expression rightState rightValues →
      leftState = rightState ∧ leftValues = rightValues)
    {state leftState rightState : State} {expressionLists : List (List Expr)}
    {leftRefs rightRefs : List (List Ref)}
    (hl : EvalRefExprListsA state expressionLists leftState leftRefs)
    (hr : EvalRefExprListsA state expressionLists rightState rightRefs) :
    leftState = rightState ∧ leftRefs = rightRefs := by
  induction hl generalizing rightState rightRefs with
  | nil =>
      cases hr
      exact ⟨rfl, rfl⟩
  | @cons state leftAfter leftState expressions expressionLists references
      leftRefs hhead hrest ih =>
      cases hr with
      | @cons _ rightAfter _ _ _ rightReferences rightRefs rightHead rightRest =>
          obtain ⟨rfl, rfl⟩ :=
            EvalRefExprsA.target_functional_of_eval evalFunctional hhead rightHead
          obtain ⟨rfl, rfl⟩ := ih rightRest
          exact ⟨rfl, rfl⟩

theorem InstantiateA.target_functional_of_eval
    (evalFunctional : ∀ {state : State} {expression : Expr}
      {leftState rightState : State} {leftValues rightValues : List Val},
      Eval_exprEraseA state expression leftState leftValues →
      Eval_exprEraseA state expression rightState rightValues →
      leftState = rightState ∧ leftValues = rightValues)
    {store : Store} {module : Module} {addresses : List ExternAddr}
    {left right : Config}
    (hl : InstantiateA store module addresses left)
    (hr : InstantiateA store module addresses right) : left = right := by
  cases hl
  cases hr
  simp_all only
  rename_i
    allocatedStoreL heapBaseL moduleTypeL initialStateL globalsStateL tablesStateL
      elementsStateL initialModuleInstL moduleInstL globalValuesL tableRefsL
      elemRefsL dataInstructionsL elemInstructionsL dataInstructionListsL
      elemInstructionListsL startInstructionL
    allocatedStoreR heapBaseR moduleTypeR initialStateR globalsStateR tablesStateR
      elementsStateR initialModuleInstR moduleInstR globalValuesR tableRefsR
      elemRefsR dataInstructionsR elemInstructionsR dataInstructionListsR
      elemInstructionListsR startInstructionR
    hinitialStateL hheapL hdataInstructionsL helemInstructionsL _ hglobalsL
      htableRefsL helemRefsL hdataListsLR helemListsLR _ _ _ _ hallocL
    hinitialStateR hheapR hdataInstructionsR helemInstructionsR _ hglobalsR
      htableRefsR helemRefsR _ _ _ _ _ _ hallocR
  obtain ⟨rfl, rfl⟩ :=
    EvalGlobalsA.target_functional_of_eval evalFunctional hglobalsL hglobalsR
  obtain ⟨rfl, rfl⟩ :=
    EvalRefExprsA.target_functional_of_eval evalFunctional htableRefsL htableRefsR
  obtain ⟨rfl, rfl⟩ :=
    EvalRefExprListsA.target_functional_of_eval evalFunctional helemRefsL helemRefsR
  obtain ⟨rfl, rfl⟩ := AllocModule.target_functional hallocL hallocR
  simp_all

end WasmGemmGnaf.Wasm.Core.Exec
