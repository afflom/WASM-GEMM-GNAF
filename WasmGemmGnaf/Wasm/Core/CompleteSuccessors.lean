import WasmGemmGnaf.Wasm.Core.AllSuccessors
import WasmGemmGnaf.Wasm.Core.ReadCompleteAll
import WasmGemmGnaf.Wasm.Core.RuntimeOrigin

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- A three-way instruction sublist inherits compatible runtime origins. -/
theorem CompatibleConfigTypeOriginsA.splitMid {dts : List DefType}
    {z : State} {source : List AdminInstr}
    (h : CompatibleConfigTypeOriginsA dts (z, source))
    (split : ListSplit3 source) :
    CompatibleConfigTypeOriginsA dts (z, split.mid) := by
  rcases h with ⟨hstore, hframe, hinstructions⟩
  have hall : AdminInstrsTypesA dts
      (split.pre ++ split.mid ++ split.post) := by
    rw [← split.rebuild]
    exact hinstructions
  have hleft :=
    (adminInstrsTypesA_append dts (split.pre ++ split.mid) split.post).mp hall
  have hmid :=
    (adminInstrsTypesA_append dts split.pre split.mid).mp hleft.1
  exact ⟨hstore, hframe, hmid.2⟩

theorem CompatibleConfigTypeOriginsA.labelBody {dts : List DefType}
    {z : State} {source continuation body : List AdminInstr} {arity : Nat}
    (h : CompatibleConfigTypeOriginsA dts (z, source))
    (hsource : source = [.label arity continuation body]) :
    CompatibleConfigTypeOriginsA dts (z, body) := by
  subst source
  simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
    AdminInstrTypesA, and_true] at h ⊢
  rcases h with ⟨hstore, hframe, hcontinuation, hbody⟩
  exact ⟨hstore, hframe, hbody⟩

theorem CompatibleConfigTypeOriginsA.frameBody {dts : List DefType}
    {z : State} {source body : List AdminInstr} {arity : Nat} {frame : Frame}
    (h : CompatibleConfigTypeOriginsA dts (z, source))
    (hsource : source = [.frame arity frame body]) :
    CompatibleConfigTypeOriginsA dts (⟨z.store, frame⟩, body) := by
  subst source
  simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
    AdminInstrTypesA, and_true] at h ⊢
  rcases h with ⟨hstore, houter, hframe, hbody⟩
  exact ⟨hstore, Or.inr hframe, hbody⟩

theorem CompatibleConfigTypeOriginsA.handlerBody {dts : List DefType}
    {z : State} {source body : List AdminInstr} {arity : Nat}
    {catches : List Catch}
    (h : CompatibleConfigTypeOriginsA dts (z, source))
    (hsource : source = [.handler arity catches body]) :
    CompatibleConfigTypeOriginsA dts (z, body) := by
  subst source
  simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
    AdminInstrTypesA, and_true] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- Lift already-computed inner results through a nontrivial instruction
context. -/
def liftInstrSplitNonemptyFrom (z : State) (source : List AdminInstr)
    (split : ListSplit3 source)
    (values : List Val) (hvalues : adminValues? split.pre = some values)
    (hnonempty : values ≠ [] ∨ split.post ≠ [])
    (innerResults : List (StepAResult (z, split.mid))) :
    List (StepAResult (z, source)) :=
  innerResults.map fun result =>
    let rebuilt :=
      StepAResult.mk
        (.ctxtInstrs values.length split.post.length result.event)
        (result.next.1, vals values ++ result.next.2 ++ split.post)
        (StepA.ctxtInstrs result.step hnonempty)
    rebuilt.castSource (by
      have hpre : split.pre = vals values :=
        adminValues?_eq_some_vals hvalues
      have hrebuild : vals values ++ split.mid ++ split.post = source := by
        calc
          vals values ++ split.mid ++ split.post =
              split.pre ++ split.mid ++ split.post := by rw [hpre]
          _ = source := split.rebuild.symm
      exact congrArg (fun instructions => (z, instructions)) hrebuild)

/-- Lift already-computed inner results through an instruction split. -/
def liftInstrSplitResultsFrom (z : State) (source : List AdminInstr)
    (split : ListSplit3 source)
    (innerResults : List (StepAResult (z, split.mid))) :
    List (StepAResult (z, source)) :=
  match hvalues : adminValues? split.pre with
  | none => []
  | some [] =>
      match hpost : split.post with
      | [] => []
      | instruction :: rest =>
          liftInstrSplitNonemptyFrom z source split [] hvalues
            (Or.inr (by simp [hpost])) innerResults
  | some (value :: values) =>
      liftInstrSplitNonemptyFrom z source split (value :: values) hvalues
        (Or.inl (by simp)) innerResults

/-- Lift precomputed inner results through a handler, including the handler's
own singleton-trap propagation edge. -/
def liftHandlerResultsFrom (state : State) (arity : Nat)
    (catches : List Catch) (body : List AdminInstr)
    (innerResults : List (StepAResult (state, body))) :
    List (StepAResult (state, [.handler arity catches body])) :=
  match body with
  | [.trap] =>
      { event := .trapHandler arity
        next := (state, [.trap])
        step := .trapHandler } ::
        innerResults.map fun result =>
          { event := .ctxtHandler arity result.event
            next := (result.next.1,
              [.handler arity catches result.next.2])
            step := .ctxtHandler result.step }
  | body =>
      innerResults.map fun result =>
        { event := .ctxtHandler arity result.event
          next := (result.next.1,
            [.handler arity catches result.next.2])
          step := .ctxtHandler result.step }

/-- The complete non-context layer at a state carrying runtime-origin
compatibility. -/
def compatibleBaseStepResults (dts : List DefType) (matchFuel : Nat)
    (matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1)
    (config : Config) (compatible : CompatibleConfigTypeOriginsA dts config) :
    List (StepAResult config) :=
  pureStepResults config.1 config.2 ++
    completeReadResultsOf matchFuel config.1
      (matchComplete config compatible) config.2 ++
    directStepResults config

/-- Close the complete non-context layer under every recursive Core context.
The runtime-origin proof supplies matcher completeness at each nested frame. -/
def compatibleSuccessorResultsN (dts : List DefType) (matchFuel : Nat)
    (matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1) :
    (fuel : Nat) → (config : Config) →
      CompatibleConfigTypeOriginsA dts config → List (StepAResult config)
  | 0, config, compatible =>
      compatibleBaseStepResults dts matchFuel matchComplete config compatible
  | fuel + 1, (state, instructions), compatible =>
      let base := compatibleBaseStepResults dts matchFuel matchComplete
        (state, instructions) compatible
      let instrContexts :=
        (listSplits3 instructions).flatMap fun split =>
          let innerCompatible := compatible.splitMid split
          let innerResults := compatibleSuccessorResultsN dts matchFuel
            matchComplete fuel (state, split.mid) innerCompatible
          liftInstrSplitResultsFrom state instructions split innerResults
      let wrapperContexts :=
        match hinstructions : instructions with
        | [.label arity continuation body] =>
            let innerCompatible := compatible.labelBody rfl
            (compatibleSuccessorResultsN dts matchFuel matchComplete fuel
              (state, body) innerCompatible).map fun result =>
                { event := .ctxtLabel arity result.event
                  next := (result.next.1,
                    [.label arity continuation result.next.2])
                  step := .ctxtLabel result.step }
        | [.frame arity innerFrame body] =>
            let innerCompatible := compatible.frameBody rfl
            (compatibleSuccessorResultsN dts matchFuel matchComplete fuel
              (⟨state.store, innerFrame⟩, body) innerCompatible).map fun result =>
                { event := .ctxtFrame arity result.event
                  next := (⟨result.next.1.store, state.frame⟩,
                    [.frame arity result.next.1.frame result.next.2])
                  step := .ctxtFrame result.step }
        | [.handler arity catches body] =>
            let innerCompatible := compatible.handlerBody rfl
            let innerResults := compatibleSuccessorResultsN dts matchFuel
              matchComplete fuel (state, body) innerCompatible
            liftHandlerResultsFrom state arity catches body innerResults
        | _ => []
      base ++ instrContexts ++ wrapperContexts

theorem mem_compatibleSuccessorResultsN_stepA
    {dts : List DefType} {matchFuel fuel : Nat}
    {matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1}
    {config : Config} {compatible : CompatibleConfigTypeOriginsA dts config}
    {result : StepAResult config}
    (h : result ∈ compatibleSuccessorResultsN dts matchFuel matchComplete
      fuel config compatible) :
    StepA config result.event result.next := result.step

theorem pure_mem_compatibleBaseStepResults
    {dts : List DefType} {matchFuel : Nat}
    {matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1}
    {z : State} {is is' : List AdminInstr} {pe : PureEvent}
    {compatible : CompatibleConfigTypeOriginsA dts (z, is)}
    (h : (pe, is') ∈ pureSuccessors releasedNumerics is) :
    ∃ result ∈ compatibleBaseStepResults dts matchFuel matchComplete
        (z, is) compatible,
      result.toPair = (.pure pe (sourcePlains is), (z, is')) := by
  let candidate : StepAResult (z, is) :=
    { event := .pure pe (sourcePlains is)
      next := (z, is')
      step := .pure h }
  refine ⟨candidate, ?_, rfl⟩
  simp only [compatibleBaseStepResults, pureStepResults, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.mpr
    ⟨⟨(pe, is'), h⟩, List.mem_attach _ _, rfl⟩))

theorem completeRead_mem_compatibleBaseStepResults
    {dts : List DefType} {matchFuel : Nat}
    {matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1}
    {config : Config} {compatible : CompatibleConfigTypeOriginsA dts config}
    {event : Event} {next : Config}
    (h : (event, next) ∈ completeReadSuccessorsOf matchFuel config
      (matchComplete config compatible)) :
    ∃ result ∈ compatibleBaseStepResults dts matchFuel matchComplete
        config compatible,
      result.toPair = (event, next) := by
  rcases config with ⟨z, is⟩
  simp only [completeReadSuccessorsOf, List.mem_map] at h
  obtain ⟨result, hresult, heq⟩ := h
  refine ⟨result, ?_, heq⟩
  simp only [compatibleBaseStepResults, List.mem_append]
  exact Or.inl (Or.inr hresult)

theorem direct_mem_compatibleBaseStepResults
    {dts : List DefType} {matchFuel : Nat}
    {matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1}
    {config : Config} {compatible : CompatibleConfigTypeOriginsA dts config}
    {event : Event} {next : Config}
    (h : (event, next) ∈ directSuccessors config) :
    ∃ result ∈ compatibleBaseStepResults dts matchFuel matchComplete
        config compatible,
      result.toPair = (event, next) := by
  let result : StepAResult config :=
    { event := event
      next := next
      step := mem_directSuccessors_stepA h }
  refine ⟨result, ?_, rfl⟩
  simp only [compatibleBaseStepResults, List.mem_append]
  right
  simp only [directStepResults, List.mem_map]
  exact ⟨⟨(event, next), h⟩, List.mem_attach _ _, rfl⟩

theorem mem_compatibleSuccessorResultsN_of_mem_base
    {dts : List DefType} {matchFuel fuel : Nat}
    {matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1}
    {config : Config} {compatible : CompatibleConfigTypeOriginsA dts config}
    {result : StepAResult config}
    (h : result ∈ compatibleBaseStepResults dts matchFuel matchComplete
      config compatible) :
    result ∈ compatibleSuccessorResultsN dts matchFuel matchComplete fuel
      config compatible := by
  cases fuel with
  | zero => exact h
  | succ fuel =>
      simp only [compatibleSuccessorResultsN, List.mem_append]
      exact Or.inl (Or.inl h)

theorem pair_mem_liftInstrSplitResultsFrom {z z' : State}
    {values : List Val} {inner inner' post : List AdminInstr}
    {event : Event} {innerResult : StepAResult (z, inner)}
    (hevent : innerResult.event = event)
    (hnext : innerResult.next = (z', inner'))
    (hnonempty : values ≠ [] ∨ post ≠ [])
    (innerResults : List (StepAResult (z, inner)))
    (hmem : innerResult ∈ innerResults) :
    let split : ListSplit3 (vals values ++ inner ++ post) :=
      { pre := vals values, mid := inner, post := post, rebuild := rfl }
    ∃ result ∈ liftInstrSplitResultsFrom z
        (vals values ++ inner ++ post) split innerResults,
      result.toPair =
        (.ctxtInstrs values.length post.length event,
          (z', vals values ++ inner' ++ post)) := by
  dsimp only
  unfold liftInstrSplitResultsFrom
  split
  case h_1 heq =>
    change adminValues? (vals values) = none at heq
    rw [adminValues?_vals] at heq
    contradiction
  case h_2 heq =>
    change adminValues? (vals values) = some [] at heq
    rw [adminValues?_vals] at heq
    have hvalues : values = [] := Option.some.inj heq
    subst values
    cases post with
    | nil =>
        exact False.elim (hnonempty.elim (fun h => h rfl) (fun h => h rfl))
    | cons instruction rest =>
        unfold liftInstrSplitNonemptyFrom
        refine ⟨_, List.mem_map.mpr ⟨innerResult, hmem, rfl⟩, ?_⟩
        simp [StepAResult.toPair, StepAResult.castSource, hevent, hnext]
  case h_3 value' values' heq =>
    change adminValues? (vals values) = some (value' :: values') at heq
    rw [adminValues?_vals] at heq
    have hvalues : values = value' :: values' := Option.some.inj heq
    subst values
    unfold liftInstrSplitNonemptyFrom
    refine ⟨_, List.mem_map.mpr ⟨innerResult, hmem, rfl⟩, ?_⟩
    simp [StepAResult.toPair, StepAResult.castSource, hevent, hnext]

/-- Every amended Core step from a runtime-origin-compatible configuration is
present in the complete fuel-indexed successor list. -/
theorem stepA_pair_mem_compatibleSuccessorResultsN
    {dts : List DefType} {matchFuel : Nat}
    (matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1)
    {config : Config} {event : Event} {next : Config}
    (hstep : StepA config event next) :
    ∀ (compatible : CompatibleConfigTypeOriginsA dts config) fuel,
      adminInstrsTreeSize config.2 < fuel →
      ∃ result ∈ compatibleSuccessorResultsN dts matchFuel matchComplete
          fuel config compatible,
        result.toPair = (event, next) := by
  induction hstep with
  | pure hp =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        pure_mem_compatibleBaseStepResults (compatible := compatible) hp
      exact ⟨result,
        mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | @read z rule is is' hr =>
      intro compatible fuel hfuel
      have hread := step_readA_mem_completeReadSuccessorsOf
        (matchComplete (z, is) compatible) hr
      obtain ⟨result, hresult, heq⟩ :=
        completeRead_mem_compatibleBaseStepResults
          (compatible := compatible) hread
      exact ⟨result,
        mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | @ctxtInstrs z z' values inner inner' post event hinner hnonempty ih =>
      intro compatible fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            change adminInstrsTreeSize (vals values ++ inner ++ post) <
              fuel + 1 at hfuel
            simp only [adminInstrsTreeSize_append,
              adminInstrsTreeSize_vals] at hfuel
            rcases hnonempty with hvalues | hpost
            · have hpositive : 0 < values.length := by
                cases values with
                | nil => exact False.elim (hvalues rfl)
                | cons _ _ => simp
              omega
            · have hpositive := adminInstrsTreeSize_pos_of_ne_nil hpost
              omega
          let split : ListSplit3 (vals values ++ inner ++ post) :=
            { pre := vals values, mid := inner, post := post, rebuild := rfl }
          have hsplit : split ∈ listSplits3 (vals values ++ inner ++ post) :=
            chosenSplit_mem values inner post
          let innerCompatible := compatible.splitMid split
          obtain ⟨innerResult, hinnerResult, heq⟩ :=
            ih innerCompatible fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let innerResults := compatibleSuccessorResultsN dts matchFuel
            matchComplete fuel (z, inner) innerCompatible
          obtain ⟨result, hresult, hpair⟩ :=
            pair_mem_liftInstrSplitResultsFrom hevent hnext hnonempty
              innerResults hinnerResult
          refine ⟨result, ?_, hpair⟩
          simp only [compatibleSuccessorResultsN, List.mem_append]
          exact Or.inl (Or.inr (List.mem_flatMap.mpr
            ⟨split, hsplit, hresult⟩))
  | @ctxtLabel z z' n cont inner inner' event hinner ih =>
      intro compatible fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          let innerCompatible := compatible.labelBody rfl
          obtain ⟨innerResult, hinnerResult, heq⟩ :=
            ih innerCompatible fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let result : StepAResult (z, [.label n cont inner]) :=
            { event := .ctxtLabel n innerResult.event
              next := (innerResult.next.1,
                [.label n cont innerResult.next.2])
              step := .ctxtLabel innerResult.step }
          refine ⟨result, ?_, ?_⟩
          · simp only [compatibleSuccessorResultsN, List.mem_append]
            apply Or.inr
            exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
          · simp [result, StepAResult.toPair, hevent, hnext]
  | @ctxtFrame s s' frame innerFrame nextFrame n inner inner' event
      hinner ih =>
      intro compatible fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          let innerCompatible := compatible.frameBody rfl
          obtain ⟨innerResult, hinnerResult, heq⟩ :=
            ih innerCompatible fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (⟨s', nextFrame⟩, inner') :=
            congrArg Prod.snd heq
          let result : StepAResult (⟨⟨s, frame⟩,
              [.frame n innerFrame inner]⟩) :=
            { event := .ctxtFrame n innerResult.event
              next := (⟨innerResult.next.1.store, frame⟩,
                [.frame n innerResult.next.1.frame innerResult.next.2])
              step := .ctxtFrame innerResult.step }
          refine ⟨result, ?_, ?_⟩
          · simp only [compatibleSuccessorResultsN, List.mem_append]
            apply Or.inr
            exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
          · simp [result, StepAResult.toPair, hevent, hnext]
  | @ctxtHandler z z' n catches inner inner' event hinner ih =>
      intro compatible fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          let innerCompatible := compatible.handlerBody rfl
          obtain ⟨innerResult, hinnerResult, heq⟩ :=
            ih innerCompatible fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let result : StepAResult (z, [.handler n catches inner]) :=
            { event := .ctxtHandler n innerResult.event
              next := (innerResult.next.1,
                [.handler n catches innerResult.next.2])
              step := .ctxtHandler innerResult.step }
          refine ⟨result, ?_, ?_⟩
          · simp only [compatibleSuccessorResultsN, List.mem_append]
            apply Or.inr
            cases inner with
            | nil =>
                exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
            | cons instruction rest =>
                cases instruction <;>
                  try exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
                case trap =>
                  cases rest with
                  | nil =>
                      exact List.mem_cons_of_mem _
                        (List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩)
                  | cons next rest =>
                      exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
          · simp [result, StepAResult.toPair, hevent, hnext]
  | @trapHandler z n catches =>
      intro compatible fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          let result : StepAResult (z, [.handler n catches [.trap]]) :=
            { event := .trapHandler n
              next := (z, [.trap])
              step := .trapHandler }
          refine ⟨result, ?_, rfl⟩
          simp only [compatibleSuccessorResultsN, List.mem_append]
          apply Or.inr
          change result ∈ liftHandlerResultsFrom z n catches [.trap] _
          simp only [liftHandlerResultsFrom]
          exact List.mem_cons_self
  | throw htag hdt hexpand ht hvs ha hta hex =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (throw_mem_directSuccessors htag hdt hexpand ht hvs ha hta hex)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | localSet hset =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (localSet_mem_directSuccessors hset)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | globalSet hset =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (globalSet_mem_directSuccessors hset)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | tableSetOob htable hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (tableSetOob_mem_directSuccessors htable hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | tableSetVal htable hin hset =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (tableSetVal_mem_directSuccessors htable hin hset)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | tableGrowSucceed htable hgrow hset hsize =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (tableGrowSucceed_mem_directSuccessors htable hgrow hset hsize)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | tableGrowFail heqFail =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (tableGrowFail_mem_directSuccessors heqFail)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | elemDrop hdrop =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (elemDrop_mem_directSuccessors hdrop)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | storeNumOob hmem hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (storeNumOob_mem_directSuccessors hmem hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | storeNumVal hbs hmem =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (storeNumVal_mem_directSuccessors hbs hmem)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | storePackOob hmem hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (storePackOob_mem_directSuccessors hmem hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | storePackVal hbs hmem =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (storePackVal_mem_directSuccessors hbs hmem)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | vstoreOob hmem hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (vstoreOob_mem_directSuccessors hmem hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | vstoreVal hbs hmem =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (vstoreVal_mem_directSuccessors hbs hmem)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | vstoreLaneOob hmem hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (vstoreLaneOob_mem_directSuccessors hmem hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | vstoreLaneVal hsize hdim hlane hbits hbs hmem =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (vstoreLaneVal_mem_directSuccessors
            hsize hdim hlane hbits hbs hmem)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | memoryGrowSucceed hmem hgrow hset hsize =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (memoryGrowSucceed_mem_directSuccessors hmem hgrow hset hsize)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | memoryGrowFail heqFail =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (memoryGrowFail_mem_directSuccessors heqFail)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | dataDrop hdrop =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (dataDrop_mem_directSuccessors hdrop)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | structNew htype hexpand hfts hvs ha hpack hsi =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (structNew_mem_directSuccessors htype hexpand hfts hvs ha hpack hsi)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | structSetNull =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          structSetNull_mem_directSuccessors
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | structSetStruct htype hexpand hfield hpack hset =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (structSetStruct_mem_directSuccessors
            htype hexpand hfield hpack hset)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | arrayNewFixed htype hexpand hlen ha hpack hai =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (arrayNewFixed_mem_directSuccessors
            htype hexpand hlen ha hpack hai)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | arraySetNull =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          arraySetNull_mem_directSuccessors
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | arraySetOob harray hoob =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (arraySetOob_mem_directSuccessors harray hoob)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩
  | arraySetArray htype hexpand hpack hset =>
      intro compatible fuel hfuel
      obtain ⟨result, hresult, heq⟩ :=
        direct_mem_compatibleBaseStepResults (compatible := compatible)
          (arraySetArray_mem_directSuccessors htype hexpand hpack hset)
      exact ⟨result, mem_compatibleSuccessorResultsN_of_mem_base hresult, heq⟩

/-- Complete executable successors for one runtime-origin-compatible Core
configuration. -/
def compatibleSuccessors (dts : List DefType) (matchFuel : Nat)
    (matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1)
    (config : Config) (compatible : CompatibleConfigTypeOriginsA dts config) :
    List (Event × Config) :=
  (compatibleSuccessorResultsN dts matchFuel matchComplete
    (successorFuel config) config compatible).map StepAResult.toPair

theorem mem_compatibleSuccessors_iff_stepA
    {dts : List DefType} {matchFuel : Nat}
    (matchComplete : ∀ (config : Config),
      CompatibleConfigTypeOriginsA dts config →
        RefMatchCompleteAt matchFuel config.1)
    (config : Config) (compatible : CompatibleConfigTypeOriginsA dts config)
    (event : Event) (next : Config) :
    (event, next) ∈
        compatibleSuccessors dts matchFuel matchComplete config compatible ↔
      StepA config event next := by
  constructor
  · intro hmem
    simp only [compatibleSuccessors, List.mem_map] at hmem
    obtain ⟨result, _, heq⟩ := hmem
    rcases result with ⟨emitted, successor, hstep⟩
    simp only [StepAResult.toPair, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact hstep
  · intro hstep
    obtain ⟨result, hresult, heq⟩ :=
      stepA_pair_mem_compatibleSuccessorResultsN matchComplete hstep compatible
        (successorFuel config) (by
          unfold successorFuel
          omega)
    simp only [compatibleSuccessors, List.mem_map]
    exact ⟨result, hresult, heq⟩

end WasmGemmGnaf.Wasm.Core.Exec
