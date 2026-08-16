/-
  One executable successor tree for the amended Core machine.

  `Successors` covers pure rules, `ReadSuccessors` covers store-reading rules,
  and `WholeSuccessors` covers state-writing rules.  This file joins those
  three non-context layers and closes them under every recursive `StepA`
  context.  Results retain their independent `StepA` derivation until the
  final executable projection erases proofs.
-/
import WasmGemmGnaf.Wasm.Core.ReadSuccessors

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Every split `source = prefix ++ middle ++ suffix`, retained with its
reconstruction equation. -/
structure ListSplit3 {α : Type} (source : List α) where
  pre : List α
  mid : List α
  post : List α
  rebuild : source = pre ++ mid ++ post

/-- Every two-way split of a list. -/
def listSplits {α : Type} : (source : List α) →
    List ({ pair : List α × List α // source = pair.1 ++ pair.2 })
  | [] => [⟨([], []), rfl⟩]
  | value :: rest =>
      ⟨([], value :: rest), rfl⟩ ::
        (listSplits rest).map fun split =>
          ⟨(value :: split.1.1, split.1.2), by
            simpa [split.2]⟩

/-- Every ordered three-way split of a list. -/
def listSplits3 {α : Type} (source : List α) : List (ListSplit3 source) :=
  (listSplits source).flatMap fun first =>
    (listSplits first.1.2).map fun second =>
      { pre := first.1.1
        mid := second.1.1
        post := second.1.2
        rebuild := by
          calc
            source = first.1.1 ++ first.1.2 := first.2
            _ = first.1.1 ++ (second.1.1 ++ second.1.2) :=
              congrArg (fun tail => first.1.1 ++ tail) second.2
            _ = first.1.1 ++ second.1.1 ++ second.1.2 :=
              (List.append_assoc _ _ _).symm }

theorem pair_mem_listSplits {α : Type} (pre post : List α) :
    ∃ split ∈ listSplits (pre ++ post), split.1 = (pre, post) := by
  induction pre with
  | nil =>
      refine ⟨⟨([], post), rfl⟩, ?_, rfl⟩
      cases post <;> exact List.mem_cons_self
  | cons value pre ih =>
      obtain ⟨split, hmem, hpair⟩ := ih
      let lifted :
          { pair : List α × List α //
            value :: (pre ++ post) = pair.1 ++ pair.2 } :=
        ⟨(value :: split.1.1, split.1.2), by
          simpa [split.2]⟩
      refine ⟨lifted, ?_, ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨split, hmem, rfl⟩)
      · simp only [lifted]
        rw [hpair]

theorem triple_mem_listSplits3 {α : Type} (pre mid post : List α) :
    ∃ split ∈ listSplits3 (pre ++ mid ++ post),
      split.pre = pre ∧ split.mid = mid ∧ split.post = post := by
  have hsource : pre ++ mid ++ post = pre ++ (mid ++ post) :=
    List.append_assoc _ _ _
  rw [hsource]
  obtain ⟨first, hfirst, hfirstPair⟩ :=
    pair_mem_listSplits pre (mid ++ post)
  rcases first with ⟨⟨firstPre, firstRest⟩, firstRebuild⟩
  simp only [Prod.mk.injEq] at hfirstPair
  rcases hfirstPair with ⟨rfl, rfl⟩
  obtain ⟨second, hsecond, hsecondPair⟩ := pair_mem_listSplits mid post
  rcases second with ⟨⟨secondMid, secondPost⟩, secondRebuild⟩
  simp only [Prod.mk.injEq] at hsecondPair
  rcases hsecondPair with ⟨rfl, rfl⟩
  let found : ListSplit3 (firstPre ++ (secondMid ++ secondPost)) :=
    { pre := firstPre
      mid := secondMid
      post := secondPost
      rebuild := by rw [List.append_assoc] }
  refine ⟨found, ?_, rfl, rfl, rfl⟩
  unfold listSplits3
  exact List.mem_flatMap.mpr
    ⟨⟨(firstPre, secondMid ++ secondPost), firstRebuild⟩, hfirst,
      List.mem_map.mpr
        ⟨⟨(secondMid, secondPost), secondRebuild⟩, hsecond, by
          rfl⟩⟩

/-- Invert the administrative embedding on an entire list. -/
def adminValues? : List AdminInstr → Option (List Val)
  | [] => some []
  | instruction :: rest => do
      let value ← adminToVal instruction
      let values ← adminValues? rest
      pure (value :: values)

theorem adminValues?_eq_some_vals {instructions : List AdminInstr}
    {values : List Val} (h : adminValues? instructions = some values) :
    instructions = vals values := by
  induction instructions generalizing values with
  | nil => simp [adminValues?] at h; subst values; rfl
  | cons instruction rest ih =>
      cases hi : adminToVal instruction with
      | none => simp [adminValues?, hi] at h
      | some value =>
          cases hr : adminValues? rest with
          | none => simp [adminValues?, hi, hr] at h
          | some values' =>
              simp [adminValues?, hi, hr] at h
              subst values
              rw [toAdmin_of_adminToVal hi, ih hr]
              rfl

/-- Pure-rule results, with membership proofs retained. -/
def pureStepResults (z : State) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  (pureSuccessors releasedNumerics is).attach.map fun candidate =>
    { event := .pure candidate.1.1 (sourcePlains is)
      next := (z, candidate.1.2)
      step := .pure candidate.2 }

/-- State-writing results, with membership proofs retained. -/
def directStepResults (config : Config) : List (StepAResult config) :=
  (directSuccessors config).attach.map fun candidate =>
    { event := candidate.1.1
      next := candidate.1.2
      step := mem_directSuccessors_stepA candidate.2 }

/-- The three non-context rule families. -/
def baseStepResults (config : Config) : List (StepAResult config) :=
  pureStepResults config.1 config.2 ++ readResults config.1 config.2 ++
    directStepResults config

/-- Lift one inner successor through one nontrivial instruction-sequence
split. -/
def liftInstrSplitNonempty (z : State) (source : List AdminInstr)
    (split : ListSplit3 source)
    (values : List Val) (hvalues : adminValues? split.pre = some values)
    (hnonempty : values ≠ [] ∨ split.post ≠ [])
    (recurse : (inner : Config) → List (StepAResult inner)) :
    List (StepAResult (z, source)) :=
  (recurse (z, split.mid)).map fun result =>
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

/-- Lift one inner successor through one instruction-sequence split. -/
def liftInstrSplitResults (z : State) (source : List AdminInstr)
    (split : ListSplit3 source)
    (recurse : (inner : Config) → List (StepAResult inner)) :
    List (StepAResult (z, source)) :=
  match hvalues : adminValues? split.pre with
  | none => []
  | some [] =>
      match hpost : split.post with
      | [] => []
      | instruction :: rest =>
          liftInstrSplitNonempty z source split [] hvalues
            (Or.inr (by simp [hpost])) recurse
  | some (value :: values) =>
      liftInstrSplitNonempty z source split (value :: values) hvalues
        (Or.inl (by simp)) recurse

/-- Lift all inner successors through one handler body and add the handler's
own trap-propagation edge exactly when the body is the singleton trap. -/
def liftHandlerResults (state : State) (arity : Nat)
    (catches : List Catch) (body : List AdminInstr)
    (recurse : (inner : Config) → List (StepAResult inner)) :
    List (StepAResult (state, [.handler arity catches body])) :=
  match body with
  | [.trap] =>
      { event := .trapHandler arity
        next := (state, [.trap])
        step := .trapHandler } ::
        (recurse (state, [.trap])).map fun result =>
          { event := .ctxtHandler arity result.event
            next := (result.next.1,
              [.handler arity catches result.next.2])
            step := .ctxtHandler result.step }
  | body =>
      (recurse (state, body)).map fun result =>
        { event := .ctxtHandler arity result.event
          next := (result.next.1,
            [.handler arity catches result.next.2])
          step := .ctxtHandler result.step }

/-- Close the base rules under all recursive contexts up to `fuel`.  Fuel is
only a structural recursion device; `successors` supplies the exact source
size bound below. -/
def successorResultsN : Nat → (config : Config) → List (StepAResult config)
  | 0, config => baseStepResults config
  | fuel + 1, config =>
      let base := baseStepResults config
      let instrContexts :=
        (listSplits3 config.2).flatMap fun split =>
          liftInstrSplitResults config.1 config.2 split
            (successorResultsN fuel)
      let wrapperContexts :=
        match config with
        | (state, [.label arity continuation body]) =>
            (successorResultsN fuel (state, body)).map fun result =>
              { event := .ctxtLabel arity result.event
                next := (result.next.1,
                  [.label arity continuation result.next.2])
                step := .ctxtLabel result.step }
        | (state, [.frame arity innerFrame body]) =>
            (successorResultsN fuel
              (⟨state.store, innerFrame⟩, body)).map fun result =>
                { event := .ctxtFrame arity result.event
                  next := (⟨result.next.1.store, state.frame⟩,
                    [.frame arity result.next.1.frame result.next.2])
                  step := .ctxtFrame result.step }
        | (state, [.handler arity catches body]) =>
            liftHandlerResults state arity catches body
              (successorResultsN fuel)
        | _ => []
      base ++ instrContexts ++ wrapperContexts

mutual
  /-- Tree size of an administrative instruction. -/
  def adminInstrTreeSize : AdminInstr → Nat
    | .label _ continuation body =>
        1 + adminInstrsTreeSize continuation + adminInstrsTreeSize body
    | .frame _ _ body => 1 + adminInstrsTreeSize body
    | .handler _ _ body => 1 + adminInstrsTreeSize body
    | _ => 1

  /-- Sum of the tree sizes in an administrative instruction sequence. -/
  def adminInstrsTreeSize : List AdminInstr → Nat
    | [] => 0
    | instruction :: rest =>
        adminInstrTreeSize instruction + adminInstrsTreeSize rest
end

/-- One more than the source tree size is sufficient for every strict
recursive context descent. -/
def successorFuel (config : Config) : Nat := adminInstrsTreeSize config.2 + 1

/-- The single executable amended-Core successor enumerator. -/
def successors (config : Config) : List (Event × Config) :=
  (successorResultsN (successorFuel config) config).map StepAResult.toPair

/-- Soundness of every fuel-indexed edge is structural. -/
theorem mem_successorResultsN_stepA {fuel : Nat} {config : Config}
    {result : StepAResult config} (h : result ∈ successorResultsN fuel config) :
    StepA config result.event result.next := result.step

/-- No edge emitted by the whole-machine enumerator is invented. -/
theorem mem_successors_stepA {config : Config} {event : Event} {next : Config}
    (hmem : (event, next) ∈ successors config) :
    StepA config event next := by
  simp only [successors, List.mem_map] at hmem
  obtain ⟨result, _, heq⟩ := hmem
  rcases result with ⟨emitted, successor, hstep⟩
  simp only [StepAResult.toPair, Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact hstep

theorem adminValues?_vals (values : List Val) :
    adminValues? (vals values) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [show vals (value :: rest) = value.toAdmin :: vals rest by rfl]
      simp only [adminValues?, adminToVal_toAdmin, ih]
      rfl

theorem pure_mem_baseStepResults {z : State} {is is' : List AdminInstr}
    {pe : PureEvent} (h : (pe, is') ∈ pureSuccessors releasedNumerics is) :
    ∃ result ∈ baseStepResults (z, is),
      result.toPair = (.pure pe (sourcePlains is), (z, is')) := by
  let candidate : StepAResult (z, is) :=
    { event := .pure pe (sourcePlains is)
      next := (z, is')
      step := .pure h }
  refine ⟨candidate, ?_, rfl⟩
  simp only [baseStepResults, pureStepResults, List.mem_append]
  apply Or.inl
  apply Or.inl
  simp only [List.mem_map]
  exact ⟨⟨(pe, is'), h⟩, List.mem_attach _ _, rfl⟩

theorem erased_mem_baseStepResults {config : Config} {event : Event}
    {next : Config} (h :
      (event, next) ∈ readSuccessors config ∨
      (event, next) ∈ directSuccessors config) :
    ∃ result ∈ baseStepResults config, result.toPair = (event, next) := by
  rcases config with ⟨z, is⟩
  rcases h with hread | hdirect
  · simp only [readSuccessors, List.mem_map] at hread
    obtain ⟨result, hresult, heq⟩ := hread
    exact ⟨result, by simp [baseStepResults, hresult], heq⟩
  · let result : StepAResult (z, is) :=
      { event := event
        next := next
        step := mem_directSuccessors_stepA hdirect }
    refine ⟨result, ?_, rfl⟩
    simp only [baseStepResults, List.mem_append]
    right
    simp only [directStepResults, List.mem_map]
    exact ⟨⟨(event, next), hdirect⟩, List.mem_attach _ _, rfl⟩

theorem read_mem_baseStepResults {config : Config} {event : Event}
    {next : Config} (h : (event, next) ∈ readSuccessors config) :
    ∃ result ∈ baseStepResults config, result.toPair = (event, next) :=
  erased_mem_baseStepResults (Or.inl h)

theorem direct_mem_baseStepResults {config : Config} {event : Event}
    {next : Config} (h : (event, next) ∈ directSuccessors config) :
    ∃ result ∈ baseStepResults config, result.toPair = (event, next) :=
  erased_mem_baseStepResults (Or.inr h)

@[simp] theorem adminInstrsTreeSize_append (left right : List AdminInstr) :
    adminInstrsTreeSize (left ++ right) =
      adminInstrsTreeSize left + adminInstrsTreeSize right := by
  induction left with
  | nil => simp [adminInstrsTreeSize]
  | cons instruction rest ih => simp [adminInstrsTreeSize, ih, Nat.add_assoc]

@[simp] theorem adminInstrsTreeSize_vals (values : List Val) :
    adminInstrsTreeSize (vals values) = values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      rw [show vals (value :: rest) = value.toAdmin :: vals rest by rfl]
      cases value with
      | num n => simp [Val.toAdmin, adminInstrsTreeSize, adminInstrTreeSize, ih]; omega
      | vec w => simp [Val.toAdmin, adminInstrsTreeSize, adminInstrTreeSize, ih]; omega
      | ref r =>
          cases r <;> simp [Val.toAdmin, adminInstrsTreeSize,
              adminInstrTreeSize, ih] <;> omega

theorem adminInstrsTreeSize_pos_of_ne_nil {instructions : List AdminInstr}
    (h : instructions ≠ []) : 0 < adminInstrsTreeSize instructions := by
  cases instructions with
  | nil => contradiction
  | cons instruction rest =>
      cases instruction <;> simp [adminInstrsTreeSize, adminInstrTreeSize] <;> omega

theorem mem_successorResultsN_of_mem_base {fuel : Nat} {config : Config}
    {result : StepAResult config} (h : result ∈ baseStepResults config) :
    result ∈ successorResultsN fuel config := by
  cases fuel with
  | zero => exact h
  | succ fuel =>
      simp only [successorResultsN, List.mem_append]
      exact Or.inl (Or.inl h)

theorem chosenSplit_mem (values : List Val)
    (inner post : List AdminInstr) :
    let chosen : ListSplit3 (vals values ++ inner ++ post) :=
      { pre := vals values, mid := inner, post := post, rebuild := rfl }
    chosen ∈ listSplits3 (vals values ++ inner ++ post) := by
  dsimp only
  obtain ⟨found, hfound, hpre, hmid, hpost⟩ :=
    triple_mem_listSplits3 (vals values) inner post
  have heq : found =
      ({ pre := vals values, mid := inner, post := post,
         rebuild := rfl } : ListSplit3 (vals values ++ inner ++ post)) := by
    cases found with
    | mk pre mid post rebuild =>
        simp only at hpre hmid hpost
        subst pre
        subst mid
        subst post
        rfl
  rwa [← heq]

theorem pair_mem_liftInstrSplitResults {z z' : State}
    {values : List Val} {inner inner' post : List AdminInstr}
    {event : Event} {innerResult : StepAResult (z, inner)}
    (hevent : innerResult.event = event)
    (hnext : innerResult.next = (z', inner'))
    (hnonempty : values ≠ [] ∨ post ≠ [])
    (recurse : (inner : Config) → List (StepAResult inner))
    (hmem : innerResult ∈ recurse (z, inner)) :
    let split : ListSplit3 (vals values ++ inner ++ post) :=
      { pre := vals values, mid := inner, post := post, rebuild := rfl }
    ∃ result ∈ liftInstrSplitResults z
        (vals values ++ inner ++ post) split recurse,
      result.toPair =
        (.ctxtInstrs values.length post.length event,
          (z', vals values ++ inner' ++ post)) := by
  dsimp only
  unfold liftInstrSplitResults
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
        unfold liftInstrSplitNonempty
        refine ⟨_, List.mem_map.mpr ⟨innerResult, hmem, rfl⟩, ?_⟩
        simp [StepAResult.toPair, StepAResult.castSource, hevent, hnext]
  case h_3 value' values' heq =>
    change adminValues? (vals values) = some (value' :: values') at heq
    rw [adminValues?_vals] at heq
    have hvalues : values = value' :: values' := Option.some.inj heq
    subst values
    unfold liftInstrSplitNonempty
    refine ⟨_, List.mem_map.mpr ⟨innerResult, hmem, rfl⟩, ?_⟩
    simp [StepAResult.toPair, StepAResult.castSource, hevent, hnext]

theorem stepA_pair_mem_successorResultsN
    (readComplete : ∀ {z : State} {rule : ReadRule}
      {is is' : List AdminInstr}, Step_readA z rule is is' →
        (.read rule (sourcePlains is), (z, is')) ∈ readSuccessors (z, is))
    {config : Config} {event : Event} {next : Config}
    (hstep : StepA config event next) :
    ∀ fuel, adminInstrsTreeSize config.2 < fuel →
      ∃ result ∈ successorResultsN fuel config,
        result.toPair = (event, next) := by
  induction hstep with
  | pure hp =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := pure_mem_baseStepResults hp
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | @read z rule is is' hr =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := read_mem_baseStepResults
        (readComplete hr)
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | @ctxtInstrs z z' values inner inner' post event hinner hnonempty ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hstrict : adminInstrsTreeSize inner <
              adminInstrsTreeSize (vals values ++ inner ++ post) := by
            simp only [adminInstrsTreeSize_append, adminInstrsTreeSize_vals]
            rcases hnonempty with hvalues | hpost
            · have : 0 < values.length := by
                cases values with
                | nil => exact False.elim (hvalues rfl)
                | cons _ _ => simp
              omega
            · have := adminInstrsTreeSize_pos_of_ne_nil hpost
              omega
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            change adminInstrsTreeSize (vals values ++ inner ++ post) <
              fuel + 1 at hfuel
            omega
          obtain ⟨innerResult, hinnerResult, heq⟩ := ih fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let split : ListSplit3 (vals values ++ inner ++ post) :=
            { pre := vals values, mid := inner, post := post, rebuild := rfl }
          have hsplit : split ∈ listSplits3 (vals values ++ inner ++ post) :=
            chosenSplit_mem values inner post
          obtain ⟨result, hresult, hpair⟩ :=
            pair_mem_liftInstrSplitResults hevent hnext hnonempty
              (successorResultsN fuel) hinnerResult
          refine ⟨result, ?_, hpair⟩
          simp only [successorResultsN, List.mem_append]
          exact Or.inl (Or.inr (List.mem_flatMap.mpr
            ⟨split, hsplit, hresult⟩))
  | @ctxtLabel z z' n cont inner inner' event hinner ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          obtain ⟨innerResult, hinnerResult, heq⟩ := ih fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let result : StepAResult (z, [.label n cont inner]) :=
            { event := .ctxtLabel n innerResult.event
              next := (innerResult.next.1,
                [.label n cont innerResult.next.2])
              step := .ctxtLabel innerResult.step }
          refine ⟨result, ?_, ?_⟩
          · simp only [successorResultsN, List.mem_append]
            apply Or.inr
            exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
          · simp [result, StepAResult.toPair, hevent, hnext]
  | @ctxtFrame s s' frame innerFrame nextFrame n inner inner' event
      hinner ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          obtain ⟨innerResult, hinnerResult, heq⟩ := ih fuel hinnerFuel
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
          · simp only [successorResultsN, List.mem_append]
            apply Or.inr
            exact List.mem_map.mpr ⟨innerResult, hinnerResult, rfl⟩
          · simp [result, StepAResult.toPair, hevent, hnext]
  | @ctxtHandler z z' n catches inner inner' event hinner ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hinnerFuel : adminInstrsTreeSize inner < fuel := by
            simp [adminInstrsTreeSize, adminInstrTreeSize] at hfuel
            omega
          obtain ⟨innerResult, hinnerResult, heq⟩ := ih fuel hinnerFuel
          have hevent : innerResult.event = event := congrArg Prod.fst heq
          have hnext : innerResult.next = (z', inner') := congrArg Prod.snd heq
          let result : StepAResult (z, [.handler n catches inner]) :=
            { event := .ctxtHandler n innerResult.event
              next := (innerResult.next.1,
                [.handler n catches innerResult.next.2])
              step := .ctxtHandler innerResult.step }
          refine ⟨result, ?_, ?_⟩
          · simp only [successorResultsN, List.mem_append]
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
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          let result : StepAResult (z, [.handler n catches [.trap]]) :=
            { event := .trapHandler n
              next := (z, [.trap])
              step := .trapHandler }
          refine ⟨result, ?_, rfl⟩
          simp only [successorResultsN, List.mem_append]
          apply Or.inr
          change result ∈
            liftHandlerResults z n catches [.trap] (successorResultsN fuel)
          simp only [liftHandlerResults]
          exact List.mem_cons_self
  | throw htag hdt hexpand ht hvs ha hta hex =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (throw_mem_directSuccessors htag hdt hexpand ht hvs ha hta hex))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | localSet hset =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (localSet_mem_directSuccessors hset))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | globalSet hset =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (globalSet_mem_directSuccessors hset))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | tableSetOob htable hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (tableSetOob_mem_directSuccessors htable hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | tableSetVal htable hin hset =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (tableSetVal_mem_directSuccessors htable hin hset))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | tableGrowSucceed htable hgrow hset hsize =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (tableGrowSucceed_mem_directSuccessors htable hgrow hset hsize))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | tableGrowFail heqFail =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (tableGrowFail_mem_directSuccessors heqFail))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | elemDrop hdrop =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (elemDrop_mem_directSuccessors hdrop))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | storeNumOob hmem hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (storeNumOob_mem_directSuccessors hmem hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | storeNumVal hbs hmem =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (storeNumVal_mem_directSuccessors hbs hmem))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | storePackOob hmem hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (storePackOob_mem_directSuccessors hmem hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | storePackVal hbs hmem =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (storePackVal_mem_directSuccessors hbs hmem))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | vstoreOob hmem hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (vstoreOob_mem_directSuccessors hmem hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | vstoreVal hbs hmem =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (vstoreVal_mem_directSuccessors hbs hmem))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | vstoreLaneOob hmem hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (vstoreLaneOob_mem_directSuccessors hmem hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | vstoreLaneVal hsize hdim hlane hbits hbs hmem =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (vstoreLaneVal_mem_directSuccessors
          hsize hdim hlane hbits hbs hmem))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | memoryGrowSucceed hmem hgrow hset hsize =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (memoryGrowSucceed_mem_directSuccessors hmem hgrow hset hsize))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | memoryGrowFail heqFail =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (memoryGrowFail_mem_directSuccessors heqFail))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | dataDrop hdrop =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (dataDrop_mem_directSuccessors hdrop))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | structNew htype hexpand hfts hvs ha hpack hsi =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (structNew_mem_directSuccessors
          htype hexpand hfts hvs ha hpack hsi))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | structSetNull =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr structSetNull_mem_directSuccessors)
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | structSetStruct htype hexpand hfield hpack hset =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (structSetStruct_mem_directSuccessors
          htype hexpand hfield hpack hset))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | arrayNewFixed htype hexpand hlen ha hpack hai =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (arrayNewFixed_mem_directSuccessors
          htype hexpand hlen ha hpack hai))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | arraySetNull =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr arraySetNull_mem_directSuccessors)
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | arraySetOob harray hoob =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (arraySetOob_mem_directSuccessors harray hoob))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩
  | arraySetArray htype hexpand hpack hset =>
      intro fuel hfuel
      obtain ⟨result, hresult, heq⟩ := erased_mem_baseStepResults
        (Or.inr (arraySetArray_mem_directSuccessors htype hexpand hpack hset))
      exact ⟨result, mem_successorResultsN_of_mem_base hresult, heq⟩

end WasmGemmGnaf.Wasm.Core.Exec
