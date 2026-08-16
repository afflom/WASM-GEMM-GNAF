/-
  Full-domain aggregation of costs.
  Normative source: SPEC.md sections 9.1 (`Cost.ExactAggregateCost`) and 9.2
  ("The release workload is the canonical finite ordering of every raw
  invocation under the released profile").

  The predicate below is stated directly over the public amended-Core carrier
  and its executable decode and static-cost functions.

  Every declaration in this file is proved. Nothing is assumed.
-/
import WasmGemmGnaf.Cost.Trace
import WasmGemmGnaf.Foundation.Finite
import WasmGemmGnaf.Wasm.Core.CostAccounting

set_option autoImplicit false

namespace WasmGemmGnaf.Cost

/-! ## Componentwise operations on dynamic vectors -/

/-- Componentwise addition of dynamic vectors: the aggregation SPEC 9.1 folds
the full raw-invocation domain with. -/
def ComponentwiseAdd (a b : DynamicVector) : DynamicVector :=
  { instantiationSteps := a.instantiationSteps + b.instantiationSteps
    dispatchSteps := a.dispatchSteps + b.dispatchSteps
    preparationSteps := a.preparationSteps + b.preparationSteps
    wasmRuleSteps := a.wasmRuleSteps + b.wasmRuleSteps
    scalarOps := a.scalarOps + b.scalarOps
    vectorLaneOps := a.vectorLaneOps + b.vectorLaneOps
    bytesRead := a.bytesRead + b.bytesRead
    bytesWritten := a.bytesWritten + b.bytesWritten
    memoryGrowPages := a.memoryGrowPages + b.memoryGrowPages
    tableElementsAllocated := a.tableElementsAllocated + b.tableElementsAllocated
    gcObjectsAllocated := a.gcObjectsAllocated + b.gcObjectsAllocated
    gcBytesInitialized := a.gcBytesInitialized + b.gcBytesInitialized
    peakStackValues := a.peakStackValues + b.peakStackValues
    peakPages := a.peakPages + b.peakPages
    peakGcLiveBytes := a.peakGcLiveBytes + b.peakGcLiveBytes
    outputBytes := a.outputBytes + b.outputBytes }

/-- Componentwise maximum of dynamic vectors. -/
def ComponentwiseMax (a b : DynamicVector) : DynamicVector :=
  { instantiationSteps := max a.instantiationSteps b.instantiationSteps
    dispatchSteps := max a.dispatchSteps b.dispatchSteps
    preparationSteps := max a.preparationSteps b.preparationSteps
    wasmRuleSteps := max a.wasmRuleSteps b.wasmRuleSteps
    scalarOps := max a.scalarOps b.scalarOps
    vectorLaneOps := max a.vectorLaneOps b.vectorLaneOps
    bytesRead := max a.bytesRead b.bytesRead
    bytesWritten := max a.bytesWritten b.bytesWritten
    memoryGrowPages := max a.memoryGrowPages b.memoryGrowPages
    tableElementsAllocated := max a.tableElementsAllocated b.tableElementsAllocated
    gcObjectsAllocated := max a.gcObjectsAllocated b.gcObjectsAllocated
    gcBytesInitialized := max a.gcBytesInitialized b.gcBytesInitialized
    peakStackValues := max a.peakStackValues b.peakStackValues
    peakPages := max a.peakPages b.peakPages
    peakGcLiveBytes := max a.peakGcLiveBytes b.peakGcLiveBytes
    outputBytes := max a.outputBytes b.outputBytes }

theorem value_componentwiseAdd (dc : DynamicCoordinate) (a b : DynamicVector) :
    dc.value (ComponentwiseAdd a b) = dc.value a + dc.value b := by
  cases dc <;> rfl

theorem value_componentwiseMax (dc : DynamicCoordinate) (a b : DynamicVector) :
    dc.value (ComponentwiseMax a b) = max (dc.value a) (dc.value b) := by
  cases dc <;> rfl

theorem componentwiseAdd_assoc (a b c : DynamicVector) :
    ComponentwiseAdd (ComponentwiseAdd a b) c
      = ComponentwiseAdd a (ComponentwiseAdd b c) := by
  cases a; cases b; cases c; simp [ComponentwiseAdd, Nat.add_assoc]

theorem componentwiseAdd_comm (a b : DynamicVector) :
    ComponentwiseAdd a b = ComponentwiseAdd b a := by
  cases a; cases b; simp [ComponentwiseAdd, Nat.add_comm]

theorem componentwiseAdd_zero_left (a : DynamicVector) :
    ComponentwiseAdd DynamicVector.zero a = a := by
  cases a; simp [ComponentwiseAdd, DynamicVector.zero]

theorem componentwiseAdd_zero_right (a : DynamicVector) :
    ComponentwiseAdd a DynamicVector.zero = a := by
  cases a; simp [ComponentwiseAdd, DynamicVector.zero]

theorem componentwiseMax_assoc (a b c : DynamicVector) :
    ComponentwiseMax (ComponentwiseMax a b) c
      = ComponentwiseMax a (ComponentwiseMax b c) := by
  cases a; cases b; cases c; simp [ComponentwiseMax, Nat.max_assoc]

theorem componentwiseMax_comm (a b : DynamicVector) :
    ComponentwiseMax a b = ComponentwiseMax b a := by
  cases a; cases b; simp [ComponentwiseMax, Nat.max_comm]

theorem componentwiseMax_zero_left (a : DynamicVector) :
    ComponentwiseMax DynamicVector.zero a = a := by
  cases a; simp [ComponentwiseMax, DynamicVector.zero]

theorem componentwiseMax_zero_right (a : DynamicVector) :
    ComponentwiseMax a DynamicVector.zero = a := by
  cases a; simp [ComponentwiseMax, DynamicVector.zero]

/-- SPEC 9.1: `Cost.scale`, the workload-repetition multiplier. -/
def scale (n : Nat) (v : DynamicVector) : DynamicVector :=
  { instantiationSteps := n * v.instantiationSteps
    dispatchSteps := n * v.dispatchSteps
    preparationSteps := n * v.preparationSteps
    wasmRuleSteps := n * v.wasmRuleSteps
    scalarOps := n * v.scalarOps
    vectorLaneOps := n * v.vectorLaneOps
    bytesRead := n * v.bytesRead
    bytesWritten := n * v.bytesWritten
    memoryGrowPages := n * v.memoryGrowPages
    tableElementsAllocated := n * v.tableElementsAllocated
    gcObjectsAllocated := n * v.gcObjectsAllocated
    gcBytesInitialized := n * v.gcBytesInitialized
    peakStackValues := n * v.peakStackValues
    peakPages := n * v.peakPages
    peakGcLiveBytes := n * v.peakGcLiveBytes
    outputBytes := n * v.outputBytes }

theorem value_scale (dc : DynamicCoordinate) (n : Nat) (v : DynamicVector) :
    dc.value (scale n v) = n * dc.value v := by
  cases dc <;> rfl

theorem scale_one (v : DynamicVector) : scale 1 v = v := by
  cases v; simp [scale]

theorem scale_zero (v : DynamicVector) : scale 0 v = DynamicVector.zero := by
  cases v; simp [scale, DynamicVector.zero]

/-- One repetition of a nonzero workload is never lost. -/
theorem le_scale (n : Nat) (hn : 1 ≤ n) (v : DynamicVector) :
    DynamicVector.ComponentwiseLE v (scale n v) := by
  intro dc
  rw [value_scale]
  exact Nat.le_mul_of_pos_left _ hn

/-- SPEC 10.1: componentwise maximum over a finite list of costs. -/
def maxOverCosts (l : List DynamicVector) : DynamicVector :=
  l.foldr ComponentwiseMax DynamicVector.zero

theorem maxOverCosts_nil : maxOverCosts [] = DynamicVector.zero := rfl

theorem maxOverCosts_cons (v : DynamicVector) (l : List DynamicVector) :
    maxOverCosts (v :: l) = ComponentwiseMax v (maxOverCosts l) := rfl

/-- Every observed cost is dominated by the maximum over the observations. -/
theorem le_maxOverCosts {v : DynamicVector} : ∀ {l : List DynamicVector}, v ∈ l →
    DynamicVector.ComponentwiseLE v (maxOverCosts l) := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons w rest ih =>
      intro h dc
      rw [maxOverCosts_cons, value_componentwiseMax]
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem dc) (Nat.le_max_right _ _)

/-- A componentwise bound on every list member also bounds the finite
componentwise maximum. -/
theorem maxOverCosts_le {l : List DynamicVector} {bound : DynamicVector}
    (h : ∀ v ∈ l, DynamicVector.ComponentwiseLE v bound) :
    DynamicVector.ComponentwiseLE (maxOverCosts l) bound := by
  induction l with
  | nil => exact DynamicVector.zero_componentwiseLE bound
  | cons v rest ih =>
      intro dc
      rw [maxOverCosts_cons, value_componentwiseMax]
      exact Nat.max_le.mpr ⟨(h v (by simp)) dc,
        ih (fun w hw => h w (by simp [hw])) dc⟩

/-- If initialization itself and every initialized branch are bounded, then
initialization followed by the componentwise worst branch is bounded. -/
theorem sequentialCompose_maxOverCosts_le {initial bound : DynamicVector}
    {l : List DynamicVector}
    (hinitial : DynamicVector.ComponentwiseLE initial bound)
    (h : ∀ v ∈ l,
      DynamicVector.ComponentwiseLE (sequentialCompose initial v) bound) :
    DynamicVector.ComponentwiseLE
      (sequentialCompose initial (maxOverCosts l)) bound := by
  induction l with
  | nil => simpa [maxOverCosts_nil, sequentialCompose_zero_right] using hinitial
  | cons v rest ih =>
      intro dc
      have hv := (h v (by simp)) dc
      have hr := ih (fun w hw => h w (by simp [hw])) dc
      cases dc <;>
        simp only [maxOverCosts_cons, ComponentwiseMax,
          DynamicCoordinate.value, sequentialCompose] at hv hr ⊢ <;>
        omega

/--
  SPEC 9.2 / 10.1: the worst-case cost of one raw invocation.  Nondeterministic
  execution cost is the componentwise maximum over all permitted terminating
  traces, composed after the initialization cost of the fresh instance.
-/
def worstCaseInvocationCost (initialization : DynamicVector)
    (observations : List DynamicVector) : DynamicVector :=
  sequentialCompose initialization (maxOverCosts observations)

/-- Initialization work is never lost in the worst-case invocation cost: a
trapped or diverging start is still charged. -/
theorem initialization_le_worstCase (initialization : DynamicVector)
    (observations : List DynamicVector) :
    DynamicVector.ComponentwiseLE initialization
      (worstCaseInvocationCost initialization observations) :=
  sequentialCompose_le_left _ _

/-- Every recorded maximal observation is charged in the worst-case invocation
cost. -/
theorem observation_le_worstCase (initialization : DynamicVector)
    {observations : List DynamicVector} {v : DynamicVector}
    (hv : v ∈ observations) :
    DynamicVector.ComponentwiseLE v
      (worstCaseInvocationCost initialization observations) :=
  DynamicVector.componentwiseLE_trans (le_maxOverCosts hv)
    (sequentialCompose_le_right _ _)

/-! ## Folding over the whole raw-invocation domain -/

/-- Projecting a componentwise-add fold to one coordinate is the corresponding
`Nat` fold. -/
theorem foldl_add_value {Raw : Type} (f : Raw → DynamicVector)
    (dc : DynamicCoordinate) :
    ∀ (l : List Raw) (init : DynamicVector),
      dc.value (l.foldl (fun acc a => ComponentwiseAdd acc (f a)) init)
        = l.foldl (fun acc a => acc + dc.value (f a)) (dc.value init) := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (ComponentwiseAdd init (f x)), value_componentwiseAdd]

/-- Projecting a componentwise-max fold to one coordinate is the corresponding
`Nat` fold. -/
theorem foldl_max_value {Raw : Type} (f : Raw → DynamicVector)
    (dc : DynamicCoordinate) :
    ∀ (l : List Raw) (init : DynamicVector),
      dc.value (l.foldl (fun acc a => ComponentwiseMax acc (f a)) init)
        = l.foldl (fun acc a => Nat.max acc (dc.value (f a))) (dc.value init) := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (ComponentwiseMax init (f x)), value_componentwiseMax]

/-- SPEC 9.2: the componentwise full-domain sum over every raw invocation. -/
def fullDomainSum {Raw : Type} [Foundation.Fintype Raw]
    (f : Raw → DynamicVector) : DynamicVector :=
  Foundation.Finite.fold ComponentwiseAdd DynamicVector.zero f

/-- SPEC 9.2: the componentwise full-domain maximum over every raw
invocation. -/
def fullDomainMax {Raw : Type} [Foundation.Fintype Raw]
    (f : Raw → DynamicVector) : DynamicVector :=
  Foundation.Finite.fold ComponentwiseMax DynamicVector.zero f

/-- Full-domain coverage: no raw invocation's charge escapes the total. -/
theorem le_fullDomainSum {Raw : Type} [Foundation.Fintype Raw]
    (f : Raw → DynamicVector) (a : Raw) :
    DynamicVector.ComponentwiseLE (f a) (fullDomainSum f) := by
  intro dc
  rw [fullDomainSum, Foundation.Finite.fold_eq_foldl, foldl_add_value]
  rw [DynamicCoordinate.value_zero]
  exact Foundation.Finite.foldl_add_mem (fun x => dc.value (f x))
    (Foundation.Fintype.elems Raw) 0 a (Foundation.Fintype.mem_elems a)

/-- Full-domain coverage: no raw invocation's charge escapes the maximum. -/
theorem le_fullDomainMax {Raw : Type} [Foundation.Fintype Raw]
    (f : Raw → DynamicVector) (a : Raw) :
    DynamicVector.ComponentwiseLE (f a) (fullDomainMax f) := by
  intro dc
  rw [fullDomainMax, Foundation.Finite.fold_eq_foldl, foldl_max_value]
  rw [DynamicCoordinate.value_zero]
  exact Foundation.Finite.foldl_max_mem (fun x => dc.value (f x))
    (Foundation.Fintype.elems Raw) 0 a (Foundation.Fintype.mem_elems a)

/-! ## The exact aggregate cost predicate -/

/--
  SPEC 9.1, `Cost.ExactAggregateCost`.

  Every static coordinate is tied to the same public profile, byte sequence,
  and amended-Core module.  The dynamic sum and maximum range over the complete
  finite raw-input carrier.
-/
def ExactAggregateCost {Raw : Type} [Foundation.Fintype Raw]
    (P : Wasm.Profile)
    (bytes : ByteArray)
    (module : Wasm.Module)
    (repetitions : Nat)
    (dynamicFor : Raw → DynamicVector)
    (cost : CompleteSystemCost) : Prop :=
  1 ≤ repetitions ∧
  Wasm.decode bytes = .ok module ∧
  cost.static.moduleBytes = bytes.size ∧
  cost.static.decodeSteps = Wasm.decodeCost P.costTableBody bytes ∧
  cost.static.validationSteps = Wasm.validationCost P.costTableBody module ∧
  cost.static.staticDataBytes = Wasm.instantiatedStaticBytes P module ∧
  cost.dynamicSum =
    scale repetitions
      (Foundation.Finite.fold ComponentwiseAdd DynamicVector.zero dynamicFor) ∧
  cost.dynamicMax =
    Foundation.Finite.fold ComponentwiseMax DynamicVector.zero dynamicFor

section Exact

variable {Raw : Type} [Foundation.Fintype Raw]
  {P : Wasm.Profile} {bytes : ByteArray} {module : Wasm.Module}
  {repetitions : Nat}
  {dynamicFor : Raw → DynamicVector} {cost : CompleteSystemCost}

/-- SPEC 9.3: `evaluation.cost.static.moduleBytes = bytes.size`. -/
theorem module_bytes_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.static.moduleBytes = bytes.size := h.2.2.1

theorem repetitions_positive
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    1 ≤ repetitions := h.1

/-- The aggregate's bytes decode to the same public amended-Core module used by
all other static coordinates. -/
theorem decode_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    Wasm.decode bytes = .ok module := h.2.1

theorem decode_steps_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.static.decodeSteps = Wasm.decodeCost P.costTableBody bytes := h.2.2.2.1

theorem validation_steps_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.static.validationSteps = Wasm.validationCost P.costTableBody module :=
  h.2.2.2.2.1

theorem static_data_bytes_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.static.staticDataBytes = Wasm.instantiatedStaticBytes P module :=
  h.2.2.2.2.2.1

theorem dynamic_sum_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.dynamicSum = scale repetitions (fullDomainSum dynamicFor) :=
  h.2.2.2.2.2.2.1

theorem dynamic_max_exact
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) :
    cost.dynamicMax = fullDomainMax dynamicFor := h.2.2.2.2.2.2.2

/-- Full-domain accounting: every raw invocation's charge appears in the
aggregated dynamic sum. -/
theorem raw_charge_le_dynamicSum
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) (a : Raw) :
    DynamicVector.ComponentwiseLE (dynamicFor a) cost.dynamicSum := by
  rw [dynamic_sum_exact h]
  exact DynamicVector.componentwiseLE_trans (le_fullDomainSum dynamicFor a)
    (le_scale repetitions (repetitions_positive h) _)

/-- Full-domain accounting: every raw invocation's charge appears in the
aggregated dynamic maximum. -/
theorem raw_charge_le_dynamicMax
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost) (a : Raw) :
    DynamicVector.ComponentwiseLE (dynamicFor a) cost.dynamicMax := by
  rw [dynamic_max_exact h]
  exact le_fullDomainMax dynamicFor a

/-- The exact aggregate determines the whole cost vector: two vectors exact for
the same data are equal. -/
theorem exact_unique
    {cost' : CompleteSystemCost}
    (h : ExactAggregateCost P bytes module repetitions dynamicFor cost)
    (h' : ExactAggregateCost P bytes module repetitions dynamicFor cost') :
    cost = cost' := by
  obtain ⟨s, ds, dm⟩ := cost
  obtain ⟨s', ds', dm'⟩ := cost'
  obtain ⟨mb, dsn, vsn, sdb⟩ := s
  obtain ⟨mb', dsn', vsn', sdb'⟩ := s'
  simp only [ArtifactVector.mk.injEq, StaticVector.mk.injEq]
  exact ⟨⟨(module_bytes_exact h).trans (module_bytes_exact h').symm,
      (decode_steps_exact h).trans (decode_steps_exact h').symm,
      (validation_steps_exact h).trans (validation_steps_exact h').symm,
      (static_data_bytes_exact h).trans (static_data_bytes_exact h').symm⟩,
    (dynamic_sum_exact h).trans (dynamic_sum_exact h').symm,
    (dynamic_max_exact h).trans (dynamic_max_exact h').symm⟩

end Exact

end WasmGemmGnaf.Cost
