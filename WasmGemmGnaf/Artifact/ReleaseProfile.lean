import WasmGemmGnaf.Wasm.Adequacy
import WasmGemmGnaf.Wasm.Evaluate

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

/-!
# The released public-Core cost profile

The release table is built from the generated, vendored Core authority
inventory.  Every enabled authority identifier occurs exactly once.  Harness
and initialization identifiers live in disjoint explicit namespaces and are
also duplicate free.

The row contribution is the static part of a rule charge.  Operand-dependent
bytes, pages, lanes, table elements, and managed-object widths are retained by
the public event and added by `Wasm.eventCostBody`; wrapper rules therefore do
not charge a second Core step.
-/

namespace WasmGemmGnaf.Release

open WasmGemmGnaf

/-- The complete enabled pinned authority inventory, in vendored source order. -/
def core3RuleConformanceMap : List Wasm.PinnedCoreRuleId :=
  Wasm.PinnedCoreRuleId.enabledRuleIds

/-- Whether an authority row is one of the actual inner execution rules. -/
def authorityExecutesStep (id : Wasm.PinnedCoreRuleId) : Bool :=
  id.source.kind == .execution &&
    (id.source.item.startsWith "Step_pure/" ||
      id.source.item.startsWith "Step_read/" ||
      (id.source.item.startsWith "Step/" &&
        id.source.item != "Step/pure" &&
        id.source.item != "Step/read" &&
        !id.source.item.startsWith "Step/ctxt-"))

/-- Dispatch-bearing Core rules.  This list contains only static rule
classification; dynamic transfer sizes remain in the public event. -/
def authorityDispatches (id : Wasm.PinnedCoreRuleId) : Bool :=
  let item := id.source.item
  item.startsWith "Step_pure/br" || item.startsWith "Step_read/br" ||
    item.startsWith "Step_pure/call" || item.startsWith "Step_read/call" ||
    item.startsWith "Step_pure/return" || item.startsWith "Step_read/return" ||
    item.startsWith "Step/throw" || item.startsWith "Step_read/throw" ||
    item.startsWith "Step_pure/if-" || item.startsWith "Step_pure/frame-vals"

/-- Scalar primitive numeric rules whose successful result represents one
completed scalar operation.  Trapping variants are deliberately excluded. -/
def authorityScalarOperation (id : Wasm.PinnedCoreRuleId) : Bool :=
  let item := id.source.item
  item == "Step_pure/unop-val" || item == "Step_pure/binop-val" ||
    item == "Step_pure/testop" || item == "Step_pure/relop" ||
    item == "Step_pure/cvtop-val"

/-- Static contribution of one generated authority row. -/
def canonicalRuleContribution (id : Wasm.PinnedCoreRuleId) : Cost.DynamicVector :=
  { Cost.DynamicVector.zero with
      wasmRuleSteps := if authorityExecutesStep id then 1 else 0
      dispatchSteps := if authorityDispatches id then 1 else 0
      scalarOps := if authorityScalarOperation id then 1 else 0 }

def authorityRuleRow (id : Wasm.PinnedCoreRuleId) : Wasm.CostRuleRow :=
  Wasm.canonicalRow id.ruleId (canonicalRuleContribution id)

def authorityRuleRows : List Wasm.CostRuleRow :=
  core3RuleConformanceMap.map authorityRuleRow

/-- Public Harness rules are disjoint from the `spectec-rule-*` authority
namespace. -/
def harnessRuleRows : List Wasm.CostRuleRow :=
  [ Wasm.canonicalRow "harness/initialize" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "harness/core-before-entry" Cost.DynamicVector.zero
  , Wasm.canonicalRow "harness/install-raw" Wasm.canonicalDispatchContribution
  , Wasm.canonicalRow "harness/enter-gemm" Wasm.canonicalDispatchContribution
  , Wasm.canonicalRow "harness/core-after-entry" Cost.DynamicVector.zero
  , Wasm.canonicalRow "harness/return-after-entry" Wasm.canonicalDispatchContribution
  , Wasm.canonicalRow "harness/throw-before-entry" Wasm.canonicalDispatchContribution
  , Wasm.canonicalRow "harness/throw-after-entry" Wasm.canonicalDispatchContribution ]

/-- Every allocation/static-initialization phase named by the amended public
initializer, in execution order. -/
def initializationRows : List Wasm.CostRuleRow :=
  [ Wasm.canonicalRow "init/close-type" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-tag" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/eval-global" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-global" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-memory" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/eval-table" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-table" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-function" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-data" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/eval-elem" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-elem" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/alloc-export" Wasm.canonicalInstantiationContribution
  , Wasm.canonicalRow "init/construct-harness-frame"
      { Wasm.canonicalInstantiationContribution with preparationSteps := 1 } ]

/-- SPEC §7.5's first-order release cost table. -/
def wasmCostTableBody : Wasm.CostTableBody :=
  { decodeUnitPerByte := 1
    decodeTerminalUnit := 1
    validationNodeUnit := 1
    validationEdgeUnit := 1
    ruleStepUnit := 1
    installationPreparationUnit := 1
    installedByteWriteUnit := 1
    wholeVectorShuffleLanes := 16
    layout := Wasm.canonicalGcLayout
    ruleRows := authorityRuleRows ++ harnessRuleRows
    initializationRows := initializationRows }

theorem core3RuleConformanceMap_nodup : core3RuleConformanceMap.Nodup :=
  Wasm.PinnedCoreRuleId.enabledRuleIds_nodup

theorem authorityRuleIds_nodup :
    (authorityRuleRows.map Wasm.CostRuleRow.ruleId).Nodup := by
  have hids :
      (core3RuleConformanceMap.map Wasm.PinnedCoreRuleId.ruleId).Nodup :=
    by
      rw [List.Nodup, List.pairwise_map]
      exact core3RuleConformanceMap_nodup.imp (by
        intro left right hne heq
        exact hne (Wasm.PinnedCoreRuleId.ruleId_injective heq))
  simpa [authorityRuleRows, authorityRuleRow] using hids

theorem harnessRuleIds_nodup :
    (harnessRuleRows.map Wasm.CostRuleRow.ruleId).Nodup := by decide

theorem authorityRuleId_ne_harness {id : Wasm.PinnedCoreRuleId}
    {row : Wasm.CostRuleRow} (hrow : row ∈ harnessRuleRows) :
    id.ruleId ≠ row.ruleId := by
  intro heq
  have hchars := congrArg String.toList heq
  simp [harnessRuleRows] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Wasm.PinnedCoreRuleId.ruleId] at hchars

theorem wasmCostTableBody_ruleRows_nodup :
    (wasmCostTableBody.ruleRows.map Wasm.CostRuleRow.ruleId).Nodup := by
  change ((authorityRuleRows ++ harnessRuleRows).map
    Wasm.CostRuleRow.ruleId).Nodup
  simp only [List.map_append]
  rw [List.nodup_append]
  refine ⟨authorityRuleIds_nodup, harnessRuleIds_nodup, ?_⟩
  intro authorityId ha harnessId hh heq
  obtain ⟨authorityRow, haRow, haId⟩ := List.mem_map.mp ha
  obtain ⟨sourceId, _, hsource⟩ := List.mem_map.mp haRow
  obtain ⟨harnessRow, hhRow, hhId⟩ := List.mem_map.mp hh
  apply authorityRuleId_ne_harness hhRow
  calc
    sourceId.ruleId = authorityRow.ruleId := by
      have := congrArg Wasm.CostRuleRow.ruleId hsource
      simpa [authorityRuleRow] using this
    _ = authorityId := haId
    _ = harnessId := heq
    _ = harnessRow.ruleId := hhId.symm

theorem wasmCostTableBody_initializationRows_nodup :
    (wasmCostTableBody.initializationRows.map
      Wasm.CostRuleRow.ruleId).Nodup := by decide

/-- The profile body is genuinely the released authority-backed table, not
the old unit non-vacuity witness. -/
def wasmProfileBody : Wasm.ProfileBody :=
  Wasm.canonicalCore3Wasm32ProfileBody Wasm.core3RevisionCommit
    wasmCostTableBody

theorem wasmProfileBody_lawful : Wasm.ProfileLawful wasmProfileBody := by
  apply Wasm.canonicalCore3Wasm32ProfileBody_lawful
  all_goals first
    | rfl
    | exact wasmCostTableBody_ruleRows_nodup
    | exact wasmCostTableBody_initializationRows_nodup

/-- The checked released public-Core profile. -/
def wasmProfile : Wasm.Profile :=
  Wasm.Profile.checked wasmProfileBody wasmProfileBody_lawful

theorem wasmProfile_body : wasmProfile.body = wasmProfileBody := rfl

theorem profile_cost_table_exact :
    wasmProfile.costTableBody = wasmCostTableBody := rfl

theorem wasmProfile_ne_unitWitnessProfile :
    wasmProfile ≠ Wasm.unitWitnessProfile := by
  intro heq
  have htable := congrArg Wasm.Profile.costTableBody heq
  have hlength := congrArg
    (fun table : Wasm.CostTableBody => table.initializationRows.length) htable
  change wasmCostTableBody.initializationRows.length =
    Wasm.canonicalCostTableUnits.initializationRows.length at hlength
  have : 13 = 9 := by
    simpa only [wasmCostTableBody, initializationRows,
      Wasm.canonicalCostTableUnits,
      Wasm.canonicalInitializationRows_length] using hlength
  omega

end WasmGemmGnaf.Release
