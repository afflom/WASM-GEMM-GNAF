/-
  Wasm/Core/RuntimeTypeOrigin.lean --- the finite closed-type graph exposed by
  an allocated Core module instance.

  Runtime subtyping operates on closed literal `DefType`s, after source type
  indices have been substituted away.  Endpoint well-formedness alone does
  not recover the source graph: a literal type can hide an invalid intermediate
  supertype.  `SubtypeSound.heapDecision_not_complete_of_endpoint_validity`
  is the closed counterexample.

  The genuine runtime certificate is allocation provenance.  `Instantiation`
  proves that a module instance's type vector is exactly `allocTypes m.types`.
  The graph predicate below records the remaining property obtained from the
  module's `Types_okA` derivation: every closed declared-super edge points to a
  strictly earlier member of that vector.  The two bounding theorems turn that
  structural decrease into the fixed finite fuel consumed by executable
  runtime reference tests.  No subtype-completeness proposition is assumed or
  stored in a structure.
-/
import WasmGemmGnaf.Wasm.Core.Instantiation
import WasmGemmGnaf.Wasm.Core.Subtype

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Every declared-super edge of a closed allocated type resolves to a
strictly earlier closed type in the same allocation vector. -/
def ClosedTypeGraphOk (dts : List DefType) : Prop :=
  ∀ (i : Nat) (dt : DefType), dts[i]? = some dt →
    ∀ g ∈ Context.empty.heapSupers (.use (.defd dt)),
      ∃ (j : Nat) (super : DefType),
        j < i ∧ dts[j]? = some super ∧ g = .use (.defd super)

/-- The closed allocation graph computed from a source module.  The validator
must derive this predicate from `Types_okA`; it is not an admission premise. -/
def AllocatedTypeGraphOk (m : Module) : Prop :=
  ClosedTypeGraphOk (allocTypes m.types)

/-- Allocation provenance transports the source module's graph property to
the concrete module instance used by execution. -/
theorem ModuleInst.closedTypeGraphOk_of_allocated {m : Module} {mm : ModuleInst}
    (horigin : mm.AllocatedTypesFrom m) (hgraph : AllocatedTypeGraphOk m) :
    ClosedTypeGraphOk mm.types := by
  unfold ModuleInst.AllocatedTypesFrom at horigin
  unfold AllocatedTypeGraphOk at hgraph
  rwa [horigin]

/-- A successful declared-super walk starting at allocation index `i` never
needs more than `i + 1` units of fuel.  The proof follows the actual executable
walk and uses the graph certificate at every edge. -/
theorem reachDef_bounded_of_closedTypeGraphOk {dts : List DefType}
    (hgraph : ClosedTypeGraphOk dts) {i : Nat} {dt : DefType}
    (hdt : dts[i]? = some dt) {target : HeapType} {n : Nat}
    (hreach : Context.empty.reachDef n (.use (.defd dt)) target = true) :
    Context.empty.reachDef (i + 1) (.use (.defd dt)) target = true := by
  let rec go (i : Nat) (dt : DefType) (hdt : dts[i]? = some dt)
      (n : Nat)
      (hreach : Context.empty.reachDef n (.use (.defd dt)) target = true) :
      Context.empty.reachDef (i + 1) (.use (.defd dt)) target = true := by
    cases n with
    | zero =>
        rw [Context.reachDef] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        exact Or.inl hreach
    | succ n =>
        rw [Context.reachDef, Bool.or_eq_true] at hreach
        rw [Context.reachDef, Bool.or_eq_true]
        rcases hreach with heq | hsupers
        · exact Or.inl heq
        · right
          obtain ⟨g, hg, hgreach⟩ := List.any_eq_true.mp hsupers
          obtain ⟨j, super, hji, hsuper, rfl⟩ := hgraph i dt hdt g hg
          have hbounded := go j super hsuper n hgreach
          have hle : j + 1 ≤ i := hji
          exact List.any_eq_true.mpr ⟨.use (.defd super), hg,
            reachDef_mono hle hbounded⟩
  termination_by i
  exact go i dt hdt n hreach

/-- The length of the allocated type vector is one uniform executable fuel
bound for a successful walk starting at any member of that vector. -/
theorem reachDef_closedTypeFuel_of_graphOk {dts : List DefType}
    (hgraph : ClosedTypeGraphOk dts) {i : Nat} {dt : DefType}
    (hdt : dts[i]? = some dt) {target : HeapType} {n : Nat}
    (hreach : Context.empty.reachDef n (.use (.defd dt)) target = true) :
    Context.empty.reachDef dts.length (.use (.defd dt)) target = true := by
  have hbounded := reachDef_bounded_of_closedTypeGraphOk hgraph hdt hreach
  have hi := (List.getElem?_eq_some_iff.mp hdt).1
  exact reachDef_mono (by omega) hbounded

end WasmGemmGnaf.Wasm.Core.Exec
