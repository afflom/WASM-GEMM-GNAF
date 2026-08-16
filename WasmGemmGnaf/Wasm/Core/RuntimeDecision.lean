/-
  Wasm/Core/RuntimeDecision.lean --- executable principal runtime reference
  typing for the amended Core authority.

  `Ref_okA` is declarative and closed under subsumption.  This file factors
  the syntax-directed base type out of that relation.  The fuel argument is
  explicit only at nested `extern` wrappers, where the Core rule requires the
  wrapped address to inhabit non-null `ANY`; every positive subtype decision
  is proved sound before it is used.
-/
import WasmGemmGnaf.Wasm.Core.Runtime
import WasmGemmGnaf.Wasm.Core.SubtypeSound

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

private def nonnullAny : RefType := .ref none (.abs .any)

/-- The syntax-directed least type of an address reference, when its store
lookup and any enclosing `extern` check succeed. -/
def principalAddrRefTypeN (fuel : Nat) (s : Store) : AddrRef → Option RefType
  | .i31 _ => some (.ref none (.abs .i31))
  | .structAddr a =>
      (s.structs[a]?).map fun si => .ref none (.use (.defd si.type))
  | .arrayAddr a =>
      (s.arrays[a]?).map fun ai => .ref none (.use (.defd ai.type))
  | .funcAddr a =>
      (s.funcs[a]?).map fun fi => .ref none (.use (.defd fi.type))
  | .exnAddr a =>
      if s.exns[a]?.isSome then some (.ref none (.abs .exn)) else none
  | .hostAddr _ => some nonnullAny
  | .extern r => do
      let rt ← principalAddrRefTypeN fuel s r
      if decReftypeSubN Context.empty fuel rt nonnullAny then
        some (.ref none (.abs .extern))
      else none

/-- The executable principal runtime type.  Every null reference has the
amended global bottom as its nullable principal type. -/
def principalRefTypeN (fuel : Nat) (s : Store) : Ref → Option RefType
  | .null _ => some (.ref (some .null) (.abs .bot))
  | .addr r => principalAddrRefTypeN fuel s r

/-- Executable positive test used by the reference-sensitive read rules. -/
def refMatchesN (fuel : Nat) (s : Store) (r : Ref) (target : RefType) : Bool :=
  match principalRefTypeN fuel s r with
  | none => false
  | some principal => decReftypeSubN Context.empty fuel principal target

/-- Declarative reference subtyping composes when the intermediate type is
well formed; this is precisely the side condition of `Heaptype_subA/trans`. -/
theorem reftype_subA_trans {C : Context} {rt₁ rt₂ rt₃ : RefType}
    (hok : Reftype_okA C rt₂) (h₁₂ : Reftype_subA C rt₁ rt₂)
    (h₂₃ : Reftype_subA C rt₂ rt₃) : Reftype_subA C rt₁ rt₃ := by
  cases hok with
  | mk hheap =>
      cases h₁₂ with
      | nonnull h₁₂ =>
          cases h₂₃ with
          | nonnull h₂₃ => exact .nonnull (.trans hheap h₁₂ h₂₃)
          | null h₂₃ => exact .null (.trans hheap h₁₂ h₂₃)
      | null h₁₂ =>
          cases h₂₃ with
          | null h₂₃ => exact .null (.trans hheap h₁₂ h₂₃)

/-- Every answer returned for an address is a derivable amended-authority
runtime type. -/
theorem principalAddrRefTypeN_sound (fuel : Nat) (s : Store) (r : AddrRef)
    (rt : RefType) (h : principalAddrRefTypeN fuel s r = some rt) :
    Ref_okA s (.addr r) rt := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction r generalizing rt with
  | i31 i => simp [principalAddrRefTypeN] at h; subst rt; exact .i31
  | structAddr a =>
      cases hs : s.structs[a]? with
      | none => simp [principalAddrRefTypeN, hs] at h
      | some si =>
          simp [principalAddrRefTypeN, hs] at h
          subst rt
          exact .struct hs rfl
  | arrayAddr a =>
      cases hs : s.arrays[a]? with
      | none => simp [principalAddrRefTypeN, hs] at h
      | some ai =>
          simp [principalAddrRefTypeN, hs] at h
          subst rt
          exact .array hs rfl
  | funcAddr a =>
      cases hs : s.funcs[a]? with
      | none => simp [principalAddrRefTypeN, hs] at h
      | some fi =>
          simp [principalAddrRefTypeN, hs] at h
          subst rt
          exact .func hs rfl
  | exnAddr a =>
      cases hs : s.exns[a]? with
      | none => simp [principalAddrRefTypeN, hs] at h
      | some ex =>
          simp [principalAddrRefTypeN, hs] at h
          subst rt
          exact .exn hs
  | hostAddr a =>
      simp [principalAddrRefTypeN, nonnullAny] at h
      subst rt
      exact .host
  | extern r ih =>
      cases hp : principalAddrRefTypeN fuel s r with
      | none => simp [principalAddrRefTypeN, hp] at h
      | some principal =>
          cases hs : decReftypeSubN Context.empty fuel principal nonnullAny with
          | false => simp [principalAddrRefTypeN, hp, hs] at h
          | true =>
              simp [principalAddrRefTypeN, hp, hs] at h
              subst rt
              have hprincipal : Ref_okA s (.addr r) principal := ih principal hp
              have hany : Ref_okA s (.addr r) nonnullAny :=
                .sub hprincipal (decReftypeSubN_sound hs)
              exact .extern hany

/-- Every returned principal reference type is derivable in `Ref_okA`. -/
theorem principalRefTypeN_sound (fuel : Nat) (s : Store) (r : Ref)
    (rt : RefType) (h : principalRefTypeN fuel s r = some rt) :
    Ref_okA s r rt := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases r with
  | null ht =>
      simp [principalRefTypeN] at h
      subst rt
      exact .null Heaptype_subA.bot
  | addr a =>
      exact principalAddrRefTypeN_sound fuel s a rt h

/-- The runtime-typing invariant needed to compose subsumption chains.  It is
intended to be supplied by the typed-configuration/store judgment, not assumed
by the executable principal function. -/
def RefRuntimeTypesOkA (s : Store) (r : Ref) : Prop :=
  ∀ rt, Ref_okA s r rt → Reftype_okA Context.empty rt

/-- The store-wide form consumed by an executable whole-machine successor
enumerator.  It is a runtime typing invariant to be derived from validated
allocation and preserved by Core steps, not a premise attached to the raw
semantics. -/
def StoreRuntimeTypesOkA (s : Store) : Prop :=
  ∀ r, RefRuntimeTypesOkA s r

/-- Under the explicit runtime well-formedness invariant, every returned
principal is below every declarative runtime type of the same reference. -/
theorem principalRefTypeN_le_of_ok {fuel : Nat} {s : Store} {r : Ref}
    {principal target : RefType}
    (hp : principalRefTypeN fuel s r = some principal)
    (hok : RefRuntimeTypesOkA s r) (href : Ref_okA s r target) :
    Reftype_subA Context.empty principal target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction href generalizing principal with
  | null hs =>
      simp [principalRefTypeN] at hp
      subst principal
      exact .null .bot
  | i31 =>
      simp [principalRefTypeN, principalAddrRefTypeN] at hp
      subst principal
      exact .nonnull .refl
  | struct hs htype =>
      simp [principalRefTypeN, principalAddrRefTypeN, hs] at hp
      subst principal
      subst htype
      exact .nonnull .refl
  | array hs htype =>
      simp [principalRefTypeN, principalAddrRefTypeN, hs] at hp
      subst principal
      subst htype
      exact .nonnull .refl
  | func hs htype =>
      simp [principalRefTypeN, principalAddrRefTypeN, hs] at hp
      subst principal
      subst htype
      exact .nonnull .refl
  | exn hs =>
      simp [principalRefTypeN, principalAddrRefTypeN, hs] at hp
      subst principal
      exact .nonnull .refl
  | host =>
      simp [principalRefTypeN, principalAddrRefTypeN, nonnullAny] at hp
      subst principal
      exact .nonnull .refl
  | @extern underlying href ih =>
      cases hpa : principalAddrRefTypeN fuel s underlying with
      | none => simp [principalRefTypeN, principalAddrRefTypeN, hpa] at hp
      | some p =>
          cases hsub : decReftypeSubN Context.empty fuel p nonnullAny with
          | false =>
              simp [principalRefTypeN, principalAddrRefTypeN, hpa, hsub] at hp
          | true =>
              simp [principalRefTypeN, principalAddrRefTypeN, hpa, hsub] at hp
              subst principal
              exact .nonnull .refl
  | sub href hsub ih =>
      exact reftype_subA_trans (hok _ href) (ih hp hok) hsub

/-- Under exact heap-checker completeness and the store typing invariant,
every declaratively typable reference has a computable principal type.  The
only recursive case is `extern`; its required `ANY` check is discharged by
the same finite heap decision used by the successor enumerator. -/
theorem principalRefTypeN_exists_of_ref_ok
    {fuel : Nat} {s : Store} {r : Ref} {target : RefType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA Context.empty h₁ h₂ →
      decHeaptypeSubN Context.empty fuel h₁ h₂ = true)
    (hok : StoreRuntimeTypesOkA s) (href : Ref_okA s r target) :
    ∃ principal, principalRefTypeN fuel s r = some principal := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction href with
  | null hs => exact ⟨.ref (some .null) (.abs .bot), rfl⟩
  | i31 => exact ⟨.ref none (.abs .i31), rfl⟩
  | @struct a si dt hs htype =>
      exact ⟨.ref none (.use (.defd dt)), by
        simp [principalRefTypeN, principalAddrRefTypeN, hs, htype]⟩
  | @array a ai dt hs htype =>
      exact ⟨.ref none (.use (.defd dt)), by
        simp [principalRefTypeN, principalAddrRefTypeN, hs, htype]⟩
  | @func a fi dt hs htype =>
      exact ⟨.ref none (.use (.defd dt)), by
        simp [principalRefTypeN, principalAddrRefTypeN, hs, htype]⟩
  | exn hs =>
      exact ⟨.ref none (.abs .exn), by
        simp [principalRefTypeN, principalAddrRefTypeN, hs]⟩
  | host => exact ⟨nonnullAny, rfl⟩
  | @extern underlying href ih =>
      obtain ⟨principal, hp⟩ := ih
      have hle : Reftype_subA Context.empty principal nonnullAny :=
        principalRefTypeN_le_of_ok hp (hok (.addr underlying)) href
      have hdec : decReftypeSubN Context.empty fuel principal nonnullAny = true :=
        decReftypeSubN_complete_of_heap hheap hle
      change principalAddrRefTypeN fuel s underlying = some principal at hp
      exact ⟨.ref none (.abs .extern), by
        simp [principalRefTypeN, principalAddrRefTypeN, hp, hdec]⟩
  | sub href hsub ih => exact ih

/-- Exact executable/declarative runtime reference matching on a typed store.
The malformed-store counterexample below remains unchanged: neither the heap
decision theorem nor `StoreRuntimeTypesOkA` holds for that raw witness. -/
theorem refMatchesN_complete_of_heap
    {fuel : Nat} {s : Store} {r : Ref} {target : RefType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA Context.empty h₁ h₂ →
      decHeaptypeSubN Context.empty fuel h₁ h₂ = true)
    (hok : StoreRuntimeTypesOkA s)
    (href : ∃ rt, Ref_okA s r rt ∧
      Reftype_subA Context.empty rt target) :
    refMatchesN fuel s r target = true := by
  obtain ⟨rt, hr, hsub⟩ := href
  obtain ⟨principal, hp⟩ :=
    principalRefTypeN_exists_of_ref_ok hheap hok hr
  have hprincipal : Reftype_subA Context.empty principal rt :=
    principalRefTypeN_le_of_ok hp (hok r) hr
  have hcomposed : Reftype_subA Context.empty principal target :=
    reftype_subA_trans ((hok r) rt hr) hprincipal hsub
  simp [refMatchesN, hp,
    decReftypeSubN_complete_of_heap hheap hcomposed]

/-- A positive executable match always supplies exactly the two declarative
premises used by `br_on_cast`, `ref.test`, and `ref.cast`. -/
theorem refMatchesN_sound {fuel : Nat} {s : Store} {r : Ref} {target : RefType}
    (h : refMatchesN fuel s r target = true) :
    ∃ rt, Ref_okA s r rt ∧ Reftype_subA Context.empty rt target := by
  unfold refMatchesN at h
  cases hp : principalRefTypeN fuel s r with
  | none => simp [hp] at h
  | some principal =>
      refine ⟨principal, principalRefTypeN_sound fuel s r principal hp, ?_⟩
      exact decReftypeSubN_sound (by simpa [hp] using h)

/-- The typed-store matcher is exactly the existential premise appearing in
the cast/test read rules. -/
theorem refMatchesN_iff_of_heap
    {fuel : Nat} {s : Store} {r : Ref} {target : RefType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA Context.empty h₁ h₂ →
      decHeaptypeSubN Context.empty fuel h₁ h₂ = true)
    (hok : StoreRuntimeTypesOkA s) :
    refMatchesN fuel s r target = true ↔
      ∃ rt, Ref_okA s r rt ∧ Reftype_subA Context.empty rt target :=
  ⟨refMatchesN_sound, refMatchesN_complete_of_heap hheap hok⟩

/-- Closed non-vacuity: null principals compute without inspecting the store. -/
example (s : Store) (ht : HeapType) :
    principalRefTypeN 0 s (.null ht) =
      some (.ref (some .null) (.abs .bot)) := rfl

/-- Closed non-vacuity: the immediate address family is recognized. -/
example (s : Store) (i : U31) :
    principalRefTypeN 0 s (.addr (.i31 i)) =
      some (.ref none (.abs .i31)) := rfl

/-- Null matching is fully executable and independent of its annotation: the
amended principal `REF NULL BOT` inhabits exactly nullable targets. -/
theorem refMatchesN_null (fuel : Nat) (s : Store) (ht target : HeapType)
    (nul : Option Null) :
    refMatchesN fuel s (.null ht) (.ref nul target) = nul.isSome := by
  cases nul with
  | none => rfl
  | some n =>
      cases target with
      | abs a => cases a <;> rfl
      | use tu =>
          cases tu <;>
            simp [refMatchesN, principalRefTypeN, decReftypeSubN,
              decHeaptypeSubN, decHeapSubR, Context.resolveIdx, Context.empty]

/-- Runtime subsumption never changes a null reference into a non-null
runtime type. -/
theorem ref_okA_null_nullable {s : Store} {ht : HeapType} {rt : RefType}
    (h : Ref_okA s (.null ht) rt) :
    ∃ target, rt = .ref (some .null) target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  have aux : ∀ {s : Store} {r : Ref} {rt : RefType}, Ref_ok s r rt →
      ∀ ht, r = .null ht → ∃ target, rt = .ref (some .null) target := by
    intro s r rt href
    induction href with
    | null hs => intro _ _; exact ⟨_, rfl⟩
    | i31 => intro _ heq; cases heq
    | struct hs hdt => intro _ heq; cases heq
    | array hs hdt => intro _ heq; cases heq
    | func hs hdt => intro _ heq; cases heq
    | exn hs => intro _ heq; cases heq
    | host => intro _ heq; cases heq
    | extern href ih => intro _ heq; cases heq
    | sub href hs ih =>
        intro source heq
        obtain ⟨target, htarget⟩ := ih source heq
        rw [htarget] at hs
        cases hs with
        | null hheap => exact ⟨_, rfl⟩
  exact aux h ht rfl

/-- For a null reference the executable test is also complete against the
declarative existential used by the read rules. -/
theorem refMatchesN_null_iff (fuel : Nat) (s : Store) (ht target : HeapType)
    (nul : Option Null) :
    refMatchesN fuel s (.null ht) (.ref nul target) = true ↔
      ∃ rt, Ref_okA s (.null ht) rt ∧
        Reftype_subA Context.empty rt (.ref nul target) := by
  constructor
  · exact refMatchesN_sound
  · rintro ⟨rt, href, hsub⟩
    obtain ⟨source, rfl⟩ := ref_okA_null_nullable href
    cases hsub with
    | null hheap =>
        simp [refMatchesN_null]

/-! ## Why the typed-store invariant is necessary

Raw `Store` permits a structurally malformed defined type to declare an
incompatible supertype.  `Ref_okA/sub` can traverse that edge one step at a
time, while the sound executable heap checker correctly refuses to invent the
missing composite-family compatibility.  The closed witness below prevents an
unconditional completeness theorem from being attached to `refMatchesN`; the
eventual public successor theorem must consume the validated-store invariant.
-/

private def counterTypeIdx : TypeIdx := ⟨0, by decide⟩

private def counterField : FieldType :=
  .mk none (.val (.ref (.ref none (.use (.idx counterTypeIdx)))))

private def counterStruct : DefType :=
  .defd (.recr (.cons
    (.sub none .nil (.struct (.cons counterField .nil))) .nil)) 0

private def counterFunc : DefType :=
  .defd (.recr (.cons
    (.sub none (.cons (.defd counterStruct) .nil) (.func .nil .nil)) .nil)) 0

private def counterStore : Store :=
  { structs := [{ type := counterFunc, fields := [] }] }

private theorem counterFunc_shape : counterFunc.absShape = some .func := by decide

private theorem counter_ref_func :
    Ref_okA counterStore (.addr (.structAddr 0))
      (.ref none (.use (.defd counterFunc))) := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  exact .struct rfl rfl

private theorem counter_func_sub_struct :
    Reftype_subA Context.empty (.ref none (.use (.defd counterFunc)))
      (.ref none (.use (.defd counterStruct))) := by
  apply Reftype_subA.nonnull
  apply Heaptype_subA.def_
  exact Deftype_subA.super
    (fin := none) (sups := .cons (.defd counterStruct) .nil)
    (ct := .func .nil .nil) (i := 0) (tu := .defd counterStruct)
    (by decide) rfl .refl

private theorem counter_ref_struct :
    Ref_okA counterStore (.addr (.structAddr 0))
      (.ref none (.use (.defd counterStruct))) := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  exact .sub counter_ref_func counter_func_sub_struct

private theorem counter_struct_sub_abstract :
    Reftype_subA Context.empty (.ref none (.use (.defd counterStruct)))
      (.ref none (.abs .struct)) := by
  apply Reftype_subA.nonnull
  exact Heaptype_subA.struct
    (fts := .cons counterField .nil) (Expand.mk (by decide))

/-- There is no unconditional raw-store completeness law for the sound
fuel-indexed matcher.  The witness has a declarative match at every fuel while
the executable checker rejects its incompatible source composite family. -/
theorem refMatchesN_not_complete_on_raw (fuel : Nat) :
    ∃ (s : Store) (r : Ref) (target : RefType),
      refMatchesN fuel s r target = false ∧
      ∃ rt, Ref_okA s r rt ∧ Reftype_subA Context.empty rt target := by
  refine ⟨counterStore, .addr (.structAddr 0), .ref none (.abs .struct), ?_,
    _, counter_ref_struct, counter_struct_sub_abstract⟩
  simp [refMatchesN, principalRefTypeN, principalAddrRefTypeN, counterStore,
    decReftypeSubN, decHeaptypeSubN, decHeapSubR, Context.resolveIdx,
    Context.typeuseShapeA, counterFunc_shape, decAbsSub]

end WasmGemmGnaf.Wasm.Core.Exec
