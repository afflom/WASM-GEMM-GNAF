/-
  Wasm/Core/Subtype.lean --- an EXECUTABLE decision procedure for the amended
  WebAssembly Core 3.0 subtype relations, together with soundness proofs.

  NORMATIVE SOURCE.  The relations decided here are the ones transcribed in
  `Wasm/Core/Validation/Types.lean` from

      vendor/wasm-spec/specification/wasm-3.0/2.1-validation.types.spectec
      vendor/wasm-spec/specification/wasm-3.0/2.2-validation.subtyping.spectec

  at the pinned commit, plus the explicit coverage-neutral bottom-rule repair
  in `Validation/SubtypingAmended.lean`.  The pinned transcription does not
  import this file, so the declarative side is not defined through the
  executable side (SPEC 4, `xtask independence`).

  ---------------------------------------------------------------------------
  WHAT IS HARD ABOUT THIS, AND HOW IT IS ANSWERED

  `Heaptype_sub` is NOT syntax-directed.  It carries `refl` and `trans`, and
  `trans` quantifies over an arbitrary intermediate heap type, so reading the
  rules backwards neither terminates nor is well defined.  Four facts make the
  relation decidable anyway.

  (1) THE ABSTRACT HIERARCHY IS A FINITE LATTICE.  `absheaptype` has thirteen
      cases and the rules relating them (`eq-any`, `i31-eq`, `struct-eq`,
      `array-eq`, `none`, `nofunc`, `noexn`, `noextern`, `bot`) are closed;
      `decAbsSub` is that lattice's reflexive-transitive closure, written out.

  (2) SUBTYPING BETWEEN TYPE USES IS REACHABILITY THROUGH THE *DECLARED*
      SUPERTYPE LISTS.  Core 3.0 is ISO-recursive with explicitly declared
      supertypes (`subtype = SUB final? typeuse* comptype`), so "is deftype_1
      below deftype_2" is "does the declared-supertype walk out of deftype_1
      reach a node equal to deftype_2 modulo `$clos_deftype`".  `reachDef` is
      that walk.

  (3) `Deftype_sub/super` IS ALREADY TRANSITIVE.  Its premise is
      `Heaptype_sub: C |- typeuse*[i] <: deftype_2`, i.e. the declared
      supertype has to REACH deftype_2, not merely equal it.  So the whole
      typeuse-to-deftype walk is built by NESTING `Deftype_sub/super` and
      `Heaptype_sub/typeidx-l`, with NO use of `Heaptype_sub/trans` at all.
      That is what makes soundness unconditional: the one rule whose premise
      would otherwise carry a `Heaptype_ok` obligation is never used.

  (4) THE FOUR FAMILY BOTTOMS DO NOT COLLAPSE THROUGH `BOT`.  The amended
      relation restores the omitted `heaptype != BOT` side condition on the
      `NONE`, `NOFUNC`, `NOEXN`, and `NOEXTERN` rules.  The executable finite
      lattice below follows that repaired hierarchy.

  ---------------------------------------------------------------------------
  THE PINNED DEFECT IS NOT EXECUTABLE SEMANTICS.  The unedited authority
  transcription still records the missing premises.  The amended overlay
  repeats the mutually recursive heap/deftype relation with exactly those four
  premises restored and proves erasure back to the pin.  No declaration in
  this file asserts the collapsed `NONE <: BOT` or `NONE <: FUNC` behaviour.

  ---------------------------------------------------------------------------
  WHAT IS PROVED HERE AND WHAT IS PROVED NEXT DOOR

  SOUNDNESS (`dec ... = true -> relation`) is proved HERE and is
  UNCONDITIONAL at every level and for every fuel: no hypothesis on the
  context, none on the types.

  `Wasm/Core/SubtypeSound.lean` proves the finite-lattice laws and the
  load-bearing negative theorem that an amended derivation ending at `BOT`
  starts at `BOT`.  It intentionally contains no `HeapComplete` hypothesis:
  full completeness must instead be derived from the well-formed type-section
  certificate that the module validator constructs.  That context-sensitive
  step, and the checker branches which consume it, remain to be implemented.

  FUEL.  `decHeaptypeSubN` takes the walk depth as an argument.  It has to: a
  `deftype` may declare a supertype written out as a literal `deftype` rather
  than as a type index (`typeuse/sem` admits `deftype`), and `$unrolldt` can
  then produce a CYCLIC supertype graph --- `_DEF (REC [SUB (REC 0) ct]) 0`
  declares itself as its own supertype.  The relation is inductive, so a cycle
  derives nothing, but no syntactic measure of the arguments alone bounds the
  walk.  `decHeaptypeSub` fixes the fuel at
  `2 * |C.TYPES| + |C.RECS| + 1`: source validation makes each declared
  supertype index earlier, while a walk alternates through that index and its
  stored defined type.  The fuel-indexed form remains the general API used by
  the correctness theorems.
-/
import WasmGemmGnaf.Wasm.Core.Validation.SubtypingAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## The abstract heap-type lattice -/

/-- The unique semantic bottom heap type.  The four family bottoms are not
global bottoms in the amended hierarchy. -/
def AbsHeapType.isBot : AbsHeapType → Bool
  | .bot => true
  | _ => false

/-- `C |- absheaptype_1 <: absheaptype_2`, decided.

`BOT` is universal.  `NONE` bottoms out the internal hierarchy,
`NOFUNC` the function hierarchy, `NOEXN` the exception hierarchy, and
`NOEXTERN` the external hierarchy. -/
def decAbsSub : AbsHeapType → AbsHeapType → Bool
  | .bot, _ => true
  | .none, .none => true
  | .none, .i31 => true
  | .none, .struct => true
  | .none, .array => true
  | .none, .eq => true
  | .none, .any => true
  | .nofunc, .nofunc => true
  | .nofunc, .func => true
  | .noexn, .noexn => true
  | .noexn, .exn => true
  | .noextern, .noextern => true
  | .noextern, .extern => true
  | .any, .any => true
  | .eq, .any => true
  | .eq, .eq => true
  | .i31, .any => true
  | .i31, .eq => true
  | .i31, .i31 => true
  | .struct, .any => true
  | .struct, .eq => true
  | .struct, .struct => true
  | .array, .any => true
  | .array, .eq => true
  | .array, .array => true
  | .func, .func => true
  | .exn, .exn => true
  | .extern, .extern => true
  | _, _ => false

/-! ## Expansion shapes

`Heaptype_sub/struct`, `/array` and `/func` are the only rules with a `typeuse`
on the left and an abstract heap type on the right, and each fires exactly when
`$expanddt` produces a composite type of the matching shape. -/

/-- The abstract heap type a composite type inhabits: the right-hand sides of
`Heaptype_sub/struct`, `/array` and `/func`. -/
def CompType.absShape : CompType → AbsHeapType
  | .struct _ => .struct
  | .array _ => .array
  | .func _ _ => .func

/-- `$expanddt(deftype)` read as the abstract heap type the `deftype` is below;
`none` where `$expanddt` has no equation. -/
def DefType.absShape (dt : DefType) : Option AbsHeapType :=
  match expandDt dt with
  | some ct => some ct.absShape
  | none => none

namespace Context

/-- `DefType.absShape` through a `typeuse`.  `_IDX x` is resolved by
`Heaptype_sub/typeidx-l`, a DIRECT rule; `REC i` has no expansion, because
`$expanddt` is defined on `deftype` only. -/
def typeuseShape (C : Context) : TypeUse → Option AbsHeapType
  | .defd dt => dt.absShape
  | .idx x => match C.types[x.val]? with
      | some dt => dt.absShape
      | none => none
  | .recu _ => none

/-! ## Node equality and the declared-supertype walk -/

/-- The normal form `Deftype_sub/refl` compares: a `deftype` modulo
`$clos_deftype(C, -)`, everything else itself. -/
def normHeapType (C : Context) : HeapType -> HeapType
  | .abs a => .abs a
  | .use (.idx x) => .use (.idx x)
  | .use (.recu i) => .use (.recu i)
  | .use (.defd dt) => .use (.defd (C.closDefType dt))

/-- `Deftype_sub/refl` as a test on heap types, extended to the rest of the
sort by syntactic equality, which is `Heaptype_sub/refl`. -/
def heapEq (C : Context) (h₁ h₂ : HeapType) : Bool :=
  decide (C.normHeapType h₁ = C.normHeapType h₂)

/-- The DECLARED supertypes of a heap type, one step.

* `_IDX x` steps to `C.TYPES[x]` --- `Heaptype_sub/typeidx-l`;
* a `deftype` steps to each `typeuse` of `$unrolldt(deftype)` ---
  `Deftype_sub/super`;
* everything else has none.  `REC i` is DELIBERATELY inert: `Heaptype_sub/rec`
  reaches the listed supertype and no further, and continuing past it needs
  `Heaptype_sub/trans`, whose `Heaptype_ok` premise is not free when that
  supertype is a literal `deftype`.  Omitting the edge costs nothing in any
  context with `C.RECS = eps`, which is every context outside
  `Rectype_ok/_rec2`. -/
def heapSupers (C : Context) : HeapType -> List HeapType
  | .abs _ => []
  | .use (.recu _) => []
  | .use (.idx x) => match C.types[x.val]? with
      | some dt => [.use (.defd dt)]
      | none => []
  | .use (.defd dt) => match unrollDt dt with
      | some (.sub _ sups _) => (TypeUses.toList sups).map HeapType.use
      | none => []

/-- The declared-supertype walk, `n` steps deep, looking for a node equal to
`h₂` in the sense of `heapEq`. -/
def reachDef (C : Context) : Nat -> HeapType -> HeapType -> Bool
  | 0, h₁, h₂ => C.heapEq h₁ h₂
  | n + 1, h₁, h₂ =>
      C.heapEq h₁ h₂ || (C.heapSupers h₁).any (fun h => C.reachDef n h h₂)

/-- `Heaptype_sub/typeidx-r` read as a normalisation of the RIGHT-hand side: a
type index in range is interchangeable with the `deftype` it names, because
`typeidx-l` and `typeidx-r` applied to `refl` give both directions. -/
def resolveIdx (C : Context) : HeapType -> HeapType
  | .abs a => .abs a
  | .use (.recu i) => .use (.recu i)
  | .use (.defd dt) => .use (.defd dt)
  | .use (.idx x) => match C.types[x.val]? with
      | some dt => .use (.defd dt)
      | none => .use (.idx x)

/-! ## Context irrelevance for executable subtyping

The subtype walk observes only `TYPES`; `RECS` contributes only to the chosen
fuel bound.  Validation changes locals and labels between adjacent
instructions, so the executable checker needs this fact extensionally rather
than by record equality. -/

theorem typeuseShape_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (tu : TypeUse) : C.typeuseShape tu = D.typeuseShape tu := by
  cases tu <;> simp [Context.typeuseShape, h]

theorem normHeapType_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (ht : HeapType) : C.normHeapType ht = D.normHeapType ht := by
  cases ht with
  | abs a => rfl
  | use tu =>
      cases tu <;>
        simp [Context.normHeapType, Context.closDefType, Context.closTypes, h]

theorem heapEq_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (ht₁ ht₂ : HeapType) : C.heapEq ht₁ ht₂ = D.heapEq ht₁ ht₂ := by
  simp only [Context.heapEq, normHeapType_eq_of_types_eq h]

theorem heapSupers_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (ht : HeapType) : C.heapSupers ht = D.heapSupers ht := by
  cases ht with
  | abs a => rfl
  | use tu => cases tu <;> simp [Context.heapSupers, h]

theorem reachDef_eq_of_types_eq {C D : Context} (h : C.types = D.types) :
    ∀ (n : Nat) (ht₁ ht₂ : HeapType), C.reachDef n ht₁ ht₂ = D.reachDef n ht₁ ht₂ := by
  intro n
  induction n with
  | zero =>
      intro ht₁ ht₂
      simpa only [Context.reachDef] using heapEq_eq_of_types_eq h ht₁ ht₂
  | succ n ih =>
      intro ht₁ ht₂
      rw [Context.reachDef, Context.reachDef,
        heapEq_eq_of_types_eq h, heapSupers_eq_of_types_eq h]
      have hf : (fun g => C.reachDef n g ht₂) =
          (fun g => D.reachDef n g ht₂) := by
        funext g
        exact ih g ht₂
      rw [hf]

theorem resolveIdx_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (ht : HeapType) : C.resolveIdx ht = D.resolveIdx ht := by
  cases ht with
  | abs a => rfl
  | use tu => cases tu <;> simp [Context.resolveIdx, h]

end Context

/-! ## The decision procedure -/

/-- `C |- heaptype_1 <: heaptype_2` with the right-hand side already resolved
by `Context.resolveIdx`.  Five shapes:

* abstract vs abstract: the finite lattice;
* abstract vs `typeuse`: only a bottom heap type is below a type use;
* `typeuse` vs abstract: `Heaptype_sub/struct`, `/array`, `/func` followed by
  the lattice, and NOTHING else --- a longer chain would need
  `Heaptype_sub/trans` through a `deftype`, whose `Heaptype_ok` premise is a
  `Deftype_ok` obligation this procedure does not discharge;
* `typeuse` vs `deftype`: the declared-supertype walk;
* `typeuse` vs `REC i`, or vs an out-of-range `_IDX x`: those nodes are
  isolated, so equality. -/
def decHeapSubR (C : Context) (n : Nat) : HeapType -> HeapType -> Bool
  | .abs a, .abs b => decAbsSub a b
  | .abs .bot, .use _ => true
  | .abs .none, .use tu =>
      match C.typeuseShape tu with
      | some .struct => true
      | some .array => true
      | _ => false
  | .abs .nofunc, .use tu => decide (C.typeuseShape tu = some .func)
  | .abs _, .use _ => false
  | .use tu₁, .abs b =>
      match C.typeuseShape tu₁ with
      | some s => decAbsSub s b
      | none => false
  | .use tu₁, .use (.defd d₂) => C.reachDef n (.use tu₁) (.use (.defd d₂))
  | .use tu₁, .use (.idx x) => C.heapEq (.use tu₁) (.use (.idx x))
  | .use tu₁, .use (.recu i) => C.heapEq (.use tu₁) (.use (.recu i))

/-- **`relation Heaptype_sub: context |- heaptype <: heaptype`, decided**, the
declared-supertype walk bounded by `n`. -/
def decHeaptypeSubN (C : Context) (n : Nat) (h₁ h₂ : HeapType) : Bool :=
  decHeapSubR C n h₁ (C.resolveIdx h₂)

/-- The walk bound `decHeaptypeSub` uses.  In a source validation context a
declared-super chain alternates between the syntax node `_IDX i` and the
`deftype` stored at that index before taking the strictly decreasing declared
super edge.  Thus each member of `C.TYPES` costs at most two walk steps.  The
`RECS` allowance is retained for recursive-group checking, and the final unit
covers the equality base case. -/
def Context.subtypeFuel (C : Context) : Nat :=
  2 * C.types.length + C.recs.length + 1

/-- **`relation Heaptype_sub`, decided** at the context's own walk bound. -/
def decHeaptypeSub (C : Context) (h₁ h₂ : HeapType) : Bool :=
  decHeaptypeSubN C C.subtypeFuel h₁ h₂

/-- **`relation Deftype_sub: context |- deftype <: deftype`, decided.**  The
declared-supertype walk itself: `Deftype_sub/refl` is the `heapEq` base case,
`Deftype_sub/super` the step. -/
def decDeftypeSubN (C : Context) (n : Nat) (d₁ d₂ : DefType) : Bool :=
  C.reachDef n (.use (.defd d₁)) (.use (.defd d₂))

/-- **`relation Deftype_sub`, decided** at the context's own walk bound. -/
def decDeftypeSub (C : Context) (d₁ d₂ : DefType) : Bool :=
  decDeftypeSubN C C.subtypeFuel d₁ d₂

/-- **`relation Numtype_sub`, decided.**  The rule has the SAME `numtype` on
both sides, so this is equality. -/
def decNumtypeSub (nt₁ nt₂ : NumType) : Bool := decide (nt₁ = nt₂)

/-- **`relation Vectype_sub`, decided.** -/
def decVectypeSub (vt₁ vt₂ : VecType) : Bool := decide (vt₁ = vt₂)

/-- **`relation Packtype_sub`, decided.** -/
def decPacktypeSub (pt₁ pt₂ : PackType) : Bool := decide (pt₁ = pt₂)

/-- **`relation Reftype_sub: context |- reftype <: reftype`, decided.**

`Reftype_sub/nonnull` relates `REF ht_1 <: REF ht_2`, `Reftype_sub/null`
relates `REF NULL? ht_1 <: REF NULL ht_2`; between them the admissible
nullability pairs are exactly "the target is nullable, or the source is
not". -/
def decReftypeSubN (C : Context) (n : Nat) : RefType -> RefType -> Bool
  | .ref nul₁ ht₁, .ref nul₂ ht₂ =>
      (nul₂.isSome || !nul₁.isSome) && decHeaptypeSubN C n ht₁ ht₂

/-- **`relation Valtype_sub: context |- valtype <: valtype`, decided.** -/
def decValtypeSubN (C : Context) (n : Nat) : ValType -> ValType -> Bool
  | .bot, _ => true
  | .num nt₁, .num nt₂ => decNumtypeSub nt₁ nt₂
  | .vec vt₁, .vec vt₂ => decVectypeSub vt₁ vt₂
  | .ref rt₁, .ref rt₂ => decReftypeSubN C n rt₁ rt₂
  | _, _ => false

/-- **`relation Storagetype_sub`, decided.** -/
def decStoragetypeSubN (C : Context) (n : Nat) : StorageType -> StorageType -> Bool
  | .val t₁, .val t₂ => decValtypeSubN C n t₁ t₂
  | .pack pt₁, .pack pt₂ => decPacktypeSub pt₁ pt₂
  | _, _ => false

/-- **`relation Fieldtype_sub`, decided.**  `Fieldtype_sub/const` is
covariant, `Fieldtype_sub/var` invariant, and the pinned rules relate a
mutable field to an immutable one in NEITHER direction. -/
def decFieldtypeSubN (C : Context) (n : Nat) : FieldType -> FieldType -> Bool
  | .mk none zt₁, .mk none zt₂ => decStoragetypeSubN C n zt₁ zt₂
  | .mk (some .mut) zt₁, .mk (some .mut) zt₂ =>
      decStoragetypeSubN C n zt₁ zt₂ && decStoragetypeSubN C n zt₂ zt₁
  | _, _ => false

/-- `(R(x, y))*` decided pointwise on two sequences, including the length
agreement SpecTec's `(...)*` implies. -/
def decSeq₂ {α β : Type} (f : α -> β -> Bool) : List α -> List β -> Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && decSeq₂ f as bs
  | _, _ => false

/-- **`relation Resulttype_sub`, decided.** -/
def decResulttypeSubN (C : Context) (n : Nat) (ts₁ ts₂ : List ValType) : Bool :=
  decSeq₂ (decValtypeSubN C n) ts₁ ts₂

/-! The executable relation is invariant under validation-context components
other than `TYPES` when the fuel is held fixed.  The context's `RECS` length
is accounted for separately when choosing that fuel. -/

theorem decHeapSubR_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (n : Nat) (ht₁ ht₂ : HeapType) :
    decHeapSubR C n ht₁ ht₂ = decHeapSubR D n ht₁ ht₂ := by
  cases ht₁ with
  | abs a =>
      cases ht₂ with
      | abs b => rfl
      | use tu =>
          cases a <;>
            simp [decHeapSubR, Context.typeuseShape_eq_of_types_eq h]
  | use tu₁ =>
      cases ht₂ with
      | abs b =>
          simp [decHeapSubR, Context.typeuseShape_eq_of_types_eq h]
      | use tu₂ =>
          cases tu₂ <;>
            simp [decHeapSubR, Context.heapEq_eq_of_types_eq h,
              Context.reachDef_eq_of_types_eq h]

theorem decHeaptypeSubN_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (n : Nat) (ht₁ ht₂ : HeapType) :
    decHeaptypeSubN C n ht₁ ht₂ = decHeaptypeSubN D n ht₁ ht₂ := by
  unfold decHeaptypeSubN
  rw [Context.resolveIdx_eq_of_types_eq h]
  exact decHeapSubR_eq_of_types_eq h n ht₁ (D.resolveIdx ht₂)

theorem decReftypeSubN_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (n : Nat) (rt₁ rt₂ : RefType) :
    decReftypeSubN C n rt₁ rt₂ = decReftypeSubN D n rt₁ rt₂ := by
  cases rt₁
  cases rt₂
  simp [decReftypeSubN, decHeaptypeSubN_eq_of_types_eq h]

theorem decValtypeSubN_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (n : Nat) (t₁ t₂ : ValType) :
    decValtypeSubN C n t₁ t₂ = decValtypeSubN D n t₁ t₂ := by
  cases t₁ <;> cases t₂ <;>
    simp [decValtypeSubN, decReftypeSubN_eq_of_types_eq h]

theorem decResulttypeSubN_eq_of_types_eq {C D : Context} (h : C.types = D.types)
    (n : Nat) (ts₁ ts₂ : List ValType) :
    decResulttypeSubN C n ts₁ ts₂ = decResulttypeSubN D n ts₁ ts₂ := by
  unfold decResulttypeSubN
  apply congrArg (fun f => decSeq₂ f ts₁ ts₂)
  funext t₁ t₂
  exact decValtypeSubN_eq_of_types_eq h n t₁ t₂

/-- **`relation Comptype_sub`, decided.**

`Comptype_sub/struct` is WIDTH subtyping --- `STRUCT (ft_1* ft'_1*) <: STRUCT
ft_2*` with the extra fields `ft'_1*` unconstrained --- so the test is that the
target has no more fields than the source and that the source's PREFIX of that
length is pointwise below it. -/
def decComptypeSubN (C : Context) (n : Nat) : CompType -> CompType -> Bool
  | .struct fts₁, .struct fts₂ =>
      decide ((FieldTypes.toList fts₂).length ≤ (FieldTypes.toList fts₁).length) &&
        decSeq₂ (decFieldtypeSubN C n)
          ((FieldTypes.toList fts₁).take (FieldTypes.toList fts₂).length)
          (FieldTypes.toList fts₂)
  | .array ft₁, .array ft₂ => decFieldtypeSubN C n ft₁ ft₂
  | .func dom₁ cod₁, .func dom₂ cod₂ =>
      decResulttypeSubN C n (ValTypes.toList dom₂) (ValTypes.toList dom₁) &&
        decResulttypeSubN C n (ValTypes.toList cod₁) (ValTypes.toList cod₂)
  | _, _ => false

/-- **`relation Instrtype_sub`, decided.** -/
def decInstrtypeSubN (C : Context) (n : Nat) (it₁ it₂ : InstrType) : Bool :=
  decResulttypeSubN C n it₂.dom it₁.dom &&
    decResulttypeSubN C n it₁.cod it₂.cod &&
    (setminus it₂.locals it₁.locals).all (fun x =>
      match C.locals[x.val]? with
      | some lct => decide (lct.init = Init.set)
      | none => false)

/-- **`relation Limits_sub`, decided.**  The pinned rule matches BOTH maxima
without a `?`, so it relates only limits that both carry a maximum; the
transcription in `Validation/Types.lean` says so and this test agrees. -/
def decLimitsSub : Limits -> Limits -> Bool
  | ⟨n₁, some m₁⟩, ⟨n₂, some m₂⟩ => decide (n₂.val ≤ n₁.val) && decide (m₁.val ≤ m₂.val)
  | _, _ => false

/-- **`relation Tagtype_sub`, decided.**  The rule matches both sides as
`deftype`s, so a tag type written as a type index or a `REC` variable is
related to nothing. -/
def decTagtypeSubN (C : Context) (n : Nat) : TagType -> TagType -> Bool
  | .defd d₁, .defd d₂ => decDeftypeSubN C n d₁ d₂ && decDeftypeSubN C n d₂ d₁
  | _, _ => false

/-- **`relation Globaltype_sub`, decided.** -/
def decGlobaltypeSubN (C : Context) (n : Nat) (gt₁ gt₂ : GlobalType) : Bool :=
  match gt₁.mutability, gt₂.mutability with
  | none, none => decValtypeSubN C n gt₁.valtype gt₂.valtype
  | some .mut, some .mut =>
      decValtypeSubN C n gt₁.valtype gt₂.valtype &&
        decValtypeSubN C n gt₂.valtype gt₁.valtype
  | _, _ => false

/-- **`relation Memtype_sub`, decided.**  The rule writes the SAME `addrtype`
on both sides. -/
def decMemtypeSub (mt₁ mt₂ : MemType) : Bool :=
  decide (mt₁.addr = mt₂.addr) && decLimitsSub mt₁.lim mt₂.lim

/-- **`relation Tabletype_sub`, decided.**  The element type is INVARIANT. -/
def decTabletypeSubN (C : Context) (n : Nat) (tt₁ tt₂ : TableType) : Bool :=
  decide (tt₁.addr = tt₂.addr) && decLimitsSub tt₁.lim tt₂.lim &&
    decReftypeSubN C n tt₁.elem tt₂.elem && decReftypeSubN C n tt₂.elem tt₁.elem

/-- **`relation Externtype_sub`, decided.**  `Externtype_sub/func` matches
both payloads as `deftype`s. -/
def decExterntypeSubN (C : Context) (n : Nat) : ExternType -> ExternType -> Bool
  | .tag jt₁, .tag jt₂ => decTagtypeSubN C n jt₁ jt₂
  | .global gt₁, .global gt₂ => decGlobaltypeSubN C n gt₁ gt₂
  | .mem mt₁, .mem mt₂ => decMemtypeSub mt₁ mt₂
  | .table tt₁, .table tt₂ => decTabletypeSubN C n tt₁ tt₂
  | .func (.defd d₁), .func (.defd d₂) => decDeftypeSubN C n d₁ d₂
  | _, _ => false


/-! ## The repaired bottom -/

namespace Heaptype_subA

/-- `BOT`, and only `BOT`, is unconditionally below every heap type. -/
theorem abs_isBot_universal {C : Context} {a : AbsHeapType} (ha : a.isBot = true)
    {ht : HeapType} : Heaptype_subA C (.abs a) ht := by
  cases a
  case bot => exact .bot
  all_goals exact absurd ha (by decide)

end Heaptype_subA

/-! ## Soundness

Every theorem in this section is UNCONDITIONAL: no well-formedness hypothesis
on the context, none on the types, and none on the fuel. -/

/-- `decAbsSub` is sound: it answers `true` only on pairs the abstract rules
derive.  The thirteen-by-thirteen case split is the proof that `decAbsSub` is
the reflexive-transitive closure and not something larger. -/
theorem decAbsSub_soundA {C : Context} {a b : AbsHeapType} (h : decAbsSub a b = true) :
    Heaptype_subA C (.abs a) (.abs b) := by
  cases a <;> cases b <;>
    first
      | exact Heaptype_subA.abs_isBot_universal (by decide)
      | exact Heaptype_subA.refl
      | exact Heaptype_subA.eq_any
      | exact Heaptype_subA.i31_eq
      | exact Heaptype_subA.struct_eq
      | exact Heaptype_subA.array_eq
      | exact Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.i31_eq Heaptype_subA.eq_any
      | exact Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.struct_eq Heaptype_subA.eq_any
      | exact Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.array_eq Heaptype_subA.eq_any
      | exact Heaptype_subA.none_ (by decide) Heaptype_subA.refl
      | exact Heaptype_subA.none_ (by decide)
          (Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.i31_eq Heaptype_subA.eq_any)
      | exact Heaptype_subA.none_ (by decide)
          (Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.struct_eq Heaptype_subA.eq_any)
      | exact Heaptype_subA.none_ (by decide)
          (Heaptype_subA.trans Heaptype_okA.abs Heaptype_subA.array_eq Heaptype_subA.eq_any)
      | exact Heaptype_subA.none_ (by decide) Heaptype_subA.eq_any
      | exact Heaptype_subA.nofunc (by decide) Heaptype_subA.refl
      | exact Heaptype_subA.noexn (by decide) Heaptype_subA.refl
      | exact Heaptype_subA.noextern (by decide) Heaptype_subA.refl
      | exact absurd h (by decide)


/-- `Context.heapEq` is sound: it is `Heaptype_sub/refl` on everything but a
`deftype`, and `Deftype_sub/refl` composed with `Heaptype_sub/def` there. -/
theorem heapEq_sound {C : Context} {h₁ h₂ : HeapType} (h : C.heapEq h₁ h₂ = true) :
    Heaptype_subA C h₁ h₂ := by
  have h' : C.normHeapType h₁ = C.normHeapType h₂ := of_decide_eq_true h
  cases h₁ with
  | abs a =>
      cases h₂ with
      | abs b =>
          simp only [Context.normHeapType, HeapType.abs.injEq] at h'
          subst h'; exact .refl
      | use tu₂ => cases tu₂ <;> simp [Context.normHeapType] at h'
  | use tu₁ =>
      cases tu₁ with
      | idx x =>
          cases h₂ with
          | abs b => simp [Context.normHeapType] at h'
          | use tu₂ =>
              cases tu₂ <;> simp only [Context.normHeapType, HeapType.use.injEq,
                TypeUse.idx.injEq, reduceCtorEq] at h'
              subst h'; exact .refl
      | recu i =>
          cases h₂ with
          | abs b => simp [Context.normHeapType] at h'
          | use tu₂ =>
              cases tu₂ <;> simp only [Context.normHeapType, HeapType.use.injEq,
                TypeUse.recu.injEq, reduceCtorEq] at h'
              subst h'; exact .refl
      | defd d₁ =>
          cases h₂ with
          | abs b => simp [Context.normHeapType] at h'
          | use tu₂ =>
              cases tu₂ <;> simp only [Context.normHeapType, HeapType.use.injEq,
                TypeUse.defd.injEq, reduceCtorEq] at h'
              exact .def_ (.refl h')


/-- The `deftype` case of `Context.heapEq` is exactly `Deftype_sub/refl`. -/
theorem heapEq_defd {C : Context} {d₁ d₂ : DefType}
    (h : C.heapEq (.use (.defd d₁)) (.use (.defd d₂)) = true) :
    C.closDefType d₁ = C.closDefType d₂ := by
  have h' : C.normHeapType (.use (.defd d₁)) = C.normHeapType (.use (.defd d₂)) :=
    of_decide_eq_true h
  simpa only [Context.normHeapType, HeapType.use.injEq, TypeUse.defd.injEq] using h'

/-- One step of `Context.heapSupers` out of a `deftype` is one application of
`Deftype_sub/super` --- NOT of `Heaptype_sub/trans`, which is why this needs no
`Heaptype_ok` premise. -/
theorem heapSupers_defd_sound {C : Context} {d₁ d₂ : DefType} {g : HeapType}
    (hmem : g ∈ C.heapSupers (.use (.defd d₁)))
    (hsub : Heaptype_subA C g (.use (.defd d₂))) : Deftype_subA C d₁ d₂ := by
  rcases hu : unrollDt d₁ with _ | st
  · simp only [Context.heapSupers, hu] at hmem; simp at hmem
  · cases st with
    | sub fin sups ct =>
        simp only [Context.heapSupers, hu] at hmem
        obtain ⟨tu, htu, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨i, hi⟩ := List.getElem?_of_mem htu
        exact .super hu hi hsub

/-- One step of `Context.heapSupers` towards a `deftype` target.  `_IDX x` uses
`Heaptype_sub/typeidx-l` and a `deftype` uses `Heaptype_sub/def` on
`heapSupers_defd_sound`; the other two node shapes have no supertypes. -/
theorem heapSupers_sound {C : Context} {h₁ g : HeapType} {d₂ : DefType}
    (hmem : g ∈ C.heapSupers h₁) (hsub : Heaptype_subA C g (.use (.defd d₂))) :
    Heaptype_subA C h₁ (.use (.defd d₂)) := by
  cases h₁ with
  | abs a => simp [Context.heapSupers] at hmem
  | use tu =>
      cases tu with
      | recu i => simp [Context.heapSupers] at hmem
      | idx x =>
          rcases hx : C.types[x.val]? with _ | dt
          · simp only [Context.heapSupers, hx] at hmem; simp at hmem
          · simp only [Context.heapSupers, hx, List.mem_singleton] at hmem
            subst hmem
            exact .typeidx_l hx hsub
      | defd d => exact .def_ (heapSupers_defd_sound hmem hsub)

/-- **The walk is sound.**  `Context.reachDef` answers `true` only on pairs
`Heaptype_sub` derives, for every fuel and every context. -/
theorem reachDef_sound {C : Context} :
    ∀ (n : Nat) {h₁ : HeapType} {d₂ : DefType},
      C.reachDef n h₁ (.use (.defd d₂)) = true → Heaptype_subA C h₁ (.use (.defd d₂)) := by
  intro n
  induction n with
  | zero => intro h₁ d₂ h; exact heapEq_sound h
  | succ n ih =>
      intro h₁ d₂ h
      rw [Context.reachDef, Bool.or_eq_true] at h
      rcases h with he | hs
      · exact heapEq_sound he
      · obtain ⟨g, hg, hg'⟩ := List.any_eq_true.mp hs
        exact heapSupers_sound hg (ih hg')

/-- **The walk is sound at the `deftype` level too**, producing a
`Deftype_sub` derivation rather than merely the `Heaptype_sub` one that
`Heaptype_sub/def` wraps around it. -/
theorem reachDef_sound_deftype {C : Context} :
    ∀ (n : Nat) {d₁ d₂ : DefType},
      C.reachDef n (.use (.defd d₁)) (.use (.defd d₂)) = true → Deftype_subA C d₁ d₂ := by
  intro n
  cases n with
  | zero => intro d₁ d₂ h; exact .refl (heapEq_defd h)
  | succ n =>
      intro d₁ d₂ h
      rw [Context.reachDef, Bool.or_eq_true] at h
      rcases h with he | hs
      · exact .refl (heapEq_defd he)
      · obtain ⟨g, hg, hg'⟩ := List.any_eq_true.mp hs
        exact heapSupers_defd_sound hg (reachDef_sound n hg')


/-- `DefType.absShape` is sound: it fires exactly `Heaptype_sub/struct`,
`/array` and `/func`, each on its own `Expand` premise. -/
theorem absShape_sound {C : Context} {dt : DefType} {s : AbsHeapType}
    (h : dt.absShape = some s) : Heaptype_subA C (.use (.defd dt)) (.abs s) := by
  unfold DefType.absShape at h
  rcases he : expandDt dt with _ | ct
  · rw [he] at h; simp at h
  · rw [he] at h
    simp only [Option.some.injEq] at h
    subst h
    cases ct with
    | struct fts => exact Heaptype_subA.struct (Expand.mk he)
    | array ft => exact Heaptype_subA.array (Expand.mk he)
    | func dom cod => exact Heaptype_subA.func (Expand.mk he)

/-- `Context.typeuseShape` is sound; a type index goes through
`Heaptype_sub/typeidx-l`, which is a direct rule. -/
theorem typeuseShape_sound {C : Context} {tu : TypeUse} {s : AbsHeapType}
    (h : C.typeuseShape tu = some s) : Heaptype_subA C (.use tu) (.abs s) := by
  cases tu with
  | defd d => exact absShape_sound (by simpa only [Context.typeuseShape] using h)
  | recu i => simp [Context.typeuseShape] at h
  | idx x =>
      rcases hx : C.types[x.val]? with _ | dt
      · simp only [Context.typeuseShape, hx] at h; exact absurd h (by simp)
      · simp only [Context.typeuseShape, hx] at h
        exact .typeidx_l hx (absShape_sound h)

/-- `Context.resolveIdx` on the RIGHT-hand side is `Heaptype_sub/typeidx-r`. -/
theorem resolveIdx_sound {C : Context} {h₁ h₂ : HeapType}
    (h : Heaptype_subA C h₁ (C.resolveIdx h₂)) : Heaptype_subA C h₁ h₂ := by
  cases h₂ with
  | abs a => exact h
  | use tu =>
      cases tu with
      | defd d => exact h
      | recu i => exact h
      | idx x =>
          rcases hx : C.types[x.val]? with _ | dt
          · simp only [Context.resolveIdx, hx] at h; exact h
          · simp only [Context.resolveIdx, hx] at h
            exact .typeidx_r hx h

/-- `decHeapSubR` is sound on an already-resolved right-hand side. -/
theorem decHeapSubR_sound {C : Context} {n : Nat} {h₁ h₂ : HeapType}
    (h : decHeapSubR C n h₁ h₂ = true) : Heaptype_subA C h₁ h₂ := by
  cases h₁ with
  | abs a =>
      cases h₂ with
      | abs b => exact decAbsSub_soundA h
      | use tu =>
          cases a with
          | bot => exact .bot
          | none =>
              simp only [decHeapSubR] at h
              rcases hs : C.typeuseShape tu with _ | sh
              · simp only [hs] at h; exact absurd h (by simp)
              · cases sh with
                | struct => exact .none_ (by simp) (.trans .abs (typeuseShape_sound hs)
                    (.trans .abs .struct_eq .eq_any))
                | array => exact .none_ (by simp) (.trans .abs (typeuseShape_sound hs)
                    (.trans .abs .array_eq .eq_any))
                | any | eq | i31 | func | nofunc | exn | noexn | extern | noextern | none | bot =>
                    rw [hs] at h
                    exact absurd h (by simp)
          | nofunc =>
              simp only [decHeapSubR, decide_eq_true_eq] at h
              exact .nofunc (by simp) (typeuseShape_sound h)
          | any | eq | i31 | struct | array | func | noexn | exn | noextern | extern =>
              exact absurd h (by simp [decHeapSubR])
  | use tu₁ =>
      cases h₂ with
      | abs b =>
          rw [decHeapSubR] at h
          rcases hs : C.typeuseShape tu₁ with _ | sh
          · rw [hs] at h; exact absurd h (by simp)
          · rw [hs] at h
            exact .trans Heaptype_okA.abs (typeuseShape_sound hs) (decAbsSub_soundA h)
      | use tu₂ =>
          cases tu₂ with
          | defd d₂ => exact reachDef_sound n h
          | idx x => exact heapEq_sound h
          | recu i => exact heapEq_sound h

/-- **`decHeaptypeSubN` IS SOUND.**  For every context, every fuel and every
pair of heap types: if the procedure says `true` then the pinned
`Heaptype_sub` derives the judgment.  No hypothesis. -/
theorem decHeaptypeSubN_sound {C : Context} {n : Nat} {h₁ h₂ : HeapType}
    (h : decHeaptypeSubN C n h₁ h₂ = true) : Heaptype_subA C h₁ h₂ :=
  resolveIdx_sound (decHeapSubR_sound h)

/-- **`decHeaptypeSub` IS SOUND**, at the context's own walk bound. -/
theorem decHeaptypeSub_sound {C : Context} {h₁ h₂ : HeapType}
    (h : decHeaptypeSub C h₁ h₂ = true) : Heaptype_subA C h₁ h₂ :=
  decHeaptypeSubN_sound h

/-- **`decDeftypeSubN` IS SOUND.** -/
theorem decDeftypeSubN_sound {C : Context} {n : Nat} {d₁ d₂ : DefType}
    (h : decDeftypeSubN C n d₁ d₂ = true) : Deftype_subA C d₁ d₂ :=
  reachDef_sound_deftype n h

/-- **`decDeftypeSub` IS SOUND**, at the context's own walk bound. -/
theorem decDeftypeSub_sound {C : Context} {d₁ d₂ : DefType}
    (h : decDeftypeSub C d₁ d₂ = true) : Deftype_subA C d₁ d₂ :=
  decDeftypeSubN_sound h


/-! ### Soundness of the levels above `Heaptype_sub`

Every relation above the heap-type level is syntax-directed --- none of them
carries a reflexivity or transitivity rule --- so each proof is one case split
on the two types, and the whole layer is unconditional. -/

/-- `decSeq₂` is sound: it delivers BOTH halves of what a SpecTec `(...)*`
premise means, the length agreement and the elementwise relation. -/
theorem decSeq₂_sound {α β : Type} {f : α -> β -> Bool} {R : α -> β -> Prop}
    (hf : ∀ a b, f a b = true → R a b) :
    ∀ (as : List α) (bs : List β), decSeq₂ f as bs = true → SeqLen₂ as bs ∧ SeqAll₂ R as bs := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => exact ⟨rfl, fun i a b ha _ => by simp at ha⟩
      | cons b bs => simp [decSeq₂] at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [decSeq₂] at h
      | cons b bs =>
          rw [decSeq₂, Bool.and_eq_true] at h
          obtain ⟨hab, hrest⟩ := h
          obtain ⟨hlen, hall⟩ := ih bs hrest
          refine ⟨by simp only [SeqLen₂, List.length_cons, hlen], ?_⟩
          intro i a' b' ha hb
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
              subst ha; subst hb; exact hf _ _ hab
          | succ i =>
              simp only [List.getElem?_cons_succ] at ha hb
              exact hall i a' b' ha hb

/-- `decSeq₂` is complete. -/
theorem decSeq₂_complete {α β : Type} {f : α -> β -> Bool} {R : α -> β -> Prop}
    (hf : ∀ a b, R a b → f a b = true) :
    ∀ (as : List α) (bs : List β), SeqLen₂ as bs → SeqAll₂ R as bs → decSeq₂ f as bs = true := by
  intro as
  induction as with
  | nil =>
      intro bs hlen _
      cases bs with
      | nil => rfl
      | cons b bs => simp [SeqLen₂] at hlen
  | cons a as ih =>
      intro bs hlen hall
      cases bs with
      | nil => simp [SeqLen₂] at hlen
      | cons b bs =>
          rw [decSeq₂, Bool.and_eq_true]
          refine ⟨hf a b (hall 0 a b rfl rfl),
            ih bs (by simpa only [SeqLen₂, List.length_cons, Nat.add_right_cancel_iff] using hlen) ?_⟩
          intro i a' b' ha hb
          exact hall (i + 1) a' b' (by simpa using ha) (by simpa using hb)

/-- **`decNumtypeSub` IS SOUND.** -/
theorem decNumtypeSub_sound {C : Context} {nt₁ nt₂ : NumType}
    (h : decNumtypeSub nt₁ nt₂ = true) : Numtype_sub C nt₁ nt₂ := by
  have h' : nt₁ = nt₂ := of_decide_eq_true h
  subst h'; exact .mk

/-- **`decVectypeSub` IS SOUND.** -/
theorem decVectypeSub_sound {C : Context} {vt₁ vt₂ : VecType}
    (h : decVectypeSub vt₁ vt₂ = true) : Vectype_sub C vt₁ vt₂ := by
  have h' : vt₁ = vt₂ := of_decide_eq_true h
  subst h'; exact .mk

/-- **`decPacktypeSub` IS SOUND.** -/
theorem decPacktypeSub_sound {C : Context} {pt₁ pt₂ : PackType}
    (h : decPacktypeSub pt₁ pt₂ = true) : Packtype_sub C pt₁ pt₂ := by
  have h' : pt₁ = pt₂ := of_decide_eq_true h
  subst h'; exact .mk

/-- **`decReftypeSubN` IS SOUND.** -/
theorem decReftypeSubN_sound {C : Context} {n : Nat} {rt₁ rt₂ : RefType}
    (h : decReftypeSubN C n rt₁ rt₂ = true) : Reftype_subA C rt₁ rt₂ := by
  cases rt₁ with
  | ref nul₁ ht₁ =>
      cases rt₂ with
      | ref nul₂ ht₂ =>
          rw [decReftypeSubN, Bool.and_eq_true] at h
          obtain ⟨hn, hh⟩ := h
          have hsub := decHeaptypeSubN_sound hh
          cases nul₂ with
          | some nn => cases nn; exact .null hsub
          | none =>
              cases nul₁ with
              | none => exact .nonnull hsub
              | some nn => simp at hn

/-- **`decValtypeSubN` IS SOUND.** -/
theorem decValtypeSubN_sound {C : Context} {n : Nat} {t₁ t₂ : ValType}
    (h : decValtypeSubN C n t₁ t₂ = true) : Valtype_subA C t₁ t₂ := by
  cases t₁ <;> cases t₂ <;>
    first
      | exact Valtype_subA.bot
      | exact Valtype_subA.num (decNumtypeSub_sound h)
      | exact Valtype_subA.vec (decVectypeSub_sound h)
      | exact Valtype_subA.ref (decReftypeSubN_sound h)
      | simp [decValtypeSubN] at h

/-- **`decStoragetypeSubN` IS SOUND.** -/
theorem decStoragetypeSubN_sound {C : Context} {n : Nat} {zt₁ zt₂ : StorageType}
    (h : decStoragetypeSubN C n zt₁ zt₂ = true) : Storagetype_subA C zt₁ zt₂ := by
  cases zt₁ <;> cases zt₂ <;>
    first
      | exact Storagetype_subA.val (decValtypeSubN_sound h)
      | exact Storagetype_subA.pack (decPacktypeSub_sound h)
      | simp [decStoragetypeSubN] at h

/-- **`decFieldtypeSubN` IS SOUND.** -/
theorem decFieldtypeSubN_sound {C : Context} {n : Nat} {ft₁ ft₂ : FieldType}
    (h : decFieldtypeSubN C n ft₁ ft₂ = true) : Fieldtype_subA C ft₁ ft₂ := by
  cases ft₁ with
  | mk m₁ zt₁ =>
      cases ft₂ with
      | mk m₂ zt₂ =>
          cases m₁ with
          | none =>
              cases m₂ with
              | none => exact .const (decStoragetypeSubN_sound h)
              | some mm => cases mm; simp [decFieldtypeSubN] at h
          | some mm₁ =>
              cases mm₁
              cases m₂ with
              | none => simp [decFieldtypeSubN] at h
              | some mm₂ =>
                  cases mm₂
                  rw [decFieldtypeSubN, Bool.and_eq_true] at h
                  exact .var (decStoragetypeSubN_sound h.1) (decStoragetypeSubN_sound h.2)

/-- **`decResulttypeSubN` IS SOUND.** -/
theorem decResulttypeSubN_sound {C : Context} {n : Nat} {ts₁ ts₂ : List ValType}
    (h : decResulttypeSubN C n ts₁ ts₂ = true) : Resulttype_subA C ts₁ ts₂ :=
  let r := decSeq₂_sound (fun _ _ hh => decValtypeSubN_sound hh) ts₁ ts₂ h
  .mk r.1 r.2

/-- **`decComptypeSubN` IS SOUND.**  The `STRUCT` case rebuilds the rule's
`ft_1* ft'_1*` split as `take`/`drop` at the target's length. -/
theorem decComptypeSubN_sound {C : Context} {n : Nat} {ct₁ ct₂ : CompType}
    (h : decComptypeSubN C n ct₁ ct₂ = true) : Comptype_subA C ct₁ ct₂ := by
  cases ct₁ with
  | struct fts₁ =>
      cases ct₂ with
      | struct fts₂ =>
          rw [decComptypeSubN, Bool.and_eq_true] at h
          obtain ⟨_, hseq⟩ := h
          obtain ⟨hlen, hall⟩ :=
            decSeq₂_sound (fun _ _ hh => decFieldtypeSubN_sound hh) _ _ hseq
          have key := Comptype_subA.struct (C := C)
            (fts₁ := (FieldTypes.toList fts₁).take (FieldTypes.toList fts₂).length)
            (fts₁' := (FieldTypes.toList fts₁).drop (FieldTypes.toList fts₂).length)
            (fts₂ := FieldTypes.toList fts₂) hlen hall
          rwa [List.take_append_drop, FieldTypes.ofList_toList,
            FieldTypes.ofList_toList] at key
      | array _ => simp [decComptypeSubN] at h
      | func _ _ => simp [decComptypeSubN] at h
  | array ft₁ =>
      cases ct₂ with
      | array ft₂ => exact .array (decFieldtypeSubN_sound h)
      | struct _ => simp [decComptypeSubN] at h
      | func _ _ => simp [decComptypeSubN] at h
  | func dom₁ cod₁ =>
      cases ct₂ with
      | func dom₂ cod₂ =>
          rw [decComptypeSubN, Bool.and_eq_true] at h
          exact .func (decResulttypeSubN_sound h.1) (decResulttypeSubN_sound h.2)
      | struct _ => simp [decComptypeSubN] at h
      | array _ => simp [decComptypeSubN] at h

/-- **`decInstrtypeSubN` IS SOUND.** -/
theorem decInstrtypeSubN_sound {C : Context} {n : Nat} {it₁ it₂ : InstrType}
    (h : decInstrtypeSubN C n it₁ it₂ = true) : Instrtype_subA C it₁ it₂ := by
  rw [decInstrtypeSubN, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hd, hc⟩, hl⟩ := h
  refine .mk (decResulttypeSubN_sound hd) (decResulttypeSubN_sound hc) ?_
  intro x hx
  have := List.all_eq_true.mp hl x hx
  rcases hlx : C.locals[x.val]? with _ | lct
  · rw [hlx] at this; simp at this
  · rw [hlx] at this
    cases lct with
    | mk ini t =>
        have : ini = Init.set := of_decide_eq_true this
        subst this
        exact ⟨t, rfl⟩

/-- **`decLimitsSub` IS SOUND.** -/
theorem decLimitsSub_sound {C : Context} {lim₁ lim₂ : Limits}
    (h : decLimitsSub lim₁ lim₂ = true) : Limits_sub C lim₁ lim₂ := by
  cases lim₁ with
  | mk n₁ m₁ =>
      cases lim₂ with
      | mk n₂ m₂ =>
          cases m₁ with
          | none => simp [decLimitsSub] at h
          | some m₁ =>
              cases m₂ with
              | none => simp [decLimitsSub] at h
              | some m₂ =>
                  rw [decLimitsSub, Bool.and_eq_true] at h
                  exact .mk (of_decide_eq_true h.1) (of_decide_eq_true h.2)

/-- **`decTagtypeSubN` IS SOUND.** -/
theorem decTagtypeSubN_sound {C : Context} {n : Nat} {jt₁ jt₂ : TagType}
    (h : decTagtypeSubN C n jt₁ jt₂ = true) : Tagtype_subA C jt₁ jt₂ := by
  cases jt₁ <;> cases jt₂ <;>
    first
      | (rw [decTagtypeSubN, Bool.and_eq_true] at h
         exact Tagtype_subA.mk (decDeftypeSubN_sound h.1) (decDeftypeSubN_sound h.2))
      | simp [decTagtypeSubN] at h

/-- **`decGlobaltypeSubN` IS SOUND.** -/
theorem decGlobaltypeSubN_sound {C : Context} {n : Nat} {gt₁ gt₂ : GlobalType}
    (h : decGlobaltypeSubN C n gt₁ gt₂ = true) : Globaltype_subA C gt₁ gt₂ := by
  cases gt₁ with
  | mk m₁ t₁ =>
      cases gt₂ with
      | mk m₂ t₂ =>
          cases m₁ with
          | none =>
              cases m₂ with
              | none => exact .const (decValtypeSubN_sound h)
              | some mm => cases mm; simp [decGlobaltypeSubN] at h
          | some mm₁ =>
              cases mm₁
              cases m₂ with
              | none => simp [decGlobaltypeSubN] at h
              | some mm₂ =>
                  cases mm₂
                  rw [decGlobaltypeSubN, Bool.and_eq_true] at h
                  exact .var (decValtypeSubN_sound h.1) (decValtypeSubN_sound h.2)

/-- **`decMemtypeSub` IS SOUND.** -/
theorem decMemtypeSub_sound {C : Context} {mt₁ mt₂ : MemType}
    (h : decMemtypeSub mt₁ mt₂ = true) : Memtype_sub C mt₁ mt₂ := by
  cases mt₁ with
  | mk a₁ l₁ =>
      cases mt₂ with
      | mk a₂ l₂ =>
          rw [decMemtypeSub, Bool.and_eq_true] at h
          have ha : a₁ = a₂ := of_decide_eq_true h.1
          subst ha
          exact .mk (decLimitsSub_sound h.2)

/-- **`decTabletypeSubN` IS SOUND.** -/
theorem decTabletypeSubN_sound {C : Context} {n : Nat} {tt₁ tt₂ : TableType}
    (h : decTabletypeSubN C n tt₁ tt₂ = true) : Tabletype_subA C tt₁ tt₂ := by
  cases tt₁ with
  | mk a₁ l₁ r₁ =>
      cases tt₂ with
      | mk a₂ l₂ r₂ =>
          rw [decTabletypeSubN, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
          obtain ⟨⟨⟨ha, hl⟩, hr₁⟩, hr₂⟩ := h
          have ha' : a₁ = a₂ := of_decide_eq_true ha
          subst ha'
          exact .mk (decLimitsSub_sound hl) (decReftypeSubN_sound hr₁)
            (decReftypeSubN_sound hr₂)

/-- **`decExterntypeSubN` IS SOUND.** -/
theorem decExterntypeSubN_sound {C : Context} {n : Nat} {xt₁ xt₂ : ExternType}
    (h : decExterntypeSubN C n xt₁ xt₂ = true) : Externtype_subA C xt₁ xt₂ := by
  cases xt₁ with
  | tag jt₁ =>
      cases xt₂ with
      | tag jt₂ => exact .tag (decTagtypeSubN_sound h)
      | _ => simp [decExterntypeSubN] at h
  | global gt₁ =>
      cases xt₂ with
      | global gt₂ => exact .global (decGlobaltypeSubN_sound h)
      | _ => simp [decExterntypeSubN] at h
  | mem mt₁ =>
      cases xt₂ with
      | mem mt₂ => exact .mem (decMemtypeSub_sound h)
      | _ => simp [decExterntypeSubN] at h
  | table tt₁ =>
      cases xt₂ with
      | table tt₂ => exact .table (decTabletypeSubN_sound h)
      | _ => simp [decExterntypeSubN] at h
  | func tu₁ =>
      cases xt₂ with
      | func tu₂ =>
          cases tu₁ <;> cases tu₂ <;>
            first
              | exact Externtype_subA.func (decDeftypeSubN_sound h)
              | simp [decExterntypeSubN] at h
      | _ => simp [decExterntypeSubN] at h


/-! ## Completeness above the heap-type relation

Every amended subtype relation above `Heaptype_subA` is syntax-directed.  The
only genuinely non-local obligation is therefore heap-type completeness.  The
theorems below propagate any exact heap decision through the entire upper
hierarchy; there is no second gap hidden at composite, instruction, or external
types.  `SubtypeSound.lean` supplies the context-sensitive heap theorem used by
the full validator. -/

theorem decNumtypeSub_complete {C : Context} {nt₁ nt₂ : NumType}
    (h : Numtype_sub C nt₁ nt₂) : decNumtypeSub nt₁ nt₂ = true := by
  cases h
  simp [decNumtypeSub]

theorem decVectypeSub_complete {C : Context} {vt₁ vt₂ : VecType}
    (h : Vectype_sub C vt₁ vt₂) : decVectypeSub vt₁ vt₂ = true := by
  cases h
  simp [decVectypeSub]

theorem decPacktypeSub_complete {C : Context} {pt₁ pt₂ : PackType}
    (h : Packtype_sub C pt₁ pt₂) : decPacktypeSub pt₁ pt₂ = true := by
  cases h
  simp [decPacktypeSub]

theorem decLimitsSub_complete {C : Context} {lim₁ lim₂ : Limits}
    (h : Limits_sub C lim₁ lim₂) : decLimitsSub lim₁ lim₂ = true := by
  cases h with
  | mk hmin hmax => simp [decLimitsSub, hmin, hmax]

theorem decMemtypeSub_complete {C : Context} {mt₁ mt₂ : MemType}
    (h : Memtype_sub C mt₁ mt₂) : decMemtypeSub mt₁ mt₂ = true := by
  cases h with
  | mk hlim => simp [decMemtypeSub, decLimitsSub_complete hlim]

section UpperCompleteness

variable {C : Context} {n : Nat}

theorem decReftypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {rt₁ rt₂ : RefType} (h : Reftype_subA C rt₁ rt₂) :
    decReftypeSubN C n rt₁ rt₂ = true := by
  cases h with
  | nonnull hs => simp [decReftypeSubN, hheap hs]
  | null hs => simp [decReftypeSubN, hheap hs]

theorem decValtypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {t₁ t₂ : ValType} (h : Valtype_subA C t₁ t₂) :
    decValtypeSubN C n t₁ t₂ = true := by
  cases h with
  | num hs => exact decNumtypeSub_complete hs
  | vec hs => exact decVectypeSub_complete hs
  | ref hs => exact decReftypeSubN_complete_of_heap hheap hs
  | bot => rfl

theorem decStoragetypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {zt₁ zt₂ : StorageType} (h : Storagetype_subA C zt₁ zt₂) :
    decStoragetypeSubN C n zt₁ zt₂ = true := by
  cases h with
  | val hs => exact decValtypeSubN_complete_of_heap hheap hs
  | pack hs => exact decPacktypeSub_complete hs

theorem decFieldtypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {ft₁ ft₂ : FieldType} (h : Fieldtype_subA C ft₁ ft₂) :
    decFieldtypeSubN C n ft₁ ft₂ = true := by
  cases h with
  | const hs => exact decStoragetypeSubN_complete_of_heap hheap hs
  | var hs₁ hs₂ =>
      rw [decFieldtypeSubN, Bool.and_eq_true]
      exact ⟨decStoragetypeSubN_complete_of_heap hheap hs₁,
        decStoragetypeSubN_complete_of_heap hheap hs₂⟩

theorem decResulttypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {ts₁ ts₂ : List ValType} (h : Resulttype_subA C ts₁ ts₂) :
    decResulttypeSubN C n ts₁ ts₂ = true := by
  cases h with
  | mk hlen hall =>
      exact decSeq₂_complete (fun _ _ hs => decValtypeSubN_complete_of_heap hheap hs)
        ts₁ ts₂ hlen hall

theorem decComptypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {ct₁ ct₂ : CompType} (h : Comptype_subA C ct₁ ct₂) :
    decComptypeSubN C n ct₁ ct₂ = true := by
  cases h with
  | struct hlen hall =>
      rename_i fts₁ fts₁' fts₂
      simp only [decComptypeSubN, FieldTypes.toList_ofList, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · simp only [List.length_append]
        omega
      · have htake : (fts₁ ++ fts₁').take fts₂.length = fts₁ := by
          rw [← hlen, List.take_left]
        rw [htake]
        exact decSeq₂_complete
          (fun _ _ hs => decFieldtypeSubN_complete_of_heap hheap hs)
          fts₁ fts₂ hlen hall
  | array hs => exact decFieldtypeSubN_complete_of_heap hheap hs
  | func hdom hcod =>
      rw [decComptypeSubN, Bool.and_eq_true]
      exact ⟨decResulttypeSubN_complete_of_heap hheap hdom,
        decResulttypeSubN_complete_of_heap hheap hcod⟩

theorem decDeftypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {d₁ d₂ : DefType} (h : Deftype_subA C d₁ d₂) :
    decDeftypeSubN C n d₁ d₂ = true := by
  simpa [decHeaptypeSubN, decHeapSubR, Context.resolveIdx, decDeftypeSubN] using
    hheap (Heaptype_subA.def_ h)

theorem decInstrtypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {it₁ it₂ : InstrType} (h : Instrtype_subA C it₁ it₂) :
    decInstrtypeSubN C n it₁ it₂ = true := by
  cases h with
  | mk hdom hcod hloc =>
      simp only [decInstrtypeSubN, Bool.and_eq_true]
      refine ⟨⟨decResulttypeSubN_complete_of_heap hheap hdom,
        decResulttypeSubN_complete_of_heap hheap hcod⟩, ?_⟩
      exact List.all_eq_true.mpr (fun x hx => by
        obtain ⟨t, ht⟩ := hloc x hx
        rw [ht]
        simp)

theorem decTagtypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {jt₁ jt₂ : TagType} (h : Tagtype_subA C jt₁ jt₂) :
    decTagtypeSubN C n jt₁ jt₂ = true := by
  cases h with
  | mk h₁ h₂ =>
      rw [decTagtypeSubN, Bool.and_eq_true]
      exact ⟨decDeftypeSubN_complete_of_heap hheap h₁,
        decDeftypeSubN_complete_of_heap hheap h₂⟩

theorem decGlobaltypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {gt₁ gt₂ : GlobalType} (h : Globaltype_subA C gt₁ gt₂) :
    decGlobaltypeSubN C n gt₁ gt₂ = true := by
  cases h with
  | const hs => exact decValtypeSubN_complete_of_heap hheap hs
  | var hs₁ hs₂ =>
      rw [decGlobaltypeSubN, Bool.and_eq_true]
      exact ⟨decValtypeSubN_complete_of_heap hheap hs₁,
        decValtypeSubN_complete_of_heap hheap hs₂⟩

theorem decTabletypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {tt₁ tt₂ : TableType} (h : Tabletype_subA C tt₁ tt₂) :
    decTabletypeSubN C n tt₁ tt₂ = true := by
  cases h with
  | mk hlim hr₁ hr₂ =>
      simp [decTabletypeSubN, decLimitsSub_complete hlim,
        decReftypeSubN_complete_of_heap hheap hr₁,
        decReftypeSubN_complete_of_heap hheap hr₂]

theorem decExterntypeSubN_complete_of_heap
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA C h₁ h₂ →
      decHeaptypeSubN C n h₁ h₂ = true)
    {xt₁ xt₂ : ExternType} (h : Externtype_subA C xt₁ xt₂) :
    decExterntypeSubN C n xt₁ xt₂ = true := by
  cases h with
  | tag hs => exact decTagtypeSubN_complete_of_heap hheap hs
  | global hs => exact decGlobaltypeSubN_complete_of_heap hheap hs
  | mem hs => exact decMemtypeSub_complete hs
  | table hs => exact decTabletypeSubN_complete_of_heap hheap hs
  | func hs => exact decDeftypeSubN_complete_of_heap hheap hs

end UpperCompleteness


/-! ## Fuel monotonicity

The walk bound is an argument, so a consumer that needs a deeper walk raises
it; these say that raising it never loses an answer, which is what makes the
fuel-indexed statements compose. -/

/-- One more step of fuel never loses an answer. -/
theorem reachDef_succ {C : Context} :
    ∀ (n : Nat) (h₁ h₂ : HeapType), C.reachDef n h₁ h₂ = true →
      C.reachDef (n + 1) h₁ h₂ = true := by
  intro n
  induction n with
  | zero =>
      intro h₁ h₂ h
      rw [Context.reachDef, Bool.or_eq_true]
      exact Or.inl h
  | succ n ih =>
      intro h₁ h₂ h
      rw [Context.reachDef, Bool.or_eq_true] at h
      rw [Context.reachDef, Bool.or_eq_true]
      rcases h with he | hs
      · exact Or.inl he
      · refine Or.inr ?_
        obtain ⟨g, hg, hg'⟩ := List.any_eq_true.mp hs
        exact List.any_eq_true.mpr ⟨g, hg, ih g h₂ hg'⟩

/-- More fuel never loses an answer. -/
theorem reachDef_mono {C : Context} {n m : Nat} (hnm : n ≤ m) {h₁ h₂ : HeapType}
    (h : C.reachDef n h₁ h₂ = true) : C.reachDef m h₁ h₂ = true := by
  induction m with
  | zero => have : n = 0 := Nat.le_zero.mp hnm; subst this; exact h
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact reachDef_succ m h₁ h₂ (ih (Nat.le_of_lt_succ hlt))
      · have : n = m + 1 := Nat.le_antisymm hnm hge
        subst this; exact h

/-- `decHeaptypeSubN` is monotone in the fuel. -/
theorem decHeaptypeSubN_mono {C : Context} {n m : Nat} (hnm : n ≤ m) {h₁ h₂ : HeapType}
    (h : decHeaptypeSubN C n h₁ h₂ = true) : decHeaptypeSubN C m h₁ h₂ = true := by
  cases h₁ with
  | abs a =>
      cases hr : C.resolveIdx h₂ with
      | abs b => rw [decHeaptypeSubN, hr]; rw [decHeaptypeSubN, hr] at h; exact h
      | use tu =>
          rw [decHeaptypeSubN, hr]
          rw [decHeaptypeSubN, hr] at h
          cases a <;> exact h
  | use tu₁ =>
      cases hr : C.resolveIdx h₂ with
      | abs b => rw [decHeaptypeSubN, hr]; rw [decHeaptypeSubN, hr] at h; exact h
      | use tu₂ =>
          cases tu₂ with
          | defd d₂ =>
              rw [decHeaptypeSubN, hr]; rw [decHeaptypeSubN, hr] at h
              exact reachDef_mono hnm h
          | idx x => rw [decHeaptypeSubN, hr]; rw [decHeaptypeSubN, hr] at h; exact h
          | recu i => rw [decHeaptypeSubN, hr]; rw [decHeaptypeSubN, hr] at h; exact h

/-- `decDeftypeSubN` is monotone in the fuel. -/
theorem decDeftypeSubN_mono {C : Context} {n m : Nat} (hnm : n ≤ m) {d₁ d₂ : DefType}
    (h : decDeftypeSubN C n d₁ d₂ = true) : decDeftypeSubN C m d₁ d₂ = true :=
  reachDef_mono hnm h

end WasmGemmGnaf.Wasm.Core
