import WasmGemmGnaf.Wasm.Core.ValidateTypeSources
import WasmGemmGnaf.Wasm.Core.ValidateRolledSources
import WasmGemmGnaf.Wasm.Core.ValidateSeq

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

open Validate

/-- Every heap leaf in a result type comes from the checked source type graph.
Unlike semantic validity, this excludes arbitrary literal `deftype` values. -/
def ResultSourceA (C : Context) (ts : List ValType) : Prop :=
  ∀ t ∈ ts, t.SourceA C

namespace ResultSourceA

theorem nil (C : Context) : ResultSourceA C [] := by
  intro t ht
  nomatch ht

theorem cons {C : Context} {t : ValType} {ts : List ValType}
    (ht : t.SourceA C) (hts : ResultSourceA C ts) :
    ResultSourceA C (t :: ts) := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ht
  · exact hts u hu

theorem singleton {C : Context} {t : ValType} (ht : t.SourceA C) :
    ResultSourceA C [t] :=
  cons ht (nil C)

theorem append {C : Context} {ts us : List ValType}
    (hts : ResultSourceA C ts) (hus : ResultSourceA C us) :
    ResultSourceA C (ts ++ us) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hts t ht
  · exact hus t ht

theorem of_append_left {C : Context} {ts us : List ValType}
    (h : ResultSourceA C (ts ++ us)) : ResultSourceA C ts := by
  intro t ht
  exact h t (List.mem_append_left us ht)

theorem of_append_right {C : Context} {ts us : List ValType}
    (h : ResultSourceA C (ts ++ us)) : ResultSourceA C us := by
  intro t ht
  exact h t (List.mem_append_right ts ht)

theorem transport {C D : Context} (hCD : SameTypeEnv C D)
    {ts : List ValType} (h : ResultSourceA C ts) : ResultSourceA D ts := by
  intro t ht
  exact (h t ht).of_types_eq hCD.1 hCD.2

end ResultSourceA

namespace Validate

/-- Checked type-section evidence retained while validation changes locals and
control labels.  Its decision theorem is intentionally restricted to ranked
source endpoints; semantic validity by itself is not enough to bound the
declarative transitivity depth of arbitrary literal `deftype` values. -/
structure SourceTypeCompleteA (C : Context) where
  tds : List TypeDef
  dts : List DefType
  syn : tds.all TypeDef.isSyn = true
  typesOk : Types_okA Context.empty tds dts
  types : C.types = dts
  recs : C.recs = []

namespace SourceTypeCompleteA

def transport {C D : Context} (hCD : SameTypeEnv C D)
    (h : SourceTypeCompleteA C) : SourceTypeCompleteA D where
  tds := h.tds
  dts := h.dts
  syn := h.syn
  typesOk := h.typesOk
  types := hCD.1.symm.trans h.types
  recs := hCD.2.symm.trans h.recs

theorem shapes {C : Context} (h : SourceTypeCompleteA C) :
    C.ValidHeapShapesA :=
  h.typesOk.validHeapShapesA_in_context h.syn C h.types h.recs

theorem complete {C : Context} (h : SourceTypeCompleteA C)
    {left right : HeapType} (hleft : left.SourceA C)
    (hright : right.SourceA C) (hsub : Heaptype_subA C left right) :
    decHeaptypeSubN C C.subtypeFuel left right = true :=
  h.typesOk.decHeaptypeSubN_complete_of_sourceA h.syn h.types h.shapes
    hleft hright hsub

/-- One-sided source completeness.  A ranked or closed source node carries
the whole declared-supertype walk, so its target need only be semantically
well formed.  For an abstract source, well-formedness plus the empty ordinary
`REC` scratch space supplies the target shape needed by the finite lattice
case. -/
theorem completeLeft {C : Context} (h : SourceTypeCompleteA C)
    {left right : HeapType} (hleft : left.SourceA C)
    (hright : Heaptype_okA C right) (hsub : Heaptype_subA C left right) :
    decHeaptypeSubN C C.subtypeFuel left right = true := by
  cases left with
  | abs a =>
      cases right with
      | abs b => exact hsub.decHeaptypeSubN_complete_of_abs_abs h.shapes
      | use tu =>
          obtain ⟨b, hgood⟩ := h.shapes hright
          apply hsub.decHeaptypeSubN_complete_of_abs_nonrec_use h.shapes hgood
          intro i hi
          subst tu
          cases hright with
          | typeuse htu =>
              cases htu with
              | rec_ hlookup => simpa [h.recs] using hlookup
  | use tu =>
      rcases hleft with hraw | hclosed
      · obtain ⟨r, hnode⟩ := hraw
        exact h.typesOk.decHeaptypeSubN_complete_of_sourceTypeNodeA_in_context
          h.syn h.types hnode hsub
      · obtain ⟨i, dt, htu, hlookup, hrecs⟩ := hclosed
        subst tu
        have hlookup' : (closDefTypes h.dts)[i]? = some dt := by
          simpa [h.types] using hlookup
        exact h.typesOk.decHeaptypeSubN_complete_of_closed_member h.syn
          h.types h.recs hlookup' hsub

theorem reftypeComplete {C : Context} (h : SourceTypeCompleteA C)
    {left right : RefType} (hleft : left.SourceA C)
    (hright : right.SourceA C) (hsub : Reftype_subA C left right) :
    decReftypeSubN C C.subtypeFuel left right = true :=
  hsub.decReftypeSubN_complete_of_sourceA h.syn h.typesOk h.types h.shapes
    hleft hright

theorem reftypeCompleteLeft {C : Context} (h : SourceTypeCompleteA C)
    {left right : RefType} (hleft : left.SourceA C)
    (hright : Reftype_okA C right) (hsub : Reftype_subA C left right) :
    decReftypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | nonnull hs =>
      cases hright with
      | mk hrightHeap =>
          simp [decReftypeSubN, h.completeLeft hleft hrightHeap hs]
  | null hs =>
      cases hright with
      | mk hrightHeap =>
          simp [decReftypeSubN, h.completeLeft hleft hrightHeap hs]

theorem valtypeComplete {C : Context} (h : SourceTypeCompleteA C)
    {left right : ValType} (hleft : left.SourceA C)
    (hright : right.SourceA C) (hsub : Valtype_subA C left right) :
    decValtypeSubN C C.subtypeFuel left right = true :=
  hsub.decValtypeSubN_complete_of_sourceA h.syn h.typesOk h.types h.shapes
    hleft hright

theorem valtypeCompleteLeft {C : Context} (h : SourceTypeCompleteA C)
    {left right : ValType} (hleft : left.SourceA C)
    (hright : Valtype_okA C right) (hsub : Valtype_subA C left right) :
    decValtypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | num hs => exact decNumtypeSub_complete hs
  | vec hs => exact decVectypeSub_complete hs
  | ref hs =>
      cases hright with
      | ref hrightRef => exact h.reftypeCompleteLeft hleft hrightRef hs
  | bot => rfl

theorem storageComplete {C : Context} (h : SourceTypeCompleteA C)
    {left right : StorageType} (hleft : left.SourceA C)
    (hright : right.SourceA C) (hsub : Storagetype_subA C left right) :
    decStoragetypeSubN C C.subtypeFuel left right = true :=
  hsub.decStoragetypeSubN_complete_of_sourceA h.syn h.typesOk h.types h.shapes
    hleft hright

theorem resultComplete {C : Context} (h : SourceTypeCompleteA C)
    {left right : List ValType} (hleft : ResultSourceA C left)
    (hright : ResultSourceA C right) (hsub : Resulttype_subA C left right) :
    decResulttypeSubN C C.subtypeFuel left right = true :=
  hsub.decResulttypeSubN_complete_of_sourceA h.syn h.typesOk h.types h.shapes
    hleft hright

theorem resultCompleteLeft {C : Context} (h : SourceTypeCompleteA C)
    {left right : List ValType} (hleft : ResultSourceA C left)
    (hright : Resulttype_okA C right)
    (hsub : Resulttype_subA C left right) :
    decResulttypeSubN C C.subtypeFuel left right = true := by
  cases hsub with
  | mk hlen hall =>
      cases hright with
      | mk hrightAll =>
          apply decSeq₂_complete (R := fun a b =>
            a.SourceA C ∧ Valtype_okA C b ∧ Valtype_subA C a b)
            (fun a b hab => h.valtypeCompleteLeft hab.1 hab.2.1 hab.2.2)
            left right hlen
          intro i a b ha hb
          exact ⟨hleft a (List.mem_of_getElem? ha),
            hrightAll b (List.mem_of_getElem? hb), hall i a b ha hb⟩

theorem idxSource {C : Context} (h : SourceTypeCompleteA C)
    {x : TypeIdx} {dt : DefType} (hx : C.types[x.val]? = some dt) :
    (HeapType.use (.idx x)).SourceA C :=
  Or.inl ⟨2 * x.val + 1, .idx hx⟩

theorem defdSource {C : Context} (h : SourceTypeCompleteA C)
    {x : TypeIdx} {dt : DefType} (hx : C.types[x.val]? = some dt) :
    (HeapType.use (.defd dt)).SourceA C :=
  Or.inl ⟨2 * x.val, .defd hx⟩

theorem compSource {C : Context} (h : SourceTypeCompleteA C)
    {x : TypeIdx} {dt : DefType} {ct : CompType}
    (hx : C.types[x.val]? = some dt) (he : Expand dt ct) :
    ct.SourceA C := by
  have hxDts : h.dts[x.val]? = some dt := by
    simpa [h.types] using hx
  cases he with
  | mk he =>
      cases hu : unrollDt dt with
      | none => simp [expandDt, hu] at he
      | some st =>
          cases st with
          | sub fin sups expanded =>
              simp [expandDt, hu] at he
              subst expanded
              have hs := h.typesOk.storedCompSourceA h.syn x.val dt hxDts hu
              exact hs.of_types_eq
                (by simpa [Context.empty] using h.types.symm)
                (by simpa [Context.empty] using h.recs.symm)

theorem typeFuncSources {C : Context} (h : SourceTypeCompleteA C)
    {x : TypeIdx} {dt : DefType} {dom cod : ValTypes}
    (hx : C.types[x.val]? = some dt) (he : Expand dt (.func dom cod)) :
    ResultSourceA C (ValTypes.toList dom) ∧
      ResultSourceA C (ValTypes.toList cod) := by
  exact h.compSource hx he

end SourceTypeCompleteA

/-- Source provenance for every concrete value type retained by the abstract
operand stack.  Polymorphic underflow contributes `BOT`, whose source
provenance is immediate. -/
def St.SourceA (C : Context) (st : St) : Prop := ResultSourceA C st.vals

namespace St.SourceA

theorem transport {C D : Context} (hCD : SameTypeEnv C D) {st : St}
    (h : st.SourceA C) : st.SourceA D :=
  ResultSourceA.transport hCD h

theorem empty (C : Context) (p : Bool) : (St.mk p []).SourceA C :=
  ResultSourceA.nil C

theorem push {C : Context} {st : St} {t : ValType}
    (hst : st.SourceA C) (ht : t.SourceA C) : (st.push t).SourceA C := by
  simpa [St.SourceA, St.push] using ResultSourceA.cons ht hst

theorem pushs {C : Context} {st : St} {ts : List ValType}
    (hst : st.SourceA C) (hts : ResultSourceA C ts) :
    (st.pushs ts).SourceA C := by
  rw [St.SourceA, St.pushs_eq]
  exact ResultSourceA.append (by
    intro t ht
    exact hts t (by simpa using ht)) hst

theorem pop {C : Context} {st st' : St} {t : ValType}
    (hst : st.SourceA C) (hp : st.pop = some (t, st')) :
    t.SourceA C ∧ st'.SourceA C := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          simp [St.pop] at hp
          obtain ⟨_, rfl, rfl⟩ := hp
          exact ⟨trivial, hst⟩
      | cons u us =>
          simp only [St.pop, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact ⟨hst u (by simp), fun v hv => hst v (by simp [hv])⟩

theorem popEA {C : Context} {st st' : St} {t : ValType}
    (hst : st.SourceA C) (hp : st.popEA C t = some st') :
    st'.SourceA C := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at hp
          subst st'
          exact hst
      | cons u us =>
          simp only [St.popEA] at hp
          split at hp
          · injection hp with hp
            subst st'
            intro v hv
            exact hst v (by simp [hv])
          · contradiction

theorem popsA {C : Context} {st st' : St} {ts : List ValType}
    (hst : st.SourceA C) (hp : st.popsA C ts = some st') :
    st'.SourceA C := by
  induction ts generalizing st st' with
  | nil =>
      simp only [St.popsA, Option.some.injEq] at hp
      subst st'
      exact hst
  | cons t ts ih =>
      simp only [St.popsA] at hp
      cases htail : st.popsA C ts with
      | none => simp only [htail] at hp; contradiction
      | some s =>
          rw [htail] at hp
          exact popEA (ih hst htail) hp

theorem popN {C : Context} {st base : St} {n : Nat}
    {ts : List ValType} (hst : st.SourceA C)
    (hp : st.popN n = some (ts, base)) :
    ResultSourceA C ts ∧ base.SourceA C := by
  induction n generalizing st base ts with
  | zero =>
      simp only [St.popN, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨ResultSourceA.nil C, hst⟩
  | succ n ih =>
      simp only [St.popN] at hp
      cases hn : st.popN n with
      | none => simp only [hn] at hp; contradiction
      | some pair =>
          obtain ⟨us, rest⟩ := pair
          simp only [hn] at hp
          cases hpop : rest.pop with
          | none => simp only [hpop] at hp; contradiction
          | some pair =>
              obtain ⟨t, rest'⟩ := pair
              simp only [hpop, Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              obtain ⟨hus, hrest⟩ := ih hst hn
              obtain ⟨ht, hrest'⟩ := hrest.pop hpop
              exact ⟨ResultSourceA.cons ht hus, hrest'⟩

theorem popEA_weaken {C : Context} {st st' : St} {t₁ t₂ : ValType}
    (htypes : SourceTypeCompleteA C) (hst : st.SourceA C)
    (ht₁ : Valtype_okA C t₁) (ht₂ : t₂.SourceA C)
    (hsub : Valtype_subA C t₁ t₂)
    (hp : st.popEA C t₁ = some st') : st.popEA C t₂ = some st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at hp ⊢
          exact hp
      | cons a rest =>
          simp only [St.popEA] at hp ⊢
          split at hp
          · rename_i ha₁
            have haSource : a.SourceA C := hst a (by simp)
            have ha₂ : decValtypeSubN C C.subtypeFuel a t₂ = true :=
              htypes.valtypeComplete haSource ht₂
                (Valtype_subA.trans ht₁ (decValtypeSubN_sound ha₁) hsub)
            change subOfA C a t₂ = true at ha₂
            rw [if_pos ha₂]
            exact hp
          · contradiction

/-- One-sided variant used when subsumption widens a source operand to an
internal semantic type.  The widened target need not itself carry source
provenance; semantic well-formedness is sufficient because the concrete
operand on the stack is source-provenant. -/
theorem popEA_weaken_to_valid {C : Context} {st st' : St} {t₁ t₂ : ValType}
    (htypes : SourceTypeCompleteA C) (hst : st.SourceA C)
    (ht₁ : Valtype_okA C t₁) (ht₂ : Valtype_okA C t₂)
    (hsub : Valtype_subA C t₁ t₂)
    (hp : st.popEA C t₁ = some st') : st.popEA C t₂ = some st' := by
  cases st with
  | mk poly vals =>
      cases vals with
      | nil =>
          cases poly <;> simp [St.popEA] at hp ⊢
          exact hp
      | cons a rest =>
          simp only [St.popEA] at hp ⊢
          split at hp
          · rename_i ha₁
            have haSource : a.SourceA C := hst a (by simp)
            have ha₂ : decValtypeSubN C C.subtypeFuel a t₂ = true :=
              htypes.valtypeCompleteLeft haSource ht₂
                (Valtype_subA.trans ht₁ (decValtypeSubN_sound ha₁) hsub)
            change subOfA C a t₂ = true at ha₂
            rw [if_pos ha₂]
            exact hp
          · contradiction

theorem popsA_weaken {C : Context} (htypes : SourceTypeCompleteA C) :
    ∀ {ts₁ ts₂ : List ValType} {st st' : St},
      st.SourceA C → Resulttype_okA C ts₁ → ResultSourceA C ts₂ →
      Resulttype_subA C ts₁ ts₂ →
      st.popsA C ts₁ = some st' → st.popsA C ts₂ = some st' := by
  intro ts₁
  induction ts₁ with
  | nil =>
      intro ts₂ st st' hst hok hsource hsub hp
      cases hsub with
      | mk hlen _ =>
          have : ts₂ = [] :=
            List.eq_nil_of_length_eq_zero (by simpa [SeqLen₂] using hlen.symm)
          subst ts₂
          exact hp
  | cons t₁ ts₁ ih =>
      intro ts₂ st st' hst hok hsource hsub hp
      cases ts₂ with
      | nil =>
          cases hsub with
          | mk hlen _ => simp [SeqLen₂] at hlen
      | cons t₂ ts₂ =>
          cases hok with
          | mk hok =>
              cases hsub with
              | mk hlen hall =>
                  simp only [St.popsA] at hp ⊢
                  cases hp₁ : st.popsA C ts₁ with
                  | none => simp only [hp₁] at hp; contradiction
                  | some s =>
                      simp only [hp₁] at hp
                      have htailOk : Resulttype_okA C ts₁ :=
                        .mk (fun u hu => hok u (by simp [hu]))
                      have htailSource : ResultSourceA C ts₂ :=
                        fun u hu => hsource u (by simp [hu])
                      have htailSub : Resulttype_subA C ts₁ ts₂ := by
                        refine .mk (by simpa [SeqLen₂] using Nat.succ.inj hlen) ?_
                        intro i a b ha hb
                        exact hall (i + 1) a b (by simpa using ha) (by simpa using hb)
                      have hp₂ : st.popsA C ts₂ = some s :=
                        ih hst htailOk htailSource htailSub hp₁
                      simp only [hp₂]
                      exact popEA_weaken htypes (hst.popsA hp₂) -- source of the tail state
                        (hok t₁ (by simp)) (hsource t₂ (by simp))
                        (hall 0 t₁ t₂ rfl rfl) hp

theorem popsA_weaken_to_valid {C : Context} (htypes : SourceTypeCompleteA C) :
    ∀ {ts₁ ts₂ : List ValType} {st st' : St},
      st.SourceA C → Resulttype_okA C ts₁ → Resulttype_okA C ts₂ →
      Resulttype_subA C ts₁ ts₂ →
      st.popsA C ts₁ = some st' → st.popsA C ts₂ = some st' := by
  intro ts₁
  induction ts₁ with
  | nil =>
      intro ts₂ st st' hst hok₁ hok₂ hsub hp
      cases hsub with
      | mk hlen _ =>
          have : ts₂ = [] :=
            List.eq_nil_of_length_eq_zero (by simpa [SeqLen₂] using hlen.symm)
          subst ts₂
          exact hp
  | cons t₁ ts₁ ih =>
      intro ts₂ st st' hst hok₁ hok₂ hsub hp
      cases ts₂ with
      | nil =>
          cases hsub with
          | mk hlen _ => simp [SeqLen₂] at hlen
      | cons t₂ ts₂ =>
          cases hok₁ with
          | mk hok₁All =>
              cases hok₂ with
              | mk hok₂All =>
                  cases hsub with
                  | mk hlen hall =>
                      simp only [St.popsA] at hp ⊢
                      cases hp₁ : st.popsA C ts₁ with
                      | none => simp only [hp₁] at hp; contradiction
                      | some s =>
                          simp only [hp₁] at hp
                          have htailOk₁ : Resulttype_okA C ts₁ :=
                            .mk (fun u hu => hok₁All u (by simp [hu]))
                          have htailOk₂ : Resulttype_okA C ts₂ :=
                            .mk (fun u hu => hok₂All u (by simp [hu]))
                          have htailSub : Resulttype_subA C ts₁ ts₂ := by
                            refine .mk (by
                              simpa [SeqLen₂] using Nat.succ.inj hlen) ?_
                            intro i a b ha hb
                            exact hall (i + 1) a b
                              (by simpa using ha) (by simpa using hb)
                          have hp₂ : st.popsA C ts₂ = some s :=
                            ih hst htailOk₁ htailOk₂ htailSub hp₁
                          simp only [hp₂]
                          exact popEA_weaken_to_valid htypes (hst.popsA hp₂)
                            (hok₁All t₁ (by simp)) (hok₂All t₂ (by simp))
                            (hall 0 t₁ t₂ rfl rfl) hp

theorem satA_weaken {C : Context} {st : St} {ts₁ ts₂ : List ValType}
    (htypes : SourceTypeCompleteA C) (hst : st.SourceA C)
    (hok : Resulttype_okA C ts₁) (hsource : ResultSourceA C ts₂)
    (hsub : Resulttype_subA C ts₁ ts₂)
    (hsat : St.SatA C st ts₁) : St.SatA C st ts₂ := by
  obtain ⟨base, hp, hempty⟩ := hsat
  exact ⟨base, popsA_weaken htypes hst hok hsource hsub hp, hempty⟩

theorem satA_weaken_to_valid {C : Context} {st : St}
    {ts₁ ts₂ : List ValType}
    (htypes : SourceTypeCompleteA C) (hst : st.SourceA C)
    (hok₁ : Resulttype_okA C ts₁) (hok₂ : Resulttype_okA C ts₂)
    (hsub : Resulttype_subA C ts₁ ts₂)
    (hsat : St.SatA C st ts₁) : St.SatA C st ts₂ := by
  obtain ⟨base, hp, hempty⟩ := hsat
  exact ⟨base,
    popsA_weaken_to_valid htypes hst hok₁ hok₂ hsub hp, hempty⟩

/-- Applying a checked instruction type preserves source provenance whenever
its result sequence is source-provenant.  This is the dynamic invariant used
by the source-restricted sequence completeness proof; it makes no semantic
claim about arbitrary literal result types. -/
theorem of_applyTypeA {C : Context} {st st' : St} {it : InstrType}
    (hst : st.SourceA C) (hcod : ResultSourceA C it.cod)
    (hrun : applyTypeA C st it = some st') : st'.SourceA C := by
  unfold applyTypeA at hrun
  cases hp : st.popsA C it.dom with
  | none => simp only [hp] at hrun; contradiction
  | some base =>
      simp only [hp, Option.some.injEq] at hrun
      subst st'
      exact (hst.popsA hp).pushs hcod

/-- The principal reference pop retains source provenance for both the
operand (when one was present) and the remaining stack.  Polymorphic
underflow returns no concrete reference and therefore needs no fabricated
source witness. -/
theorem popRef {C : Context} {st base : St} {rt? : Option RefType}
    (hst : st.SourceA C) (hp : st.popRef = some (rt?, base)) :
    base.SourceA C ∧ ∀ rt, rt? = some rt → rt.SourceA C := by
  unfold St.popRef at hp
  cases hpop : st.pop with
  | none => simp only [hpop] at hp; contradiction
  | some pair =>
      obtain ⟨t, rest⟩ := pair
      have hsrc := hst.pop hpop
      cases t with
      | num _ | vec _ => simp only [hpop] at hp; contradiction
      | bot =>
          simp only [hpop, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact ⟨hsrc.2, fun rt h => by cases h⟩
      | ref rt =>
          simp only [hpop, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact ⟨hsrc.2, fun u h => by
            injection h with h
            subst u
            exact hsrc.1⟩

end St.SourceA
end Validate

namespace Context

/-- Source provenance for every context component capable of contributing a
heap-bearing value to validation.  It deliberately mirrors `Context.ValidA`:
validity alone admits arbitrary literal `deftype` values, while this package
records membership in the checked source graph. -/
structure SourceA (C : Context) : Prop where
  types {x : TypeIdx} {dt : DefType} {ct : CompType} :
    C.types[x.val]? = some dt → Expand dt ct → ct.SourceA C
  funcs {x : FuncIdx} {dt : DefType} {ct : CompType} :
    C.funcs[x.val]? = some dt → Expand dt ct → ct.SourceA C
  funcHeap {x : FuncIdx} {dt : DefType} :
    C.funcs[x.val]? = some dt → (HeapType.use (.defd dt)).SourceA C
  tags {x : TagIdx} {jt : TagType} {dt : DefType} {dom : ValTypes} :
    C.tags[x.val]? = some jt → asDefType jt = some dt →
    Expand dt (.func dom .nil) → ResultSourceA C (ValTypes.toList dom)
  globals {x : GlobalIdx} {gt : GlobalType} :
    C.globals[x.val]? = some gt → gt.valtype.SourceA C
  tables {x : TableIdx} {tt : TableType} :
    C.tables[x.val]? = some tt → tt.elem.SourceA C
  elems {x : ElemIdx} {rt : RefType} :
    C.elems[x.val]? = some rt → rt.SourceA C
  locals {x : LocalIdx} {lt : LocalType} :
    C.locals[x.val]? = some lt → lt.valtype.SourceA C
  labels {x : LabelIdx} {ts : List ValType} :
    C.labels[x.val]? = some ts → ResultSourceA C ts
  ret {ts : List ValType} : C.ret = some ts → ResultSourceA C ts

namespace SourceA

theorem pushLabel {C : Context} {ts : List ValType} (hC : C.SourceA)
    (hts : ResultSourceA C ts) : (Context.pushLabel ts C).SourceA := by
  have htypes : C.types = (Context.pushLabel ts C).types := rfl
  have hsame : SameTypeEnv C (Context.pushLabel ts C) := by
    simp [SameTypeEnv, Context.pushLabel]
  constructor
  · intro x dt ct hx he
    exact (hC.types (by simpa [Context.pushLabel] using hx) he).of_types_eq
      htypes hsame.2
  · intro x dt ct hx he
    exact (hC.funcs (by simpa [Context.pushLabel] using hx) he).of_types_eq
      htypes hsame.2
  · intro x dt hx
    exact (hC.funcHeap (by simpa [Context.pushLabel] using hx)).of_types_eq
      htypes hsame.2
  · intro x jt dt dom hx hj he
    exact (hC.tags (by simpa [Context.pushLabel] using hx) hj he).transport
      hsame
  · intro x gt hx
    exact (hC.globals (by simpa [Context.pushLabel] using hx)).of_types_eq
      htypes hsame.2
  · intro x tt hx
    exact (hC.tables (by simpa [Context.pushLabel] using hx)).of_types_eq
      htypes hsame.2
  · intro x rt hx
    exact (hC.elems (by simpa [Context.pushLabel] using hx)).of_types_eq
      htypes hsame.2
  · intro x lt hx
    exact (hC.locals (by simpa [Context.pushLabel] using hx)).of_types_eq
      htypes hsame.2
  · intro x us hx
    cases hn : x.val with
    | zero =>
        have heq : us = ts := by
          have : some ts = some us := by
            simpa [Context.pushLabel, hn] using hx
          exact (Option.some.inj this).symm
        subst us
        exact hts.transport hsame
    | succ n =>
        let y : LabelIdx := ⟨n, by have hb := x.property; omega⟩
        exact (hC.labels (x := y)
          (by simpa [Context.pushLabel, hn, y] using hx)).transport
          hsame
  · intro us hx
    exact (hC.ret (by simpa [Context.pushLabel] using hx)).transport
      hsame

theorem setLocal {C : Context} {x : LocalIdx} {lt : LocalType}
    (hC : C.SourceA) (hx : C.locals[x.val]? = some lt) :
    (C.setLocal x ⟨.set, lt.valtype⟩).SourceA := by
  have htypes : C.types = (C.setLocal x ⟨.set, lt.valtype⟩).types := rfl
  have hsame : SameTypeEnv C (C.setLocal x ⟨.set, lt.valtype⟩) := by
    simp [SameTypeEnv, Context.setLocal]
  constructor
  · intro y dt ct hy he
    exact (hC.types (by simpa [Context.setLocal] using hy) he).of_types_eq
      htypes hsame.2
  · intro y dt ct hy he
    exact (hC.funcs (by simpa [Context.setLocal] using hy) he).of_types_eq
      htypes hsame.2
  · intro y dt hy
    exact (hC.funcHeap (by simpa [Context.setLocal] using hy)).of_types_eq
      htypes hsame.2
  · intro y jt dt dom hy hj he
    exact (hC.tags (by simpa [Context.setLocal] using hy) hj he).transport
      hsame
  · intro y gt hy
    exact (hC.globals (by simpa [Context.setLocal] using hy)).of_types_eq
      htypes hsame.2
  · intro y tt hy
    exact (hC.tables (by simpa [Context.setLocal] using hy)).of_types_eq
      htypes hsame.2
  · intro y rt hy
    exact (hC.elems (by simpa [Context.setLocal] using hy)).of_types_eq
      htypes hsame.2
  · intro y lty hy
    by_cases heq : y.val = x.val
    · have hyx : y = x := Subtype.ext heq
      subst y
      have hlt : x.val < C.locals.length :=
        (List.getElem?_eq_some_iff.mp hx).1
      have hlocal : lty = ⟨.set, lt.valtype⟩ := by
        have : some ⟨Init.set, lt.valtype⟩ = some lty := by
          simpa [Context.setLocal, List.getElem?_set_self hlt] using hy
        exact (Option.some.inj this).symm
      subst lty
      exact (hC.locals hx).of_types_eq htypes hsame.2
    · exact (hC.locals (x := y) (lt := lty) (by
          simpa [Context.setLocal,
            List.getElem?_set_ne (Ne.symm heq)] using hy)).of_types_eq
        htypes hsame.2
  · intro y us hy
    exact (hC.labels (by simpa [Context.setLocal] using hy)).transport
      hsame
  · intro us hy
    exact (hC.ret (by simpa [Context.setLocal] using hy)).transport
      hsame

theorem withLocals {C : Context} : ∀ {xs : List LocalIdx}
    {ts : List ValType}, C.SourceA → SeqLen₂ xs ts →
    SeqAll₂ (fun (x : LocalIdx) (t : ValType) =>
      ∃ ini : Init, C.locals[x.val]? = some ⟨ini, t⟩) xs ts →
    (Context.withLocals C xs (ts.map fun t => ⟨.set, t⟩)).SourceA
  | [], [], hC, _, _ => hC
  | [], _ :: _, _, hlen, _ => by simp [SeqLen₂] at hlen
  | _ :: _, [], _, hlen, _ => by simp [SeqLen₂] at hlen
  | x :: xs, t :: ts, hC, hlen, hall => by
      obtain ⟨ini, hx⟩ := hall 0 x t (by simp) (by simp)
      have htailLen : SeqLen₂ xs ts := by
        simp only [SeqLen₂, List.length_cons] at hlen ⊢
        omega
      have htail : SeqAll₂ (fun (y : LocalIdx) (u : ValType) =>
          ∃ ini : Init,
            (C.setLocal x ⟨.set, t⟩).locals[y.val]? = some ⟨ini, u⟩)
          xs ts := by
        intro j y u hy hu
        obtain ⟨iniY, hyC⟩ := hall (j + 1) y u
          (by simpa using hy) (by simpa using hu)
        by_cases heq : y.val = x.val
        · have hyx : y = x := Subtype.ext heq
          subst y
          have hlocalEq : LocalType.mk ini t = LocalType.mk iniY u :=
            Option.some.inj (hx.symm.trans hyC)
          injection hlocalEq with hini htu
          subst u
          refine ⟨.set, ?_⟩
          have hlt : x.val < C.locals.length :=
            (List.getElem?_eq_some_iff.mp hx).1
          simp [Context.setLocal, List.getElem?_set_self hlt]
        · exact ⟨iniY, by
            simpa [Context.setLocal,
              List.getElem?_set_ne (Ne.symm heq)] using hyC⟩
      simpa only [Context.withLocals, List.map_cons] using
        withLocals (hC.setLocal hx) htailLen htail

end SourceA
end Context

end WasmGemmGnaf.Wasm.Core
