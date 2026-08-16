import WasmGemmGnaf.Wasm.Core.ValidateHeapShapes

set_option autoImplicit false
set_option maxRecDepth 12000

namespace WasmGemmGnaf.Wasm.Core

def AbsUseClassA (a b : AbsHeapType) : Prop :=
  a = .bot ∨ (a = .none ∧ (b = .struct ∨ b = .array)) ∨
    (a = .nofunc ∧ b = .func)

private theorem AbsUseClassA.of_left_sub {a m b : AbsHeapType}
    (ham : decAbsSub a m = true) (hmb : AbsUseClassA m b) :
    AbsUseClassA a b := by
  cases a <;> cases m <;> cases b <;>
    simp_all [AbsUseClassA, decAbsSub]

private def ConcreteAbsShapeA (a : AbsHeapType) : Prop :=
  a = .struct ∨ a = .array ∨ a = .func

private theorem GoodHeapShapeA.concrete_of_use {C : Context} {tu : TypeUse}
    {a : AbsHeapType} (h : GoodHeapShapeA C (.use tu) a) :
    ConcreteAbsShapeA a := by
  cases h with
  | @use _ fin sups ct hu hall =>
      cases ct <;> simp [ConcreteAbsShapeA, CompType.absShape]

private theorem AbsUseClassA.not_after_concrete {a m b : AbsHeapType}
    (ha : ConcreteAbsShapeA a) (ham : decAbsSub a m = true)
    (hmb : AbsUseClassA m b) : False := by
  cases a <;> cases m <;> cases b <;>
    simp_all [ConcreteAbsShapeA, AbsUseClassA, decAbsSub]

private def HeapShapeFlowA (C : Context) (h₁ h₂ : HeapType) : Prop :=
  C.ValidHeapShapesA →
    ((∀ {a : AbsHeapType} {tu : TypeUse} {b : AbsHeapType},
      h₁ = .abs a → h₂ = .use tu → GoodHeapShapeA C h₂ b →
      AbsUseClassA a b) ∧
    (∀ {tu₁ tu₂ : TypeUse} {a b : AbsHeapType},
      h₁ = .use tu₁ → h₂ = .use tu₂ →
      GoodHeapShapeA C h₁ a → GoodHeapShapeA C h₂ b → a = b))

private theorem Heaptype_subA.shapeFlow {C : Context} {h₁ h₂ : HeapType}
    (h : Heaptype_subA C h₁ h₂) : HeapShapeFlowA C h₁ h₂ := by
  apply Heaptype_subA.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ => True)
    (motive_14 := fun C h₁ h₂ _ => HeapShapeFlowA C h₁ h₂)
    (motive_15 := fun _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ => True)
    (motive_20 := fun _ _ _ _ => True)
    (motive_21 := fun C d₁ d₂ _ =>
      C.ValidHeapShapesA → ∀ {a b : AbsHeapType},
        GoodHeapShapeA C (.use (.defd d₁)) a →
        GoodHeapShapeA C (.use (.defd d₂)) b → a = b)
  all_goals first | (intros <;> trivial) | skip
  all_goals try simp only [HeapShapeFlowA] at *
  case refl =>
      intro D ht henv
      constructor
      · intro a tu b hleft hright
        rw [hleft] at hright
        contradiction
      · intro tu₁ tu₂ a b hleft hright ha hb
        exact ha.unique hb
  case trans =>
      intro D ht₁ ht₂ mid hok hleft hright ihok ihleft ihrigh henv
      constructor
      · intro a tu b heq₁ heq₂ hb
        subst ht₁
        subst ht₂
        cases mid with
        | abs m =>
            obtain ⟨ihr_abs, ihr_use⟩ := ihrigh henv
            have hmb := ihr_abs (a := m) (tu := tu) (b := b)
              rfl rfl hb
            have ham := hleft.goodShape henv
              (GoodHeapShapeA.abs a) (GoodHeapShapeA.abs m)
            exact hmb.of_left_sub ham
        | use u =>
            obtain ⟨m, hm⟩ := henv hok
            obtain ⟨ihl_abs, ihl_use⟩ := ihleft henv
            obtain ⟨ihr_abs, ihr_use⟩ := ihrigh henv
            have ham := ihl_abs (a := a) (tu := u) (b := m)
              rfl rfl hm
            have hmb := ihr_use (tu₁ := u) (tu₂ := tu)
              rfl rfl hm hb
            subst b
            exact ham
      · intro tu₁ tu₂ a b heq₁ heq₂ ha hb
        subst ht₁
        subst ht₂
        cases mid with
        | abs m =>
            have ham := hleft.goodShape henv ha (GoodHeapShapeA.abs m)
            obtain ⟨ihr_abs, ihr_use⟩ := ihrigh henv
            have hmb := ihr_abs (a := m) (tu := tu₂) (b := b)
              rfl rfl hb
            exact False.elim (hmb.not_after_concrete ha.concrete_of_use ham)
        | use u =>
            obtain ⟨m, hm⟩ := henv hok
            obtain ⟨ihl_abs, ihl_use⟩ := ihleft henv
            obtain ⟨ihr_abs, ihr_use⟩ := ihrigh henv
            exact (ihl_use (tu₁ := tu₁) (tu₂ := u)
              rfl rfl ha hm).trans (ihr_use
                (tu₁ := u) (tu₂ := tu₂) rfl rfl hm hb)
  case eq_any =>
      intro D henv
      constructor <;> intros <;> contradiction
  case i31_eq =>
      intro D henv
      constructor <;> intros <;> contradiction
  case struct_eq =>
      intro D henv
      constructor <;> intros <;> contradiction
  case array_eq =>
      intro D henv
      constructor <;> intros <;> contradiction
  case struct =>
      intro D dt fts hexpand henv
      constructor <;> intros <;> contradiction
  case array =>
      intro D dt ft hexpand henv
      constructor <;> intros <;> contradiction
  case func =>
      intro D dt dom cod hexpand henv
      constructor <;> intros <;> contradiction
  case def_ =>
      intro D d₁ d₂ hd ihd henv
      constructor
      · intro a tu b hleft
        contradiction
      · intro tu₁ tu₂ a b hleft hright ha hb
        have htu₁ : .defd d₁ = tu₁ := by injection hleft
        have htu₂ : .defd d₂ = tu₂ := by injection hright
        subst tu₁
        subst tu₂
        exact ihd henv ha hb
  case typeidx_l =>
      intro D x dt ht hx hs ihs henv
      constructor
      · intro a tu b hleft
        contradiction
      · intro tu₁ tu₂ a b hleft hright ha hb
        have htu₁ : .idx x = tu₁ := by injection hleft
        subst tu₁
        have ih := ihs henv
        exact ih.2 (tu₁ := .defd dt) (tu₂ := tu₂)
          rfl hright (ha.of_idx_lookup hx) hb
  case typeidx_r =>
      intro D ht x dt hx hs ihs henv
      constructor
      · intro a tu b hleft hright hb
        have htu : .idx x = tu := by injection hright
        subst tu
        have ih := ihs henv
        exact ih.1 (tu := .defd dt) hleft rfl (hb.of_idx_lookup hx)
      · intro tu₁ tu₂ a b hleft hright ha hb
        have htu₂ : .idx x = tu₂ := by injection hright
        subst tu₂
        have ih := ihs henv
        exact ih.2 (tu₁ := tu₁) (tu₂ := .defd dt)
          hleft rfl ha (hb.of_idx_lookup hx)
  case rec_ =>
      intro D i j fin sups ct tu hrec hget henv
      constructor
      · intro a u b hleft
        contradiction
      · intro tu₁ tu₂ a b hleft hright ha hb
        have htu₁ : .recu i = tu₁ := by injection hleft
        have htu₂ : tu = tu₂ := by injection hright
        subst tu₁
        subst tu₂
        cases ha with
        | @use _ fin' sups' ct' hu hall =>
            simp only [Context.unrollHt, hrec] at hu
            have heq : SubType.sub fin sups ct =
                SubType.sub fin' sups' ct' := Option.some.inj hu
            injection heq with hfin hsups hct
            subst fin' sups' ct'
            have hm : tu ∈ TypeUses.toList sups := List.mem_of_getElem? hget
            exact (hall tu hm).unique hb
  case rec_struct =>
      intro D i fin sups fts hrec henv
      constructor <;> intros <;> contradiction
  case rec_array =>
      intro D i fin sups ft hrec henv
      constructor <;> intros <;> contradiction
  case rec_func =>
      intro D i fin sups dom cod hrec henv
      constructor <;> intros <;> contradiction
  case none_ =>
      intro D ht hne hs ihs henv
      constructor
      · intro a tu b hleft hright hb
        have ha : .none = a := by injection hleft
        subst a
        subst ht
        have hba := hs.goodShape henv hb (GoodHeapShapeA.abs .any)
        cases hb with
        | @use _ fin sups ct hu hall =>
            cases ct <;> simp_all [AbsUseClassA, decAbsSub, CompType.absShape]
      · intro tu₁ tu₂ a b hleft
        contradiction
  case nofunc =>
      intro D ht hne hs ihs henv
      constructor
      · intro a tu b hleft hright hb
        have ha : .nofunc = a := by injection hleft
        subst a
        subst ht
        have hbf := hs.goodShape henv hb (GoodHeapShapeA.abs .func)
        cases hb with
        | @use _ fin sups ct hu hall =>
            cases ct <;> simp_all [AbsUseClassA, decAbsSub, CompType.absShape]
      · intro tu₁ tu₂ a b hleft
        contradiction
  case noexn =>
      intro D ht hne hs ihs henv
      constructor
      · intro a tu b hleft hright hb
        subst ht
        have hbe := hs.goodShape henv hb (GoodHeapShapeA.abs .exn)
        cases hb with
        | @use _ fin sups ct hu hall =>
            cases ct <;> simp_all [decAbsSub, CompType.absShape]
      · intro tu₁ tu₂ a b hleft
        contradiction
  case noextern =>
      intro D ht hne hs ihs henv
      constructor
      · intro a tu b hleft hright hb
        subst ht
        have hbe := hs.goodShape henv hb (GoodHeapShapeA.abs .extern)
        cases hb with
        | @use _ fin sups ct hu hall =>
            cases ct <;> simp_all [decAbsSub, CompType.absShape]
      · intro tu₁ tu₂ a b hleft
        contradiction
  case bot =>
      intro D ht henv
      constructor
      · intro a tu b hleft hright hb
        exact Or.inl (by injection hleft with h; exact h.symm)
      · intro tu₁ tu₂ a b hleft
        contradiction
  case refl =>
      intro D d₁ d₂ heq henv a b ha hb
      have hh : D.heapEq (.use (.defd d₁)) (.use (.defd d₂)) = true := by
        simp [Context.heapEq, Context.normHeapType, heq]
      have hs := Context.typeuseShape_eq_of_heapEq hh
      have ha' := ha.typeuseShape (fun i h => by cases h)
      have hb' := hb.typeuseShape (fun i h => by cases h)
      exact Option.some.inj (ha'.symm.trans (hs.trans hb'))
  case super =>
      intro D d₁ d₂ fin sups ct i tu hunroll hget htail ihtail
        henv a b ha hb
      cases ha with
      | @use _ fin' sups' ct' hu hall =>
          simp only [Context.unrollHt] at hu
          rw [hunroll] at hu
          have heq : SubType.sub fin sups ct =
              SubType.sub fin' sups' ct' := Option.some.inj hu
          injection heq with hfin hsups hct
          subst fin' sups' ct'
          have hm : _ ∈ TypeUses.toList sups := List.mem_of_getElem? hget
          have iht := ihtail henv
          exact iht.2 rfl rfl (hall _ hm) hb

theorem Heaptype_subA.absUseClass {C : Context} {h₁ h₂ : HeapType}
    (h : Heaptype_subA C h₁ h₂) (henv : C.ValidHeapShapesA)
    {a : AbsHeapType} {tu : TypeUse} {b : AbsHeapType}
    (hleft : h₁ = .abs a) (hright : h₂ = .use tu)
    (hb : GoodHeapShapeA C h₂ b) : AbsUseClassA a b :=
  (h.shapeFlow henv).1 hleft hright hb

theorem Heaptype_subA.useShape_eq {C : Context} {h₁ h₂ : HeapType}
    (h : Heaptype_subA C h₁ h₂) (henv : C.ValidHeapShapesA)
    {tu₁ tu₂ : TypeUse} {a b : AbsHeapType}
    (hleft : h₁ = .use tu₁) (hright : h₂ = .use tu₂)
    (ha : GoodHeapShapeA C h₁ a) (hb : GoodHeapShapeA C h₂ b) :
    a = b :=
  (h.shapeFlow henv).2 hleft hright ha hb

end WasmGemmGnaf.Wasm.Core
