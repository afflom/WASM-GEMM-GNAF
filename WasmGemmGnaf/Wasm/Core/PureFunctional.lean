import WasmGemmGnaf.Wasm.Core.Successors

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

/-! ## Event-key uniqueness for executable pure successors

`pureSuccessors` records the selected result index in each `PureEvent`.  The
event projection is therefore duplicate-free even when the numerical result
list itself contains repeated values. -/

private theorem single_events_nodup (r : PureRule) (is' : List AdminInstr) :
    ((single r is').map Prod.fst).Nodup := by
  simp [single]

private theorem choices_events_nodup {α : Type} (r : PureRule) (l : List α)
    (g : α → List AdminInstr) : ((choices r l g).map Prod.fst).Nodup := by
  unfold choices
  rw [List.map_map]
  refine List.Pairwise.map _ ?_ (withIndex_pairwise_snd l 0)
  intro p q hpq
  simp only [Function.comp_apply, ne_eq]
  intro he
  exact absurd (congrArg PureEvent.choice he) hpq

private theorem target_eq_of_event_keys_nodup
    {α β : Type} {entries : List (α × β)} {event : α} {left right : β}
    (hn : (entries.map Prod.fst).Nodup)
    (hl : (event, left) ∈ entries) (hr : (event, right) ∈ entries) :
    left = right := by
  induction entries with
  | nil => simp at hl
  | cons head tail ih =>
      rcases head with ⟨headEvent, headTarget⟩
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases hn with ⟨hhead, htail⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hl hr
      rcases hl with ⟨he, ht⟩ | hl
      · rcases hr with ⟨he', ht'⟩ | hr
        · simp [ht, ht']
        · exfalso
          apply hhead
          exact List.mem_map.mpr ⟨(event, right), hr, by simp [he]⟩
      · rcases hr with ⟨he', ht'⟩ | hr
        · exfalso
          apply hhead
          exact List.mem_map.mpr ⟨(event, left), hl, by simp [he']⟩
        · exact ih htail hl hr

private theorem pureOfInstr_events_nodup
    (Nm : Numerics) (vs : List Val) (i : Instr) :
    ((pureOfInstr Nm vs i).map Prod.fst).Nodup := by
  unfold pureOfInstr
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_events_nodup _ _
    | exact choices_events_nodup _ _ _

private theorem pureOfLabel_events_nodup
    (n : Nat) (cont body : List AdminInstr) :
    ((pureOfLabel n cont body).map Prod.fst).Nodup := by
  unfold pureOfLabel
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_events_nodup _ _

private theorem pureOfFrame_events_nodup (n : Nat) (body : List AdminInstr) :
    ((pureOfFrame n body).map Prod.fst).Nodup := by
  unfold pureOfFrame
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_events_nodup _ _

private theorem pureOfHandler_events_nodup (body : List AdminInstr) :
    ((pureOfHandler body).map Prod.fst).Nodup := by
  unfold pureOfHandler
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_events_nodup _ _

private theorem pureOfSplit_events_nodup
    (Nm : Numerics) (vs : List Val) (rest : List AdminInstr) :
    ((pureOfSplit Nm vs rest).map Prod.fst).Nodup := by
  unfold pureOfSplit
  repeat' split
  all_goals first
    | exact List.nodup_nil
    | exact single_events_nodup _ _
    | exact pureOfInstr_events_nodup _ _ _
    | exact pureOfLabel_events_nodup _ _ _
    | exact pureOfFrame_events_nodup _ _
    | exact pureOfHandler_events_nodup _

/-- No two entries in `pureSuccessors` use the same event key. -/
theorem pureSuccessors_events_nodup (Nm : Numerics) (is : List AdminInstr) :
    ((pureSuccessors Nm is).map Prod.fst).Nodup :=
  pureOfSplit_events_nodup Nm _ _

/-- A fixed executable pure-successor event determines its target. -/
theorem pureSuccessors_event_target_functional
    {Nm : Numerics} {source left right : List AdminInstr} {event : PureEvent}
    (hl : (event, left) ∈ pureSuccessors Nm source)
    (hr : (event, right) ∈ pureSuccessors Nm source) : left = right :=
  target_eq_of_event_keys_nodup (pureSuccessors_events_nodup Nm source) hl hr

end WasmGemmGnaf.Wasm.Core.Exec
