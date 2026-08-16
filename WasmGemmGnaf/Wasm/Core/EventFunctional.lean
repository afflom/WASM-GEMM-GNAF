import WasmGemmGnaf.Wasm.Core.ReadFunctionalAll
import WasmGemmGnaf.Wasm.Core.PureFunctional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

theorem append3_eq_parts_of_outer_lengths {type : Type}
    {leftPrefix leftMiddle leftSuffix rightPrefix rightMiddle rightSuffix :
      List type}
    (h : leftPrefix ++ (leftMiddle ++ leftSuffix) =
      rightPrefix ++ (rightMiddle ++ rightSuffix))
    (hprefix : leftPrefix.length = rightPrefix.length)
    (hsuffix : leftSuffix.length = rightSuffix.length) :
    leftPrefix = rightPrefix ∧ leftMiddle = rightMiddle ∧
      leftSuffix = rightSuffix := by
  have hp : leftPrefix = rightPrefix := List.append_inj_left h hprefix
  subst rightPrefix
  have htail : leftMiddle ++ leftSuffix = rightMiddle ++ rightSuffix :=
    List.append_cancel_left h
  have hs : leftSuffix = rightSuffix :=
    List.append_inj_right' htail hsuffix
  subst rightSuffix
  exact ⟨rfl, List.append_cancel_right htail, rfl⟩

theorem vals_middle_suffix_eq_parts
    {leftValues rightValues : List Val}
    {leftMiddle leftSuffix rightMiddle rightSuffix : List AdminInstr}
    (h : vals leftValues ++ (leftMiddle ++ leftSuffix) =
      vals rightValues ++ (rightMiddle ++ rightSuffix))
    (hvalues : leftValues.length = rightValues.length)
    (hsuffix : leftSuffix.length = rightSuffix.length) :
    leftValues = rightValues ∧ leftMiddle = rightMiddle ∧
      leftSuffix = rightSuffix := by
  have hparts := append3_eq_parts_of_outer_lengths h
    (by simpa using hvalues) hsuffix
  exact ⟨vals_injective hparts.1, hparts.2⟩

theorem Ref.toAdmin_injective {left right : Ref}
    (h : left.toAdmin = right.toAdmin) : left = right := by
  have hv : Val.ref left = .ref right :=
    Val.toAdmin_injective (left := .ref left) (right := .ref right) h
  injection hv

@[simp] theorem Ref.toAdmin_eq_iff {left right : Ref} :
    left.toAdmin = right.toAdmin ↔ left = right :=
  ⟨Ref.toAdmin_injective, congrArg Ref.toAdmin⟩

@[simp] theorem Inn.toNumType_eq_iff {left right : Inn} :
    left.toNumType = right.toNumType ↔ left = right :=
  ⟨Inn.toNumType_injective, congrArg Inn.toNumType⟩

theorem constInn_injective {inn : Inn} {left right : InnLit inn}
    (h : constInn inn left = constInn inn right) : left = right := by
  cases inn <;> simp_all [constInn, innLitToNum]

theorem State.store_eq_of_eq {left right : State} (h : left = right) :
    left.store = right.store := congrArg State.store h

theorem State.frame_eq_of_eq {left right : State} (h : left = right) :
    left.frame = right.frame := congrArg State.frame h

theorem Option.some_output_functional {type : Type} {input : Option type}
    {left right : type} (hl : input = some left) (hr : input = some right) :
    left = right := Option.some.inj (hl.symm.trans hr)

theorem vstoreLane_write_functional
    {state leftState rightState : State} {att : AddrType}
    {address : AddrLit att} {literal : V128Lit} {size : Sz}
    {memory : MemIdx} {argument : MemArg} {index : LaneIdx}
    {leftShape rightShape : Shape}
    {leftLane : Lane_ leftShape.lane} {rightLane : Lane_ rightShape.lane}
    {leftBits : IN leftShape.lane.size} {rightBits : IN rightShape.lane.size}
    (hleftWrite : state.withMem memory
      (address.val + argument.offset.val) (size.toNat / 8)
      (releasedNumerics.ibytes_ leftShape.lane.size leftBits) =
        some leftState)
    (hleftSize : leftShape.lane.size = size.toNat)
    (hleftDim : leftShape.dim.toNat = 128 / size.toNat)
    (hleftLane : (releasedNumerics.lanes_ leftShape literal)[index.val]? =
      some leftLane)
    (hleftBits : laneToIN leftShape.lane leftLane = some leftBits)
    (hrightWrite : state.withMem memory
      (address.val + argument.offset.val) (size.toNat / 8)
      (releasedNumerics.ibytes_ rightShape.lane.size rightBits) =
        some rightState)
    (hrightSize : rightShape.lane.size = size.toNat)
    (hrightDim : rightShape.dim.toNat = 128 / size.toNat)
    (hrightLane : (releasedNumerics.lanes_ rightShape literal)[index.val]? =
      some rightLane)
    (hrightBits : laneToIN rightShape.lane rightLane = some rightBits) :
    leftState = rightState := by
  have hleftShape := shape_eq_storeLaneShape_of_laneToIN
    hleftSize hleftDim hleftBits
  have hrightShape := shape_eq_storeLaneShape_of_laneToIN
    hrightSize hrightDim hrightBits
  subst leftShape
  subst rightShape
  have hlane : leftLane = rightLane :=
    Option.some.inj (hleftLane.symm.trans hrightLane)
  subst rightLane
  have hbits : leftBits = rightBits :=
    Option.some.inj (hleftBits.symm.trans hrightBits)
  subst rightBits
  exact Option.some.inj (hleftWrite.symm.trans hrightWrite)

theorem StepA.unindexSourceEventTarget
    {source : Config} {event : Event} {target : Config}
    (h : StepA source event target) :
    ∃ unindexedSource unindexedEvent unindexedTarget,
      unindexedSource = source ∧ unindexedEvent = event ∧
        unindexedTarget = target ∧
          StepA unindexedSource unindexedEvent unindexedTarget := by
  exact ⟨source, event, target, rfl, rfl, rfl, h⟩

/-- A fixed labelled Core source and event determine at most one target. -/
theorem StepA.target_functional
    {source : Config} {event : Event} {left right : Config}
    (hl : StepA source event left) (hr : StepA source event right) :
    left = right := by
  induction hl generalizing right <;>
    obtain ⟨rightSource, rightEvent, rightTarget, hrightSource, hrightEvent,
      hrightTarget, rightProof⟩ := hr.unindexSourceEventTarget <;>
    rw [← hrightTarget] <;>
    clear hr hrightTarget right <;>
    cases rightProof <;>
    simp_all
  all_goals try solve_by_elim
  case pure.pure =>
    apply pureSuccessors_event_target_functional <;> assumption
  case read.read =>
    apply Step_readA.target_functional <;> assumption
  case ctxtInstrs.ctxtInstrs =>
    have hparts := vals_middle_suffix_eq_parts hrightSource.2
      hrightEvent.1 hrightEvent.2.1
    simp_all
    solve_by_elim
  case ctxtFrame.ctxtFrame =>
    rename_i sLeft sLeft' fOuterLeft fInnerLeft fTargetLeft nLeft
      isLeft isLeft' eventLeft hstepLeft sRight sRight' fOuterRight
      fInnerRight fTargetRight nRight isRight isRight' eventRight ih hstepRight
    obtain ⟨hstate, hinstructions⟩ := ih _ _ hstepRight
    injection hstate with hstore hframe
    exact ⟨hstore, hframe, hinstructions⟩
  case tableGrowFail.tableGrowFail =>
    cases hrightSource.2.2.1.1
    rfl
  case memoryGrowFail.memoryGrowFail =>
    cases hrightSource.2.1.1
    rfl
  case storeNumVal.storeNumVal =>
    obtain ⟨htype, hvalue⟩ := hrightSource.2.2.1
    cases htype
    cases hvalue
    simp_all
  case storePackVal.storePackVal =>
    obtain ⟨_, _, hconst, hinn, _, _, _⟩ := hrightSource
    cases hinn
    have hvalue := constInn_injective hconst
    cases hvalue
    simp_all
    subst_vars
    apply Option.some_output_functional <;> assumption
  case vstoreLaneVal.vstoreLaneVal =>
    apply vstoreLane_write_functional <;> assumption

end WasmGemmGnaf.Wasm.Core.Exec
