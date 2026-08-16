import WasmGemmGnaf.Wasm.Core.CompleteSuccessors
import Lean.Elab.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- An opaque proof snapshot used only by the elaborator below.  The wrapper lets
the first simplification pass normalize constructor indices without consuming the
byte and arithmetic equalities that establish uniqueness of decoded results. -/
structure EqSnapshot {type : Type} (left right : type) : Prop where
  proof : left = right

open Lean Meta Elab Tactic in
elab "snapshot_equalities" : tactic => do
  let goals ← getGoals
  let mut newGoals := []
  for originalGoal in goals do
    let goal ← originalGoal.withContext do
      let declarations := (← getLCtx).decls.toList
      let rec visit (goal : MVarId) : List LocalDecl → MetaM MVarId
        | [] => pure goal
        | declaration :: rest => do
            let mut nextGoal := goal
            unless declaration.isImplementationDetail do
              let type ← whnf declaration.type
              if type.isAppOfArity ``Eq 3 then
                let arguments := type.getAppArgs
                let valueType ← whnf (← inferType arguments[1]!)
                unless valueType.isAppOf ``Option ||
                    declaration.userName == `sourcesEqual ||
                    declaration.userName == `splitSourcesEqual do
                  let savedType ←
                    mkAppM ``EqSnapshot #[arguments[1]!, arguments[2]!]
                  let proof ← mkAppM ``EqSnapshot.mk #[declaration.toExpr]
                  let (_, notedGoal) ← nextGoal.note `_savedEq proof (some savedType)
                  nextGoal := notedGoal
                  try
                    nextGoal ← nextGoal.clear declaration.fvarId
                  catch _ => pure ()
            visit nextGoal rest
      visit originalGoal (declarations.filterMap id)
    newGoals := newGoals ++ [goal]
  setGoals newGoals

open Lean Meta Elab Tactic in
elab "restore_equalities" : tactic => do
  let goals ← getGoals
  let mut newGoals := []
  for originalGoal in goals do
    let goal ← originalGoal.withContext do
      let declarations := (← getLCtx).decls.toList
      let rec visit (goal : MVarId) : List LocalDecl → MetaM MVarId
        | [] => pure goal
        | declaration :: rest => do
            let mut nextGoal := goal
            unless declaration.isImplementationDetail do
              let type ← whnf declaration.type
              if type.isAppOfArity ``EqSnapshot 3 then
                let proof ← mkAppM ``EqSnapshot.proof #[declaration.toExpr]
                let (_, notedGoal) ← nextGoal.note `_restoredEq proof none
                nextGoal := notedGoal
            visit nextGoal rest
      visit originalGoal (declarations.filterMap id)
    newGoals := newGoals ++ [goal]
  setGoals newGoals

theorem nbytes_injective_of_wf {type : NumType}
    {left right : Num_ type}
    (hleft : ByteSolvedNumWfFor (authority := amendedExecutionAuthority)
      type left)
    (hright : ByteSolvedNumWfFor (authority := amendedExecutionAuthority)
      type right)
    (hbytes : releasedNumerics.nbytes_ type left =
      releasedNumerics.nbytes_ type right) : left = right := by
  have leftDecoded := numOfBytes?_nbytes_complete left hleft
  have rightDecoded := numOfBytes?_nbytes_complete right hright
  rw [hbytes] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

theorem ibytes_injective {width : Nat} {left right : IN width}
    (hmultiple : 8 * (width / 8) = width)
    (hbytes : releasedNumerics.ibytes_ width left =
      releasedNumerics.ibytes_ width right) : left = right := by
  have leftDecoded := ofNatWrap_leNat_ibytes left hmultiple
  have rightDecoded := ofNatWrap_leNat_ibytes right hmultiple
  rw [hbytes] at leftDecoded
  exact leftDecoded.symm.trans rightDecoded

@[simp] theorem ibytes_sz_eq_iff {size : Sz}
    {left right : IN size.toNat} :
    releasedNumerics.ibytes_ size.toNat left =
        releasedNumerics.ibytes_ size.toNat right ↔ left = right := by
  constructor
  · apply ibytes_injective
    cases size <;> decide
  · exact congrArg (releasedNumerics.ibytes_ size.toNat)

theorem loadPack_output_injective {inn : Inn} {size : Sz} {signed : Sx}
    {left right : IN size.toNat} {leftOutput rightOutput : InnLit inn}
    {bytes : List Byte}
    (hleftOutput : releasedNumerics.extend__ size.toNat inn.size signed left =
      leftOutput)
    (hrightOutput : releasedNumerics.extend__ size.toNat inn.size signed right =
      rightOutput)
    (hleftBytes : releasedNumerics.ibytes_ size.toNat left = bytes)
    (hrightBytes : releasedNumerics.ibytes_ size.toNat right = bytes) :
    constInn inn leftOutput = constInn inn rightOutput := by
  have hmultiple : 8 * (size.toNat / 8) = size.toNat := by
    cases size <;> decide
  have hinput : left = right :=
    ibytes_injective hmultiple (hleftBytes.trans hrightBytes.symm)
  subst right
  have houtput : leftOutput = rightOutput :=
    hleftOutput.symm.trans hrightOutput
  exact congrArg (constInn inn) houtput

@[simp] theorem in_val_eq_iff {width : Nat} {left right : IN width} :
    left.val = right.val ↔ left = right := by
  constructor
  · exact Subtype.ext
  · intro h
    exact congrArg Subtype.val h

theorem vbytes_v128_injective {left right : V128Lit}
    (hbytes : releasedNumerics.vbytes_ .v128 left =
      releasedNumerics.vbytes_ .v128 right) : left = right := by
  have leftDecoded := ofNatWrap_leNat_vbytes_v128 left
  have rightDecoded := ofNatWrap_leNat_vbytes_v128 right
  rw [hbytes] at leftDecoded
  exact leftDecoded.symm.trans rightDecoded

theorem Dim.toNat_injective {left right : Dim}
    (h : left.toNat = right.toNat) : left = right := by
  cases left <;> cases right <;> simp_all [Dim.toNat]

theorem LaneType.eq_of_size_of_inToLane_some
    {left right : LaneType} {leftInput : IN left.size}
    {rightInput : IN right.size} {leftLane : Lane_ left}
    {rightLane : Lane_ right}
    (hsize : left.size = right.size)
    (hleft : inToLane left leftInput = some leftLane)
    (hright : inToLane right rightInput = some rightLane) : left = right := by
  cases left with
  | num leftNum =>
      cases right with
      | num rightNum =>
          cases leftNum <;> cases rightNum <;>
            simp_all [LaneType.size, NumType.size, inToLane]
      | pack rightPack =>
          cases leftNum <;> cases rightPack <;>
            simp_all [LaneType.size, NumType.size, PackType.size, inToLane]
  | pack leftPack =>
      cases right with
      | num rightNum =>
          cases leftPack <;> cases rightNum <;>
            simp_all [LaneType.size, NumType.size, PackType.size, inToLane]
      | pack rightPack =>
          cases leftPack <;> cases rightPack <;>
            simp_all [LaneType.size, PackType.size, inToLane]

theorem Shape.eq_of_size_dim_inToLane_some
    {left right : Shape} {leftInput : IN left.lane.size}
    {rightInput : IN right.lane.size} {leftLane : Lane_ left.lane}
    {rightLane : Lane_ right.lane}
    (hsize : left.lane.size = right.lane.size)
    (hdim : left.dim.toNat = right.dim.toNat)
    (hleft : inToLane left.lane leftInput = some leftLane)
    (hright : inToLane right.lane rightInput = some rightLane) : left = right := by
  cases left with
  | mk leftLaneType leftDim =>
      cases right with
      | mk rightLaneType rightDim =>
          have hlane : leftLaneType = rightLaneType :=
            LaneType.eq_of_size_of_inToLane_some hsize hleft hright
          have hdimension : leftDim = rightDim := Dim.toNat_injective hdim
          subst rightLaneType
          subst rightDim
          rfl

theorem vloadSplat_output_injective {size : Sz} {leftShape rightShape : Shape}
    {leftInput : IN leftShape.lane.size} {rightInput : IN rightShape.lane.size}
    {leftLane : Lane_ leftShape.lane} {rightLane : Lane_ rightShape.lane}
    {leftOutput rightOutput : V128Lit} {bytes : List Byte}
    (hleftOutput : releasedNumerics.inv_lanes_ leftShape
      (List.replicate (128 / size.toNat) leftLane) = leftOutput)
    (hrightOutput : releasedNumerics.inv_lanes_ rightShape
      (List.replicate (128 / size.toNat) rightLane) = rightOutput)
    (hleftLane : inToLane leftShape.lane leftInput = some leftLane)
    (hrightLane : inToLane rightShape.lane rightInput = some rightLane)
    (hleftSize : leftShape.lane.size = size.toNat)
    (hrightSize : rightShape.lane.size = size.toNat)
    (hleftDim : leftShape.dim.toNat = 128 / size.toNat)
    (hrightDim : rightShape.dim.toNat = 128 / size.toNat)
    (hleftBytes : releasedNumerics.ibytes_ leftShape.lane.size leftInput = bytes)
    (hrightBytes : releasedNumerics.ibytes_ rightShape.lane.size rightInput = bytes) :
    leftOutput = rightOutput := by
  have hshape : leftShape = rightShape :=
    Shape.eq_of_size_dim_inToLane_some
      (hleftSize.trans hrightSize.symm) (hleftDim.trans hrightDim.symm)
      hleftLane hrightLane
  subst rightShape
  have hmultiple : 8 * (leftShape.lane.size / 8) = leftShape.lane.size := by
    rw [hleftSize]
    cases size <;> decide
  have hinput : leftInput = rightInput :=
    ibytes_injective hmultiple (hleftBytes.trans hrightBytes.symm)
  subst rightInput
  have hlane : leftLane = rightLane :=
    Option.some.inj (hleftLane.symm.trans hrightLane)
  subst rightLane
  exact hleftOutput.symm.trans hrightOutput

theorem vloadZero_output_injective {size : Sz}
    {leftInput rightInput : IN size.toNat}
    {leftOutput rightOutput : V128Lit} {bytes : List Byte}
    (hleftOutput : releasedNumerics.extend__ size.toNat 128 .u leftInput =
      leftOutput)
    (hrightOutput : releasedNumerics.extend__ size.toNat 128 .u rightInput =
      rightOutput)
    (hleftBytes : releasedNumerics.ibytes_ size.toNat leftInput = bytes)
    (hrightBytes : releasedNumerics.ibytes_ size.toNat rightInput = bytes) :
    leftOutput = rightOutput := by
  have hmultiple : 8 * (size.toNat / 8) = size.toNat := by
    cases size <;> decide
  have hinput : leftInput = rightInput :=
    ibytes_injective hmultiple (hleftBytes.trans hrightBytes.symm)
  subst rightInput
  exact hleftOutput.symm.trans hrightOutput

theorem vloadLane_output_injective {size : Sz} {base : V128Lit}
    {laneIndex : LaneIdx} {leftShape rightShape : Shape}
    {leftInput : IN leftShape.lane.size} {rightInput : IN rightShape.lane.size}
    {leftLane : Lane_ leftShape.lane} {rightLane : Lane_ rightShape.lane}
    {leftLanes : List (Lane_ leftShape.lane)}
    {rightLanes : List (Lane_ rightShape.lane)}
    {leftOutput rightOutput : V128Lit} {bytes : List Byte}
    (hleftOutput : releasedNumerics.inv_lanes_ leftShape leftLanes = leftOutput)
    (hrightOutput : releasedNumerics.inv_lanes_ rightShape rightLanes = rightOutput)
    (hleftSet : setAt? (releasedNumerics.lanes_ leftShape base)
      laneIndex.val leftLane = some leftLanes)
    (hrightSet : setAt? (releasedNumerics.lanes_ rightShape base)
      laneIndex.val rightLane = some rightLanes)
    (hleftLane : inToLane leftShape.lane leftInput = some leftLane)
    (hrightLane : inToLane rightShape.lane rightInput = some rightLane)
    (hleftSize : leftShape.lane.size = size.toNat)
    (hrightSize : rightShape.lane.size = size.toNat)
    (hleftDim : leftShape.dim.toNat = VecType.v128.size / size.toNat)
    (hrightDim : rightShape.dim.toNat = VecType.v128.size / size.toNat)
    (hleftBytes : releasedNumerics.ibytes_ leftShape.lane.size leftInput = bytes)
    (hrightBytes : releasedNumerics.ibytes_ rightShape.lane.size rightInput = bytes) :
    leftOutput = rightOutput := by
  have hshape : leftShape = rightShape :=
    Shape.eq_of_size_dim_inToLane_some
      (hleftSize.trans hrightSize.symm) (hleftDim.trans hrightDim.symm)
      hleftLane hrightLane
  subst rightShape
  have hmultiple : 8 * (leftShape.lane.size / 8) = leftShape.lane.size := by
    rw [hleftSize]
    cases size <;> decide
  have hinput : leftInput = rightInput :=
    ibytes_injective hmultiple (hleftBytes.trans hrightBytes.symm)
  subst rightInput
  have hlane : leftLane = rightLane :=
    Option.some.inj (hleftLane.symm.trans hrightLane)
  subst rightLane
  have hlanes : leftLanes = rightLanes :=
    Option.some.inj (hleftSet.symm.trans hrightSet)
  subst rightLanes
  exact hleftOutput.symm.trans hrightOutput

theorem ibytes_lists_injective {size : Sz} {left right : List (IN size.toNat)}
    {bytesAt : Nat → List Byte}
    (hlength : left.length = right.length)
    (hleft : ∀ (index value : Nat) (hvalue : value < 2 ^ size.toNat),
      left[index]? = some ⟨value, hvalue⟩ →
        releasedNumerics.ibytes_ size.toNat ⟨value, hvalue⟩ = bytesAt index)
    (hright : ∀ (index value : Nat) (hvalue : value < 2 ^ size.toNat),
      right[index]? = some ⟨value, hvalue⟩ →
        releasedNumerics.ibytes_ size.toNat ⟨value, hvalue⟩ = bytesAt index) :
    left = right := by
  apply List.ext_getElem hlength
  intro index hleftIndex hrightIndex
  have hleftBytes := hleft index left[index].val left[index].property (by
    exact List.getElem?_eq_getElem hleftIndex)
  have hrightBytes := hright index right[index].val right[index].property (by
    exact List.getElem?_eq_getElem hrightIndex)
  have hmultiple : 8 * (size.toNat / 8) = size.toNat := by
    cases size <;> decide
  exact ibytes_injective hmultiple (hleftBytes.trans hrightBytes.symm)

theorem exists_head_result_of_mapM_some {input output : Type}
    {function : input → Option output} {head : input} {tail : List input}
    {outputs : List output}
    (h : (head :: tail).mapM function = some outputs) :
    ∃ result, function head = some result := by
  rw [List.mapM_cons] at h
  cases hhead : function head with
  | none => simp [hhead] at h
  | some result => exact ⟨result, rfl⟩

theorem vloadPack_output_injective {size : Sz} {count : Nat} {signed : Sx}
    {leftShape rightShape : Shape}
    {leftInputs rightInputs : List (IN size.toNat)}
    {leftLanes : List (Lane_ leftShape.lane)}
    {rightLanes : List (Lane_ rightShape.lane)}
    {leftOutput rightOutput : V128Lit}
    {bytesAt : Nat → List Byte}
    (hleftOutput : releasedNumerics.inv_lanes_ leftShape leftLanes = leftOutput)
    (hrightOutput : releasedNumerics.inv_lanes_ rightShape rightLanes = rightOutput)
    (hleftMap : leftInputs.mapM (fun input =>
      inToLane leftShape.lane
        (releasedNumerics.extend__ size.toNat leftShape.lane.size signed input)) =
      some leftLanes)
    (hrightMap : rightInputs.mapM (fun input =>
      inToLane rightShape.lane
        (releasedNumerics.extend__ size.toNat rightShape.lane.size signed input)) =
      some rightLanes)
    (hleftSize : leftShape.lane.size = size.toNat * 2)
    (hrightSize : rightShape.lane.size = size.toNat * 2)
    (hleftDim : leftShape.dim.toNat = count)
    (hrightDim : rightShape.dim.toNat = count)
    (hleftLength : leftInputs.length = count)
    (hrightLength : rightInputs.length = count)
    (hleftBytes : ∀ (index value : Nat) (hvalue : value < 2 ^ size.toNat),
      leftInputs[index]? = some ⟨value, hvalue⟩ →
        releasedNumerics.ibytes_ size.toNat ⟨value, hvalue⟩ = bytesAt index)
    (hrightBytes : ∀ (index value : Nat) (hvalue : value < 2 ^ size.toNat),
      rightInputs[index]? = some ⟨value, hvalue⟩ →
        releasedNumerics.ibytes_ size.toNat ⟨value, hvalue⟩ = bytesAt index) :
    leftOutput = rightOutput := by
  have hinputs : leftInputs = rightInputs :=
    ibytes_lists_injective (hleftLength.trans hrightLength.symm)
      hleftBytes hrightBytes
  subst rightInputs
  have hnonempty : leftInputs ≠ [] := by
    intro hempty
    subst leftInputs
    have hpositive : 0 < leftShape.dim.toNat := by
      cases leftShape.dim <;> decide
    simp at hleftLength
    omega
  cases leftInputs with
  | nil => exact (hnonempty rfl).elim
  | cons head tail =>
      obtain ⟨leftLane, hleftHead⟩ :=
        exists_head_result_of_mapM_some hleftMap
      obtain ⟨rightLane, hrightHead⟩ :=
        exists_head_result_of_mapM_some hrightMap
      have hshape : leftShape = rightShape :=
        Shape.eq_of_size_dim_inToLane_some
          (hleftSize.trans hrightSize.symm) (hleftDim.trans hrightDim.symm)
          hleftHead hrightHead
      subst rightShape
      have hlanes : leftLanes = rightLanes :=
        Option.some.inj (hleftMap.symm.trans hrightMap)
      subst rightLanes
      exact hleftOutput.symm.trans hrightOutput

theorem zbytes_injective_of_wf {storage : StorageType}
    {left right : Lit_ storage}
    (hleft : ByteSolvedLiteralWfFor
      (authority := amendedExecutionAuthority) storage left)
    (hright : ByteSolvedLiteralWfFor
      (authority := amendedExecutionAuthority) storage right)
    (hbytes : releasedNumerics.zbytes_ storage left =
      releasedNumerics.zbytes_ storage right) : left = right := by
  have leftDecoded := storageLiteralCandidate?_zbytes_complete left hleft
  have rightDecoded := storageLiteralCandidate?_zbytes_complete right hright
  rw [hbytes] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

theorem zbytes_length_of_zsize {storage : StorageType}
    {literal : Lit_ storage} {storageBits : Nat}
    (hsize : zsize storage = some storageBits) :
    (releasedNumerics.zbytes_ storage literal).length = storageBits / 8 := by
  cases storage with
  | val valueType =>
      cases valueType with
      | num numberType =>
          cases numberType <;>
            simp_all [zsize, ConcreteNumerics.zbytes, ConcreteNumerics.nbytes,
              ConcreteNumerics.ibytes, NumType.size]
      | vec vectorType =>
          cases vectorType <;>
            simp_all [zsize, ConcreteNumerics.zbytes, ConcreteNumerics.vbytes,
              ConcreteNumerics.ibytes, VecType.size]
      | ref referenceType => nomatch literal
      | bot => nomatch literal
  | pack packedType =>
      cases packedType <;>
        simp_all [zsize, ConcreteNumerics.zbytes, ConcreteNumerics.ibytes,
          PackType.size]

theorem zbytes_lists_injective {storage : StorageType} {width : Nat}
    {left right : List (Lit_ storage)}
    (hlength : left.length = right.length)
    (hleftFlatten :
      (left.map (releasedNumerics.zbytes_ storage)).flatten =
        (right.map (releasedNumerics.zbytes_ storage)).flatten)
    (hleftLengths : ∀ value ∈ left,
      (releasedNumerics.zbytes_ storage value).length = width)
    (hrightLengths : ∀ value ∈ right,
      (releasedNumerics.zbytes_ storage value).length = width)
    (hleftWf : ∀ value ∈ left,
      ByteSolvedLiteralWfFor
        (authority := amendedExecutionAuthority) storage value)
    (hrightWf : ∀ value ∈ right,
      ByteSolvedLiteralWfFor
        (authority := amendedExecutionAuthority) storage value) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at hlength
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp at hlength
      | cons rightHead rightTail =>
          have htailLength : leftTail.length = rightTail.length :=
            Nat.succ.inj hlength
          simp only [List.map_cons, List.flatten_cons] at hleftFlatten
          have hleftHeadLength := hleftLengths leftHead (by simp)
          have hrightHeadLength := hrightLengths rightHead (by simp)
          have hheadBytes : releasedNumerics.zbytes_ storage leftHead =
              releasedNumerics.zbytes_ storage rightHead :=
            List.append_inj_left hleftFlatten
              (hleftHeadLength.trans hrightHeadLength.symm)
          have htailFlatten :
              (leftTail.map (releasedNumerics.zbytes_ storage)).flatten =
                (rightTail.map (releasedNumerics.zbytes_ storage)).flatten :=
            List.append_inj_right hleftFlatten
              (hleftHeadLength.trans hrightHeadLength.symm)
          have hhead : leftHead = rightHead :=
            zbytes_injective_of_wf
              (hleftWf leftHead (by simp)) (hrightWf rightHead (by simp))
              hheadBytes
          subst rightHead
          have htail : leftTail = rightTail := ih htailLength htailFlatten
            (fun value hvalue => hleftLengths value (by simp [hvalue]))
            (fun value hvalue => hrightLengths value (by simp [hvalue]))
            (fun value hvalue => hleftWf value (by simp [hvalue]))
            (fun value hvalue => hrightWf value (by simp [hvalue]))
          subst rightTail
          rfl

theorem arrayNewData_output_injective {storage : StorageType} {storageBits : Nat}
    {leftInputs rightInputs : List (Lit_ storage)}
    {leftOutput rightOutput : List Instr} {bytes : List Byte}
    (hleftOutput : leftInputs.mapM (releasedNumerics.cunpackConst storage) =
      some leftOutput)
    (hrightOutput : rightInputs.mapM (releasedNumerics.cunpackConst storage) =
      some rightOutput)
    (hlength : leftInputs.length = rightInputs.length)
    (hleftFlatten :
      (leftInputs.map (releasedNumerics.zbytes_ storage)).flatten = bytes)
    (hrightFlatten :
      (rightInputs.map (releasedNumerics.zbytes_ storage)).flatten = bytes)
    (hstorageSize : zsize storage = some storageBits)
    (hleftWf : ∀ value ∈ leftInputs,
      ByteSolvedLiteralWfFor
        (authority := amendedExecutionAuthority) storage value)
    (hrightWf : ∀ value ∈ rightInputs,
      ByteSolvedLiteralWfFor
        (authority := amendedExecutionAuthority) storage value) :
    plains leftOutput = plains rightOutput := by
  have hinputs : leftInputs = rightInputs :=
    zbytes_lists_injective hlength (hleftFlatten.trans hrightFlatten.symm)
      (fun value _ => zbytes_length_of_zsize hstorageSize)
      (fun value _ => zbytes_length_of_zsize hstorageSize)
      hleftWf hrightWf
  subst rightInputs
  have houtput : leftOutput = rightOutput :=
    Option.some.inj (hleftOutput.symm.trans hrightOutput)
  subst rightOutput
  rfl

theorem cunpackConst_output_injective_of_field_eq
    {leftField rightField : FieldType}
    {left : Lit_ (fieldStorage leftField)}
    {right : Lit_ (fieldStorage rightField)}
    {leftOutput rightOutput : Instr} {bytes : List Byte}
    (hleftOutput :
      releasedNumerics.cunpackConst (fieldStorage leftField) left =
        some leftOutput)
    (hrightOutput :
      releasedNumerics.cunpackConst (fieldStorage rightField) right =
        some rightOutput)
    (hfield : leftField = rightField)
    (hleftWf : ByteSolvedLiteralWfFor
      (authority := amendedExecutionAuthority) (fieldStorage leftField) left)
    (hrightWf : ByteSolvedLiteralWfFor
      (authority := amendedExecutionAuthority) (fieldStorage rightField) right)
    (hleftBytes : releasedNumerics.zbytes_ (fieldStorage leftField) left = bytes)
    (hrightBytes : releasedNumerics.zbytes_ (fieldStorage rightField) right = bytes) :
    leftOutput = rightOutput := by
  subst rightField
  have hliteral : left = right :=
    zbytes_injective_of_wf hleftWf hrightWf
      (hleftBytes.trans hrightBytes.symm)
  subst right
  exact Option.some.inj (hleftOutput.symm.trans hrightOutput)

theorem Step_readA.unindexSourceTarget
    {state : State} {rule : ReadRule} {source target : List AdminInstr}
    (h : Step_readA state rule source target) :
    ∃ unindexedSource unindexedTarget : List AdminInstr,
      unindexedSource = source ∧ unindexedTarget = target ∧
        Step_readA state rule unindexedSource unindexedTarget := by
  exact ⟨source, target, rfl, rfl, h⟩

theorem constI32_injective {left right : U32}
    (h : constI32 left = constI32 right) : left = right := by
  simp [constI32] at h
  exact h

theorem Inn.toNumType_injective {left right : Inn}
    (h : left.toNumType = right.toNumType) : left = right := by
  cases left <;> cases right <;> simp_all [Inn.toNumType]

@[simp] theorem constI32_eq_iff {left right : U32} :
    constI32 left = constI32 right ↔ left = right :=
  ⟨constI32_injective, congrArg constI32⟩

def adminConstNat? : AdminInstr → Option Nat
  | .plain (.const .i32 value) => some value.val
  | .plain (.const .i64 value) => some value.val
  | _ => none

def adminConstAddrType? : AdminInstr → Option AddrType
  | .plain (.const .i32 _) => some .i32
  | .plain (.const .i64 _) => some .i64
  | _ => none

theorem constAddr_type_eq {leftType rightType : AddrType}
    {left : AddrLit leftType} {right : AddrLit rightType}
    (h : constAddr leftType left = constAddr rightType right) :
    leftType = rightType := by
  have htype := congrArg adminConstAddrType? h
  cases leftType <;> cases rightType <;>
    simp_all [adminConstAddrType?, constAddr, addrLitToNum, addrNumType]

theorem constAddr_val_eq {leftType rightType : AddrType}
    {left : AddrLit leftType} {right : AddrLit rightType}
    (h : constAddr leftType left = constAddr rightType right) :
    left.val = right.val := by
  have hvalue := congrArg adminConstNat? h
  cases leftType <;> cases rightType <;>
    simp_all [adminConstNat?, constAddr, addrLitToNum, addrNumType]

@[simp] theorem constAddr_eq_iff {leftType rightType : AddrType}
    {left : AddrLit leftType} {right : AddrLit rightType} :
    constAddr leftType left = constAddr rightType right ↔
      leftType = rightType ∧ left.val = right.val := by
  constructor
  · intro h
    exact ⟨constAddr_type_eq h, constAddr_val_eq h⟩
  · rintro ⟨rfl, hval⟩
    have hvalue : left = right := Subtype.ext hval
    subst right
    rfl

@[simp] theorem expand_iff {dt : DefType} {ct : CompType} :
    Expand dt ct ↔ expandDt dt = some ct := by
  constructor
  · intro h
    cases h with
    | mk h => exact h
  · exact Expand.mk

theorem Val.toAdmin_injective {left right : Val}
    (h : left.toAdmin = right.toAdmin) : left = right := by
  have valueEquality := congrArg adminToVal h
  simpa using valueEquality

@[simp] theorem Val.toAdmin_eq_iff {left right : Val} :
    left.toAdmin = right.toAdmin ↔ left = right :=
  ⟨Val.toAdmin_injective, congrArg Val.toAdmin⟩

@[simp] theorem vals_eq_iff {left right : List Val} :
    vals left = vals right ↔ left = right := by
  constructor
  · exact vals_injective
  · exact congrArg vals

@[simp] theorem append_singleton_eq_append_singleton_iff {type : Type}
    {left right : List type} {leftLast rightLast : type} :
    left ++ [leftLast] = right ++ [rightLast] ↔
      left = right ∧ leftLast = rightLast := by
  constructor
  · intro h
    have hreversed := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_singleton,
      List.singleton_append] at hreversed
    have hparts := List.cons.inj hreversed
    constructor
    · have := congrArg List.reverse hparts.2
      simpa using this
    · exact hparts.1
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem append_pair_eq_append_pair_iff {type : Type}
    {left right : List type} {leftFirst leftLast rightFirst rightLast : type} :
    left ++ [leftFirst, leftLast] = right ++ [rightFirst, rightLast] ↔
      left = right ∧ leftFirst = rightFirst ∧ leftLast = rightLast := by
  constructor
  · intro h
    have h' : (left ++ [leftFirst]) ++ [leftLast] =
        (right ++ [rightFirst]) ++ [rightLast] := by
      simpa only [List.append_assoc] using h
    have hlast := append_singleton_eq_append_singleton_iff.mp h'
    have hfirst := append_singleton_eq_append_singleton_iff.mp hlast.1
    exact ⟨hfirst.1, hfirst.2, hlast.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

@[simp] theorem splitVals_vals_addrref_plain (values : List Val)
    (address : AddrRef) (instruction : Instr) (suffix : List AdminInstr)
    (hnonvalue : adminToVal (.plain instruction) = none) :
    splitVals (vals values ++ [.addrref address, .plain instruction] ++ suffix) =
      (values ++ [.ref (.addr address)], .plain instruction :: suffix) := by
  calc
    splitVals (vals values ++ [.addrref address, .plain instruction] ++ suffix) =
        splitVals
          (vals (values ++ [.ref (.addr address)]) ++
            .plain instruction :: suffix) := by
      congr 1
      simp [vals, Val.toAdmin, List.map_append, List.append_assoc]
    _ = (values ++ [.ref (.addr address)], .plain instruction :: suffix) :=
      splitVals_vals_append_nonval
        (values ++ [.ref (.addr address)]) hnonvalue suffix

@[simp] theorem splitVals_vals_plain (values : List Val)
    (instruction : Instr) (suffix : List AdminInstr)
    (hnonvalue : adminToVal (.plain instruction) = none) :
    splitVals (vals values ++ .plain instruction :: suffix) =
      (values, .plain instruction :: suffix) :=
  splitVals_vals_append_nonval values hnonvalue suffix

theorem returnCallRef_source_injective
    {leftValues rightValues : List Val} {leftTypeUse rightTypeUse : TypeUse}
    {leftSuffix rightSuffix : List AdminInstr}
    (hsource :
      vals leftValues ++ .plain (.returnCallRef leftTypeUse) :: leftSuffix =
      vals rightValues ++ .plain (.returnCallRef rightTypeUse) :: rightSuffix) :
    leftValues = rightValues ∧ leftTypeUse = rightTypeUse := by
  have hsplit := congrArg splitVals hsource
  rw [splitVals_vals_plain leftValues (.returnCallRef leftTypeUse) leftSuffix rfl,
    splitVals_vals_plain rightValues (.returnCallRef rightTypeUse) rightSuffix rfl]
    at hsplit
  have hparts : leftValues = rightValues ∧
      leftTypeUse = rightTypeUse ∧ leftSuffix = rightSuffix := by
    simpa using hsplit
  exact ⟨hparts.1, hparts.2.1⟩

theorem vals_addrref_plain_source_injective
    {leftValues rightValues : List Val} {leftAddress rightAddress : AddrRef}
    {leftInstruction rightInstruction : Instr}
    {leftSuffix rightSuffix : List AdminInstr}
    (hleftNonvalue : adminToVal (.plain leftInstruction) = none)
    (hrightNonvalue : adminToVal (.plain rightInstruction) = none)
    (hsource :
      vals leftValues ++ .addrref leftAddress ::
          .plain leftInstruction :: leftSuffix =
        vals rightValues ++ .addrref rightAddress ::
          .plain rightInstruction :: rightSuffix) :
    leftValues = rightValues ∧ leftAddress = rightAddress ∧
      leftInstruction = rightInstruction := by
  have hsource' :
      vals (leftValues ++ [.ref (.addr leftAddress)]) ++
          .plain leftInstruction :: leftSuffix =
        vals (rightValues ++ [.ref (.addr rightAddress)]) ++
          .plain rightInstruction :: rightSuffix := by
    simpa [vals, Val.toAdmin, List.map_append, List.append_assoc] using hsource
  have hsplit := congrArg splitVals hsource'
  rw [splitVals_vals_plain _ _ _ hleftNonvalue,
    splitVals_vals_plain _ _ _ hrightNonvalue] at hsplit
  have hvalues := congrArg Prod.fst hsplit
  have hsuffix := congrArg Prod.snd hsplit
  have hvalueParts := append_singleton_eq_append_singleton_iff.mp hvalues
  have haddress : leftAddress = rightAddress := by
    simpa using hvalueParts.2
  have hinstruction := (List.cons.inj hsuffix).1
  exact ⟨hvalueParts.1, haddress, by simpa using hinstruction⟩

theorem returnCallRefFrameAddr_source_injective
    {state : State}
    {leftDiscarded leftArguments rightDiscarded rightArguments : List Val}
    {leftAddress rightAddress : FuncAddr}
    {leftTypeUse rightTypeUse : TypeUse}
    {leftSuffix rightSuffix : List AdminInstr}
    {leftFunction rightFunction : FuncInst}
    {leftDomain leftCodomain rightDomain rightCodomain : ValTypes}
    {leftArity leftResults rightArity rightResults : Nat}
    (hleftFunction : state.funcinst[leftAddress]? = some leftFunction)
    (hrightFunction : state.funcinst[rightAddress]? = some rightFunction)
    (hleftExpand : expandDt leftFunction.type =
      some (.func leftDomain leftCodomain))
    (hrightExpand : expandDt rightFunction.type =
      some (.func rightDomain rightCodomain))
    (hleftDomain : leftDomain.length = leftArity)
    (hleftCodomain : leftCodomain.length = leftResults)
    (hleftArguments : leftArguments.length = leftArity)
    (hrightDomain : rightDomain.length = rightArity)
    (hrightCodomain : rightCodomain.length = rightResults)
    (hrightArguments : rightArguments.length = rightArity)
    (hsource :
      vals leftDiscarded ++ vals leftArguments ++
          [.addrref (.funcAddr leftAddress),
            .plain (.returnCallRef leftTypeUse)] ++ leftSuffix =
        vals rightDiscarded ++ vals rightArguments ++
          [.addrref (.funcAddr rightAddress),
            .plain (.returnCallRef rightTypeUse)] ++ rightSuffix) :
    leftArguments = rightArguments ∧ leftAddress = rightAddress ∧
      leftTypeUse = rightTypeUse := by
  have hsource' :
      vals (leftDiscarded ++ leftArguments ++
          [.ref (.addr (.funcAddr leftAddress))]) ++
          .plain (.returnCallRef leftTypeUse) :: leftSuffix =
        vals (rightDiscarded ++ rightArguments ++
          [.ref (.addr (.funcAddr rightAddress))]) ++
          .plain (.returnCallRef rightTypeUse) :: rightSuffix := by
    simpa [vals, Val.toAdmin, List.map_append, List.append_assoc] using hsource
  have hsplit := congrArg splitVals hsource'
  rw [splitVals_vals_plain _ _ _ rfl, splitVals_vals_plain _ _ _ rfl] at hsplit
  have hvalues :
      leftDiscarded ++ leftArguments ++
          [.ref (.addr (.funcAddr leftAddress))] =
        rightDiscarded ++ rightArguments ++
          [.ref (.addr (.funcAddr rightAddress))] :=
    congrArg Prod.fst hsplit
  have hsuffix := congrArg Prod.snd hsplit
  have hinstruction := (List.cons.inj hsuffix).1
  have hvalueParts := append_singleton_eq_append_singleton_iff.mp hvalues
  have haddress : leftAddress = rightAddress := by
    simpa using hvalueParts.2
  have htypeUse : leftTypeUse = rightTypeUse := by
    simpa using hinstruction
  subst rightAddress
  have hfunction : leftFunction = rightFunction :=
    Option.some.inj (hleftFunction.symm.trans hrightFunction)
  subst rightFunction
  have htypes : CompType.func leftDomain leftCodomain =
      .func rightDomain rightCodomain :=
    Option.some.inj (hleftExpand.symm.trans hrightExpand)
  injection htypes with hdomain hcodomain
  subst rightDomain
  subst rightCodomain
  have harity : leftArguments.length = rightArguments.length := by
    omega
  have harguments : leftArguments = rightArguments :=
    List.append_inj_right' hvalueParts.1 harity
  exact ⟨harguments, rfl, htypeUse⟩

/-- A proof-engineering partition of the 105 read rules.  It has no semantic
content; keeping each inversion theorem below one fifth of the authority relation
also keeps the serialized kernel proof shallow enough for ordinary release builds. -/
def ReadRule.functionalGroup : ReadRule → Nat
  | .block | .loop | .brOnCastSucceed | .brOnCastFail
  | .brOnCastFailSucceed => 0
  | .brOnCastFailFail | .call | .callRefNull | .callRefFunc | .returnCall => 1
  | .returnCallRefLabel | .returnCallRefHandler | .returnCallRefFrameNull
  | .returnCallRefFrameAddr | .throwRefNull => 2
  | .throwRefInstrs | .throwRefLabel | .throwRefFrame
  | .throwRefHandlerEmpty | .throwRefHandlerCatch => 3
  | .throwRefHandlerCatchRef | .throwRefHandlerCatchAll
  | .throwRefHandlerCatchAllRef | .throwRefHandlerNext | .tryTable => 4
  | .localGet | .globalGet | .tableGetOob | .tableGetVal | .tableSize => 5
  | .tableFillOob | .tableFillZero | .tableFillSucc
  | .tableCopyOob | .tableCopyZero => 6
  | .tableCopyLe | .tableCopyGt | .tableInitOob
  | .tableInitZero | .tableInitSucc => 7
  | .loadNumOob | .loadNumVal | .loadPackOob | .loadPackVal | .vloadOob => 8
  | .vloadVal | .vloadPackOob | .vloadPackVal
  | .vloadSplatOob | .vloadSplatVal => 9
  | .vloadZeroOob | .vloadZeroVal | .vloadLaneOob
  | .vloadLaneVal | .memorySize => 10
  | .memoryFillOob | .memoryFillZero | .memoryFillSucc
  | .memoryCopyOob | .memoryCopyZero => 11
  | .memoryCopyLe | .memoryCopyGt | .memoryInitOob
  | .memoryInitZero | .memoryInitSucc => 12
  | .refNullIdx | .refFunc | .refTestTrue | .refTestFalse
  | .refCastSucceed => 13
  | .refCastFail | .structNewDefault | .structGetNull
  | .structGetStruct | .arrayNewDefault => 14
  | .arrayNewElemOob | .arrayNewElemAlloc | .arrayNewDataOob
  | .arrayNewDataNum | .arrayGetNull => 15
  | .arrayGetOob | .arrayGetArray | .arrayLenNull
  | .arrayLenArray | .arrayFillNull => 16
  | .arrayFillOob | .arrayFillZero | .arrayFillSucc
  | .arrayCopyNull1 | .arrayCopyNull2 => 17
  | .arrayCopyOob1 | .arrayCopyOob2 | .arrayCopyZero
  | .arrayCopyLe | .arrayCopyGt => 18
  | .arrayInitElemNull | .arrayInitElemOob1 | .arrayInitElemOob2
  | .arrayInitElemZero | .arrayInitElemSucc => 19
  | .arrayInitDataNull | .arrayInitDataOob1 | .arrayInitDataOob2
  | .arrayInitDataZero | .arrayInitDataNum => 20

theorem Step_readA.target_functional_group0
    {state : State} {rule : ReadRule} {source left right : List AdminInstr}
    (hgroup : rule.functionalGroup = 0)
    (hl : Step_readA state rule source left)
    (hr : Step_readA state rule source right) : left = right := by
  obtain ⟨leftSource, leftTarget, hleftSource, hleftTarget, leftProof⟩ :=
    hl.unindexSourceTarget
  obtain ⟨rightSource, rightTarget, hrightSource, hrightTarget, rightProof⟩ :=
    hr.unindexSourceTarget
  have sourcesEqual : leftSource = rightSource := hleftSource.trans hrightSource.symm
  rw [← hleftTarget, ← hrightTarget]
  clear hl hr hleftSource hrightSource hleftTarget hrightTarget source left right
  cases rule <;> simp [ReadRule.functionalGroup] at hgroup
  all_goals cases leftProof <;> cases rightProof
  all_goals have splitSourcesEqual := congrArg splitVals sourcesEqual
  all_goals snapshot_equalities
  all_goals simp_all [constI32_eq_iff, constAddr_eq_iff, Val.toAdmin_eq_iff,
    splitVals_append]
  all_goals restore_equalities
  all_goals simp_all [constI32_eq_iff, constAddr_eq_iff, Val.toAdmin_eq_iff]

end WasmGemmGnaf.Wasm.Core.Exec
