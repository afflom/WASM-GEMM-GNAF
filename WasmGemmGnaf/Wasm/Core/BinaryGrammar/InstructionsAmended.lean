/-
  Coverage-neutral binary-instruction repairs for AMD-008, AMD-010, and
  AMD-012.

  The pinned transcription remains unchanged.  `BinstrNum'` removes only the
  malformed 0xBB result/operand ordering and adds its corrected production;
  `BinstrControl'` preserves every pinned production and adds the two omitted
  typed-reference call opcodes; `BinstrVecInt32And64'` replaces only the
  malformed relaxed dot-add operand shape.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Instructions
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Vector
import WasmGemmGnaf.Wasm.AuthorityAmendments

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

/-! ## AMD-012 vector-leaf repair

The pinned opcode-275 production constructs an `I16x8` operand shape, but the
independent `vextternop__` family premise requires `I8x16`.  Keep the pinned
relation byte-identical and select the one-constructor replacement only under
the amended authority. -/

/-- The internally ill-formed abstract instruction constructed by the pinned
opcode-275 production. -/
def pinnedBadRelaxedDotAdd : Instr :=
  .vextternop ishI32x4 ishI16x8 (.relaxedDotAdd .s)

/-- Every pinned `vec-int32-and64` production except malformed opcode 275,
plus the corrected `I8x16` opcode-275 production required by AMD-012. -/
inductive BinstrVecInt32And64' : Bytes → Instr → Prop where
  | ofPinned (bs : Bytes) (instr : Instr) :
      BinstrVecInt32And64 bs instr → instr ≠ pinnedBadRelaxedDotAdd →
      BinstrVecInt32And64' bs instr
  | correctedRelaxedDotAdd (bo : Bytes) :
      Bprefixed 0xFD 275 bo →
      BinstrVecInt32And64' bo
        (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s))

/-- The vector leaf selected by the finite binary authority. -/
def BinstrVecInt32And64For [authority : BinaryAuthority]
    (bs : Bytes) (instr : Instr) : Prop :=
  match authority.revision with
  | .pinned => BinstrVecInt32And64 bs instr
  | .amended => BinstrVecInt32And64' bs instr

@[simp] theorem BinstrVecInt32And64For_pinned :
    @BinstrVecInt32And64For pinnedBinaryAuthority = BinstrVecInt32And64 := rfl

@[simp] theorem BinstrVecInt32And64For_amended :
    @BinstrVecInt32And64For amendedBinaryAuthority = BinstrVecInt32And64' := rfl

theorem BinstrVecInt32And64For.ofPinned [authority : BinaryAuthority]
    {bs : Bytes} {instr : Instr} (h : BinstrVecInt32And64 bs instr)
    (hne : instr ≠ pinnedBadRelaxedDotAdd) :
    BinstrVecInt32And64For bs instr := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact h
      | amended => exact @BinstrVecInt32And64'.ofPinned bs instr h hne

theorem BinstrVecInt32And64For.correctedRelaxedDotAdd {bo : Bytes}
    (h : Bprefixed 0xFD 275 bo) :
    @BinstrVecInt32And64For amendedBinaryAuthority bo
      (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s)) :=
  @BinstrVecInt32And64'.correctedRelaxedDotAdd bo h

/-- Kernel regression for the exact malformed pinned abstract instruction. -/
theorem pinnedBadRelaxedDotAdd_not_wf :
    Instr.wf pinnedBadRelaxedDotAdd = false := by decide

/-- Kernel regression for AMD-012's unique well-formed replacement. -/
theorem correctedRelaxedDotAdd_wf :
    Instr.wf (.vextternop ishI32x4 ishI8x16 (.relaxedDotAdd .s)) = true := by decide

/-- The malformed abstract instruction derived by the pinned 0xBB production. -/
def pinnedBadPromote : Instr := .cvtop .f32 .f64 (.ff .promote)

/-- Every pinned numeric production except the malformed 0xBB production,
plus the corrected `F64 <- F32 PROMOTE` production. -/
inductive BinstrNum' : Bytes → Instr → Prop where
  | ofPinned (bs : Bytes) (instr : Instr) :
      BinstrNum bs instr → instr ≠ pinnedBadPromote → BinstrNum' bs instr
  | f64PromoteF32 :
      BinstrNum' [tb 0xBB] (.cvtop .f64 .f32 (.ff .promote))

/-- Every pinned non-recursive control production plus the two productions
omitted at the pin. -/
inductive BinstrControl' : Bytes → Instr → Prop where
  | ofPinned (bs : Bytes) (instr : Instr) :
      BinstrControl bs instr → BinstrControl' bs instr
  | callRef (bs : Bytes) (x : TypeIdx) :
      Btypeidx bs x → BinstrControl' (tb 0x14 :: bs) (.callRef (.idx x))
  | returnCallRef (bs : Bytes) (x : TypeIdx) :
      Btypeidx bs x →
      BinstrControl' (tb 0x15 :: bs) (.returnCallRef (.idx x))

/-- The numeric leaf selected by the current binary-grammar authority. -/
def BinstrNumFor [authority : BinaryAuthority] (bs : Bytes) (instr : Instr) : Prop :=
  match authority.revision with
  | .pinned => BinstrNum bs instr
  | .amended => BinstrNum' bs instr

/-- The non-recursive control leaf selected by the current binary-grammar
authority. -/
def BinstrControlFor [authority : BinaryAuthority]
    (bs : Bytes) (instr : Instr) : Prop :=
  match authority.revision with
  | .pinned => BinstrControl bs instr
  | .amended => BinstrControl' bs instr

@[simp] theorem BinstrNumFor_pinned :
    @BinstrNumFor pinnedBinaryAuthority = BinstrNum := rfl

@[simp] theorem BinstrNumFor_amended :
    @BinstrNumFor amendedBinaryAuthority = BinstrNum' := rfl

@[simp] theorem BinstrControlFor_pinned :
    @BinstrControlFor pinnedBinaryAuthority = BinstrControl := rfl

@[simp] theorem BinstrControlFor_amended :
    @BinstrControlFor amendedBinaryAuthority = BinstrControl' := rfl

/-- Lift an unchanged pinned control production into either selected
authority. -/
theorem BinstrControlFor.ofPinned [authority : BinaryAuthority]
    {bs : Bytes} {instr : Instr} (h : BinstrControl bs instr) :
    BinstrControlFor bs instr := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact h
      | amended => exact @BinstrControl'.ofPinned bs instr h

/-- Lift an unchanged pinned numeric production into either selected
authority.  The side condition is load-bearing only for the amended case. -/
theorem BinstrNumFor.ofPinned [authority : BinaryAuthority]
    {bs : Bytes} {instr : Instr} (h : BinstrNum bs instr)
    (hne : instr ≠ pinnedBadPromote) : BinstrNumFor bs instr := by
  cases authority with
  | mk revision =>
      cases revision with
      | pinned => exact h
      | amended => exact @BinstrNum'.ofPinned bs instr h hne

/-- The corrected promote production is selected by the amended authority. -/
theorem BinstrNumFor.correctedPromote :
    @BinstrNumFor amendedBinaryAuthority [tb 0xBB]
      (.cvtop .f64 .f32 (.ff .promote)) :=
  .f64PromoteF32

/-- The two AMD-010 productions are selected by the amended authority. -/
theorem BinstrControlFor.callRef {bs : Bytes} {x : TypeIdx}
    (h : Btypeidx bs x) :
    @BinstrControlFor amendedBinaryAuthority (tb 0x14 :: bs)
      (.callRef (.idx x)) :=
  @BinstrControl'.callRef bs x h

theorem BinstrControlFor.returnCallRef {bs : Bytes} {x : TypeIdx}
    (h : Btypeidx bs x) :
    @BinstrControlFor amendedBinaryAuthority (tb 0x15 :: bs)
      (.returnCallRef (.idx x)) :=
  @BinstrControl'.returnCallRef bs x h

theorem BinstrNum'.pinned_of_ne_bad {bs : Bytes} {instr : Instr}
    (h : BinstrNum bs instr) (hne : instr ≠ pinnedBadPromote) :
    BinstrNum' bs instr :=
  .ofPinned bs instr h hne

theorem BinstrControl.to_amended {bs : Bytes} {instr : Instr}
    (h : BinstrControl bs instr) : BinstrControl' bs instr :=
  .ofPinned bs instr h

/-- The corrected production is well-formed according to the independent
operator syntax; the pinned reversed production is not. -/
theorem correctedPromote_wf :
    Cvtop.wf .f32 .f64 (.ff .promote) = true := by decide

theorem pinnedBadPromote_not_wf :
    Cvtop.wf .f64 .f32 (.ff .promote) = false := by decide

theorem promoteOpcodeAmendment_target :
    core3PromoteOpcodeAuthorityAmendment.patches.flatMap
        AuthorityPatchBody.amendedLeanDeclarations =
      ["WasmGemmGnaf.Wasm.Core.Binary.BinstrNum'",
       "WasmGemmGnaf.Wasm.Core.Decode.op0'"] := rfl

theorem callRefOpcodeAmendment_target :
    core3CallRefAuthorityAmendment.patches.flatMap
        AuthorityPatchBody.amendedLeanDeclarations =
      ["WasmGemmGnaf.Wasm.Core.Binary.BinstrControl'",
       "WasmGemmGnaf.Wasm.Core.Decode.decOp1'"] := rfl

end WasmGemmGnaf.Wasm.Core.Binary
