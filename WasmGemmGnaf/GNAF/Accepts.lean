import WasmGemmGnaf.GNAF.SupportedSemantics
import WasmGemmGnaf.Wasm.Run

set_option autoImplicit false

/-!
# Checked-plan acceptance at the public execution boundary

This module turns the independently defined `Plan.eval` source semantics into
the raw-invocation/observation relation used by SPEC §11.4.  It contains no
compiler, module, initializer, execution relation, or evaluator reference.

The source and Core machines use different carriers for the same public byte
image: GNAF keeps bytes as natural-number cells, while amended Core uses its
bounded `Byte` subtype and allocates whole 64-KiB pages.  `MemoryMatches`
therefore compares the complete source-memory prefix byte-for-byte and leaves
only the compiler-private page tail unobserved.  In particular, acceptance
does not require the final store to equal the entry store: observable C writes
must agree with the independently evaluated source plan.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

/-- Install raw ABI bytes into a finite source memory image.  Out-of-range
writes have the ordinary `List.set` behavior and leave the list unchanged. -/
def installRawCells : List Nat → Nat → List UInt8 → List Nat
  | memory, _, [] => memory
  | memory, address, byte :: rest =>
      installRawCells (memory.set address byte.toNat) (address + 1) rest

@[simp] theorem installRawCells_length (bytes : List UInt8) :
    ∀ (memory : List Nat) (address : Nat),
      (installRawCells memory address bytes).length = memory.length := by
  induction bytes with
  | nil => simp [installRawCells]
  | cons byte rest ih =>
      intro memory address
      simp only [installRawCells, ih, List.length_set]

/-- Installing a raw byte window leaves every earlier source-memory cell
unchanged. -/
theorem installRawCells_getElem?_lt (bytes : List UInt8) :
    ∀ (memory : List Nat) (address i : Nat), i < address →
      (installRawCells memory address bytes)[i]? = memory[i]? := by
  induction bytes with
  | nil => intro memory address i _; rfl
  | cons byte rest ih =>
      intro memory address i hi
      rw [installRawCells, ih _ _ _ (by omega),
        List.getElem?_set_ne (by omega)]

/-- Every cell inside an in-bounds raw installation contains exactly the
corresponding ABI byte. -/
theorem installRawCells_getElem?_mem (bytes : List UInt8) :
    ∀ (memory : List Nat) (address k : Nat), k < bytes.length →
      address + bytes.length ≤ memory.length →
      (installRawCells memory address bytes)[address + k]? =
        (bytes[k]?).map UInt8.toNat := by
  induction bytes with
  | nil => intro _ _ _ hk _; simp at hk
  | cons byte rest ih =>
      intro memory address k hk hwindow
      simp only [List.length_cons] at hk hwindow
      match k with
      | 0 =>
          rw [Nat.add_zero, installRawCells,
            installRawCells_getElem?_lt _ _ _ _ (by omega),
            List.getElem?_set_self (by omega)]
          simp
      | k + 1 =>
          have haddress : address + (k + 1) = (address + 1) + k := by omega
          rw [haddress, installRawCells,
            ih _ _ _ (by omega) (by simp only [List.length_set]; omega)]
          simp

theorem installRawCells_getD_mem (bytes : List UInt8)
    (memory : List Nat) (address k : Nat) (hk : k < bytes.length)
    (hwindow : address + bytes.length ≤ memory.length) :
    (installRawCells memory address bytes).getD (address + k) 0 =
      (bytes.getD k 0).toNat := by
  have h := installRawCells_getElem?_mem bytes memory address k hk hwindow
  have hget := congrArg (fun value => value.getD 0) h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using hget

/-- Source memory extent needed to retain both the checked source interface
and the complete lawful raw window at its public wasm32 pointer. -/
def initialMemoryLength {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) : Nat :=
  max checked.inputSig.mem
    (raw.body.ptr.toNat + raw.body.bytes.size)

/-- Forget the report payload while retaining the exact four-way result of the
public GEMM classifier. -/
def classificationOf {P : Wasm.Profile} :
    Gemm.Classification P → Classification
  | .valid _ => .valid
  | .invalid _ => .invalid
  | .unsupported _ => .unsupported
  | .resourceExhausted _ => .resourceExhausted

/-- Canonical source-machine input for a checked plan and lawful raw ABI
invocation.  All private resources begin zeroed; the source memory grows to
retain the complete raw window before installation, matching the public
Harness protocol even when `raw.ptr` is above the compiler's small module
minimum. -/
def initialMachine {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) : Machine :=
  { inputBase := raw.body.ptr.toNat
    inputLength := raw.body.bytes.size
    classification := classificationOf (Gemm.classify P raw.body)
    mem := installRawCells (List.replicate (initialMemoryLength checked raw) 0)
      raw.body.ptr.toNat raw.body.bytes.toList
    scratch := List.replicate checked.inputSig.scratch 0
    regs := List.replicate checked.inputSig.regs 0
    vregs := List.replicate checked.inputSig.vregs []
    tables := List.replicate checked.inputSig.tables []
    status := 0
    out := [] }

@[simp] theorem initialMachine_classify
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (initialMachine checked raw).classify =
      classificationOf (Gemm.classify P raw.body) := rfl

@[simp] theorem initialMachine_mem_length
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (initialMachine checked raw).mem.length = initialMemoryLength checked raw := by
  simp [initialMachine]

theorem inputSig_mem_le_initialMemoryLength
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    checked.inputSig.mem ≤ initialMemoryLength checked raw := by
  exact Nat.le_max_left _ _

theorem raw_window_le_initialMemoryLength
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    raw.body.ptr.toNat + raw.body.bytes.size ≤
      initialMemoryLength checked raw := by
  exact Nat.le_max_right _ _

/-- Reading any installed raw byte from the canonical source image returns
the exact byte supplied by the lawful invocation. -/
theorem initialMachine_mem_getD_raw
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) (offset : Nat)
    (hoffset : offset < raw.body.bytes.size) :
    (initialMachine checked raw).mem.getD
        (raw.body.ptr.toNat + offset) 0 =
      (raw.body.bytes.toList.getD offset 0).toNat := by
  apply installRawCells_getD_mem
  · simpa [Foundation.Bytes.byteArray_toList] using hoffset
  · simp only [List.length_replicate]
    simpa [Foundation.Bytes.byteArray_toList] using
      raw_window_le_initialMemoryLength checked raw

/-- The GNAF source word reader agrees with the ABI's recursive
little-endian decoder on a complete byte list. -/
theorem leWord_map_toNat_zero : ∀ bytes : List UInt8,
    leWord (bytes.map UInt8.toNat) 0 bytes.length =
      Gemm.natOfBytesLE bytes := by
  intro bytes
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      rw [List.length_cons, leWord_succ]
      have htail := leWord_cons rest.length byte.toNat
        (rest.map UInt8.toNat) 0
      simp only [List.map_cons, Nat.zero_add] at htail ⊢
      rw [htail, ih]
      simp [Gemm.natOfBytesLE, List.getD_eq_getElem?_getD]

theorem getD_map_drop_take_toNat (bytes : List UInt8) (offset width k : Nat)
    (hk : k < width) (hwindow : offset + width ≤ bytes.length) :
    (((bytes.drop offset).take width).map UInt8.toNat).getD k 0 =
      (bytes.getD (offset + k) 0).toNat := by
  have hindex : offset + k < bytes.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk, hindex]

/-- A little-endian source load from the installed raw window is definitionally
the ABI field at the same relative offset and width. -/
theorem initialMachine_leWord_eq_fieldValue
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation)
    (offset width : Nat) (hwindow : offset + width ≤ raw.body.bytes.size) :
    leWord (initialMachine checked raw).mem
        (raw.body.ptr.toNat + offset) width =
      Gemm.fieldValue raw.body.bytes.toList offset width := by
  let bytes := raw.body.bytes.toList
  let field := (bytes.drop offset).take width
  have hwindowList : offset + width ≤ bytes.length := by
    simpa [bytes, Foundation.Bytes.byteArray_toList] using hwindow
  have hfieldLength : field.length = width := by
    simp [field, bytes, List.length_take, List.length_drop]
    omega
  calc
    leWord (initialMachine checked raw).mem
        (raw.body.ptr.toNat + offset) width =
        leWord (field.map UInt8.toNat) 0 width := by
          apply leWord_ext
          intro k hk
          have hraw := initialMachine_mem_getD_raw checked raw (offset + k) (by omega)
          have hfield := getD_map_drop_take_toNat bytes offset width k hk hwindowList
          rw [Nat.zero_add, hfield]
          simpa [bytes, Nat.add_assoc] using hraw
    _ = leWord (field.map UInt8.toNat) 0 field.length := by rw [hfieldLength]
    _ = Gemm.natOfBytesLE field := leWord_map_toNat_zero field
    _ = Gemm.fieldValue raw.body.bytes.toList offset width := rfl

/-- The dynamically grown canonical source machine conforms to the checked
interface's lower bounds. -/
theorem initialMachine_conforms
    {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (initialMachine checked raw).Conforms checked.inputSig := by
  refine ⟨by simp [initialMachine], by simp [initialMachine], ?_,
    by simp [initialMachine], by simp [initialMachine]⟩
  rw [initialMachine_mem_length]
  exact inputSig_mem_le_initialMemoryLength checked raw

@[simp] theorem initialMachine_status {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (initialMachine checked raw).status = 0 := rfl

/-- Extract an unsigned `i32` result from a public Core value. -/
def returnedI32? : Wasm.Value → Option Nat
  | .num ⟨.i32, value⟩ => some value.val
  | _ => none

/-- The bounded amended-Core byte image denoted by a GNAF source machine.
`Byte.ofNat` is intentional: Core numeric stores retain the low eight bits of
each source cell, which is also the interpretation used by `leWord`. -/
def Machine.byteImage (machine : Machine) : List Wasm.Core.Byte :=
  machine.mem.map Wasm.Core.Byte.ofNat

/-- A public Core store agrees with every source-visible memory cell.  Core
memory is page-sized, so bytes after the source extent are compiler-private
and are deliberately outside this relation. -/
def MemoryMatches (machine : Machine) (store : Wasm.ObservableStore) : Prop :=
  store.bytes.take machine.mem.length = machine.byteImage

namespace MemoryMatches

theorem congrMachine {first second : Machine} {store : Wasm.ObservableStore}
    (memory : first.mem = second.mem)
    (hmatches : MemoryMatches first store) : MemoryMatches second store := by
  simpa [MemoryMatches, Machine.byteImage, memory] using hmatches

end MemoryMatches

/-- **SPEC §11.4, source side.**  A checked GNAF plan accepts a public
execution observation exactly when it is a normal `i32` return of the status
computed by the independent plan semantics, its entry memory is the installed
raw source image, and its final memory is the complete byte image produced by
source evaluation.  The closed public profile has one possible non-memory
effect observation, required here explicitly.

The trace is retained by the observation but is not source behavior: compiler
refinement proves the result and frame facts for every relational trace. -/
def Accepts {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (raw : G.RawInvocation)
    (observation : Wasm.ExecutionObservation) : Prop :=
  match observation with
  | .returned _ entry value final effects =>
      let sourceEntry := initialMachine checked raw
      let sourceFinal := checked.eval sourceEntry
      MemoryMatches sourceEntry entry ∧
        returnedI32? value = some sourceFinal.status ∧
        MemoryMatches sourceFinal final ∧
        effects = Wasm.ObservableEffects.none
  | .trappedBeforeEntry _ _ _ _ | .trappedAfterEntry _ _ _ _ _ |
      .thrownBeforeEntry _ _ _ _ | .thrownAfterEntry _ _ _ _ _ => False

/-- The source result appearing in `Accepts` is exactly the closed
straight-line status transformer and is representable as a Core `i32`. -/
theorem evaluatedStatus_eq_returnedStatus {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (checked.eval (initialMachine checked raw)).status = checked.returnedStatus :=
  checked.eval_status_of_zero (initialMachine checked raw) rfl

theorem evaluatedStatus_lt_two_pow_32 {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (checked.eval (initialMachine checked raw)).status < 2 ^ 32 := by
  rw [evaluatedStatus_eq_returnedStatus]
  exact checked.returnedStatus_lt_two_pow_32

/-- For the currently admitted source fragment the independently evaluated
memory image is a frame.  This theorem is supporting evidence for the scalar
simulation only; `Accepts` itself permits and checks observable memory writes
when the admission checker is widened to the GEMM path. -/
theorem evaluatedMemory_eq_initial {P : Wasm.Profile}
    {G : Gemm.Problem P} (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    (checked.eval (initialMachine checked raw)).mem =
      (initialMachine checked raw).mem :=
  (checked.eval_frame (initialMachine checked raw)).1

end WasmGemmGnaf.GNAF
