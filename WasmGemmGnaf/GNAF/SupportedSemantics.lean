import WasmGemmGnaf.GNAF.Typing

set_option autoImplicit false

/-!
# Semantics of the independently admitted compiler fragment

`Plan.coreSupported` is the source-side admission check consumed by the direct
public-Core compiler.  This file records semantic consequences of that check;
it does not mention the compiler or a Wasm run.  In particular, every admitted
node is confined to private scalar registers, private scratch allocation, the
returned status word, and source-private output-view construction.  Raw memory,
vector registers, and code/data tables are therefore exact frames of source
evaluation; `Machine.out` is intentionally absent because `buildOutput` changes
it without changing an ABI-visible byte.

These frame equalities are the source half of the public compiler simulation.
They are proved by recursion over the complete plan language, with every
currently unsupported constructor eliminated by the executable checker.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace Plan

/-- Status transformer of the admitted straight-line fragment.  Constructors
outside that fragment are assigned the identity transformer because
`status_of_coreSupported` eliminates them before this function is used. -/
def supportedStatus : Plan → Nat → Nat
  | .seq first second, initial =>
      second.supportedStatus (first.supportedStatus initial)
  | .allocScratch _ body, initial | .opaqueProcess _ body, initial =>
      body.supportedStatus initial
  | .setStatus status, _ => status.code
  | _, initial => initial

/-- Source evaluation of every admitted plan has exactly the status computed
by the independent straight-line status transformer. -/
theorem status_of_coreSupported {P : Wasm.Profile} {G : Gemm.Problem P}
    {s : Sig} {plan : Plan}
    (supported : plan.coreSupported P G s = true) (machine : Machine) :
    (plan.eval machine).status = plan.supportedStatus machine.status := by
  induction plan generalizing machine with
  | nop => rfl
  | seq first second ihFirst ihSecond =>
      simp only [coreSupported, Bool.and_eq_true] at supported
      rw [eval_seq, ihSecond supported.2, ihFirst supported.1]
      rfl
  | classifyRaw => simp [coreSupported] at supported
  | dispatchLayout => simp [coreSupported] at supported
  | branch => simp [coreSupported] at supported
  | pack => simp [coreSupported] at supported
  | unpack => simp [coreSupported] at supported
  | storeReg => simp [coreSupported] at supported
  | loadReg => simp [coreSupported] at supported
  | loopNest => simp [coreSupported] at supported
  | loopReg => simp [coreSupported] at supported
  | tiled => simp [coreSupported] at supported
  | reduce => simp [coreSupported] at supported
  | allocScratch bytes body ih =>
      simp only [coreSupported] at supported
      simpa [eval_allocScratch, supportedStatus] using
        ih supported
          { machine with
            scratch := machine.scratch ++ List.replicate bytes 0 }
  | setReg => rfl
  | scalarOp operation =>
      cases operation <;> simp [coreSupported, coreScalarOpSupported] at supported ⊢ <;>
        rfl
  | vectorOp => simp [coreSupported] at supported
  | emitTable => simp [coreSupported] at supported
  | tableLoad => simp [coreSupported] at supported
  | setStatus => rfl
  | buildOutput => rfl
  | opaqueProcess spec body ih =>
      simp only [coreSupported] at supported
      simpa [eval_opaqueProcess, supportedStatus] using ih supported machine

/-- Starting from a wasm32 status word, the admitted fragment cannot produce a
status value outside wasm32.  The only replacement values are the closed
released `Status` codes. -/
theorem supportedStatus_lt_two_pow_32 {P : Wasm.Profile} {G : Gemm.Problem P}
    {s : Sig} {plan : Plan}
    (supported : plan.coreSupported P G s = true) {initial : Nat}
    (initialBound : initial < 2 ^ 32) :
    plan.supportedStatus initial < 2 ^ 32 := by
  induction plan generalizing initial with
  | nop => exact initialBound
  | seq first second ihFirst ihSecond =>
      simp only [coreSupported, Bool.and_eq_true] at supported
      exact ihSecond supported.2 (ihFirst supported.1 initialBound)
  | classifyRaw => simp [coreSupported] at supported
  | dispatchLayout => simp [coreSupported] at supported
  | branch => simp [coreSupported] at supported
  | pack => simp [coreSupported] at supported
  | unpack => simp [coreSupported] at supported
  | storeReg => simp [coreSupported] at supported
  | loadReg => simp [coreSupported] at supported
  | loopNest => simp [coreSupported] at supported
  | loopReg => simp [coreSupported] at supported
  | tiled => simp [coreSupported] at supported
  | reduce => simp [coreSupported] at supported
  | allocScratch bytes body ih =>
      simp only [coreSupported] at supported
      simpa [supportedStatus] using ih supported initialBound
  | setReg => exact initialBound
  | scalarOp operation =>
      cases operation <;> simp [coreSupported, coreScalarOpSupported] at supported ⊢ <;>
        exact initialBound
  | vectorOp => simp [coreSupported] at supported
  | emitTable => simp [coreSupported] at supported
  | tableLoad => simp [coreSupported] at supported
  | setStatus status =>
      cases status <;> simp [supportedStatus] <;> decide
  | buildOutput => exact initialBound
  | opaqueProcess spec body ih =>
      simp only [coreSupported] at supported
      simpa [supportedStatus] using ih supported initialBound

/-- Every plan admitted by the independent Core-support checker preserves the
source components that are observable beyond its scalar/status fragment. -/
theorem eval_frame_of_coreSupported {P : Wasm.Profile} {G : Gemm.Problem P}
    {s : Sig} {plan : Plan}
    (supported : plan.coreSupported P G s = true) (machine : Machine) :
    (plan.eval machine).mem = machine.mem ∧
      (plan.eval machine).vregs = machine.vregs ∧
      (plan.eval machine).tables = machine.tables := by
  induction plan generalizing machine with
  | nop => simp [Plan.eval]
  | seq first second ihFirst ihSecond =>
      simp only [coreSupported, Bool.and_eq_true] at supported
      rw [eval_seq]
      have firstFrame := ihFirst supported.1 machine
      have secondFrame := ihSecond supported.2 (first.eval machine)
      exact
        ⟨secondFrame.1.trans firstFrame.1,
          secondFrame.2.1.trans firstFrame.2.1,
          secondFrame.2.2.trans firstFrame.2.2⟩
  | classifyRaw => simp [coreSupported] at supported
  | dispatchLayout => simp [coreSupported] at supported
  | branch => simp [coreSupported] at supported
  | pack => simp [coreSupported] at supported
  | unpack => simp [coreSupported] at supported
  | storeReg => simp [coreSupported] at supported
  | loadReg => simp [coreSupported] at supported
  | loopNest => simp [coreSupported] at supported
  | loopReg => simp [coreSupported] at supported
  | tiled => simp [coreSupported] at supported
  | reduce => simp [coreSupported] at supported
  | allocScratch bytes body ih =>
      simp only [coreSupported] at supported
      simpa [eval_allocScratch] using
        ih supported
          { machine with
            scratch := machine.scratch ++ List.replicate bytes 0 }
  | setReg => simp [Plan.eval, Machine.withReg]
  | scalarOp operation =>
      cases operation <;> simp [coreSupported, coreScalarOpSupported] at supported ⊢ <;>
        simp [Plan.eval, Machine.withReg]
  | vectorOp => simp [coreSupported] at supported
  | emitTable => simp [coreSupported] at supported
  | tableLoad => simp [coreSupported] at supported
  | setStatus => simp [Plan.eval]
  | buildOutput => simp [Plan.eval]
  | opaqueProcess spec body ih =>
      simp only [coreSupported] at supported
      simpa [eval_opaqueProcess] using ih supported machine

end Plan

namespace CheckedPlan

/-- Public checked plans inherit the exact source frame theorem from their
retained independent support certificate. -/
theorem eval_frame {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (machine : Machine) :
    (checked.eval machine).mem = machine.mem ∧
      (checked.eval machine).vregs = machine.vregs ∧
      (checked.eval machine).tables = machine.tables := by
  exact Plan.eval_frame_of_coreSupported checked.coreSupported machine

/-- The exact source status returned by an admitted checked plan from the
fresh ABI initial status `0`. -/
def returnedStatus {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) : Nat := checked.plan.supportedStatus 0

theorem eval_status_of_zero {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) (machine : Machine) (statusZero : machine.status = 0) :
    (checked.eval machine).status = checked.returnedStatus := by
  rw [CheckedPlan.eval, Eval_apply,
    Plan.status_of_coreSupported checked.coreSupported, statusZero]
  rfl

theorem returnedStatus_lt_two_pow_32 {P : Wasm.Profile} {G : Gemm.Problem P}
    (checked : CheckedPlan P G) : checked.returnedStatus < 2 ^ 32 := by
  exact Plan.supportedStatus_lt_two_pow_32 checked.coreSupported (by decide)

end CheckedPlan

end WasmGemmGnaf.GNAF
