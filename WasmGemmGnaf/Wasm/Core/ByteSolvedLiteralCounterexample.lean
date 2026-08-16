import WasmGemmGnaf.Wasm.Core.Execution

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Exec

private def rawZeroF32 : F32 := .pos (.subnorm 0)

private def rawWrappedF32 : F32 := .pos (.subnorm (2 ^ 32))

private theorem rawZeroF32_ne_rawWrappedF32 :
    rawZeroF32 ≠ rawWrappedF32 := by
  decide

private theorem rawZeroF32_bytes_eq_rawWrappedF32 :
    ConcreteNumerics.nbytes .f32 rawZeroF32 =
      ConcreteNumerics.nbytes .f32 rawWrappedF32 := by
  decide

private def rawZeroLoadMemory : MemInst :=
  { type := default
    bytes := [default, default, default, default] }

private def rawZeroLoadState : State :=
  { store := { mems := [rawZeroLoadMemory] }
    frame := { mod := { mems := [0] } } }

private theorem rawZeroLoadState_memOf :
    rawZeroLoadState.memOf (⟨0, by decide⟩ : MemIdx) =
      some rawZeroLoadMemory := by
  decide

private theorem rawZeroLoadState_zeroBytes :
    ConcreteNumerics.nbytes .f32 rawZeroF32 =
      slice rawZeroLoadMemory.bytes 0 (32 / 8) := by
  decide

/-- Without AMD-016's explicit rendering of the pinned numeric syntax sort,
raw `FN` constructors make a fixed `load-num-val` source admit distinct targets
with identical bytes. -/
theorem step_read_loadNumVal_raw_not_target_functional :
    ¬ (∀ {z : State} {rule : ReadRule}
        {source left right : List AdminInstr},
      @Step_read pinnedExecutionAuthority releasedNumerics
          z rule source left →
      @Step_read pinnedExecutionAuthority releasedNumerics
          z rule source right →
      left = right) := by
  intro functional
  let memoryIndex : MemIdx := ⟨0, by decide⟩
  let address : AddrLit .i32 := ⟨0, by decide⟩
  let source :=
    [constAddr .i32 address,
      AdminInstr.plain (.load .f32 none memoryIndex .zero)]
  let left := [AdminInstr.plain (.const .f32 rawZeroF32)]
  let right := [AdminInstr.plain (.const .f32 rawWrappedF32)]
  have hwrapped :
      ConcreteNumerics.nbytes .f32 rawWrappedF32 =
        slice rawZeroLoadMemory.bytes
          (address.val + MemArg.zero.offset.val) (32 / 8) := by
    rw [← rawZeroF32_bytes_eq_rawWrappedF32]
    simpa [address, MemArg.zero] using rawZeroLoadState_zeroBytes
  have hleft :
      @Step_read pinnedExecutionAuthority releasedNumerics
        rawZeroLoadState .loadNumVal source left := by
    exact Step_read.loadNumVal rawZeroLoadState_memOf
      (by simpa [address, MemArg.zero] using rawZeroLoadState_zeroBytes) trivial
  have hright :
      @Step_read pinnedExecutionAuthority releasedNumerics
        rawZeroLoadState .loadNumVal source right := by
    exact Step_read.loadNumVal rawZeroLoadState_memOf hwrapped trivial
  have heq := functional hleft hright
  have hinstruction := (List.cons.inj heq).1
  have hconst := AdminInstr.plain.inj hinstruction
  injection hconst with _ hliteral
  exact rawZeroF32_ne_rawWrappedF32 hliteral

end WasmGemmGnaf.Wasm.Core.Exec
