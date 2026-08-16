import WasmGemmGnaf.GNAF.Semantics
import WasmGemmGnaf.Wasm.Core.ConcreteNumerics
import WasmGemmGnaf.Wasm.Core.Runtime

set_option autoImplicit false

namespace WasmGemmGnaf.GNAF

open Wasm.Core

/-- The released Core `i32` byte image is the GNAF source machine's
little-endian four-byte image. -/
theorem map_released_nbytes_i32 (x : U32) :
    (Exec.releasedNumerics.nbytes_ .i32 x).map Subtype.val =
      leBytes x.val 4 := by
  simp [Exec.releasedNumerics, Exec.ConcreteNumerics.released,
    Exec.ConcreteNumerics.nbytes, Exec.ConcreteNumerics.ibytes, leBytes,
    Nat.div_div_eq_div_mul, List.range_succ, Byte.ofNat]

/-- The released Core `i64` byte image is the GNAF source machine's
little-endian eight-byte image. -/
theorem map_released_nbytes_i64 (x : U64) :
    (Exec.releasedNumerics.nbytes_ .i64 x).map Subtype.val =
      leBytes x.val 8 := by
  simp [Exec.releasedNumerics, Exec.ConcreteNumerics.released,
    Exec.ConcreteNumerics.nbytes, Exec.ConcreteNumerics.ibytes, leBytes,
    Nat.div_div_eq_div_mul, List.range_succ, Byte.ofNat]

/-- A released Core `i32` load equation determines exactly the source
little-endian word at that address. -/
theorem leWord_of_released_nbytes_i32
    {bytes : List Byte} {addr : Nat} {x : U32}
    (h : Exec.releasedNumerics.nbytes_ .i32 x =
      Exec.slice bytes addr 4) :
    leWord (bytes.map Subtype.val) addr 4 = x.val := by
  have hlen : (Exec.slice bytes addr 4).length = 4 := by
    rw [← h]
    simp [Exec.releasedNumerics, Exec.ConcreteNumerics.released,
      Exec.ConcreteNumerics.nbytes, Exec.ConcreteNumerics.ibytes]
  have hwindow : addr + 4 ≤ bytes.length := by
    simp [Exec.slice, List.length_take, List.length_drop] at hlen
    omega
  have hmap :
      (Exec.releasedNumerics.nbytes_ .i32 x).map Subtype.val =
        Exec.slice (bytes.map Subtype.val) addr 4 := by
    rw [h]
    simp [Exec.slice]
  calc
    leWord (bytes.map Subtype.val) addr 4 =
        leWord (Exec.slice (bytes.map Subtype.val) addr 4) 0 4 := by
      apply leWord_ext
      intro k hk
      have hindex : addr + k < bytes.length := by omega
      simp [Exec.slice, List.getD_eq_getElem?_getD,
        List.getElem?_drop, hk, hindex]
    _ = leWord ((Exec.releasedNumerics.nbytes_ .i32 x).map
        Subtype.val) 0 4 := by rw [hmap]
    _ = leWord (leBytes x.val 4) 0 4 := by
      rw [map_released_nbytes_i32]
    _ = x.val % 256 ^ 4 := leWord_leBytes 4 x.val
    _ = x.val := by
      apply Nat.mod_eq_of_lt
      simpa using x.property

/-- A released Core `i64` load equation determines exactly the source
little-endian word at that address. -/
theorem leWord_of_released_nbytes_i64
    {bytes : List Byte} {addr : Nat} {x : U64}
    (h : Exec.releasedNumerics.nbytes_ .i64 x =
      Exec.slice bytes addr 8) :
    leWord (bytes.map Subtype.val) addr 8 = x.val := by
  have hlen : (Exec.slice bytes addr 8).length = 8 := by
    rw [← h]
    simp [Exec.releasedNumerics, Exec.ConcreteNumerics.released,
      Exec.ConcreteNumerics.nbytes, Exec.ConcreteNumerics.ibytes]
  have hwindow : addr + 8 ≤ bytes.length := by
    simp [Exec.slice, List.length_take, List.length_drop] at hlen
    omega
  have hmap :
      (Exec.releasedNumerics.nbytes_ .i64 x).map Subtype.val =
        Exec.slice (bytes.map Subtype.val) addr 8 := by
    rw [h]
    simp [Exec.slice]
  calc
    leWord (bytes.map Subtype.val) addr 8 =
        leWord (Exec.slice (bytes.map Subtype.val) addr 8) 0 8 := by
      apply leWord_ext
      intro k hk
      have hindex : addr + k < bytes.length := by omega
      simp [Exec.slice, List.getD_eq_getElem?_getD,
        List.getElem?_drop, hk, hindex]
    _ = leWord ((Exec.releasedNumerics.nbytes_ .i64 x).map
        Subtype.val) 0 8 := by rw [hmap]
    _ = leWord (leBytes x.val 8) 0 8 := by
      rw [map_released_nbytes_i64]
    _ = x.val % 256 ^ 8 := leWord_leBytes 8 x.val
    _ = x.val := by
      apply Nat.mod_eq_of_lt
      simpa using x.property

end WasmGemmGnaf.GNAF
