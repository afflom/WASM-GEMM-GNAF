import WasmGemmGnaf.Wasm.Core.ReadSuccessors

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Completeness of canonical byte-solved literals

AMD-016 restricts byte-solved floating literals to the pinned syntax sort.
This file proves that the executable little-endian decoders recover every
such literal, including the structural floating-point representation.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

open ConcreteNumerics
open WasmGemmGnaf.Foundation

private theorem fnOfBitsWith_fnBitsWith32_sign (sign : Bool)
    (magnitude : FNMag 32) (hwf : FNMag.wf magnitude = true) :
    fnOfBitsWith FloatFormat.binary32
      (fnBitsWith FloatFormat.binary32 (withSign sign magnitude)) =
        withSign sign magnitude := by
  cases magnitude with
  | norm mantissa exponent =>
      simp [FNMag.wf, signif, expon] at hwf
      have hmantissa : mantissa < 2 ^ 23 := hwf.1.1
      have hexponentLow : (-126 : Int) ≤ exponent := hwf.1.2
      have hexponentHigh : exponent ≤ (127 : Int) := hwf.2
      have hnonneg : (0 : Int) ≤ exponent + 127 := by omega
      have hupper : exponent + 127 ≤ (254 : Int) := by
        calc
          exponent + 127 ≤ 127 + 127 :=
            Int.add_le_add_right hexponentHigh 127
          _ = 254 := by decide
      have hcast : (((exponent + 127).toNat : Nat) : Int) =
          exponent + 127 := Int.toNat_of_nonneg hnonneg
      have hpositive : 0 < (exponent + 127).toNat := by
        apply Nat.zero_lt_of_ne_zero
        intro hzero
        have hzeroInt : (((exponent + 127).toNat : Nat) : Int) = 0 := by
          simp [hzero]
        rw [hcast] at hzeroInt
        omega
      have hless : (exponent + 127).toNat < 256 := by
        have hle : (exponent + 127).toNat ≤ 254 := Int.toNat_le.mpr hupper
        omega
      have hlessMax : (exponent + 127).toNat < 255 := by
        have hle : (exponent + 127).toNat ≤ 254 := Int.toNat_le.mpr hupper
        omega
      have hnotMax : (exponent + 127).toNat ≠ 255 :=
        Nat.ne_of_lt hlessMax
      let decodedClass : FloatFormat.FloatClass :=
        .normal sign (exponent + 127).toNat mantissa
      have hvalid : decodedClass.Valid FloatFormat.binary32 := by
        change 0 < (exponent + 127).toNat ∧
          (exponent + 127).toNat ≠ 255 ∧
          (exponent + 127).toNat < 256 ∧ mantissa < 2 ^ 23
        exact ⟨hpositive, hnotMax, hless, hmantissa⟩
      have hbits : fnBitsWith FloatFormat.binary32
          (withSign sign (.norm mantissa exponent) : FN 32) =
          FloatFormat.binary32.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary32 (by decide) hvalid]
      simp only [decodedClass, FloatFormat.bias, FloatFormat.binary32]
      cases sign <;> simp [withSign, hcast]
  | subnorm mantissa =>
      simp [FNMag.wf, signif] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary32.mantBits := by
        simpa [FloatFormat.binary32] using hwf
      by_cases hzero : mantissa = 0
      · subst mantissa
        let decodedClass : FloatFormat.FloatClass := .zero sign
        have hvalid : decodedClass.Valid FloatFormat.binary32 := by trivial
        have hbits : fnBitsWith FloatFormat.binary32
            (withSign sign (.subnorm 0) : FN 32) =
            FloatFormat.binary32.encode decodedClass := by
          cases sign <;> rfl
        rw [hbits]
        unfold fnOfBitsWith
        rw [FloatFormat.decode_encode FloatFormat.binary32 (by decide) hvalid]
      · let decodedClass : FloatFormat.FloatClass := .subnormal sign mantissa
        have hvalid : decodedClass.Valid FloatFormat.binary32 :=
          ⟨Nat.zero_lt_of_ne_zero hzero, hmantissa⟩
        have hbits : fnBitsWith FloatFormat.binary32
            (withSign sign (.subnorm mantissa) : FN 32) =
            FloatFormat.binary32.encode decodedClass := by
          cases sign <;> rfl
        rw [hbits]
        unfold fnOfBitsWith
        rw [FloatFormat.decode_encode FloatFormat.binary32 (by decide) hvalid]
  | inf =>
      let decodedClass : FloatFormat.FloatClass := .infinity sign
      have hvalid : decodedClass.Valid FloatFormat.binary32 := by trivial
      have hbits : fnBitsWith FloatFormat.binary32
          (withSign sign .inf : FN 32) =
          FloatFormat.binary32.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary32 (by decide) hvalid]
  | nan payload =>
      simp [FNMag.wf, signif] at hwf
      have hpayload : payload < 2 ^ FloatFormat.binary32.mantBits := by
        simpa [FloatFormat.binary32] using hwf.2
      let decodedClass : FloatFormat.FloatClass := .nan sign
        (decide (FloatFormat.binary32.quietBitMask ≤ payload)) payload
      have hvalid : decodedClass.Valid FloatFormat.binary32 :=
        ⟨by omega, hpayload, rfl⟩
      have hbits : fnBitsWith FloatFormat.binary32
          (withSign sign (.nan payload) : FN 32) =
          FloatFormat.binary32.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary32 (by decide) hvalid]

private theorem fnOfBitsWith_fnBitsWith32 (value : FN 32)
    (hwf : FN.wf value = true) :
    fnOfBitsWith FloatFormat.binary32
      (fnBitsWith FloatFormat.binary32 value) = value := by
  cases value with
  | pos magnitude =>
      simpa [FN.wf] using
        fnOfBitsWith_fnBitsWith32_sign false magnitude hwf
  | neg magnitude =>
      simpa [FN.wf] using
        fnOfBitsWith_fnBitsWith32_sign true magnitude hwf

private theorem fnOfBitsWith_fnBitsWith64_sign (sign : Bool)
    (magnitude : FNMag 64) (hwf : FNMag.wf magnitude = true) :
    fnOfBitsWith FloatFormat.binary64
      (fnBitsWith FloatFormat.binary64 (withSign sign magnitude)) =
        withSign sign magnitude := by
  cases magnitude with
  | norm mantissa exponent =>
      simp [FNMag.wf, signif, expon] at hwf
      have hmantissa : mantissa < 2 ^ 52 := hwf.1.1
      have hexponentLow : (-1022 : Int) ≤ exponent := hwf.1.2
      have hexponentHigh : exponent ≤ (1023 : Int) := hwf.2
      have hnonneg : (0 : Int) ≤ exponent + 1023 := by omega
      have hupper : exponent + 1023 ≤ (2046 : Int) := by
        calc
          exponent + 1023 ≤ 1023 + 1023 :=
            Int.add_le_add_right hexponentHigh 1023
          _ = 2046 := by decide
      have hcast : (((exponent + 1023).toNat : Nat) : Int) =
          exponent + 1023 := Int.toNat_of_nonneg hnonneg
      have hpositive : 0 < (exponent + 1023).toNat := by
        apply Nat.zero_lt_of_ne_zero
        intro hzero
        have hzeroInt : (((exponent + 1023).toNat : Nat) : Int) = 0 := by
          simp [hzero]
        rw [hcast] at hzeroInt
        omega
      have hless : (exponent + 1023).toNat < 2048 := by
        have hle : (exponent + 1023).toNat ≤ 2046 := Int.toNat_le.mpr hupper
        omega
      have hlessMax : (exponent + 1023).toNat < 2047 := by
        have hle : (exponent + 1023).toNat ≤ 2046 := Int.toNat_le.mpr hupper
        omega
      have hnotMax : (exponent + 1023).toNat ≠ 2047 :=
        Nat.ne_of_lt hlessMax
      let decodedClass : FloatFormat.FloatClass :=
        .normal sign (exponent + 1023).toNat mantissa
      have hvalid : decodedClass.Valid FloatFormat.binary64 := by
        change 0 < (exponent + 1023).toNat ∧
          (exponent + 1023).toNat ≠ 2047 ∧
          (exponent + 1023).toNat < 2048 ∧ mantissa < 2 ^ 52
        exact ⟨hpositive, hnotMax, hless, hmantissa⟩
      have hbits : fnBitsWith FloatFormat.binary64
          (withSign sign (.norm mantissa exponent) : FN 64) =
          FloatFormat.binary64.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary64 (by decide) hvalid]
      simp only [decodedClass, FloatFormat.bias, FloatFormat.binary64]
      cases sign <;> simp [withSign, hcast]
  | subnorm mantissa =>
      simp [FNMag.wf, signif] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary64.mantBits := by
        simpa [FloatFormat.binary64] using hwf
      by_cases hzero : mantissa = 0
      · subst mantissa
        let decodedClass : FloatFormat.FloatClass := .zero sign
        have hvalid : decodedClass.Valid FloatFormat.binary64 := by trivial
        have hbits : fnBitsWith FloatFormat.binary64
            (withSign sign (.subnorm 0) : FN 64) =
            FloatFormat.binary64.encode decodedClass := by
          cases sign <;> rfl
        rw [hbits]
        unfold fnOfBitsWith
        rw [FloatFormat.decode_encode FloatFormat.binary64 (by decide) hvalid]
      · let decodedClass : FloatFormat.FloatClass := .subnormal sign mantissa
        have hvalid : decodedClass.Valid FloatFormat.binary64 :=
          ⟨Nat.zero_lt_of_ne_zero hzero, hmantissa⟩
        have hbits : fnBitsWith FloatFormat.binary64
            (withSign sign (.subnorm mantissa) : FN 64) =
            FloatFormat.binary64.encode decodedClass := by
          cases sign <;> rfl
        rw [hbits]
        unfold fnOfBitsWith
        rw [FloatFormat.decode_encode FloatFormat.binary64 (by decide) hvalid]
  | inf =>
      let decodedClass : FloatFormat.FloatClass := .infinity sign
      have hvalid : decodedClass.Valid FloatFormat.binary64 := by trivial
      have hbits : fnBitsWith FloatFormat.binary64
          (withSign sign .inf : FN 64) =
          FloatFormat.binary64.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary64 (by decide) hvalid]
  | nan payload =>
      simp [FNMag.wf, signif] at hwf
      have hpayload : payload < 2 ^ FloatFormat.binary64.mantBits := by
        simpa [FloatFormat.binary64] using hwf.2
      let decodedClass : FloatFormat.FloatClass := .nan sign
        (decide (FloatFormat.binary64.quietBitMask ≤ payload)) payload
      have hvalid : decodedClass.Valid FloatFormat.binary64 :=
        ⟨by omega, hpayload, rfl⟩
      have hbits : fnBitsWith FloatFormat.binary64
          (withSign sign (.nan payload) : FN 64) =
          FloatFormat.binary64.encode decodedClass := by
        cases sign <;> rfl
      rw [hbits]
      unfold fnOfBitsWith
      rw [FloatFormat.decode_encode FloatFormat.binary64 (by decide) hvalid]

private theorem fnOfBitsWith_fnBitsWith64 (value : FN 64)
    (hwf : FN.wf value = true) :
    fnOfBitsWith FloatFormat.binary64
      (fnBitsWith FloatFormat.binary64 value) = value := by
  cases value with
  | pos magnitude =>
      simpa [FN.wf] using
        fnOfBitsWith_fnBitsWith64_sign false magnitude hwf
  | neg magnitude =>
      simpa [FN.wf] using
        fnOfBitsWith_fnBitsWith64_sign true magnitude hwf

private theorem fnBitsWith32_sign_lt (sign : Bool) (magnitude : FNMag 32)
    (hwf : FNMag.wf magnitude = true) :
    fnBitsWith FloatFormat.binary32 (withSign sign magnitude) < 2 ^ 32 := by
  cases magnitude with
  | norm mantissa exponent =>
      simp [FNMag.wf, signif, expon] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary32.mantBits := by
        simpa [FloatFormat.binary32] using hwf.1.1
      have hnonneg : (0 : Int) ≤ exponent + 127 := by omega
      have hexponentHigh : exponent ≤ (127 : Int) := hwf.2
      have hupper : exponent + 127 ≤ (254 : Int) := by
        calc
          exponent + 127 ≤ 127 + 127 :=
            Int.add_le_add_right hexponentHigh 127
          _ = 254 := by decide
      have hexponent : (exponent + 127).toNat <
          2 ^ FloatFormat.binary32.expBits := by
        change (exponent + 127).toNat < 256
        have hle : (exponent + 127).toNat ≤ 254 := Int.toNat_le.mpr hupper
        omega
      have hpack := FloatFormat.pack_lt FloatFormat.binary32 sign
        hexponent hmantissa
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary32] using hpack
  | subnorm mantissa =>
      simp [FNMag.wf, signif] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary32.mantBits := by
        simpa [FloatFormat.binary32] using hwf
      have hpack := FloatFormat.pack_lt FloatFormat.binary32 sign
        (Nat.two_pow_pos 8) hmantissa
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary32] using hpack
  | inf =>
      have hpack := FloatFormat.pack_lt FloatFormat.binary32 sign
        (FloatFormat.expMax_lt FloatFormat.binary32) (Nat.two_pow_pos 23)
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary32, FloatFormat.expMax] using hpack
  | nan payload =>
      simp [FNMag.wf, signif] at hwf
      have hpayload : payload < 2 ^ FloatFormat.binary32.mantBits := by
        simpa [FloatFormat.binary32] using hwf.2
      have hpack := FloatFormat.pack_lt FloatFormat.binary32 sign
        (FloatFormat.expMax_lt FloatFormat.binary32) hpayload
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary32, FloatFormat.expMax] using hpack

private theorem fnBitsWith32_lt (value : FN 32) (hwf : FN.wf value = true) :
    fnBitsWith FloatFormat.binary32 value < 2 ^ 32 := by
  cases value with
  | pos magnitude =>
      simpa [FN.wf] using fnBitsWith32_sign_lt false magnitude hwf
  | neg magnitude =>
      simpa [FN.wf] using fnBitsWith32_sign_lt true magnitude hwf

private theorem fnBitsWith64_sign_lt (sign : Bool) (magnitude : FNMag 64)
    (hwf : FNMag.wf magnitude = true) :
    fnBitsWith FloatFormat.binary64 (withSign sign magnitude) < 2 ^ 64 := by
  cases magnitude with
  | norm mantissa exponent =>
      simp [FNMag.wf, signif, expon] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary64.mantBits := by
        simpa [FloatFormat.binary64] using hwf.1.1
      have hnonneg : (0 : Int) ≤ exponent + 1023 := by omega
      have hexponentHigh : exponent ≤ (1023 : Int) := hwf.2
      have hupper : exponent + 1023 ≤ (2046 : Int) := by
        calc
          exponent + 1023 ≤ 1023 + 1023 :=
            Int.add_le_add_right hexponentHigh 1023
          _ = 2046 := by decide
      have hexponent : (exponent + 1023).toNat <
          2 ^ FloatFormat.binary64.expBits := by
        change (exponent + 1023).toNat < 2048
        have hle : (exponent + 1023).toNat ≤ 2046 :=
          Int.toNat_le.mpr hupper
        omega
      have hpack := FloatFormat.pack_lt FloatFormat.binary64 sign
        hexponent hmantissa
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary64] using hpack
  | subnorm mantissa =>
      simp [FNMag.wf, signif] at hwf
      have hmantissa : mantissa < 2 ^ FloatFormat.binary64.mantBits := by
        simpa [FloatFormat.binary64] using hwf
      have hpack := FloatFormat.pack_lt FloatFormat.binary64 sign
        (Nat.two_pow_pos 11) hmantissa
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary64] using hpack
  | inf =>
      have hpack := FloatFormat.pack_lt FloatFormat.binary64 sign
        (FloatFormat.expMax_lt FloatFormat.binary64) (Nat.two_pow_pos 52)
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary64, FloatFormat.expMax] using hpack
  | nan payload =>
      simp [FNMag.wf, signif] at hwf
      have hpayload : payload < 2 ^ FloatFormat.binary64.mantBits := by
        simpa [FloatFormat.binary64] using hwf.2
      have hpack := FloatFormat.pack_lt FloatFormat.binary64 sign
        (FloatFormat.expMax_lt FloatFormat.binary64) hpayload
      cases sign <;> simpa [fnBitsWith, fnSign, fnMag, withSign,
        FloatFormat.binary64, FloatFormat.expMax] using hpack

private theorem fnBitsWith64_lt (value : FN 64) (hwf : FN.wf value = true) :
    fnBitsWith FloatFormat.binary64 value < 2 ^ 64 := by
  cases value with
  | pos magnitude =>
      simpa [FN.wf] using fnBitsWith64_sign_lt false magnitude hwf
  | neg magnitude =>
      simpa [FN.wf] using fnBitsWith64_sign_lt true magnitude hwf

private theorem mod_mul_digits (value base radix : Nat) :
    value % base + base * (value / base % radix) =
      value % (base * radix) := by
  let reduced := value % (base * radix)
  calc
    value % base + base * (value / base % radix) =
        reduced % base + base * (reduced / base) := by
      rw [show reduced % base = value % base by
        exact Nat.mod_mul_right_mod value base radix,
        show reduced / base = value / base % radix by
          exact Nat.mod_mul_right_div_self value base radix]
    _ = reduced := Nat.mod_add_div reduced base

private theorem leNat_append (left right : List Byte) :
    Binary.leNat (left ++ right) =
      Binary.leNat left + 256 ^ left.length * Binary.leNat right := by
  induction left with
  | nil => simp [Binary.leNat]
  | cons head tail ih =>
      simp [Binary.leNat, ih, Nat.pow_succ, Nat.mul_add,
        Nat.mul_comm, Nat.add_assoc]
      ac_rfl

private theorem leNat_digits (value count : Nat) :
    Binary.leNat ((List.range count).map
      (fun position => Byte.ofNat (value / 2 ^ (8 * position)))) =
        value % 2 ^ (8 * count) := by
  induction count with
  | zero => simp [Binary.leNat, Nat.mod_one]
  | succ count ih =>
      rw [List.range_succ, List.map_append, leNat_append, ih]
      simp only [List.map_singleton, List.length_map, List.length_range,
        Binary.leNat]
      change value % 2 ^ (8 * count) + 256 ^ count *
          (value / 2 ^ (8 * count) % 256) =
        value % 2 ^ (8 * (count + 1))
      have hpow : 256 ^ count = 2 ^ (8 * count) := by
        rw [show 256 = 2 ^ 8 by decide, Nat.pow_mul]
      rw [hpow]
      rw [show 2 ^ (8 * (count + 1)) = 2 ^ (8 * count) * 256 by
        rw [show 8 * (count + 1) = 8 * count + 8 by omega, Nat.pow_add]]
      exact mod_mul_digits value (2 ^ (8 * count)) 256

private theorem invFbytes32_eq_fnOfBitsWith {bytes : List Byte}
    (hlength : bytes.length = 4) :
    Binary.invFbytes 32 bytes = some
      (fnOfBitsWith FloatFormat.binary32 (Binary.leNat bytes)) := by
  unfold Binary.invFbytes fnOfBitsWith FloatFormat.decode
  simp only [signif, expon, hlength, if_pos]
  have hsign : Binary.leNat bytes / 2 ^ (23 + 8) % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have hsignCases : Binary.leNat bytes / 2 ^ (23 + 8) % 2 = 0 ∨
      Binary.leNat bytes / 2 ^ (23 + 8) % 2 = 1 := by omega
  rcases hsignCases with hsignZero | hsignOne
  · by_cases hexponentZero : Binary.leNat bytes / 2 ^ 23 % 2 ^ 8 = 0
    · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 23 = 0 <;>
        simp [FloatFormat.binary32, FloatFormat.mantOf, FloatFormat.expOf,
          FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
          hsignZero, hexponentZero, hmantissaZero, withSign]
    · by_cases hexponentMax :
          Binary.leNat bytes / 2 ^ 23 % 2 ^ 8 = 255
      · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 23 = 0 <;>
          simp [FloatFormat.binary32, FloatFormat.mantOf, FloatFormat.expOf,
            FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
            hsignZero, hexponentZero, hexponentMax, hmantissaZero, withSign]
      · simp [FloatFormat.binary32, FloatFormat.mantOf,
          FloatFormat.expOf, FloatFormat.signOf, FloatFormat.expMax,
          FloatFormat.bias, hsignZero, hexponentZero, hexponentMax, withSign]
  · have hsignNotZero :
        ¬ Binary.leNat bytes / 2 ^ (23 + 8) % 2 = 0 := by omega
    by_cases hexponentZero : Binary.leNat bytes / 2 ^ 23 % 2 ^ 8 = 0
    · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 23 = 0 <;>
        simp [FloatFormat.binary32, FloatFormat.mantOf, FloatFormat.expOf,
          FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
          hsignNotZero, hsignOne, hexponentZero, hmantissaZero, withSign]
    · by_cases hexponentMax :
          Binary.leNat bytes / 2 ^ 23 % 2 ^ 8 = 255
      · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 23 = 0 <;>
          simp [FloatFormat.binary32, FloatFormat.mantOf, FloatFormat.expOf,
            FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
            hsignNotZero, hsignOne, hexponentZero, hexponentMax,
            hmantissaZero, withSign]
      · simp [FloatFormat.binary32, FloatFormat.mantOf,
          FloatFormat.expOf, FloatFormat.signOf, FloatFormat.expMax,
          FloatFormat.bias, hsignNotZero, hsignOne, hexponentZero,
          hexponentMax, withSign]

private theorem invFbytes64_eq_fnOfBitsWith {bytes : List Byte}
    (hlength : bytes.length = 8) :
    Binary.invFbytes 64 bytes = some
      (fnOfBitsWith FloatFormat.binary64 (Binary.leNat bytes)) := by
  unfold Binary.invFbytes fnOfBitsWith FloatFormat.decode
  simp only [signif, expon, hlength, if_pos]
  have hsign : Binary.leNat bytes / 2 ^ (52 + 11) % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have hsignCases : Binary.leNat bytes / 2 ^ (52 + 11) % 2 = 0 ∨
      Binary.leNat bytes / 2 ^ (52 + 11) % 2 = 1 := by omega
  rcases hsignCases with hsignZero | hsignOne
  · by_cases hexponentZero : Binary.leNat bytes / 2 ^ 52 % 2 ^ 11 = 0
    · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 52 = 0 <;>
        simp [FloatFormat.binary64, FloatFormat.mantOf, FloatFormat.expOf,
          FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
          hsignZero, hexponentZero, hmantissaZero, withSign]
    · by_cases hexponentMax :
          Binary.leNat bytes / 2 ^ 52 % 2 ^ 11 = 2047
      · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 52 = 0 <;>
          simp [FloatFormat.binary64, FloatFormat.mantOf, FloatFormat.expOf,
            FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
            hsignZero, hexponentZero, hexponentMax, hmantissaZero, withSign]
      · simp [FloatFormat.binary64, FloatFormat.mantOf,
          FloatFormat.expOf, FloatFormat.signOf, FloatFormat.expMax,
          FloatFormat.bias, hsignZero, hexponentZero, hexponentMax, withSign]
  · have hsignNotZero :
        ¬ Binary.leNat bytes / 2 ^ (52 + 11) % 2 = 0 := by omega
    by_cases hexponentZero : Binary.leNat bytes / 2 ^ 52 % 2 ^ 11 = 0
    · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 52 = 0 <;>
        simp [FloatFormat.binary64, FloatFormat.mantOf, FloatFormat.expOf,
          FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
          hsignNotZero, hsignOne, hexponentZero, hmantissaZero, withSign]
    · by_cases hexponentMax :
          Binary.leNat bytes / 2 ^ 52 % 2 ^ 11 = 2047
      · by_cases hmantissaZero : Binary.leNat bytes % 2 ^ 52 = 0 <;>
          simp [FloatFormat.binary64, FloatFormat.mantOf, FloatFormat.expOf,
            FloatFormat.signOf, FloatFormat.expMax, FloatFormat.bias,
            hsignNotZero, hsignOne, hexponentZero, hexponentMax,
            hmantissaZero, withSign]
      · simp [FloatFormat.binary64, FloatFormat.mantOf,
          FloatFormat.expOf, FloatFormat.signOf, FloatFormat.expMax,
          FloatFormat.bias, hsignNotZero, hsignOne, hexponentZero,
          hexponentMax, withSign]

/-- The canonical full-width numeric decoder recovers every AMD-016-sorted
literal from its semantic little-endian byte representation. -/
theorem nbytes_length_eq_size_div_eight {type : NumType}
    (value : Num_ type) :
    (releasedNumerics.nbytes_ type value).length = type.size / 8 := by
  cases type <;>
    simp [ConcreteNumerics.nbytes, ConcreteNumerics.ibytes, NumType.size]

theorem ofNatWrap_leNat_ibytes {width : Nat} (value : IN width)
    (hmultiple : 8 * (width / 8) = width) :
    Numerics.ofNatWrap width
        (Binary.leNat (releasedNumerics.ibytes_ width value)) = value := by
  apply Subtype.ext
  simpa [ConcreteNumerics.ibytes, Numerics.ofNatWrap, leNat_digits,
    hmultiple, Nat.mod_eq_of_lt value.property]
    using value.property

theorem ofNatWrap_leNat_vbytes_v128 (value : V128Lit) :
    Numerics.ofNatWrap 128
        (Binary.leNat (releasedNumerics.vbytes_ .v128 value)) = value := by
  simpa [ConcreteNumerics.vbytes] using
    ofNatWrap_leNat_ibytes value (by decide)

theorem numOfBytes?_nbytes_complete {type : NumType} (value : Num_ type)
    (hwf : ByteSolvedNumWfFor (authority := amendedExecutionAuthority)
      type value) :
    numOfBytes? type (releasedNumerics.nbytes_ type value) = some value := by
  cases type with
  | i32 =>
      apply congrArg some
      apply Subtype.ext
      simpa [numOfBytes?, ConcreteNumerics.nbytes, ConcreteNumerics.ibytes,
        Numerics.ofNatWrap, leNat_digits] using value.property
  | i64 =>
      apply congrArg some
      apply Subtype.ext
      simpa [numOfBytes?, ConcreteNumerics.nbytes, ConcreteNumerics.ibytes,
        Numerics.ofNatWrap, leNat_digits] using value.property
  | f32 =>
      change Binary.invFbytes 32 (ConcreteNumerics.nbytes .f32 value) =
        some value
      have hbits := fnBitsWith32_lt value hwf
      have hbitsNumeral : fnBitsWith FloatFormat.binary32 value <
          4294967296 := by simpa using hbits
      have hlength : (ConcreteNumerics.nbytes .f32 value).length = 4 := by
        simp [ConcreteNumerics.nbytes, ConcreteNumerics.ibytes]
      have hleNat : Binary.leNat (ConcreteNumerics.nbytes .f32 value) =
          fnBitsWith FloatFormat.binary32 value := by
        simp [ConcreteNumerics.nbytes, ConcreteNumerics.ibytes,
          Numerics.ofNatWrap, leNat_digits,
          Nat.mod_eq_of_lt hbitsNumeral]
      rw [invFbytes32_eq_fnOfBitsWith hlength, hleNat]
      exact congrArg some (fnOfBitsWith_fnBitsWith32 value hwf)
  | f64 =>
      change Binary.invFbytes 64 (ConcreteNumerics.nbytes .f64 value) =
        some value
      have hbits := fnBitsWith64_lt value hwf
      have hbitsNumeral : fnBitsWith FloatFormat.binary64 value <
          18446744073709551616 := by simpa using hbits
      have hlength : (ConcreteNumerics.nbytes .f64 value).length = 8 := by
        simp [ConcreteNumerics.nbytes, ConcreteNumerics.ibytes]
      have hleNat : Binary.leNat (ConcreteNumerics.nbytes .f64 value) =
          fnBitsWith FloatFormat.binary64 value := by
        simp [ConcreteNumerics.nbytes, ConcreteNumerics.ibytes,
          Numerics.ofNatWrap, leNat_digits,
          Nat.mod_eq_of_lt hbitsNumeral]
      rw [invFbytes64_eq_fnOfBitsWith hlength, hleNat]
      exact congrArg some (fnOfBitsWith_fnBitsWith64 value hwf)

/-- The canonical fixed-width storage decoder recovers every AMD-016-sorted
literal from its semantic bytes. -/
theorem storageLiteralCandidate?_zbytes_complete {storage : StorageType}
    (literal : Lit_ storage)
    (hwf : ByteSolvedLiteralWfFor
      (authority := amendedExecutionAuthority) storage literal) :
    storageLiteralCandidate? storage
      (releasedNumerics.zbytes_ storage literal) = some literal := by
  cases storage with
  | val type =>
      cases type with
      | num numberType => exact numOfBytes?_nbytes_complete literal hwf
      | vec vectorType =>
          cases vectorType
          apply congrArg some
          apply Subtype.ext
          simpa [storageLiteralCandidate?, ConcreteNumerics.zbytes,
            ConcreteNumerics.vbytes, ConcreteNumerics.ibytes,
            Numerics.ofNatWrap, leNat_digits] using literal.property
      | ref referenceType => exact literal.elim
      | bot => exact literal.elim
  | pack packType =>
      cases packType with
      | i8 =>
          apply congrArg some
          apply Subtype.ext
          have hbound : literal.val < 256 := by
            simpa [PackType.size] using literal.property
          simp [ConcreteNumerics.zbytes, ConcreteNumerics.ibytes,
            Binary.leNat, Numerics.ofNatWrap, PackType.size,
            Nat.mod_eq_of_lt hbound]
          rw [Byte.ofNat]
          simp [Nat.mod_eq_of_lt hbound]
      | i16 =>
          apply congrArg some
          apply Subtype.ext
          have hbound : literal.val < 65536 := by
            simpa [PackType.size] using literal.property
          simp [ConcreteNumerics.zbytes, ConcreteNumerics.ibytes,
            Numerics.ofNatWrap, PackType.size, leNat_digits,
            Nat.mod_eq_of_lt hbound]

/-- Repeated canonical decoding recovers a list of sorted, equally wide
storage literals from the flattening of their semantic bytes. -/
theorem storageLiteralCandidates_zbytes_complete (storage : StorageType)
    (width : Nat) :
    ∀ (literals : List (Lit_ storage)),
      (∀ literal ∈ literals,
        (releasedNumerics.zbytes_ storage literal).length = width) →
      (∀ literal ∈ literals,
        ByteSolvedLiteralWfFor (authority := amendedExecutionAuthority)
          storage literal) →
      storageLiteralCandidates storage width literals.length
          (literals.map (fun literal =>
            releasedNumerics.zbytes_ storage literal)).flatten = some literals
  | [], _, _ => by simp [storageLiteralCandidates]
  | head :: tail, hwidth, hwf => by
      have hheadWidth := hwidth head List.mem_cons_self
      have hheadWf := hwf head List.mem_cons_self
      have htailWidth : ∀ literal ∈ tail,
          (releasedNumerics.zbytes_ storage literal).length = width := by
        intro literal hmem
        exact hwidth literal (List.mem_cons_of_mem head hmem)
      have htailWf : ∀ literal ∈ tail,
          ByteSolvedLiteralWfFor (authority := amendedExecutionAuthority)
            storage literal := by
        intro literal hmem
        exact hwf literal (List.mem_cons_of_mem head hmem)
      simp only [List.length_cons, List.map_cons, List.flatten_cons,
        storageLiteralCandidates]
      rw [show slice
          (releasedNumerics.zbytes_ storage head ++
            (tail.map (fun literal =>
              releasedNumerics.zbytes_ storage literal)).flatten)
          0 width = releasedNumerics.zbytes_ storage head by
        unfold slice
        simp only [List.drop_zero]
        rw [← hheadWidth]
        simp]
      rw [storageLiteralCandidate?_zbytes_complete head hheadWf]
      rw [show (releasedNumerics.zbytes_ storage head ++
            (tail.map (fun literal =>
              releasedNumerics.zbytes_ storage literal)).flatten).drop width =
          (tail.map (fun literal =>
            releasedNumerics.zbytes_ storage literal)).flatten by
        rw [← hheadWidth]
        simp]
      rw [storageLiteralCandidates_zbytes_complete storage width tail
        htailWidth htailWf]
      rfl

end WasmGemmGnaf.Wasm.Core.Exec
