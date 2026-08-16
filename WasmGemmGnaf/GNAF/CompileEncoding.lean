import WasmGemmGnaf.GNAF.Compile

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Constructive amended-Core encoding of compiled GNAF plans

This module proves, by structural recursion over the source plan, that every
instruction sequence produced by the direct compiler has concrete amended-Core
binary bytes.  The proof does not call a native evaluator and does not assume
encoder completeness: each primitive instruction is related to its declarative
binary production, and sequence/control encodings are composed explicitly.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf

namespace DirectEncoding

def EncodedInstr (i : Wasm.Core.Instr) : Prop :=
  ∃ bs, @Wasm.Core.Binary.encInstr Wasm.Core.Binary.amendedBinaryAuthority i = some bs ∧
    bs.length ≤ 16 * Wasm.Core.Binary.instrSize i

def EncodedSeq (is : List Wasm.Core.Instr) : Prop :=
  ∃ bs, @Wasm.Core.Binary.encInstrs Wasm.Core.Binary.amendedBinaryAuthority
      (Wasm.Core.InstrSeq.ofList is) = some bs ∧
    bs.length ≤ 16 * Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList is)

theorem lebU_u32_length_le (n : Wasm.Core.U32) :
    (Wasm.Core.Binary.lebU n.val).length ≤ 5 := by
  have hn : n.val ≤ 2 ^ 32 - 1 := by omega
  have h := Wasm.Core.Binary.lebU_length_mono hn
  have hm : (Wasm.Core.Binary.lebU (2 ^ 32 - 1)).length = 5 := by decide
  omega

theorem lebU_u64_length_le (n : Wasm.Core.U64) :
    (Wasm.Core.Binary.lebU n.val).length ≤ 10 := by
  have hn : n.val ≤ 2 ^ 64 - 1 := by omega
  have h := Wasm.Core.Binary.lebU_length_mono hn
  have hm : (Wasm.Core.Binary.lebU (2 ^ 64 - 1)).length = 10 := by decide
  omega

theorem encoded_of_binstr {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : @Wasm.Core.Binary.Binstr Wasm.Core.Binary.amendedBinaryAuthority bs i)
    (hlen : bs.length ≤ 16 * Wasm.Core.Binary.instrSize i) : EncodedInstr i := by
  obtain ⟨out, hout, houtlen⟩ :=
    @Wasm.Core.Binary.encInstr_completeLe
      Wasm.Core.Binary.amendedBinaryAuthority bs i h
  exact ⟨out, hout, Nat.le_trans houtlen hlen⟩

theorem encoded_pinned_num {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : Wasm.Core.Binary.BinstrNum bs i)
    (hne : i ≠ Wasm.Core.Binary.pinnedBadPromote)
    (hsize : Wasm.Core.Binary.instrSize i = 1) (hlen : bs.length ≤ 16) :
    EncodedInstr i := by
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ofNum Wasm.Core.Binary.amendedBinaryAuthority
      bs i (@Wasm.Core.Binary.BinstrNumFor.ofPinned
        Wasm.Core.Binary.amendedBinaryAuthority bs i h hne)
  · rw [hsize, Nat.mul_one]
    exact hlen

theorem encoded_local {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : Wasm.Core.Binary.BinstrLocal bs i)
    (hsize : Wasm.Core.Binary.instrSize i = 1) (hlen : bs.length ≤ 16) :
    EncodedInstr i := by
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ofLocal Wasm.Core.Binary.amendedBinaryAuthority bs i h
  · rw [hsize, Nat.mul_one]
    exact hlen

theorem encoded_control {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : Wasm.Core.Binary.BinstrControl bs i)
    (hsize : Wasm.Core.Binary.instrSize i = 1) (hlen : bs.length ≤ 16) :
    EncodedInstr i := by
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ofControl Wasm.Core.Binary.amendedBinaryAuthority
      bs i (@Wasm.Core.Binary.BinstrControlFor.ofPinned
        Wasm.Core.Binary.amendedBinaryAuthority bs i h)
  · rw [hsize, Nat.mul_one]
    exact hlen

theorem encoded_memory {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : Wasm.Core.Binary.BinstrMemory bs i)
    (hsize : Wasm.Core.Binary.instrSize i = 1) (hlen : bs.length ≤ 16) :
    EncodedInstr i := by
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ofMemory Wasm.Core.Binary.amendedBinaryAuthority bs i h
  · rw [hsize, Nat.mul_one]
    exact hlen

theorem encoded_parametric {bs : Wasm.Core.Binary.Bytes} {i : Wasm.Core.Instr}
    (h : @Wasm.Core.Binary.BinstrParametric
      Wasm.Core.Binary.amendedBinaryAuthority bs i)
    (hsize : Wasm.Core.Binary.instrSize i = 1) (hlen : bs.length ≤ 16) :
    EncodedInstr i := by
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ofParametric Wasm.Core.Binary.amendedBinaryAuthority bs i h
  · rw [hsize, Nat.mul_one]
    exact hlen

theorem constI_encoded (n : Nat) : EncodedInstr (constI n) := by
  let bs := Wasm.Core.Binary.lebU (coreU32 n).val
  apply encoded_of_binstr (bs := Wasm.Core.Binary.tb 0x41 :: bs)
  · exact @Wasm.Core.Binary.Binstr.ofNum Wasm.Core.Binary.amendedBinaryAuthority
      _ _ (@Wasm.Core.Binary.BinstrNumFor.ofPinned
      Wasm.Core.Binary.amendedBinaryAuthority _ _
      (.i32Const bs (coreU32 n) (Wasm.Core.Binary.encU32_Bu32 _))
      (by simp [constI, Wasm.Core.Binary.pinnedBadPromote]))
  · have h := lebU_u32_length_le (coreU32 n)
    rw [show Wasm.Core.Binary.instrSize (constI n) = 1 by rfl]
    simp only [List.length_cons, Nat.mul_one]
    simp only [bs]
    omega

theorem constL_encoded (n : Nat) : EncodedInstr (constL n) := by
  let bs := Wasm.Core.Binary.lebU (coreU64 n).val
  apply encoded_of_binstr (bs := Wasm.Core.Binary.tb 0x42 :: bs)
  · exact @Wasm.Core.Binary.Binstr.ofNum Wasm.Core.Binary.amendedBinaryAuthority
      _ _ (@Wasm.Core.Binary.BinstrNumFor.ofPinned
      Wasm.Core.Binary.amendedBinaryAuthority _ _
      (.i64Const bs (coreU64 n) (Wasm.Core.Binary.encU64_Bu64 _))
      (by simp [constL, Wasm.Core.Binary.pinnedBadPromote]))
  · have h := lebU_u64_length_le (coreU64 n)
    rw [show Wasm.Core.Binary.instrSize (constL n) = 1 by rfl]
    simp only [List.length_cons, Nat.mul_one]
    simp only [bs]
    omega

theorem localGet_encoded (n : Nat) : EncodedInstr (localGet n) := by
  let bs := Wasm.Core.Binary.lebU (coreU32 n).val
  apply encoded_local
  · exact .get bs (coreU32 n) (Wasm.Core.Binary.encU32_Bu32 _)
  · rfl
  · have h := lebU_u32_length_le (coreU32 n)
    simp only [bs, List.length_cons]
    omega

theorem localSet_encoded (n : Nat) : EncodedInstr (localSet n) := by
  let bs := Wasm.Core.Binary.lebU (coreU32 n).val
  apply encoded_local
  · exact .set bs (coreU32 n) (Wasm.Core.Binary.encU32_Bu32 _)
  · rfl
  · have h := lebU_u32_length_le (coreU32 n)
    simp only [bs, List.length_cons]
    omega

theorem br_encoded (n : Nat) : EncodedInstr (br n) := by
  let bs := Wasm.Core.Binary.lebU (coreU32 n).val
  apply encoded_control
  · exact .br bs (coreU32 n) (Wasm.Core.Binary.encU32_Bu32 _)
  · rfl
  · have h := lebU_u32_length_le (coreU32 n)
    simp only [bs, List.length_cons]
    omega

theorem brIf_encoded (n : Nat) : EncodedInstr (brIf n) := by
  let bs := Wasm.Core.Binary.lebU (coreU32 n).val
  apply encoded_control
  · exact .brIf bs (coreU32 n) (Wasm.Core.Binary.encU32_Bu32 _)
  · rfl
  · have h := lebU_u32_length_le (coreU32 n)
    simp only [bs, List.length_cons]
    omega

theorem loadW_encoded : EncodedInstr loadW := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i32Load
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem load8U_encoded : EncodedInstr load8U := by
  let ba := Wasm.Core.Binary.lebU (coreU32 0).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i32Load8U
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 0) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 0)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem storeW_encoded : EncodedInstr storeW := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i32Store
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

private theorem memarg_length_le (align : Wasm.Core.U32) :
    1 + (Wasm.Core.Binary.lebU align.val).length +
        (Wasm.Core.Binary.lebU (coreU32 0).val).length ≤ 16 := by
  have ha := lebU_u32_length_le align
  have ho := lebU_u32_length_le (coreU32 0)
  omega

theorem loadL_encoded : EncodedInstr loadL := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Load
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem load8UL_encoded : EncodedInstr load8UL := by
  let ba := Wasm.Core.Binary.lebU (coreU32 0).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Load8U
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 0) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 0)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem load16UL_encoded : EncodedInstr load16UL := by
  let ba := Wasm.Core.Binary.lebU (coreU32 1).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Load16U
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 1) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 1)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem load32UL_encoded : EncodedInstr load32UL := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Load32U
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem storeL_encoded : EncodedInstr storeL := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Store
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem store8L_encoded : EncodedInstr store8L := by
  let ba := Wasm.Core.Binary.lebU (coreU32 0).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Store8
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 0) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 0)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem store16L_encoded : EncodedInstr store16L := by
  let ba := Wasm.Core.Binary.lebU (coreU32 1).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Store16
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 1) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 1)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem store32L_encoded : EncodedInstr store32L := by
  let ba := Wasm.Core.Binary.lebU (coreU32 2).val
  let bo := Wasm.Core.Binary.lebU (coreU32 0).val
  apply encoded_memory
  · apply Wasm.Core.Binary.BinstrMemory.i64Store32
    exact Wasm.Core.Binary.Bmemarg.mem0 ba bo (coreU32 2) (coreU32 0) (coreU32 0)
      (Wasm.Core.Binary.encU32_Bu32 _) (Wasm.Core.Binary.encU32_Bu32 _)
      (by decide) (by decide)
  · rfl
  · have ha := lebU_u32_length_le (coreU32 2)
    have ho := lebU_u32_length_le (coreU32 0)
    simp only [ba, bo, List.length_cons, List.length_append]
    omega

theorem addI_encoded : EncodedInstr addI :=
  encoded_pinned_num .i32Add (by decide) rfl (by decide)
theorem subI_encoded : EncodedInstr subI :=
  encoded_pinned_num .i32Sub (by decide) rfl (by decide)
theorem mulI_encoded : EncodedInstr mulI :=
  encoded_pinned_num .i32Mul (by decide) rfl (by decide)
theorem andI_encoded : EncodedInstr andI :=
  encoded_pinned_num .i32And (by decide) rfl (by decide)
theorem orI_encoded : EncodedInstr orI :=
  encoded_pinned_num .i32Or (by decide) rfl (by decide)
theorem eqI_encoded : EncodedInstr eqI :=
  encoded_pinned_num .i32Eq (by decide) rfl (by decide)
theorem ltUI_encoded : EncodedInstr ltUI :=
  encoded_pinned_num .i32LtU (by decide) rfl (by decide)
theorem gtUI_encoded : EncodedInstr gtUI :=
  encoded_pinned_num .i32GtU (by decide) rfl (by decide)
theorem geUI_encoded : EncodedInstr geUI :=
  encoded_pinned_num .i32GeU (by decide) rfl (by decide)
theorem addL_encoded : EncodedInstr addL :=
  encoded_pinned_num .i64Add (by decide) rfl (by decide)
theorem subL_encoded : EncodedInstr subL :=
  encoded_pinned_num .i64Sub (by decide) rfl (by decide)
theorem mulL_encoded : EncodedInstr mulL :=
  encoded_pinned_num .i64Mul (by decide) rfl (by decide)
theorem andL_encoded : EncodedInstr andL :=
  encoded_pinned_num .i64And (by decide) rfl (by decide)
theorem orL_encoded : EncodedInstr orL :=
  encoded_pinned_num .i64Or (by decide) rfl (by decide)
theorem eqL_encoded : EncodedInstr eqL :=
  encoded_pinned_num .i64Eq (by decide) rfl (by decide)
theorem ltUL_encoded : EncodedInstr ltUL :=
  encoded_pinned_num .i64LtU (by decide) rfl (by decide)
theorem gtUL_encoded : EncodedInstr gtUL :=
  encoded_pinned_num .i64GtU (by decide) rfl (by decide)
theorem geUL_encoded : EncodedInstr geUL :=
  encoded_pinned_num .i64GeU (by decide) rfl (by decide)
theorem extendI32U_encoded : EncodedInstr extendI32U :=
  encoded_pinned_num .i64ExtendI32U (by decide) rfl (by decide)
theorem wrapI64_encoded : EncodedInstr wrapI64 :=
  encoded_pinned_num .i32WrapI64 (by decide) rfl (by decide)
theorem unreachable_encoded : EncodedInstr Wasm.Core.Instr.unreachable :=
  encoded_parametric
    (@Wasm.Core.Binary.BinstrParametric.unreachable
      Wasm.Core.Binary.amendedBinaryAuthority) rfl (by decide)

theorem nil_encoded : EncodedSeq [] := ⟨[], rfl, by simp⟩

theorem cons_encoded {i : Wasm.Core.Instr} {is : List Wasm.Core.Instr}
    (hi : EncodedInstr i) (his : EncodedSeq is) : EncodedSeq (i :: is) := by
  obtain ⟨bi, hbi, hli⟩ := hi
  obtain ⟨bis, hbis, hlis⟩ := his
  refine ⟨bi ++ bis, ?_, ?_⟩
  · change Wasm.Core.Binary.catO
      (@Wasm.Core.Binary.encInstr Wasm.Core.Binary.amendedBinaryAuthority i)
      (@Wasm.Core.Binary.encInstrs Wasm.Core.Binary.amendedBinaryAuthority
        (Wasm.Core.InstrSeq.ofList is)) = some (bi ++ bis)
    exact Wasm.Core.Binary.catO_some hbi hbis
  · simp only [List.length_append, Wasm.Core.InstrSeq.ofList,
      Wasm.Core.Binary.instrsSize]
    omega

theorem singleton_encoded {i : Wasm.Core.Instr} (hi : EncodedInstr i) :
    EncodedSeq [i] := cons_encoded hi nil_encoded

theorem instrsSize_append (a b : List Wasm.Core.Instr) :
    Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList (a ++ b)) =
      Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList a) +
        Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList b) := by
  induction a with
  | nil => simp [Wasm.Core.InstrSeq.ofList, Wasm.Core.Binary.instrsSize]
  | cons i is ih =>
      simp only [List.cons_append, Wasm.Core.InstrSeq.ofList,
        Wasm.Core.Binary.instrsSize, ih]
      omega

theorem binstrs_append {ba bb : Wasm.Core.Binary.Bytes}
    {a b : List Wasm.Core.Instr}
    (ha : @Wasm.Core.Binary.Binstrs Wasm.Core.Binary.amendedBinaryAuthority ba a)
    (hb : @Wasm.Core.Binary.Binstrs Wasm.Core.Binary.amendedBinaryAuthority bb b) :
    @Wasm.Core.Binary.Binstrs Wasm.Core.Binary.amendedBinaryAuthority (ba ++ bb) (a ++ b) := by
  induction a generalizing ba with
  | nil =>
      cases ha
      simpa using hb
  | cons i is ih =>
      cases ha with
      | cons bi bis _ _ hi his =>
          have hrest := ih his
          simpa [List.append_assoc] using
            (@Wasm.Core.Binary.Binstrs.cons Wasm.Core.Binary.amendedBinaryAuthority
              bi (bis ++ bb) i (is ++ b) hi hrest)

theorem append_encoded {a b : List Wasm.Core.Instr}
    (ha : EncodedSeq a) (hb : EncodedSeq b) : EncodedSeq (a ++ b) := by
  obtain ⟨ba, hea, hla⟩ := ha
  obtain ⟨bb, heb, hlb⟩ := hb
  have hga := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList a) ba hea
  have hgb := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList b) bb heb
  rw [Wasm.Core.InstrSeq.toList_ofList] at hga hgb
  have hg := binstrs_append hga hgb
  obtain ⟨out, hout, houtlen⟩ :=
    @Wasm.Core.Binary.encInstrs_completeLe
      Wasm.Core.Binary.amendedBinaryAuthority (ba ++ bb) (a ++ b) hg
  refine ⟨out, hout, ?_⟩
  rw [instrsSize_append]
  simp only [List.length_append] at houtlen
  omega

theorem blockE_encoded {body : List Wasm.Core.Instr} (hb : EncodedSeq body) :
    EncodedInstr (blockE body) := by
  obtain ⟨bb, heb, hlb⟩ := hb
  have hgb := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList body) bb heb
  rw [Wasm.Core.InstrSeq.toList_ofList] at hgb
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.block Wasm.Core.Binary.amendedBinaryAuthority
      [Wasm.Core.Binary.tb 0x40] bb (.result none) body
      (@Wasm.Core.Binary.Bblocktype.empty
        Wasm.Core.Binary.amendedBinaryAuthority) hgb
  · rw [show Wasm.Core.Binary.instrSize (blockE body) =
      Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList body) + 1 by rfl]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

theorem loopE_encoded {body : List Wasm.Core.Instr} (hb : EncodedSeq body) :
    EncodedInstr (loopE body) := by
  obtain ⟨bb, heb, hlb⟩ := hb
  have hgb := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList body) bb heb
  rw [Wasm.Core.InstrSeq.toList_ofList] at hgb
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.loop Wasm.Core.Binary.amendedBinaryAuthority
      [Wasm.Core.Binary.tb 0x40] bb (.result none) body
      (@Wasm.Core.Binary.Bblocktype.empty
        Wasm.Core.Binary.amendedBinaryAuthority) hgb
  · rw [show Wasm.Core.Binary.instrSize (loopE body) =
      Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList body) + 1 by rfl]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

theorem ifE_encoded {onTrue onFalse : List Wasm.Core.Instr}
    (ht : EncodedSeq onTrue) (hf : EncodedSeq onFalse) :
    EncodedInstr (ifE onTrue onFalse) := by
  obtain ⟨bt, het, hlt⟩ := ht
  obtain ⟨bf, hef, hlf⟩ := hf
  have hgt := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList onTrue) bt het
  have hgf := @Wasm.Core.Binary.encInstrs_B
    Wasm.Core.Binary.amendedBinaryAuthority (Wasm.Core.InstrSeq.ofList onFalse) bf hef
  rw [Wasm.Core.InstrSeq.toList_ofList] at hgt hgf
  apply encoded_of_binstr
  · exact @Wasm.Core.Binary.Binstr.ifElse Wasm.Core.Binary.amendedBinaryAuthority
      [Wasm.Core.Binary.tb 0x40] bt bf (.result none) onTrue onFalse
      (@Wasm.Core.Binary.Bblocktype.empty
        Wasm.Core.Binary.amendedBinaryAuthority) hgt hgf
  · rw [show Wasm.Core.Binary.instrSize (ifE onTrue onFalse) =
      Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList onTrue) +
        Wasm.Core.Binary.instrsSize (Wasm.Core.InstrSeq.ofList onFalse) + 1 by rfl]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

theorem loadAt_encoded (addr : Nat) : EncodedSeq (loadAt addr) :=
  cons_encoded (constI_encoded addr) (cons_encoded loadW_encoded nil_encoded)

theorem loadCellAt_encoded (addr : Nat) : EncodedSeq (loadCellAt addr) :=
  cons_encoded (constI_encoded addr) (cons_encoded load8U_encoded nil_encoded)

theorem inputAddr_encoded (offset : Nat) : EncodedSeq (inputAddr offset) :=
  cons_encoded (localGet_encoded 0)
    (cons_encoded (constI_encoded offset) (cons_encoded addI_encoded nil_encoded))

theorem inputAddr64_encoded (offset : Nat) : EncodedSeq (inputAddr64 offset) :=
  cons_encoded (localGet_encoded 0)
    (cons_encoded extendI32U_encoded
      (cons_encoded (constL_encoded offset) (cons_encoded addL_encoded nil_encoded)))

theorem loadInputCell_encoded (offset : Nat) : EncodedSeq (loadInputCell offset) :=
  append_encoded (inputAddr_encoded offset) (singleton_encoded load8U_encoded)

theorem loadWidthL_encoded (width : Nat) : EncodedInstr (loadWidthL width) := by
  cases width with
  | zero => exact unreachable_encoded
  | succ width =>
      cases width with
      | zero => exact load8UL_encoded
      | succ width =>
          cases width with
          | zero => exact load16UL_encoded
          | succ width =>
              cases width with
              | zero => exact unreachable_encoded
              | succ width =>
                  cases width with
                  | zero => exact load32UL_encoded
                  | succ width =>
                      cases width with
                      | zero => exact unreachable_encoded
                      | succ width =>
                          cases width with
                          | zero => exact unreachable_encoded
                          | succ width =>
                              cases width with
                              | zero => exact unreachable_encoded
                              | succ width =>
                                  cases width with
                                  | zero => exact loadL_encoded
                                  | succ width => exact unreachable_encoded

theorem storeWidthL_encoded (width : Nat) : EncodedInstr (storeWidthL width) := by
  cases width with
  | zero => exact unreachable_encoded
  | succ width =>
      cases width with
      | zero => exact store8L_encoded
      | succ width =>
          cases width with
          | zero => exact store16L_encoded
          | succ width =>
              cases width with
              | zero => exact unreachable_encoded
              | succ width =>
                  cases width with
                  | zero => exact store32L_encoded
                  | succ width =>
                      cases width with
                      | zero => exact unreachable_encoded
                      | succ width =>
                          cases width with
                          | zero => exact unreachable_encoded
                          | succ width =>
                              cases width with
                              | zero => exact unreachable_encoded
                              | succ width =>
                                  cases width with
                                  | zero => exact storeL_encoded
                                  | succ width => exact unreachable_encoded

theorem mappedInputAddr_encoded (e : CompileEnv) (region : RegionRef)
    (map : IndexMap) : EncodedSeq (mappedInputAddr e region map) := by
  apply append_encoded (inputAddr64_encoded (e.memAddr (region.base + map.c0)))
  exact cons_encoded (localGet_encoded (e.regLocal 0))
    (cons_encoded (constL_encoded map.cb)
      (cons_encoded mulL_encoded (cons_encoded addL_encoded
        (cons_encoded (localGet_encoded (e.regLocal 1))
          (cons_encoded (constL_encoded map.ci)
            (cons_encoded mulL_encoded (cons_encoded addL_encoded
              (cons_encoded (localGet_encoded (e.regLocal 2))
                (cons_encoded (constL_encoded map.cj)
                  (cons_encoded mulL_encoded (cons_encoded addL_encoded
                    (cons_encoded wrapI64_encoded nil_encoded))))))))))))

theorem countLoop_encoded (counter extent : Nat) {body : List Wasm.Core.Instr}
    (hbody : EncodedSeq body) : EncodedSeq (countLoop counter extent body) := by
  have htest : EncodedSeq
      ([localGet counter, constL extent, geUL, brIf 1] ++ body ++
        [localGet counter, constL 1, addL, localSet counter, br 0]) := by
    apply append_encoded
    · apply append_encoded
      · exact cons_encoded (localGet_encoded counter)
          (cons_encoded (constL_encoded extent)
            (cons_encoded geUL_encoded (cons_encoded (brIf_encoded 1) nil_encoded)))
      · exact hbody
    · exact cons_encoded (localGet_encoded counter)
        (cons_encoded (constL_encoded 1)
          (cons_encoded addL_encoded
            (cons_encoded (localSet_encoded counter)
              (cons_encoded (br_encoded 0) nil_encoded))))
  exact cons_encoded (constL_encoded 0)
    (cons_encoded (localSet_encoded counter)
      (cons_encoded (blockE_encoded
        (singleton_encoded (loopE_encoded htest))) nil_encoded))

theorem countLoopVar_encoded (counter extent : Nat) {body : List Wasm.Core.Instr}
    (hbody : EncodedSeq body) : EncodedSeq (countLoopVar counter extent body) := by
  have htest : EncodedSeq
      ([localGet counter, localGet extent, geUL, brIf 1,
        localGet counter, constL loopRegMaxTrips, geUL, brIf 1] ++ body ++
        [localGet counter, constL 1, addL, localSet counter, br 0]) := by
    apply append_encoded
    · apply append_encoded
      · exact cons_encoded (localGet_encoded counter)
          (cons_encoded (localGet_encoded extent)
            (cons_encoded geUL_encoded (cons_encoded (brIf_encoded 1)
              (cons_encoded (localGet_encoded counter)
                (cons_encoded (constL_encoded loopRegMaxTrips)
                  (cons_encoded geUL_encoded
                    (cons_encoded (brIf_encoded 1) nil_encoded)))))))
      · exact hbody
    · exact cons_encoded (localGet_encoded counter)
        (cons_encoded (constL_encoded 1)
          (cons_encoded addL_encoded
            (cons_encoded (localSet_encoded counter)
              (cons_encoded (br_encoded 0) nil_encoded))))
  exact cons_encoded (constL_encoded 0)
    (cons_encoded (localSet_encoded counter)
      (cons_encoded (blockE_encoded
        (singleton_encoded (loopE_encoded htest))) nil_encoded))

theorem dispatchOn_encoded (tag key : Nat) {yes no : List Wasm.Core.Instr}
    (hy : EncodedSeq yes) (hn : EncodedSeq no) :
    EncodedSeq (dispatchOn tag key yes no) :=
  cons_encoded (localGet_encoded tag)
    (cons_encoded (constL_encoded key)
      (cons_encoded eqL_encoded
        (cons_encoded (ifE_encoded hy hn) nil_encoded)))

theorem tableStores_encoded (base : Nat) : ∀ index data,
    EncodedSeq (tableStores base index data) := by
  intro index data
  induction data generalizing index with
  | nil => exact nil_encoded
  | cons value values ih =>
      exact cons_encoded (constI_encoded (base + 8 * index))
        (cons_encoded (constL_encoded value)
          (cons_encoded storeL_encoded (ih (index + 1))))

theorem cellCode_encoded (e : CompileEnv) (index : Nat) :
    EncodedSeq (cellCode e index) :=
  append_encoded (loadInputCell_encoded (e.memAddr index))
    (singleton_encoded extendI32U_encoded)

theorem eqConst_encoded (n : Nat) : EncodedSeq (eqConst n) :=
  cons_encoded (constL_encoded n) (cons_encoded eqL_encoded nil_encoded)

theorem u16Code_encoded (e : CompileEnv) (index : Nat) :
    EncodedSeq (u16Code e index) := by
  have h := append_encoded (cellCode_encoded e index)
    (append_encoded (singleton_encoded (constL_encoded 256))
      (append_encoded (cellCode_encoded e (index + 1))
        (cons_encoded mulL_encoded (cons_encoded addL_encoded nil_encoded))))
  simpa only [u16Code, List.append_assoc] using h

theorem headerOkCode_encoded (e : CompileEnv) : EncodedSeq (headerOkCode e) := by
  have h0 := append_encoded (cellCode_encoded e 0) (eqConst_encoded 87)
  have h1 := append_encoded (cellCode_encoded e 1)
    (append_encoded (eqConst_encoded 71) (singleton_encoded andI_encoded))
  have h2 := append_encoded (cellCode_encoded e 2)
    (append_encoded (eqConst_encoded 78) (singleton_encoded andI_encoded))
  have h3 := append_encoded (cellCode_encoded e 3)
    (append_encoded (eqConst_encoded 71) (singleton_encoded andI_encoded))
  have h4 := append_encoded (u16Code_encoded e 4)
    (append_encoded (eqConst_encoded 1) (singleton_encoded andI_encoded))
  have h5 := append_encoded (u16Code_encoded e 6)
    (append_encoded (eqConst_encoded headerSize) (singleton_encoded andI_encoded))
  simpa only [headerOkCode, List.append_assoc] using
    append_encoded h0 (append_encoded h1
      (append_encoded h2 (append_encoded h3 (append_encoded h4 h5))))

theorem tagsKnownCode_encoded (e : CompileEnv) : EncodedSeq (tagsKnownCode e) := by
  have h0 := append_encoded (cellCode_encoded e 8)
    (cons_encoded (constL_encoded 13) (cons_encoded ltUL_encoded nil_encoded))
  have h1 := append_encoded (cellCode_encoded e 11)
    (cons_encoded (constL_encoded 13)
      (cons_encoded ltUL_encoded (cons_encoded andI_encoded nil_encoded)))
  have h2 := append_encoded (cellCode_encoded e 12)
    (cons_encoded (constL_encoded 4)
      (cons_encoded ltUL_encoded (cons_encoded andI_encoded nil_encoded)))
  simpa only [tagsKnownCode, List.append_assoc] using
    append_encoded h0 (append_encoded h1 h2)

theorem keyCode_encoded (e : CompileEnv) : EncodedSeq (keyCode e) := by
  have h0 := append_encoded (cellCode_encoded e 12)
    (cons_encoded (constL_encoded 169) (cons_encoded mulL_encoded nil_encoded))
  have h1 := append_encoded (cellCode_encoded e 8)
    (cons_encoded (constL_encoded 13)
      (cons_encoded mulL_encoded (cons_encoded addL_encoded nil_encoded)))
  have h2 := append_encoded (cellCode_encoded e 11)
    (cons_encoded addL_encoded nil_encoded)
  simpa only [keyCode, List.append_assoc] using
    append_encoded h0 (append_encoded h1 h2)

theorem keyChain_encoded (e : CompileEnv) : ∀ keys, EncodedSeq (keyChain e keys) := by
  intro keys
  induction keys with
  | nil => exact nil_encoded
  | cons key keys ih =>
      have h := append_encoded (keyCode_encoded e)
        (cons_encoded (constL_encoded key)
          (cons_encoded eqL_encoded (cons_encoded orI_encoded ih)))
      simpa only [keyChain, List.append_assoc] using h

theorem compatCode_encoded (e : CompileEnv) : EncodedSeq (compatCode e) :=
  cons_encoded (constI_encoded 0) (keyChain_encoded e compatibleKeys)

theorem classifyCode_encoded (e : CompileEnv) (temp : Nat) :
    EncodedSeq (classifyCode e temp) := by
  unfold classifyCode
  split
  · exact cons_encoded (constL_encoded 1)
      (cons_encoded (localSet_encoded temp) nil_encoded)
  · have hcompatBranch : EncodedSeq
        (compatCode e ++ [ifE [] [constL 1, localSet temp]]) :=
      append_encoded (compatCode_encoded e)
        (singleton_encoded (ifE_encoded nil_encoded
          (cons_encoded (constL_encoded 1)
            (cons_encoded (localSet_encoded temp) nil_encoded))))
    have htags : EncodedSeq
        (tagsKnownCode e ++
          [ifE (compatCode e ++ [ifE [] [constL 1, localSet temp]])
            [constL 2, localSet temp]]) :=
      append_encoded (tagsKnownCode_encoded e)
        (singleton_encoded (ifE_encoded hcompatBranch
          (cons_encoded (constL_encoded 2)
            (cons_encoded (localSet_encoded temp) nil_encoded))))
    exact cons_encoded (constL_encoded (if e.memWords ≤ maxRawExtent then 0 else 3))
      (cons_encoded (localSet_encoded temp)
        (append_encoded (headerOkCode_encoded e)
          (singleton_encoded (ifE_encoded htags
            (cons_encoded (constL_encoded 1)
              (cons_encoded (localSet_encoded temp) nil_encoded))))))

theorem widthChain_encoded (e : CompileEnv) : ∀ kinds,
    EncodedSeq (widthChain e kinds) := by
  intro kinds
  induction kinds with
  | nil => exact nil_encoded
  | cons kind kinds ih =>
      have h := append_encoded (cellCode_encoded e 8)
        (cons_encoded (constL_encoded kind.tag)
          (cons_encoded eqL_encoded
            (cons_encoded extendI32U_encoded
              (cons_encoded (constL_encoded kind.byteWidth)
                (cons_encoded mulL_encoded (cons_encoded addL_encoded ih))))))
      simpa only [widthChain, List.append_assoc] using h

theorem widthCode_encoded (e : CompileEnv) : EncodedSeq (widthCode e) :=
  cons_encoded (constL_encoded 0) (widthChain_encoded e ScalarKind.all)

theorem layoutTestCode_encoded (e : CompileEnv) (temp field cls : Nat) :
    EncodedSeq (layoutTestCode e temp field cls) := by
  have h := append_encoded (u16Code_encoded e field)
    (append_encoded (widthCode_encoded e)
      (cons_encoded eqL_encoded
        (cons_encoded (ifE_encoded
          (cons_encoded (constL_encoded cls)
            (cons_encoded (localSet_encoded temp) nil_encoded)) nil_encoded)
          nil_encoded)))
  simpa only [layoutTestCode, List.append_assoc] using h

theorem layoutCode_encoded (e : CompileEnv) (temp : Nat) :
    EncodedSeq (layoutCode e temp) := by
  have h := cons_encoded (constL_encoded 2)
    (cons_encoded (localSet_encoded temp)
      (append_encoded (layoutTestCode_encoded e temp 56 1)
        (layoutTestCode_encoded e temp 64 0)))
  simpa only [layoutCode, List.append_assoc] using h

theorem condCode_encoded (e : CompileEnv) (scratch : Nat) (cond : Cond) :
    EncodedSeq (condCode e scratch cond) := by
  cases cond with
  | statusIs status =>
      exact cons_encoded (localGet_encoded e.statusLocal) (eqConst_encoded status.code)
  | regEq reg value =>
      exact cons_encoded (localGet_encoded (e.regLocal reg))
        (cons_encoded (constL_encoded value)
          (cons_encoded eqL_encoded nil_encoded))
  | regLt reg value =>
      exact cons_encoded (localGet_encoded (e.regLocal reg))
        (cons_encoded (constL_encoded value)
          (cons_encoded ltUL_encoded nil_encoded))
  | scratchAtLeast bytes =>
      exact singleton_encoded
        (constI_encoded (if bytes ≤ scratch then 1 else 0))

theorem code_encoded (e : CompileEnv) : ∀ (plan : Plan) (depth scratch : Nat),
    EncodedSeq (code e depth scratch plan) := by
  intro plan
  induction plan with
  | nop => intro depth scratch; exact nil_encoded
  | seq first second ihFirst ihSecond =>
      intro depth scratch
      exact append_encoded (ihFirst depth scratch) (ihSecond depth scratch)
  | classifyRaw onValid onInvalid onUnsupported onExhausted
      ihValid ihInvalid ihUnsupported ihExhausted =>
      intro depth scratch
      have hdispatch := dispatchOn_encoded (e.tempLocal depth) 0
        (ihValid depth scratch)
        (dispatchOn_encoded (e.tempLocal depth) 1 (ihInvalid depth scratch)
          (dispatchOn_encoded (e.tempLocal depth) 2 (ihUnsupported depth scratch)
            (ihExhausted depth scratch)))
      exact append_encoded (classifyCode_encoded e (e.tempLocal depth)) hdispatch
  | dispatchLayout onRow onCol onGeneral ihRow ihCol ihGeneral =>
      intro depth scratch
      have hdispatch := dispatchOn_encoded (e.tempLocal depth) 0
        (ihRow depth scratch)
        (dispatchOn_encoded (e.tempLocal depth) 1 (ihCol depth scratch)
          (ihGeneral depth scratch))
      exact append_encoded (layoutCode_encoded e (e.tempLocal depth)) hdispatch
  | branch cond onTrue onFalse ihTrue ihFalse =>
      intro depth scratch
      exact append_encoded (condCode_encoded e scratch cond)
        (singleton_encoded (ifE_encoded (ihTrue depth scratch) (ihFalse depth scratch)))
  | pack src dst map width =>
      intro depth scratch
      apply countLoop_encoded
      have hdst := cons_encoded (constI_encoded (e.scratchAddr dst.base))
        (cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (constL_encoded 8)
        (cons_encoded mulL_encoded
          (cons_encoded wrapI64_encoded
            (cons_encoded addI_encoded nil_encoded)))))
      have hsrc := append_encoded
        (inputAddr64_encoded (e.memAddr (src.base + map.c0)))
        (cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (constL_encoded map.cb)
        (cons_encoded mulL_encoded
        (cons_encoded addL_encoded
        (cons_encoded wrapI64_encoded
          (cons_encoded load8UL_encoded nil_encoded))))))
      simpa only [code, List.append_assoc] using
        append_encoded hdst
          (append_encoded hsrc (singleton_encoded storeL_encoded))
  | unpack src dst map width =>
      intro depth scratch
      apply countLoop_encoded
      have hdst := append_encoded (inputAddr64_encoded (e.memAddr dst.base))
        (cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (constL_encoded 1)
        (cons_encoded mulL_encoded
          (cons_encoded addL_encoded
            (cons_encoded wrapI64_encoded nil_encoded)))))
      have hsrc := cons_encoded (constI_encoded (e.scratchAddr (src.base + map.c0)))
        (cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (constL_encoded (8 * map.cb))
        (cons_encoded mulL_encoded
        (cons_encoded wrapI64_encoded
        (cons_encoded addI_encoded
          (cons_encoded loadL_encoded nil_encoded))))))
      simpa only [code, List.append_assoc] using
        append_encoded hdst
          (append_encoded hsrc (singleton_encoded store8L_encoded))
  | storeReg dst map width src =>
      intro depth scratch
      have hv := cons_encoded (localGet_encoded (e.regLocal src))
        (cons_encoded (storeWidthL_encoded width) nil_encoded)
      exact append_encoded (mappedInputAddr_encoded e dst map) hv
  | loadReg dst src map width =>
      intro depth scratch
      have hv := cons_encoded (loadWidthL_encoded width)
        (cons_encoded (localSet_encoded (e.regLocal dst)) nil_encoded)
      exact append_encoded (mappedInputAddr_encoded e src map) hv
  | loopNest axis body ih =>
      intro depth scratch
      apply countLoop_encoded
      exact cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (localSet_encoded (e.regLocal axis.indexReg))
          (ih (depth + 1) scratch))
  | loopReg indexReg extentReg map body ih =>
      intro depth scratch
      apply countLoopVar_encoded
      exact cons_encoded (localGet_encoded (e.tempLocal depth))
        (cons_encoded (localSet_encoded (e.regLocal indexReg))
          (ih (depth + 1) scratch))
  | tiled order tiling extents body ih =>
      intro depth scratch
      apply countLoop_encoded
      by_cases hregs : 0 < e.regs
      · simpa [hregs] using
          cons_encoded (localGet_encoded (e.tempLocal depth))
            (cons_encoded (localSet_encoded (e.regLocal 0))
              (ih (depth + 1) scratch))
      · simpa [hregs] using ih (depth + 1) scratch
  | reduce contract acc lhs rhs =>
      intro depth scratch
      unfold code
      split
      · apply countLoop_encoded
        have hacc := singleton_encoded (localGet_encoded (e.regLocal acc))
        have hlhs := append_encoded (inputAddr64_encoded (e.memAddr lhs.base))
          (cons_encoded (localGet_encoded (e.tempLocal depth))
          (cons_encoded (constL_encoded 4)
          (cons_encoded mulL_encoded
          (cons_encoded addL_encoded
            (cons_encoded wrapI64_encoded
              (cons_encoded load32UL_encoded nil_encoded))))))
        have hrhs := append_encoded (inputAddr64_encoded (e.memAddr rhs.base))
          (cons_encoded (localGet_encoded (e.tempLocal depth))
          (cons_encoded (constL_encoded 4)
          (cons_encoded mulL_encoded
          (cons_encoded addL_encoded
          (cons_encoded wrapI64_encoded
          (cons_encoded load32UL_encoded
          (cons_encoded mulL_encoded
          (cons_encoded addL_encoded
            (cons_encoded (localSet_encoded (e.regLocal acc)) nil_encoded)))))))))
        simpa only [List.append_assoc] using
          append_encoded hacc (append_encoded hlhs hrhs)
      · exact singleton_encoded unreachable_encoded
  | allocScratch bytes body ih =>
      intro depth scratch
      exact ih depth (scratch + bytes)
  | setReg _ _ =>
      intro depth scratch
      exact nil_encoded
  | scalarOp _ _ _ _ =>
      intro depth scratch
      exact nil_encoded
  | vectorOp op lanes dst lhs rhs =>
      intro depth scratch
      exact singleton_encoded unreachable_encoded
  | emitTable index data =>
      intro depth scratch
      exact tableStores_encoded (e.tableBase + 8 * (index * e.tableStride)) 0 data
  | tableLoad table index dst =>
      intro depth scratch
      exact append_encoded
        (cons_encoded
          (constI_encoded (e.tableBase + 8 * (table * e.tableStride + index)))
          (cons_encoded loadL_encoded nil_encoded))
        (singleton_encoded (localSet_encoded (e.regLocal dst)))
  | setStatus status =>
      intro depth scratch
      exact cons_encoded (constL_encoded status.code)
        (cons_encoded (localSet_encoded e.statusLocal) nil_encoded)
  | buildOutput _ =>
      intro depth scratch
      exact nil_encoded
  | opaqueProcess spec body ih =>
      intro depth scratch
      exact ih depth scratch

theorem bodyCode_encoded (e : CompileEnv) (scratch : Nat) (plan : Plan) :
    EncodedSeq (bodyCode e scratch plan) :=
  append_encoded (code_encoded e plan 0 scratch)
    (cons_encoded (localGet_encoded e.statusLocal)
      (cons_encoded wrapI64_encoded nil_encoded))

end DirectEncoding
end WasmGemmGnaf.GNAF
