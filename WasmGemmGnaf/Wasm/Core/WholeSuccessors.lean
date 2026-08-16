/-
  Executable successors for the state-writing top-level Core rules.

  This file is the second layer of the single Core successor enumerator:
  `Successors.lean` covers `Step_pure`; the definitions below cover every
  non-context constructor of `Exec.StepA` that writes the state.  Store reads
  and recursive administrative contexts are layered below this file, rather
  than represented by a second semantic relation.
-/
import WasmGemmGnaf.Wasm.Core.EventExecution

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- A dependent address literal recovered from a runtime value. -/
structure AddressLiteral where
  type : AddrType
  value : AddrLit type

/-- Recover the two address-number cases without losing their width. -/
def addressLiteral? : Val → Option AddressLiteral
  | .num ⟨.i32, value⟩ => some ⟨.i32, value⟩
  | .num ⟨.i64, value⟩ => some ⟨.i64, value⟩
  | _ => none

/-- Re-embed a recovered address literal as its Core constant. -/
def AddressLiteral.toAdmin (a : AddressLiteral) : AdminInstr :=
  constAddr a.type a.value

/-- The value whose administrative embedding is `toAdmin`. -/
def AddressLiteral.toVal (a : AddressLiteral) : Val :=
  .num ⟨addrNumType a.type, addrLitToNum a.type a.value⟩

@[simp] theorem AddressLiteral.toVal_toAdmin (a : AddressLiteral) :
    a.toVal.toAdmin = a.toAdmin := by cases a.type <;> rfl

@[simp] theorem addressLiteral?_toVal (a : AddressLiteral) :
    addressLiteral? a.toVal = some a := by
  cases a with
  | mk type value => cases type <;> rfl

theorem eq_toVal_of_addressLiteral?_eq_some {v : Val} {a : AddressLiteral}
    (h : addressLiteral? v = some a) : v = a.toVal := by
  cases v with
  | num n =>
      cases n with
      | mk nt c =>
          cases nt with
          | i32 =>
              have ha : (⟨.i32, c⟩ : AddressLiteral) = a :=
                Option.some.inj h
              subst a
              rfl
          | i64 =>
              have ha : (⟨.i64, c⟩ : AddressLiteral) = a :=
                Option.some.inj h
              subst a
              rfl
          | f32 => simp [addressLiteral?] at h
          | f64 => simp [addressLiteral?] at h
  | vec w => simp [addressLiteral?] at h
  | ref r => simp [addressLiteral?] at h

/-- A bounded address literal at the requested address width. -/
def addressLiteralOfNat? : (type : AddrType) → Nat → Option (AddrLit type)
  | .i32, n => u32? n
  | .i64, n => u64? n

theorem addressLiteralOfNat?_eq_some_value {type : AddrType} {n : Nat}
    {value : AddrLit type} (h : addressLiteralOfNat? type n = some value) :
    value.val = n := by
  cases type with
  | i32 =>
      change u32? n = some value at h
      unfold u32? at h
      split at h
      · injection h with heq
        exact congrArg Subtype.val heq.symm
      · contradiction
  | i64 =>
      change u64? n = some value at h
      unfold u64? at h
      split at h
      · injection h with heq
        exact congrArg Subtype.val heq.symm
      · contradiction

@[simp] theorem addressLiteralOfNat?_val (type : AddrType)
    (value : AddrLit type) :
    addressLiteralOfNat? type value.val = some value := by
  cases type with
  | i32 =>
      rcases value with ⟨n, hn⟩
      change u32? n = some ⟨n, hn⟩
      unfold u32?
      split
      · congr
      · exact False.elim (by contradiction)
  | i64 =>
      rcases value with ⟨n, hn⟩
      change u64? n = some ⟨n, hn⟩
      unfold u64?
      split
      · congr
      · exact False.elim (by contradiction)

/-- The exact signed `-1` sentinel at an address width. -/
def addressFailure (type : AddrType) : AddrLit type :=
  Numerics.inv_signed_ (addrSize type) (-1)

/-- Recover a reference value. -/
def refValue? : Val → Option Ref
  | .ref r => some r
  | _ => none

theorem eq_ref_of_refValue?_eq_some {v : Val} {r : Ref}
    (h : refValue? v = some r) : v = .ref r := by
  cases v <;> simp [refValue?] at h
  case ref => cases h; rfl

/-- Recover a `v128` value. -/
def v128Value? : Val → Option V128Lit
  | .vec ⟨.v128, c⟩ => some c
  | _ => none

theorem eq_v128_of_v128Value?_eq_some {v : Val} {c : V128Lit}
    (h : v128Value? v = some c) : v = .vec ⟨.v128, c⟩ := by
  cases v with
  | num n => simp [v128Value?] at h
  | ref r => simp [v128Value?] at h
  | vec w => cases w; simp [v128Value?] at h; cases h; rfl

/-- The unique integer/packed shape admitted by `vstore_lane` at a byte
width.  Float shapes cannot satisfy `laneToIN`, so no semantic branch is
discarded by this choice. -/
def storeLaneShape : Sz → Shape
  | .s8 => { lane := .pack .i8, dim := .d16 }
  | .s16 => { lane := .pack .i16, dim := .d8 }
  | .s32 => { lane := .num .i32, dim := .d4 }
  | .s64 => { lane := .num .i64, dim := .d2 }

@[simp] theorem storeLaneShape_laneSize (sz : Sz) :
    (storeLaneShape sz).lane.size = sz.toNat := by cases sz <;> rfl

@[simp] theorem storeLaneShape_dim (sz : Sz) :
    (storeLaneShape sz).dim.toNat = 128 / sz.toNat := by cases sz <;> rfl

/-- The successful lane-store premises determine the unique integer lane
shape used by the executable selector.  Float lanes are excluded by the
successful `laneToIN` premise itself. -/
theorem shape_eq_storeLaneShape_of_laneToIN
    {sh : Shape} {sz : Sz} {lv : Lane_ sh.lane} {k : IN sh.lane.size}
    (hsize : sh.lane.size = sz.toNat)
    (hdim : sh.dim.toNat = 128 / sz.toNat)
    (hbits : laneToIN sh.lane lv = some k) :
    sh = storeLaneShape sz := by
  rcases sh with ⟨lane, dim⟩
  cases lane with
  | num nt =>
      cases nt <;> cases dim <;> cases sz <;>
        simp [LaneType.size, NumType.size, Sz.toNat, Dim.toNat, laneToIN,
          storeLaneShape] at hsize hdim hbits ⊢
  | pack pt =>
      cases pt <;> cases dim <;> cases sz <;>
        simp [LaneType.size, PackType.size, Sz.toNat, Dim.toNat, laneToIN,
          storeLaneShape] at hsize hdim hbits ⊢

/-- At most one deterministic state-writing result, packaged as a list. -/
def stateWrite? (event : Event) (state? : Option State)
    (result : List AdminInstr) : List (Event × Config) :=
  match state? with
  | none => []
  | some state => [(event, (state, result))]

theorem mem_stateWrite?_iff {event emitted : Event} {state? : Option State}
    {state : State} {result emittedResult : List AdminInstr} :
    (emitted, (state, emittedResult)) ∈ stateWrite? event state? result ↔
      emitted = event ∧ emittedResult = result ∧ state? = some state := by
  cases state? with
  | none => simp [stateWrite?]
  | some next =>
      simp only [stateWrite?, List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, h⟩
        injection h with h
        subst h
        exact ⟨rfl, rfl, rfl⟩

/-- The two permitted `table.grow` outcomes.  Refusal is always present;
successful growth is present exactly when all pinned partial updates compute. -/
def tableGrowSuccessors (z : State) (r : Ref) (n : AddressLiteral)
    (x : TableIdx) : List (Event × Config) :=
  let failure : Event × Config :=
    (.tableGrowFail x n.value.val,
      (z, [constAddr n.type (addressFailure n.type)]))
  match z.tableOf x with
  | none => [failure]
  | some table =>
      match growTable table n.value.val r with
      | none => [failure]
      | some grown =>
          match z.withTableInst x grown,
              addressLiteralOfNat? n.type table.refs.length with
          | some next, some oldSize =>
              [(.tableGrowSucceed x n.value.val table.refs.length
                    grown.refs.length,
                  (next, [constAddr n.type oldSize])), failure]
          | _, _ => [failure]

theorem mem_tableGrowSuccessors_stepA {z : State} {r : Ref}
    {n : AddressLiteral} {x : TableIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ tableGrowSuccessors z r n x) :
    StepA (z, [r.toAdmin, n.toAdmin, .plain (.tableGrow x)]) event next := by
  have hfail : StepA
      (z, [r.toAdmin, n.toAdmin, .plain (.tableGrow x)])
      (.tableGrowFail x n.value.val)
      (z, [constAddr n.type (addressFailure n.type)]) := by
    exact .tableGrowFail rfl
  unfold tableGrowSuccessors at hmem
  dsimp only at hmem
  cases htable : z.tableOf x with
  | none =>
      simp only [htable, List.mem_singleton] at hmem
      cases hmem
      exact hfail
  | some table =>
      simp only [htable] at hmem
      cases hgrow : growTable table n.value.val r with
      | none =>
          simp only [hgrow, List.mem_singleton] at hmem
          cases hmem
          exact hfail
      | some grown =>
          simp only [hgrow] at hmem
          cases hset : z.withTableInst x grown with
          | none =>
              simp only [hset, List.mem_singleton] at hmem
              cases hmem
              exact hfail
          | some nextState =>
              simp only [hset] at hmem
              cases hsize : addressLiteralOfNat? n.type table.refs.length with
              | none =>
                  simp only [hsize, List.mem_singleton] at hmem
                  cases hmem
                  exact hfail
              | some oldSize =>
                  simp only [hsize, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with hsuccess | hfailure
                  · cases hsuccess
                    exact .tableGrowSucceed htable hgrow hset
                      (addressLiteralOfNat?_eq_some_value hsize)
                  · cases hfailure
                    exact hfail

/-- The two permitted `memory.grow` outcomes. -/
def memoryGrowSuccessors (z : State) (n : AddressLiteral)
    (x : MemIdx) : List (Event × Config) :=
  let failure : Event × Config :=
    (.memoryGrowFail x n.value.val,
      (z, [constAddr n.type (addressFailure n.type)]))
  match z.memOf x with
  | none => [failure]
  | some memory =>
      match growMem memory n.value.val with
      | none => [failure]
      | some grown =>
          let oldPages := memory.bytes.length / (64 * Ki)
          match z.withMemInst x grown,
              addressLiteralOfNat? n.type oldPages with
          | some next, some oldSize =>
              [(.memoryGrowSucceed x n.value.val oldPages
                    (grown.bytes.length / (64 * Ki)),
                  (next, [constAddr n.type oldSize])), failure]
          | _, _ => [failure]

theorem mem_memoryGrowSuccessors_stepA {z : State} {n : AddressLiteral}
    {x : MemIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ memoryGrowSuccessors z n x) :
    StepA (z, [n.toAdmin, .plain (.memoryGrow x)]) event next := by
  have hfail : StepA (z, [n.toAdmin, .plain (.memoryGrow x)])
      (.memoryGrowFail x n.value.val)
      (z, [constAddr n.type (addressFailure n.type)]) := by
    exact .memoryGrowFail rfl
  unfold memoryGrowSuccessors at hmem
  dsimp only at hmem
  cases hmemory : z.memOf x with
  | none =>
      simp only [hmemory, List.mem_singleton] at hmem
      cases hmem
      exact hfail
  | some memory =>
      simp only [hmemory] at hmem
      cases hgrow : growMem memory n.value.val with
      | none =>
          simp only [hgrow, List.mem_singleton] at hmem
          cases hmem
          exact hfail
      | some grown =>
          simp only [hgrow] at hmem
          cases hset : z.withMemInst x grown with
          | none =>
              simp only [hset, List.mem_singleton] at hmem
              cases hmem
              exact hfail
          | some nextState =>
              simp only [hset] at hmem
              cases hsize : addressLiteralOfNat? n.type
                  (memory.bytes.length / (64 * Ki)) with
              | none =>
                  simp only [hsize, List.mem_singleton] at hmem
                  cases hmem
                  exact hfail
              | some oldSize =>
                  simp only [hsize, List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with hsuccess | hfailure
                  · cases hsuccess
                    exact .memoryGrowSucceed hmemory hgrow hset
                      (addressLiteralOfNat?_eq_some_value hsize)
                  · cases hfailure
                    exact hfail

/-- Full-width numeric store. -/
def storeNumSuccessors (z : State) (address : AddressLiteral) (v : Val)
    (nt : NumType) (x : MemIdx) (ao : MemArg) : List (Event × Config) :=
  match valNum nt v with
  | none => []
  | some c =>
      let width := nt.size / 8
      match z.memOf x with
      | none => []
      | some memory =>
          if address.value.val + ao.offset.val + width > memory.bytes.length then
            [(.storeNumOob x width, (z, [.trap]))]
          else
            stateWrite? (.storeNumVal x width)
              (z.withMem x (address.value.val + ao.offset.val) width
                (releasedNumerics.nbytes_ nt c)) []

theorem mem_storeNumSuccessors_stepA {z : State} {address : AddressLiteral}
    {v : Val} {nt : NumType} {x : MemIdx} {ao : MemArg}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ storeNumSuccessors z address v nt x ao) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store nt none x ao)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  unfold storeNumSuccessors at hmem
  cases hvalue : valNum nt v with
  | none => simp [hvalue] at hmem
  | some c =>
      have hv := valNum_eq hvalue
      subst v
      simp only [hvalue] at hmem
      cases hmemory : z.memOf x with
      | none => simp [hmemory] at hmem
      | some memory =>
          simp only [hmemory] at hmem
          split at hmem
          next hoob =>
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact .storeNumOob hmemory hoob
          next hin =>
            rw [mem_stateWrite?_iff] at hmem
            rcases hmem with ⟨rfl, rfl, hwrite⟩
            exact .storeNumVal rfl hwrite

/-- Packed integer store, after the instruction's integer family has refined
the dependent literal type. -/
def storePackI32Successors (z : State) (address : AddressLiteral) (v : Val)
    (op : StoreOp) (x : MemIdx) (ao : MemArg) : List (Event × Config) :=
  match valNum .i32 v with
  | none => []
  | some c =>
      let width := op.sz.toNat / 8
      match z.memOf x with
      | none => []
      | some memory =>
          if address.value.val + ao.offset.val + width > memory.bytes.length then
            [(.storePackOob x width, (z, [.trap]))]
          else
            stateWrite? (.storePackVal x width)
              (z.withMem x (address.value.val + ao.offset.val) width
                (releasedNumerics.ibytes_ op.sz.toNat
                  (releasedNumerics.wrap__ 32 op.sz.toNat c))) []

theorem mem_storePackI32Successors_stepA {z : State}
    {address : AddressLiteral} {v : Val} {op : StoreOp} {x : MemIdx}
    {ao : MemArg} {event : Event} {next : Config}
    (hmem : (event, next) ∈ storePackI32Successors z address v op x ao) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store .i32 (some op) x ao)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  rcases op with ⟨sz⟩
  unfold storePackI32Successors at hmem
  cases hvalue : valNum .i32 v with
  | none => simp [hvalue] at hmem
  | some c =>
      have hv := valNum_eq hvalue
      subst v
      simp only [hvalue] at hmem
      cases hmemory : z.memOf x with
      | none => simp [hmemory] at hmem
      | some memory =>
          simp only [hmemory] at hmem
          split at hmem
          next hoob =>
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact .storePackOob (inn := .i32) hmemory hoob
          next hin =>
            rw [mem_stateWrite?_iff] at hmem
            rcases hmem with ⟨rfl, rfl, hwrite⟩
            exact .storePackVal (inn := .i32) rfl hwrite

def storePackI64Successors (z : State) (address : AddressLiteral) (v : Val)
    (op : StoreOp) (x : MemIdx) (ao : MemArg) : List (Event × Config) :=
  match valNum .i64 v with
  | none => []
  | some c =>
      let width := op.sz.toNat / 8
      match z.memOf x with
      | none => []
      | some memory =>
          if address.value.val + ao.offset.val + width > memory.bytes.length then
            [(.storePackOob x width, (z, [.trap]))]
          else
            stateWrite? (.storePackVal x width)
              (z.withMem x (address.value.val + ao.offset.val) width
                (releasedNumerics.ibytes_ op.sz.toNat
                  (releasedNumerics.wrap__ 64 op.sz.toNat c))) []

theorem mem_storePackI64Successors_stepA {z : State}
    {address : AddressLiteral} {v : Val} {op : StoreOp} {x : MemIdx}
    {ao : MemArg} {event : Event} {next : Config}
    (hmem : (event, next) ∈ storePackI64Successors z address v op x ao) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store .i64 (some op) x ao)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  rcases op with ⟨sz⟩
  unfold storePackI64Successors at hmem
  cases hvalue : valNum .i64 v with
  | none => simp [hvalue] at hmem
  | some c =>
      have hv := valNum_eq hvalue
      subst v
      simp only [hvalue] at hmem
      cases hmemory : z.memOf x with
      | none => simp [hmemory] at hmem
      | some memory =>
          simp only [hmemory] at hmem
          split at hmem
          next hoob =>
            simp only [List.mem_singleton] at hmem
            cases hmem
            exact .storePackOob (inn := .i64) hmemory hoob
          next hin =>
            rw [mem_stateWrite?_iff] at hmem
            rcases hmem with ⟨rfl, rfl, hwrite⟩
            exact .storePackVal (inn := .i64) rfl hwrite

/-- Whole-vector store. -/
def vstoreSuccessors (z : State) (address : AddressLiteral) (v : Val)
    (x : MemIdx) (ao : MemArg) : List (Event × Config) :=
  match v128Value? v with
  | none => []
  | some c =>
      let width := VecType.v128.size / 8
      match z.memOf x with
      | none => []
      | some memory =>
          if address.value.val + ao.offset.val + width > memory.bytes.length then
            [(.vstoreOob x width, (z, [.trap]))]
          else
            stateWrite? (.vstoreVal x width)
              (z.withMem x (address.value.val + ao.offset.val) width
                (releasedNumerics.vbytes_ .v128 c)) []

theorem mem_vstoreSuccessors_stepA {z : State} {address : AddressLiteral}
    {v : Val} {x : MemIdx} {ao : MemArg} {event : Event} {next : Config}
    (hmem : (event, next) ∈ vstoreSuccessors z address v x ao) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.vstore .v128 x ao)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  unfold vstoreSuccessors at hmem
  cases hvalue : v128Value? v with
  | none => simp [hvalue] at hmem
  | some c =>
      cases v with
      | vec vector =>
          cases vector with
          | mk vt value =>
              cases vt
              simp only [v128Value?] at hvalue
              injection hvalue with hvalue
              subst value
              simp only [v128Value?] at hmem
              cases hmemory : z.memOf x with
              | none => simp [hmemory] at hmem
              | some memory =>
                  simp only [hmemory] at hmem
                  split at hmem
                  next hoob =>
                    simp only [List.mem_singleton] at hmem
                    cases hmem
                    exact .vstoreOob hmemory hoob
                  next hin =>
                    rw [mem_stateWrite?_iff] at hmem
                    rcases hmem with ⟨rfl, rfl, hwrite⟩
                    exact .vstoreVal rfl hwrite
      | num n => simp [v128Value?] at hvalue
      | ref r => simp [v128Value?] at hvalue

/-- Lane store.  The pinned out-of-bounds premise uses `sz`, while the write
itself uses `sz / 8`; both quantities are preserved exactly. -/
def vstoreLaneSuccessors (z : State) (address : AddressLiteral) (v : Val)
    (sz : Sz) (x : MemIdx) (ao : MemArg) (j : LaneIdx) :
    List (Event × Config) :=
  match v128Value? v with
  | none => []
  | some c =>
      let width := sz.toNat / 8
      match z.memOf x with
      | none => []
      | some memory =>
          let failure :=
            if address.value.val + ao.offset.val + sz.toNat > memory.bytes.length then
              [(.vstoreLaneOob x width, (z, [.trap]))]
            else []
          let sh := storeLaneShape sz
          let success :=
            match (releasedNumerics.lanes_ sh c)[j.val]? with
            | none => []
            | some lane =>
                match laneToIN sh.lane lane with
                | none => []
                | some bits =>
                    stateWrite? (.vstoreLaneVal x width)
                      (z.withMem x (address.value.val + ao.offset.val) width
                        (releasedNumerics.ibytes_ sh.lane.size bits)) []
          failure ++ success

theorem mem_vstoreLaneSuccessors_stepA {z : State}
    {address : AddressLiteral} {v : Val} {sz : Sz} {x : MemIdx}
    {ao : MemArg} {j : LaneIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈
      vstoreLaneSuccessors z address v sz x ao j) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.vstoreLane .v128 sz x ao j)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  unfold vstoreLaneSuccessors at hmem
  cases hvalue : v128Value? v with
  | none => simp [hvalue] at hmem
  | some c =>
      cases v with
      | vec vector =>
          cases vector with
          | mk vt value =>
              cases vt
              simp only [v128Value?] at hvalue
              injection hvalue with hvalue
              subst value
              simp only [v128Value?] at hmem
              cases hmemory : z.memOf x with
              | none => simp [hmemory] at hmem
              | some memory =>
                  simp only [hmemory, List.mem_append] at hmem
                  rcases hmem with hfailure | hsuccess
                  · split at hfailure
                    next hoob =>
                      simp only [List.mem_singleton] at hfailure
                      cases hfailure
                      exact .vstoreLaneOob hmemory hoob
                    next hin => simp at hfailure
                  · generalize hlane :
                      (releasedNumerics.lanes_ (storeLaneShape sz) c)[j.val]? =
                        laneResult at hsuccess
                    cases laneResult with
                    | none =>
                        simp at hsuccess
                    | some lane =>
                        simp only at hsuccess
                        generalize hbits :
                          laneToIN (storeLaneShape sz).lane lane = bitsResult at hsuccess
                        cases bitsResult with
                        | none =>
                            simp at hsuccess
                        | some bits =>
                            simp only at hsuccess
                            rw [mem_stateWrite?_iff] at hsuccess
                            rcases hsuccess with ⟨rfl, rfl, hwrite⟩
                            exact .vstoreLaneVal
                              (storeLaneShape_laneSize sz)
                              (storeLaneShape_dim sz) hlane hbits rfl hwrite
      | num n => simp [v128Value?] at hvalue
      | ref r => simp [v128Value?] at hvalue

/-- The state-writing successors of one canonical value prefix followed by
one plain instruction.  Every arm corresponds to one of the 26 non-context,
non-read, non-pure constructors of `Exec.StepA`. -/
def directSuccessorsOf (z : State) (vs : List Val) (instruction : Instr) :
    List (Event × Config) :=
  match instruction with
  | .throw x =>
      match z.tagOf x with
      | none => []
      | some tag =>
          match asDefType tag.type with
          | none => []
          | some dt =>
              match expandDt dt with
              | some (.func domain .nil) =>
                  if domain.length = vs.length then
                    match z.tagaddr[x.val]? with
                    | none => []
                    | some tagAddress =>
                        let exception : ExnInst :=
                          { tag := tagAddress, fields := vs }
                        [(.throw x vs.length,
                          (z.addExnInst [exception],
                            [.addrref (.exnAddr z.exninst.length),
                             .plain .throwRef]))]
                  else []
              | _ => []
  | .localSet x =>
      match vs with
      | [v] => stateWrite? (.localSet x) (z.withLocal x v) []
      | _ => []
  | .globalSet x =>
      match vs with
      | [v] => stateWrite? (.globalSet x) (z.withGlobal x v) []
      | _ => []
  | .tableSet x =>
      match vs with
      | [addressValue, referenceValue] =>
          match addressLiteral? addressValue, refValue? referenceValue with
          | some address, some reference =>
              match z.tableOf x with
              | none => []
              | some table =>
                  if address.value.val ≥ table.refs.length then
                    [(.tableSetOob x, (z, [.trap]))]
                  else stateWrite? (.tableSetVal x)
                    (z.withTable x address.value.val reference) []
          | _, _ => []
      | _ => []
  | .tableGrow x =>
      match vs with
      | [referenceValue, addressValue] =>
          match refValue? referenceValue, addressLiteral? addressValue with
          | some reference, some address => tableGrowSuccessors z reference address x
          | _, _ => []
      | _ => []
  | .elemDrop x =>
      if vs.isEmpty then stateWrite? (.elemDrop x) (z.withElem x []) [] else []
  | .store nt none x ao =>
      match vs with
      | [addressValue, value] =>
          match addressLiteral? addressValue with
          | some address => storeNumSuccessors z address value nt x ao
          | none => []
      | _ => []
  | .store .i32 (some op) x ao =>
      match vs with
      | [addressValue, value] =>
          match addressLiteral? addressValue with
          | some address => storePackI32Successors z address value op x ao
          | none => []
      | _ => []
  | .store .i64 (some op) x ao =>
      match vs with
      | [addressValue, value] =>
          match addressLiteral? addressValue with
          | some address => storePackI64Successors z address value op x ao
          | none => []
      | _ => []
  | .store .f32 (some _) _ _ | .store .f64 (some _) _ _ => []
  | .vstore .v128 x ao =>
      match vs with
      | [addressValue, value] =>
          match addressLiteral? addressValue with
          | some address => vstoreSuccessors z address value x ao
          | none => []
      | _ => []
  | .vstoreLane .v128 sz x ao j =>
      match vs with
      | [addressValue, value] =>
          match addressLiteral? addressValue with
          | some address => vstoreLaneSuccessors z address value sz x ao j
          | none => []
      | _ => []
  | .memoryGrow x =>
      match vs with
      | [addressValue] =>
          match addressLiteral? addressValue with
          | some address => memoryGrowSuccessors z address x
          | none => []
      | _ => []
  | .dataDrop x =>
      if vs.isEmpty then stateWrite? (.dataDrop x) (z.withData x []) [] else []
  | .structNew x =>
      match z.typeOf x with
      | none => []
      | some dt =>
          match expandDt dt with
          | some (.struct fields) =>
              if fields.toList.length = vs.length then
                match (fields.toList.zip vs).mapM
                    (fun p => releasedNumerics.packfield_ (fieldStorage p.1) p.2) with
                | none => []
                | some packed =>
                    let newStruct : StructInst := { type := dt, fields := packed }
                    [(.structNew x vs.length,
                      (z.addStructInst [newStruct],
                        [.addrref (.structAddr z.structinst.length)]))]
              else []
          | _ => []
  | .structSet x field =>
      match vs with
      | [.ref (.null _), _] => [(.structSetNull x field, (z, [.trap]))]
      | [.ref (.addr (.structAddr address)), value] =>
          match z.typeOf x with
          | none => []
          | some dt =>
              match expandDt dt with
              | some (.struct fields) =>
                  match fields.toList[field.val]? with
                  | none => []
                  | some ft =>
                      match releasedNumerics.packfield_ (fieldStorage ft) value with
                      | none => []
                      | some packed => stateWrite? (.structSetStruct x field)
                          (z.withStruct address field.val packed) []
              | _ => []
      | _ => []
  | .arrayNewFixed x n =>
      if vs.length = n.val then
        match z.typeOf x with
        | none => []
        | some dt =>
            match expandDt dt with
            | some (.array field) =>
                match vs.mapM
                    (releasedNumerics.packfield_ (fieldStorage field)) with
                | none => []
                | some packed =>
                    let newArray : ArrayInst := { type := dt, fields := packed }
                    [(.arrayNewFixed x n.val,
                      (z.addArrayInst [newArray],
                        [.addrref (.arrayAddr z.arrayinst.length)]))]
            | _ => []
      else []
  | .arraySet x =>
      match vs with
      | [.ref (.null _), .num ⟨.i32, _⟩, _] =>
          [(.arraySetNull x, (z, [.trap]))]
      | [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩, value] =>
          match z.arrayinst[address]? with
          | none => []
          | some array =>
              if index.val ≥ array.fields.length then
                [(.arraySetOob x, (z, [.trap]))]
              else
                match z.typeOf x with
                | none => []
                | some dt =>
                    match expandDt dt with
                    | some (.array field) =>
                        match releasedNumerics.packfield_ (fieldStorage field) value with
                        | none => []
                        | some packed => stateWrite? (.arraySetArray x)
                            (z.withArray address index.val packed) []
                    | _ => []
      | _ => []
  | _ => []

/-! ### Soundness at the canonical operand shapes -/

theorem mem_directLocalSet_stepA {z : State} {v : Val} {x : LocalIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z [v] (.localSet x)) :
    StepA (z, [v.toAdmin, .plain (.localSet x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf] at hmem
  rw [mem_stateWrite?_iff] at hmem
  rcases hmem with ⟨rfl, rfl, hset⟩
  exact .localSet hset

theorem mem_directGlobalSet_stepA {z : State} {v : Val} {x : GlobalIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z [v] (.globalSet x)) :
    StepA (z, [v.toAdmin, .plain (.globalSet x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf] at hmem
  rw [mem_stateWrite?_iff] at hmem
  rcases hmem with ⟨rfl, rfl, hset⟩
  exact .globalSet hset

theorem mem_directThrow_stepA {z : State} {vs : List Val} {x : TagIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z vs (.throw x)) :
    StepA (z, vals vs ++ [.plain (.throw x)]) event next := by
  unfold directSuccessorsOf at hmem
  cases htag : z.tagOf x with
  | none => simp [htag] at hmem
  | some tag =>
      simp only [htag] at hmem
      cases hdt : asDefType tag.type with
      | none => simp [hdt] at hmem
      | some dt =>
          simp only [hdt] at hmem
          cases hexpand : expandDt dt with
          | none => simp [hexpand] at hmem
          | some composite =>
              cases composite with
              | struct fields => simp [hexpand] at hmem
              | array field => simp [hexpand] at hmem
              | func domain codomain =>
                  cases codomain with
                  | cons t ts => simp [hexpand] at hmem
                  | nil =>
                      simp only [hexpand] at hmem
                      split at hmem
                      next hlength =>
                        cases htagAddress : z.tagaddr[x.val]? with
                        | none => simp [htagAddress] at hmem
                        | some tagAddress =>
                            simp only [htagAddress, List.mem_singleton] at hmem
                            cases hmem
                            exact .throw htag hdt (.mk hexpand) hlength rfl rfl
                              htagAddress rfl
                      next hlength => simp at hmem

theorem mem_directTableSet_stepA {z : State} {address : AddressLiteral}
    {reference : Ref} {x : TableIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z
      [address.toVal, .ref reference] (.tableSet x)) :
    StepA (z, [address.toAdmin, reference.toAdmin,
      .plain (.tableSet x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf, addressLiteral?_toVal, refValue?] at hmem
  cases htable : z.tableOf x with
  | none => simp [htable] at hmem
  | some table =>
      simp only [htable] at hmem
      split at hmem
      next hoob =>
        simp only [List.mem_singleton] at hmem
        cases hmem
        exact .tableSetOob htable hoob
      next hin =>
        rw [mem_stateWrite?_iff] at hmem
        rcases hmem with ⟨rfl, rfl, hset⟩
        exact .tableSetVal htable (by omega) hset

theorem mem_directElemDrop_stepA {z : State} {x : ElemIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z [] (.elemDrop x)) :
    StepA (z, [.plain (.elemDrop x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf, List.isEmpty_nil, if_true] at hmem
  rw [mem_stateWrite?_iff] at hmem
  rcases hmem with ⟨rfl, rfl, hdrop⟩
  exact .elemDrop hdrop

theorem mem_directDataDrop_stepA {z : State} {x : DataIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z [] (.dataDrop x)) :
    StepA (z, [.plain (.dataDrop x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf, List.isEmpty_nil, if_true] at hmem
  rw [mem_stateWrite?_iff] at hmem
  rcases hmem with ⟨rfl, rfl, hdrop⟩
  exact .dataDrop hdrop

theorem mem_directTableGrow_stepA {z : State} {r : Ref}
    {address : AddressLiteral} {x : TableIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [.ref r, address.toVal] (.tableGrow x)) :
    StepA (z, [r.toAdmin, address.toAdmin, .plain (.tableGrow x)])
      event next := by
  simp only [directSuccessorsOf, refValue?, addressLiteral?_toVal] at hmem
  exact mem_tableGrowSuccessors_stepA hmem

theorem mem_directMemoryGrow_stepA {z : State} {address : AddressLiteral}
    {x : MemIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [address.toVal] (.memoryGrow x)) :
    StepA (z, [address.toAdmin, .plain (.memoryGrow x)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_memoryGrowSuccessors_stepA hmem

theorem mem_directStoreNum_stepA {z : State} {address : AddressLiteral}
    {v : Val} {nt : NumType} {x : MemIdx} {ao : MemArg}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [address.toVal, v] (.store nt none x ao)) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store nt none x ao)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_storeNumSuccessors_stepA hmem

theorem mem_directStorePackI32_stepA {z : State} {address : AddressLiteral}
    {v : Val} {op : StoreOp} {x : MemIdx} {ao : MemArg}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [address.toVal, v] (.store .i32 (some op) x ao)) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store .i32 (some op) x ao)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_storePackI32Successors_stepA hmem

theorem mem_directStorePackI64_stepA {z : State} {address : AddressLiteral}
    {v : Val} {op : StoreOp} {x : MemIdx} {ao : MemArg}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [address.toVal, v] (.store .i64 (some op) x ao)) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.store .i64 (some op) x ao)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_storePackI64Successors_stepA hmem

theorem mem_directVstore_stepA {z : State} {address : AddressLiteral}
    {v : Val} {x : MemIdx} {ao : MemArg} {event : Event} {next : Config}
    (hmem : (event, next) ∈
      directSuccessorsOf z [address.toVal, v] (.vstore .v128 x ao)) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.vstore .v128 x ao)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_vstoreSuccessors_stepA hmem

theorem mem_directVstoreLane_stepA {z : State} {address : AddressLiteral}
    {v : Val} {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z [address.toVal, v]
      (.vstoreLane .v128 sz x ao j)) :
    StepA (z, [address.toAdmin, v.toAdmin,
      .plain (.vstoreLane .v128 sz x ao j)]) event next := by
  simp only [directSuccessorsOf, addressLiteral?_toVal] at hmem
  exact mem_vstoreLaneSuccessors_stepA hmem

theorem mem_directStructNew_stepA {z : State} {vs : List Val}
    {x : TypeIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z vs (.structNew x)) :
    StepA (z, vals vs ++ [.plain (.structNew x)]) event next := by
  unfold directSuccessorsOf at hmem
  cases htype : z.typeOf x with
  | none => simp [htype] at hmem
  | some dt =>
      simp only [htype] at hmem
      cases hexpand : expandDt dt with
      | none => simp [hexpand] at hmem
      | some composite =>
          cases composite with
          | array field => simp [hexpand] at hmem
          | func domain codomain => simp [hexpand] at hmem
          | struct fields =>
              simp only [hexpand] at hmem
              split at hmem
              next hlength =>
                cases hpack : (fields.toList.zip vs).mapM
                    (fun p => releasedNumerics.packfield_
                      (fieldStorage p.1) p.2) with
                | none => simp [hpack] at hmem
                | some packed =>
                    simp only [hpack, List.mem_singleton] at hmem
                    cases hmem
                    exact .structNew htype (.mk hexpand) hlength rfl rfl
                      hpack rfl
              next hlength => simp at hmem

theorem mem_directStructSetNull_stepA {z : State} {ht : HeapType}
    {v : Val} {x : TypeIdx} {field : U32} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z
      [.ref (.null ht), v] (.structSet x field)) :
    StepA (z, [Ref.toAdmin (.null ht), v.toAdmin,
      .plain (.structSet x field)]) event next := by
  simp only [directSuccessorsOf, List.mem_singleton] at hmem
  cases hmem
  exact .structSetNull

theorem mem_directStructSetStruct_stepA {z : State} {address : StructAddr}
    {v : Val} {x : TypeIdx} {field : U32} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z
      [.ref (.addr (.structAddr address)), v] (.structSet x field)) :
    StepA (z, [.addrref (.structAddr address), v.toAdmin,
      .plain (.structSet x field)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf] at hmem
  cases htype : z.typeOf x with
  | none => simp [htype] at hmem
  | some dt =>
      simp only [htype] at hmem
      cases hexpand : expandDt dt with
      | none => simp [hexpand] at hmem
      | some composite =>
          cases composite with
          | array ft => simp [hexpand] at hmem
          | func domain codomain => simp [hexpand] at hmem
          | struct fields =>
              simp only [hexpand] at hmem
              cases hfield : fields.toList[field.val]? with
              | none => simp [hfield] at hmem
              | some ft =>
                  simp only [hfield] at hmem
                  cases hpack : releasedNumerics.packfield_ (fieldStorage ft) v with
                  | none => simp [hpack] at hmem
                  | some packed =>
                      simp only [hpack] at hmem
                      rw [mem_stateWrite?_iff] at hmem
                      rcases hmem with ⟨rfl, rfl, hset⟩
                      exact .structSetStruct htype (.mk hexpand) hfield hpack hset

theorem mem_directArrayNewFixed_stepA {z : State} {vs : List Val}
    {x : TypeIdx} {n : U32} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z vs (.arrayNewFixed x n)) :
    StepA (z, vals vs ++ [.plain (.arrayNewFixed x n)]) event next := by
  simp only [directSuccessorsOf] at hmem
  by_cases hlength : vs.length = n.val
  · simp only [if_pos hlength] at hmem
    cases htype : z.typeOf x with
    | none => simp [htype] at hmem
    | some dt =>
        simp only [htype] at hmem
        cases hexpand : expandDt dt with
        | none => simp [hexpand] at hmem
        | some composite =>
            cases composite with
            | struct fields => simp [hexpand] at hmem
            | func domain codomain => simp [hexpand] at hmem
            | array field =>
                simp only [hexpand] at hmem
                cases hpack : vs.mapM
                    (releasedNumerics.packfield_ (fieldStorage field)) with
                | none => simp [hpack] at hmem
                | some packed =>
                    simp only [hpack, List.mem_singleton] at hmem
                    cases hmem
                    exact .arrayNewFixed htype (.mk hexpand) hlength rfl hpack rfl
  · simp [if_neg hlength] at hmem

theorem mem_directArraySetNull_stepA {z : State} {ht : HeapType}
    {index : U32} {v : Val} {x : TypeIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z
      [.ref (.null ht), .num ⟨.i32, index⟩, v] (.arraySet x)) :
    StepA (z, [Ref.toAdmin (.null ht), constI32 index, v.toAdmin,
      .plain (.arraySet x)]) event next := by
  simp only [directSuccessorsOf, List.mem_singleton] at hmem
  cases hmem
  exact .arraySetNull

theorem mem_directArraySetArray_stepA {z : State} {address : ArrayAddr}
    {index : U32} {v : Val} {x : TypeIdx} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z
      [.ref (.addr (.arrayAddr address)), .num ⟨.i32, index⟩, v]
      (.arraySet x)) :
    StepA (z, [.addrref (.arrayAddr address), constI32 index, v.toAdmin,
      .plain (.arraySet x)]) event next := by
  rcases next with ⟨nextState, nextResult⟩
  simp only [directSuccessorsOf] at hmem
  cases harray : z.arrayinst[address]? with
  | none => simp [harray] at hmem
  | some array =>
      simp only [harray] at hmem
      split at hmem
      next hoob =>
        simp only [List.mem_singleton] at hmem
        cases hmem
        exact .arraySetOob harray hoob
      next hin =>
        cases htype : z.typeOf x with
        | none => simp [htype] at hmem
        | some dt =>
            simp only [htype] at hmem
            cases hexpand : expandDt dt with
            | none => simp [hexpand] at hmem
            | some composite =>
                cases composite with
                | struct fields => simp [hexpand] at hmem
                | func domain codomain => simp [hexpand] at hmem
                | array field =>
                    simp only [hexpand] at hmem
                    cases hpack : releasedNumerics.packfield_
                        (fieldStorage field) v with
                    | none => simp [hpack] at hmem
                    | some packed =>
                        simp only [hpack] at hmem
                        rw [mem_stateWrite?_iff] at hmem
                        rcases hmem with ⟨rfl, rfl, hset⟩
                        exact .arraySetArray htype (.mk hexpand) hpack hset

/-! ### Soundness for every direct instruction shape -/

/-- Whether an event belongs to the non-context, state-writing layer. -/
def Event.isDirect : Event → Bool
  | .pure _ _ | .read _ _ | .ctxtInstrs _ _ _ | .ctxtLabel _ _
  | .ctxtFrame _ _ => false
  | _ => true

/- The canonical value-prefix splitter recognizes each direct redex without
searching over alternative sequence decompositions. -/
@[simp] theorem splitVals_throw (vs : List Val) (x : TagIdx) :
    splitVals (vals vs ++ [.plain (.throw x)]) =
      (vs, [.plain (.throw x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_localSet (vs : List Val) (x : LocalIdx) :
    splitVals (vals vs ++ [.plain (.localSet x)]) =
      (vs, [.plain (.localSet x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_globalSet (vs : List Val) (x : GlobalIdx) :
    splitVals (vals vs ++ [.plain (.globalSet x)]) =
      (vs, [.plain (.globalSet x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_tableSet (vs : List Val) (x : TableIdx) :
    splitVals (vals vs ++ [.plain (.tableSet x)]) =
      (vs, [.plain (.tableSet x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_tableGrow (vs : List Val) (x : TableIdx) :
    splitVals (vals vs ++ [.plain (.tableGrow x)]) =
      (vs, [.plain (.tableGrow x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_elemDrop (vs : List Val) (x : ElemIdx) :
    splitVals (vals vs ++ [.plain (.elemDrop x)]) =
      (vs, [.plain (.elemDrop x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_store (vs : List Val) (nt : NumType)
    (op : Option StoreOp) (x : MemIdx) (ao : MemArg) :
    splitVals (vals vs ++ [.plain (.store nt op x ao)]) =
      (vs, [.plain (.store nt op x ao)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_vstore (vs : List Val) (vt : VecType)
    (x : MemIdx) (ao : MemArg) :
    splitVals (vals vs ++ [.plain (.vstore vt x ao)]) =
      (vs, [.plain (.vstore vt x ao)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_vstoreLane (vs : List Val) (vt : VecType)
    (sz : Sz) (x : MemIdx) (ao : MemArg) (j : LaneIdx) :
    splitVals (vals vs ++ [.plain (.vstoreLane vt sz x ao j)]) =
      (vs, [.plain (.vstoreLane vt sz x ao j)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_memoryGrow (vs : List Val) (x : MemIdx) :
    splitVals (vals vs ++ [.plain (.memoryGrow x)]) =
      (vs, [.plain (.memoryGrow x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_dataDrop (vs : List Val) (x : DataIdx) :
    splitVals (vals vs ++ [.plain (.dataDrop x)]) =
      (vs, [.plain (.dataDrop x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_structNew (vs : List Val) (x : TypeIdx) :
    splitVals (vals vs ++ [.plain (.structNew x)]) =
      (vs, [.plain (.structNew x)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_structSet (vs : List Val) (x : TypeIdx)
    (field : U32) :
    splitVals (vals vs ++ [.plain (.structSet x field)]) =
      (vs, [.plain (.structSet x field)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_arrayNewFixed (vs : List Val) (x : TypeIdx)
    (n : U32) :
    splitVals (vals vs ++ [.plain (.arrayNewFixed x n)]) =
      (vs, [.plain (.arrayNewFixed x n)]) :=
  splitVals_vals_append_nonval vs rfl []

@[simp] theorem splitVals_arraySet (vs : List Val) (x : TypeIdx) :
    splitVals (vals vs ++ [.plain (.arraySet x)]) =
      (vs, [.plain (.arraySet x)]) :=
  splitVals_vals_append_nonval vs rfl []

/-- The direct executable layer never emits a pure, read, or context event. -/
theorem event_isDirect_of_mem_directSuccessorsOf {z : State} {vs : List Val}
    {instruction : Instr} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z vs instruction) :
    event.isDirect = true := by
  cases instruction <;> simp [directSuccessorsOf] at hmem
  all_goals repeat' split at hmem
  all_goals
    simp_all [stateWrite?, tableGrowSuccessors, memoryGrowSuccessors,
      storeNumSuccessors, storePackI32Successors, storePackI64Successors,
      vstoreSuccessors, vstoreLaneSuccessors]
  all_goals repeat' split at hmem
  all_goals
    cases event <;>
      simp_all [Event.isDirect]

/-- Membership in the direct state-writing layer is a labelled Core step.
The proof first recovers the operand shapes that made the executable matcher
succeed, then applies the corresponding rule-exact lemma above. -/
theorem mem_directSuccessorsOf_stepA {z : State} {vs : List Val}
    {instruction : Instr} {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessorsOf z vs instruction) :
    StepA (z, vals vs ++ [.plain instruction]) event next := by
  cases instruction
  case throw x => exact mem_directThrow_stepA hmem
  case localSet x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons v rest =>
          cases rest with
          | nil => exact mem_directLocalSet_stepA hmem
          | cons w rest => simp [directSuccessorsOf] at hmem
  case globalSet x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons v rest =>
          cases rest with
          | nil => exact mem_directGlobalSet_stepA hmem
          | cons w rest => simp [directSuccessorsOf] at hmem
  case tableSet x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons addressValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons referenceValue tail =>
              cases tail with
              | cons w tail => simp [directSuccessorsOf] at hmem
              | nil =>
                  cases ha : addressLiteral? addressValue with
                  | none => simp [directSuccessorsOf, ha] at hmem
                  | some address =>
                      have hav := eq_toVal_of_addressLiteral?_eq_some ha
                      subst addressValue
                      cases hr : refValue? referenceValue with
                      | none => simp [directSuccessorsOf, hr] at hmem
                      | some reference =>
                          have hrv := eq_ref_of_refValue?_eq_some hr
                          subst referenceValue
                          exact mem_directTableSet_stepA hmem
  case tableGrow x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons referenceValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons addressValue tail =>
              cases tail with
              | cons w tail => simp [directSuccessorsOf] at hmem
              | nil =>
                  cases hr : refValue? referenceValue with
                  | none => simp [directSuccessorsOf, hr] at hmem
                  | some reference =>
                      have hrv := eq_ref_of_refValue?_eq_some hr
                      subst referenceValue
                      cases ha : addressLiteral? addressValue with
                      | none => simp [directSuccessorsOf, ha] at hmem
                      | some address =>
                          have hav := eq_toVal_of_addressLiteral?_eq_some ha
                          subst addressValue
                          exact mem_directTableGrow_stepA hmem
  case elemDrop x =>
      cases vs with
      | nil => exact mem_directElemDrop_stepA hmem
      | cons v rest => simp [directSuccessorsOf] at hmem
  case dataDrop x =>
      cases vs with
      | nil => exact mem_directDataDrop_stepA hmem
      | cons v rest => simp [directSuccessorsOf] at hmem
  case store nt op x ao =>
      cases op with
      | none =>
          cases vs with
          | nil => simp [directSuccessorsOf] at hmem
          | cons addressValue rest =>
              cases rest with
              | nil => simp [directSuccessorsOf] at hmem
              | cons value tail =>
                  cases tail with
                  | cons w tail => simp [directSuccessorsOf] at hmem
                  | nil =>
                      cases ha : addressLiteral? addressValue with
                      | none => simp [directSuccessorsOf, ha] at hmem
                      | some address =>
                          have hav := eq_toVal_of_addressLiteral?_eq_some ha
                          subst addressValue
                          exact mem_directStoreNum_stepA hmem
      | some storeOp =>
          cases nt with
          | f32 => simp [directSuccessorsOf] at hmem
          | f64 => simp [directSuccessorsOf] at hmem
          | i32 =>
              cases vs with
              | nil => simp [directSuccessorsOf] at hmem
              | cons addressValue rest =>
                  cases rest with
                  | nil => simp [directSuccessorsOf] at hmem
                  | cons value tail =>
                      cases tail with
                      | cons w tail => simp [directSuccessorsOf] at hmem
                      | nil =>
                          cases ha : addressLiteral? addressValue with
                          | none => simp [directSuccessorsOf, ha] at hmem
                          | some address =>
                              have hav := eq_toVal_of_addressLiteral?_eq_some ha
                              subst addressValue
                              exact mem_directStorePackI32_stepA hmem
          | i64 =>
              cases vs with
              | nil => simp [directSuccessorsOf] at hmem
              | cons addressValue rest =>
                  cases rest with
                  | nil => simp [directSuccessorsOf] at hmem
                  | cons value tail =>
                      cases tail with
                      | cons w tail => simp [directSuccessorsOf] at hmem
                      | nil =>
                          cases ha : addressLiteral? addressValue with
                          | none => simp [directSuccessorsOf, ha] at hmem
                          | some address =>
                              have hav := eq_toVal_of_addressLiteral?_eq_some ha
                              subst addressValue
                              exact mem_directStorePackI64_stepA hmem
  case vstore vt x ao =>
      cases vt
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons addressValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons value tail =>
              cases tail with
              | cons w tail => simp [directSuccessorsOf] at hmem
              | nil =>
                  cases ha : addressLiteral? addressValue with
                  | none => simp [directSuccessorsOf, ha] at hmem
                  | some address =>
                      have hav := eq_toVal_of_addressLiteral?_eq_some ha
                      subst addressValue
                      exact mem_directVstore_stepA hmem
  case vstoreLane vt sz x ao j =>
      cases vt
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons addressValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons value tail =>
              cases tail with
              | cons w tail => simp [directSuccessorsOf] at hmem
              | nil =>
                  cases ha : addressLiteral? addressValue with
                  | none => simp [directSuccessorsOf, ha] at hmem
                  | some address =>
                      have hav := eq_toVal_of_addressLiteral?_eq_some ha
                      subst addressValue
                      exact mem_directVstoreLane_stepA hmem
  case memoryGrow x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons addressValue rest =>
          cases rest with
          | cons w tail => simp [directSuccessorsOf] at hmem
          | nil =>
              cases ha : addressLiteral? addressValue with
              | none => simp [directSuccessorsOf, ha] at hmem
              | some address =>
                  have hav := eq_toVal_of_addressLiteral?_eq_some ha
                  subst addressValue
                  exact mem_directMemoryGrow_stepA hmem
  case structNew x => exact mem_directStructNew_stepA hmem
  case structSet x field =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons referenceValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons value tail =>
              cases tail with
              | cons w tail => simp [directSuccessorsOf] at hmem
              | nil =>
                  cases referenceValue with
                  | num n => simp [directSuccessorsOf] at hmem
                  | vec v => simp [directSuccessorsOf] at hmem
                  | ref reference =>
                      cases reference with
                      | null ht => exact mem_directStructSetNull_stepA hmem
                      | addr address =>
                          cases address with
                          | structAddr address =>
                              exact mem_directStructSetStruct_stepA hmem
                          | i31 i => simp [directSuccessorsOf] at hmem
                          | arrayAddr address => simp [directSuccessorsOf] at hmem
                          | funcAddr address => simp [directSuccessorsOf] at hmem
                          | exnAddr address => simp [directSuccessorsOf] at hmem
                          | hostAddr address => simp [directSuccessorsOf] at hmem
                          | extern reference => simp [directSuccessorsOf] at hmem
  case arrayNewFixed x n => exact mem_directArrayNewFixed_stepA hmem
  case arraySet x =>
      cases vs with
      | nil => simp [directSuccessorsOf] at hmem
      | cons referenceValue rest =>
          cases rest with
          | nil => simp [directSuccessorsOf] at hmem
          | cons indexValue rest =>
              cases rest with
              | nil => simp [directSuccessorsOf] at hmem
              | cons value tail =>
                  cases tail with
                  | cons w tail => simp [directSuccessorsOf] at hmem
                  | nil =>
                      cases referenceValue with
                      | num n => simp [directSuccessorsOf] at hmem
                      | vec v => simp [directSuccessorsOf] at hmem
                      | ref reference =>
                          cases indexValue with
                          | vec v => simp [directSuccessorsOf] at hmem
                          | ref r => simp [directSuccessorsOf] at hmem
                          | num index =>
                              cases index with
                              | mk nt index =>
                                  cases nt with
                                  | i64 => simp [directSuccessorsOf] at hmem
                                  | f32 => simp [directSuccessorsOf] at hmem
                                  | f64 => simp [directSuccessorsOf] at hmem
                                  | i32 =>
                                      cases reference with
                                      | null ht =>
                                          exact mem_directArraySetNull_stepA hmem
                                      | addr address =>
                                          cases address with
                                          | arrayAddr address =>
                                              exact mem_directArraySetArray_stepA hmem
                                          | i31 i => simp [directSuccessorsOf] at hmem
                                          | structAddr address =>
                                              simp [directSuccessorsOf] at hmem
                                          | funcAddr address =>
                                              simp [directSuccessorsOf] at hmem
                                          | exnAddr address =>
                                              simp [directSuccessorsOf] at hmem
                                          | hostAddr address =>
                                              simp [directSuccessorsOf] at hmem
                                          | extern reference =>
                                              simp [directSuccessorsOf] at hmem
  all_goals simp [directSuccessorsOf] at hmem

/-- The state-writing top-level successor list for a raw Core configuration. -/
def directSuccessors (config : Config) : List (Event × Config) :=
  let split := splitVals config.2
  match split.2 with
  | [.plain instruction] => directSuccessorsOf config.1 split.1 instruction
  | _ => []

/-- Every member emitted by the direct configuration layer is a labelled Core
step from the original, unsplit configuration. -/
theorem mem_directSuccessors_stepA {config : Config} {event : Event}
    {next : Config} (hmem : (event, next) ∈ directSuccessors config) :
    StepA config event next := by
  unfold directSuccessors at hmem
  cases htail : (splitVals config.2).2 with
  | nil => simp [htail] at hmem
  | cons first rest =>
      cases rest with
      | cons second rest => simp [htail] at hmem
      | nil =>
          cases first with
          | plain instruction =>
              simp only [htail] at hmem
              have hstep := mem_directSuccessorsOf_stepA hmem
              have hreassemble :
                  vals (splitVals config.2).1 ++ [.plain instruction] =
                    config.2 := by
                rw [← htail]
                exact splitVals_append config.2
              rw [hreassemble] at hstep
              exact hstep
          | addrref reference => simp [htail] at hmem
          | label n cont body => simp [htail] at hmem
          | frame n frame body => simp [htail] at hmem
          | handler n catches body => simp [htail] at hmem
          | trap => simp [htail] at hmem

theorem event_isDirect_of_mem_directSuccessors {config : Config}
    {event : Event} {next : Config}
    (hmem : (event, next) ∈ directSuccessors config) :
    event.isDirect = true := by
  unfold directSuccessors at hmem
  cases htail : (splitVals config.2).2 with
  | nil => simp [htail] at hmem
  | cons first rest =>
      cases rest with
      | cons second rest => simp [htail] at hmem
      | nil =>
          cases first with
          | plain instruction =>
              simp only [htail] at hmem
              exact event_isDirect_of_mem_directSuccessorsOf hmem
          | addrref reference => simp [htail] at hmem
          | label n cont body => simp [htail] at hmem
          | frame n frame body => simp [htail] at hmem
          | handler n catches body => simp [htail] at hmem
          | trap => simp [htail] at hmem

/-- Lift membership from one canonical direct redex to the raw configuration
whose maximal value prefix is that redex's operand list. -/
theorem mem_directSuccessors_of_mem_directSuccessorsOf {z : State}
    {vs : List Val} {instruction : Instr} {event : Event} {next : Config}
    (hnonval : adminToVal (.plain instruction) = none)
    (hmem : (event, next) ∈ directSuccessorsOf z vs instruction) :
    (event, next) ∈
      directSuccessors (z, vals vs ++ [.plain instruction]) := by
  unfold directSuccessors
  rw [splitVals_vals_append_nonval vs hnonval []]
  exact hmem

/-- Membership at the canonical split lifts to the raw configuration. -/
theorem mem_directSuccessors_of_split {z : State} {is : List AdminInstr}
    {instruction : Instr} {event : Event} {next : Config}
    (htail : (splitVals is).2 = [.plain instruction])
    (hmem : (event, next) ∈
      directSuccessorsOf z (splitVals is).1 instruction) :
    (event, next) ∈ directSuccessors (z, is) := by
  unfold directSuccessors
  dsimp only
  rw [htail]
  exact hmem

/-! ### Completeness of the direct layer -/

theorem localSet_mem_directSuccessors {z z' : State} {v : Val}
    {x : LocalIdx} (hset : z.withLocal x v = some z') :
    ((.localSet x), (z', [])) ∈
      directSuccessors (z, [v.toAdmin, .plain (.localSet x)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := [v]) (instruction := .localSet x) rfl
    (by simp [directSuccessorsOf, stateWrite?, hset])

theorem globalSet_mem_directSuccessors {z z' : State} {v : Val}
    {x : GlobalIdx} (hset : z.withGlobal x v = some z') :
    ((.globalSet x), (z', [])) ∈
      directSuccessors (z, [v.toAdmin, .plain (.globalSet x)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := [v]) (instruction := .globalSet x) rfl
    (by simp [directSuccessorsOf, stateWrite?, hset])

theorem elemDrop_mem_directSuccessors {z z' : State} {x : ElemIdx}
    (hdrop : z.withElem x [] = some z') :
    ((.elemDrop x), (z', [])) ∈
      directSuccessors (z, [.plain (.elemDrop x)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := []) (instruction := .elemDrop x) rfl
    (by simp [directSuccessorsOf, stateWrite?, hdrop])

theorem dataDrop_mem_directSuccessors {z z' : State} {x : DataIdx}
    (hdrop : z.withData x [] = some z') :
    ((.dataDrop x), (z', [])) ∈
      directSuccessors (z, [.plain (.dataDrop x)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := []) (instruction := .dataDrop x) rfl
    (by simp [directSuccessorsOf, stateWrite?, hdrop])

theorem throw_mem_directSuccessors {z : State} {vs : List Val}
    {x : TagIdx} {ti : TagInst} {dt : DefType} {t : ValTypes}
    {n : Nat} {a : ExnAddr} {ta : TagAddr} {ex : ExnInst}
    (htag : z.tagOf x = some ti) (hdt : asDefType ti.type = some dt)
    (hexpand : Expand dt (.func t .nil)) (ht : t.length = n)
    (hvs : vs.length = n) (ha : a = z.exninst.length)
    (hta : z.tagaddr[x.val]? = some ta)
    (hex : ex = { tag := ta, fields := vs }) :
    ((.throw x n),
      (z.addExnInst [ex], [.addrref (.exnAddr a), .plain .throwRef])) ∈
      directSuccessors (z, vals vs ++ [.plain (.throw x)]) := by
  apply mem_directSuccessors_of_mem_directSuccessorsOf rfl
  simp only [directSuccessorsOf, htag, hdt]
  rcases hexpand with ⟨hexpand⟩
  rw [hexpand]
  simp only
  rw [if_pos (ht.trans hvs.symm), hta]
  subst a
  subst ex
  simp [hvs]

theorem tableSetOob_mem_directSuccessors {z : State} {att : AddrType}
    {i : AddrLit att} {r : Ref} {x : TableIdx} {ti : TableInst}
    (htable : z.tableOf x = some ti) (hoob : i.val ≥ ti.refs.length) :
    ((.tableSetOob x), (z, [.trap])) ∈ directSuccessors
      (z, [constAddr att i, r.toAdmin, .plain (.tableSet x)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [(AddressLiteral.mk att i).toVal, .ref r])
      (instruction := .tableSet x) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal, refValue?, htable]
        rw [if_pos hoob]
        simp)

theorem tableSetVal_mem_directSuccessors {z z' : State}
    {att : AddrType} {i : AddrLit att} {r : Ref} {x : TableIdx}
    {ti : TableInst} (htable : z.tableOf x = some ti)
    (hin : i.val < ti.refs.length)
    (hset : z.withTable x i.val r = some z') :
    ((.tableSetVal x), (z', [])) ∈ directSuccessors
      (z, [constAddr att i, r.toAdmin, .plain (.tableSet x)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [(AddressLiteral.mk att i).toVal, .ref r])
      (instruction := .tableSet x) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal, refValue?, htable]
        rw [if_neg (Nat.not_le_of_lt hin)]
        simp [stateWrite?, hset])

theorem tableGrowFail_mem_directSuccessors {z : State} {att : AddrType}
    {n : AddrLit att} {r : Ref} {x : TableIdx} {e : AddrLit att}
    (he : e = Numerics.inv_signed_ (addrSize att) (-1)) :
    ((.tableGrowFail x n.val), (z, [constAddr att e])) ∈
      directSuccessors
        (z, [r.toAdmin, constAddr att n, .plain (.tableGrow x)]) := by
  subst e
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, addressFailure] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [.ref r, (AddressLiteral.mk att n).toVal])
      (instruction := .tableGrow x) rfl
      (by
        simp only [directSuccessorsOf, refValue?, addressLiteral?_toVal]
        unfold tableGrowSuccessors
        dsimp only
        cases htable : z.tableOf x with
        | none => simp [addressFailure]
        | some table =>
            dsimp only
            cases hgrow : growTable table n.val r with
            | none =>
                dsimp only
                exact List.mem_cons_self
            | some grown =>
                dsimp only
                cases hset : z.withTableInst x grown with
                | none =>
                    dsimp only
                    exact List.mem_cons_self
                | some nextState =>
                    cases hsize : addressLiteralOfNat? att table.refs.length with
                    | none =>
                        dsimp only
                        exact List.mem_cons_self
                    | some oldSize =>
                        dsimp only
                        exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem memoryGrowFail_mem_directSuccessors {z : State} {att : AddrType}
    {n : AddrLit att} {x : MemIdx} {e : AddrLit att}
    (he : e = Numerics.inv_signed_ (addrSize att) (-1)) :
    ((.memoryGrowFail x n.val), (z, [constAddr att e])) ∈
      directSuccessors (z, [constAddr att n, .plain (.memoryGrow x)]) := by
  subst e
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, addressFailure] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [(AddressLiteral.mk att n).toVal])
      (instruction := .memoryGrow x) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold memoryGrowSuccessors
        dsimp only
        cases hmemory : z.memOf x with
        | none => simp [addressFailure]
        | some memory =>
            dsimp only
            cases hgrow : growMem memory n.val with
            | none =>
                dsimp only
                exact List.mem_cons_self
            | some grown =>
                dsimp only
                cases hset : z.withMemInst x grown with
                | none =>
                    dsimp only
                    exact List.mem_cons_self
                | some nextState =>
                    cases hsize : addressLiteralOfNat? att
                        (memory.bytes.length / (64 * Ki)) with
                    | none =>
                        dsimp only
                        exact List.mem_cons_self
                    | some oldSize =>
                        dsimp only
                        exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem tableGrowSucceed_mem_directSuccessors {z z' : State}
    {att : AddrType} {n sz : AddrLit att} {r : Ref} {x : TableIdx}
    {ti ti' : TableInst} (htable : z.tableOf x = some ti)
    (hgrow : growTable ti n.val r = some ti')
    (hset : z.withTableInst x ti' = some z')
    (hsz : sz.val = ti.refs.length) :
    ((.tableGrowSucceed x n.val ti.refs.length ti'.refs.length),
      (z', [constAddr att sz])) ∈ directSuccessors
        (z, [r.toAdmin, constAddr att n, .plain (.tableGrow x)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [.ref r, (AddressLiteral.mk att n).toVal])
      (instruction := .tableGrow x) rfl
      (by
        simp only [directSuccessorsOf, refValue?, addressLiteral?_toVal]
        unfold tableGrowSuccessors
        dsimp only
        rw [htable]
        dsimp only
        rw [hgrow]
        dsimp only
        rw [hset, ← hsz, addressLiteralOfNat?_val]
        exact List.mem_cons_self)

theorem memoryGrowSucceed_mem_directSuccessors {z z' : State}
    {att : AddrType} {n sz : AddrLit att} {x : MemIdx}
    {mi mi' : MemInst} (hmemory : z.memOf x = some mi)
    (hgrow : growMem mi n.val = some mi')
    (hset : z.withMemInst x mi' = some z')
    (hsz : sz.val = mi.bytes.length / (64 * Ki)) :
    ((.memoryGrowSucceed x n.val (mi.bytes.length / (64 * Ki))
        (mi'.bytes.length / (64 * Ki))), (z', [constAddr att sz])) ∈
      directSuccessors (z, [constAddr att n, .plain (.memoryGrow x)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [(AddressLiteral.mk att n).toVal])
      (instruction := .memoryGrow x) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold memoryGrowSuccessors
        dsimp only
        rw [hmemory]
        dsimp only
        rw [hgrow]
        dsimp only
        rw [hset, ← hsz, addressLiteralOfNat?_val]
        exact List.mem_cons_self)

/-- A successful memory splice exposes the same memory and in-bounds window
used by the executable store selector. -/
theorem withMem_eq_some_memOf_and_bound {z z' : State} {x : MemIdx}
    {i j : Nat} {bs : List Byte} (hwrite : z.withMem x i j bs = some z') :
    ∃ mi, z.memOf x = some mi ∧ i + j ≤ mi.bytes.length := by
  unfold State.withMem at hwrite
  cases ha : z.frame.mod.mems[x.val]? with
  | none => simp [ha] at hwrite
  | some a =>
      cases hmemory : z.store.mems[a]? with
      | none => simp [ha, hmemory] at hwrite
      | some memory =>
          by_cases hbound : i + j ≤ memory.bytes.length
          · exact ⟨memory, by simp [State.memOf, ha, hmemory], hbound⟩
          · simp [ha, hmemory, spliceAt?, hbound] at hwrite

theorem storeNumOob_mem_directSuccessors {z : State}
    {att : AddrType} {i : AddrLit att} {nt : NumType} {c : Num_ nt}
    {x : MemIdx} {ao : MemArg} {mi : MemInst}
    (hmemory : z.memOf x = some mi)
    (hoob : i.val + ao.offset.val + nt.size / 8 > mi.bytes.length) :
    ((.storeNumOob x (nt.size / 8)), (z, [.trap])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.const nt c),
        .plain (.store nt none x ao)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .num ⟨nt, c⟩])
      (instruction := .store nt none x ao) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold storeNumSuccessors
        simp only [valNum_num]
        rw [hmemory]
        dsimp only
        rw [if_pos hoob]
        exact List.mem_cons_self)

theorem storeNumVal_mem_directSuccessors {z z' : State}
    {att : AddrType} {i : AddrLit att} {nt : NumType} {c : Num_ nt}
    {x : MemIdx} {ao : MemArg} {bs : List Byte}
    (hbs : bs = releasedNumerics.nbytes_ nt c)
    (hwrite : z.withMem x (i.val + ao.offset.val) (nt.size / 8) bs = some z') :
    ((.storeNumVal x (nt.size / 8)), (z', [])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.const nt c),
        .plain (.store nt none x ao)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .num ⟨nt, c⟩])
      (instruction := .store nt none x ao) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold storeNumSuccessors
        simp only [valNum_num]
        obtain ⟨memory, hmemory, hbound⟩ :=
          withMem_eq_some_memOf_and_bound hwrite
        rw [hmemory]
        dsimp only
        rw [if_neg (Nat.not_lt_of_ge hbound)]
        rw [mem_stateWrite?_iff]
        exact ⟨rfl, rfl, by simpa [hbs] using hwrite⟩)

theorem storePackOob_mem_directSuccessors {z : State}
    {att : AddrType} {i : AddrLit att} {inn : Inn} {c : InnLit inn}
    {sz : Sz} {x : MemIdx} {ao : MemArg} {mi : MemInst}
    (hmemory : z.memOf x = some mi)
    (hoob : i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length) :
    ((.storePackOob x (sz.toNat / 8)), (z, [.trap])) ∈ directSuccessors
      (z, [constAddr att i, constInn inn c,
        .plain (.store inn.toNumType (some ⟨sz⟩) x ao)]) := by
  cases inn with
  | i32 =>
      simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, constInn,
        innLitToNum] using
        mem_directSuccessors_of_mem_directSuccessorsOf
          (z := z)
          (vs := [(AddressLiteral.mk att i).toVal, .num ⟨.i32, c⟩])
          (instruction := .store .i32 (some ⟨sz⟩) x ao) rfl
          (by
            simp only [directSuccessorsOf, addressLiteral?_toVal]
            unfold storePackI32Successors
            simp only [valNum_num]
            rw [hmemory]
            dsimp only
            rw [if_pos hoob]
            exact List.mem_cons_self)
  | i64 =>
      simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, constInn,
        innLitToNum] using
        mem_directSuccessors_of_mem_directSuccessorsOf
          (z := z)
          (vs := [(AddressLiteral.mk att i).toVal, .num ⟨.i64, c⟩])
          (instruction := .store .i64 (some ⟨sz⟩) x ao) rfl
          (by
            simp only [directSuccessorsOf, addressLiteral?_toVal]
            unfold storePackI64Successors
            simp only [valNum_num]
            rw [hmemory]
            dsimp only
            rw [if_pos hoob]
            exact List.mem_cons_self)

theorem storePackVal_mem_directSuccessors {z z' : State}
    {att : AddrType} {i : AddrLit att} {inn : Inn} {c : InnLit inn}
    {sz : Sz} {x : MemIdx} {ao : MemArg} {bs : List Byte}
    (hbs : bs = releasedNumerics.ibytes_ sz.toNat
      (releasedNumerics.wrap__ inn.size sz.toNat c))
    (hwrite : z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z') :
    ((.storePackVal x (sz.toNat / 8)), (z', [])) ∈ directSuccessors
      (z, [constAddr att i, constInn inn c,
        .plain (.store inn.toNumType (some ⟨sz⟩) x ao)]) := by
  cases inn with
  | i32 =>
      simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, constInn,
        innLitToNum] using
        mem_directSuccessors_of_mem_directSuccessorsOf
          (z := z)
          (vs := [(AddressLiteral.mk att i).toVal, .num ⟨.i32, c⟩])
          (instruction := .store .i32 (some ⟨sz⟩) x ao) rfl
          (by
            simp only [directSuccessorsOf, addressLiteral?_toVal]
            unfold storePackI32Successors
            simp only [valNum_num]
            obtain ⟨memory, hmemory, hbound⟩ :=
              withMem_eq_some_memOf_and_bound hwrite
            rw [hmemory]
            dsimp only
            rw [if_neg (Nat.not_lt_of_ge hbound)]
            rw [mem_stateWrite?_iff]
            exact ⟨rfl, rfl, by simpa [hbs] using hwrite⟩)
  | i64 =>
      simpa [AddressLiteral.toAdmin, AddressLiteral.toVal, constInn,
        innLitToNum] using
        mem_directSuccessors_of_mem_directSuccessorsOf
          (z := z)
          (vs := [(AddressLiteral.mk att i).toVal, .num ⟨.i64, c⟩])
          (instruction := .store .i64 (some ⟨sz⟩) x ao) rfl
          (by
            simp only [directSuccessorsOf, addressLiteral?_toVal]
            unfold storePackI64Successors
            simp only [valNum_num]
            obtain ⟨memory, hmemory, hbound⟩ :=
              withMem_eq_some_memOf_and_bound hwrite
            rw [hmemory]
            dsimp only
            rw [if_neg (Nat.not_lt_of_ge hbound)]
            rw [mem_stateWrite?_iff]
            exact ⟨rfl, rfl, by simpa [hbs] using hwrite⟩)

theorem vstoreOob_mem_directSuccessors {z : State}
    {att : AddrType} {i : AddrLit att} {c : V128Lit}
    {x : MemIdx} {ao : MemArg} {mi : MemInst}
    (hmemory : z.memOf x = some mi)
    (hoob : i.val + ao.offset.val + VecType.v128.size / 8 > mi.bytes.length) :
    ((.vstoreOob x (VecType.v128.size / 8)), (z, [.trap])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.vconst .v128 c),
        .plain (.vstore .v128 x ao)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .vec ⟨.v128, c⟩])
      (instruction := .vstore .v128 x ao) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold vstoreSuccessors
        simp only [v128Value?]
        rw [hmemory]
        dsimp only
        rw [if_pos hoob]
        exact List.mem_cons_self)

theorem vstoreVal_mem_directSuccessors {z z' : State}
    {att : AddrType} {i : AddrLit att} {c : V128Lit}
    {x : MemIdx} {ao : MemArg} {bs : List Byte}
    (hbs : bs = releasedNumerics.vbytes_ .v128 c)
    (hwrite : z.withMem x (i.val + ao.offset.val)
      (VecType.v128.size / 8) bs = some z') :
    ((.vstoreVal x (VecType.v128.size / 8)), (z', [])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.vconst .v128 c),
        .plain (.vstore .v128 x ao)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .vec ⟨.v128, c⟩])
      (instruction := .vstore .v128 x ao) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold vstoreSuccessors
        simp only [v128Value?]
        obtain ⟨memory, hmemory, hbound⟩ :=
          withMem_eq_some_memOf_and_bound hwrite
        rw [hmemory]
        dsimp only
        rw [if_neg (Nat.not_lt_of_ge hbound)]
        rw [mem_stateWrite?_iff]
        exact ⟨rfl, rfl, by simpa [hbs] using hwrite⟩)

theorem vstoreLaneOob_mem_directSuccessors {z : State}
    {att : AddrType} {i : AddrLit att} {c : V128Lit} {sz : Sz}
    {x : MemIdx} {ao : MemArg} {j : LaneIdx} {mi : MemInst}
    (hmemory : z.memOf x = some mi)
    (hoob : i.val + ao.offset.val + sz.toNat > mi.bytes.length) :
    ((.vstoreLaneOob x (sz.toNat / 8)), (z, [.trap])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.vconst .v128 c),
        .plain (.vstoreLane .v128 sz x ao j)]) := by
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .vec ⟨.v128, c⟩])
      (instruction := .vstoreLane .v128 sz x ao j) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold vstoreLaneSuccessors
        simp only [v128Value?]
        rw [hmemory]
        dsimp only
        rw [if_pos hoob]
        exact List.mem_append_left _ List.mem_cons_self)

/-- A successful authority lane-store rule is retained even when the pinned
out-of-bounds rule also applies.  The authority compares `sz` in the trap
premise but writes `sz / 8` bytes in the value premise, so those outcomes are
not exclusive and the enumerator appends them independently. -/
theorem vstoreLaneVal_mem_directSuccessors {z z' : State}
    {att : AddrType} {i : AddrLit att} {c : V128Lit} {sz : Sz}
    {x : MemIdx} {ao : MemArg} {j : LaneIdx} {sh : Shape}
    {lv : Lane_ sh.lane} {k : IN sh.lane.size} {bs : List Byte}
    (hsize : sh.lane.size = sz.toNat)
    (hdim : sh.dim.toNat = 128 / sz.toNat)
    (hlane : (releasedNumerics.lanes_ sh c)[j.val]? = some lv)
    (hbits : laneToIN sh.lane lv = some k)
    (hbs : bs = releasedNumerics.ibytes_ sh.lane.size k)
    (hwrite : z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z') :
    ((.vstoreLaneVal x (sz.toNat / 8)), (z', [])) ∈ directSuccessors
      (z, [constAddr att i, .plain (.vconst .v128 c),
        .plain (.vstoreLane .v128 sz x ao j)]) := by
  have hshape := shape_eq_storeLaneShape_of_laneToIN hsize hdim hbits
  subst sh
  simpa [AddressLiteral.toAdmin, AddressLiteral.toVal] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z)
      (vs := [(AddressLiteral.mk att i).toVal, .vec ⟨.v128, c⟩])
      (instruction := .vstoreLane .v128 sz x ao j) rfl
      (by
        simp only [directSuccessorsOf, addressLiteral?_toVal]
        unfold vstoreLaneSuccessors
        simp only [v128Value?]
        obtain ⟨memory, hmemory, hbound⟩ :=
          withMem_eq_some_memOf_and_bound hwrite
        rw [hmemory]
        dsimp only
        rw [hlane]
        dsimp only
        rw [hbits]
        simp only [List.mem_append]
        right
        rw [mem_stateWrite?_iff]
        exact ⟨rfl, rfl, by simpa [hbs] using hwrite⟩)

theorem structNew_mem_directSuccessors {z : State} {vs : List Val}
    {x : TypeIdx} {dt : DefType} {fts : FieldTypes} {n : Nat}
    {a : StructAddr} {fvs : List FieldVal} {si : StructInst}
    (htype : z.typeOf x = some dt) (hexpand : Expand dt (.struct fts))
    (hfts : fts.toList.length = n) (hvs : vs.length = n)
    (ha : a = z.structinst.length)
    (hpack : (fts.toList.zip vs).mapM
      (fun p => releasedNumerics.packfield_ (fieldStorage p.1) p.2) = some fvs)
    (hsi : si = { type := dt, fields := fvs }) :
    ((.structNew x n),
      (z.addStructInst [si], [.addrref (.structAddr a)])) ∈
      directSuccessors (z, vals vs ++ [.plain (.structNew x)]) := by
  apply mem_directSuccessors_of_mem_directSuccessorsOf rfl
  rcases hexpand with ⟨hexpand⟩
  simp only [directSuccessorsOf, htype]
  rw [hexpand]
  simp only
  rw [if_pos (hfts.trans hvs.symm), hpack]
  subst a
  subst si
  simp [hvs]

theorem structSetNull_mem_directSuccessors {z : State} {ht : HeapType}
    {v : Val} {x : TypeIdx} {i : U32} :
    ((.structSetNull x i), (z, [.trap])) ∈ directSuccessors
      (z, [Ref.toAdmin (.null ht), v.toAdmin, .plain (.structSet x i)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := [.ref (.null ht), v]) (instruction := .structSet x i) rfl
    (by simp [directSuccessorsOf])

theorem structSetStruct_mem_directSuccessors {z z' : State}
    {a : StructAddr} {v : Val} {x : TypeIdx} {i : U32} {dt : DefType}
    {fts : FieldTypes} {ft : FieldType} {fv : FieldVal}
    (htype : z.typeOf x = some dt) (hexpand : Expand dt (.struct fts))
    (hfield : fts.toList[i.val]? = some ft)
    (hpack : releasedNumerics.packfield_ (fieldStorage ft) v = some fv)
    (hset : z.withStruct a i.val fv = some z') :
    ((.structSetStruct x i), (z', [])) ∈ directSuccessors
      (z, [.addrref (.structAddr a), v.toAdmin, .plain (.structSet x i)]) := by
  simpa [vals, Val.toAdmin] using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := [.ref (.addr (.structAddr a)), v])
      (instruction := .structSet x i) rfl (by
        rcases hexpand with ⟨hexpand⟩
        simp only [directSuccessorsOf, htype]
        rw [hexpand]
        simp only
        rw [hfield]
        simp only
        rw [hpack]
        simp [stateWrite?, hset])

theorem arrayNewFixed_mem_directSuccessors {z : State} {vs : List Val}
    {x : TypeIdx} {n : U32} {dt : DefType} {ft : FieldType}
    {a : ArrayAddr} {fvs : List FieldVal} {ai : ArrayInst}
    (htype : z.typeOf x = some dt) (hexpand : Expand dt (.array ft))
    (hlen : vs.length = n.val) (ha : a = z.arrayinst.length)
    (hpack : vs.mapM
      (fun v => releasedNumerics.packfield_ (fieldStorage ft) v) = some fvs)
    (hai : ai = { type := dt, fields := fvs }) :
    ((.arrayNewFixed x n.val),
      (z.addArrayInst [ai], [.addrref (.arrayAddr a)])) ∈
      directSuccessors (z, vals vs ++ [.plain (.arrayNewFixed x n)]) := by
  apply mem_directSuccessors_of_mem_directSuccessorsOf rfl
  rcases hexpand with ⟨hexpand⟩
  simp only [directSuccessorsOf, hlen, ↓reduceIte, htype]
  rw [hexpand]
  simp only
  rw [show vs.mapM (releasedNumerics.packfield_ (fieldStorage ft)) = some fvs by
    simpa using hpack]
  subst a
  subst ai
  simp

theorem arraySetNull_mem_directSuccessors {z : State} {ht : HeapType}
    {i : U32} {v : Val} {x : TypeIdx} :
    ((.arraySetNull x), (z, [.trap])) ∈ directSuccessors
      (z, [Ref.toAdmin (.null ht), constI32 i, v.toAdmin,
        .plain (.arraySet x)]) := by
  simpa using mem_directSuccessors_of_mem_directSuccessorsOf
    (z := z) (vs := [.ref (.null ht), .num ⟨.i32, i⟩, v])
      (instruction := .arraySet x) rfl
      (by simp [directSuccessorsOf])

theorem withArray_eq_some_arrayinst_and_bound {z z' : State}
    {a : ArrayAddr} {i : Nat} {fv : FieldVal}
    (hset : z.withArray a i fv = some z') :
    ∃ ai, z.arrayinst[a]? = some ai ∧ i < ai.fields.length := by
  unfold State.withArray at hset
  cases harray : z.store.arrays[a]? with
  | none => simp [harray] at hset
  | some ai =>
      cases hfields : setAt? ai.fields i fv with
      | none => simp [harray, hfields] at hset
      | some fields =>
          refine ⟨ai, harray, ?_⟩
          unfold setAt? at hfields
          split at hfields
          · assumption
          · contradiction

theorem arraySetOob_mem_directSuccessors {z : State} {a : ArrayAddr}
    {i : U32} {v : Val} {x : TypeIdx} {ai : ArrayInst}
    (harray : z.arrayinst[a]? = some ai) (hoob : i.val ≥ ai.fields.length) :
    ((.arraySetOob x), (z, [.trap])) ∈ directSuccessors
      (z, [.addrref (.arrayAddr a), constI32 i, v.toAdmin,
        .plain (.arraySet x)]) := by
  simpa [vals, Val.toAdmin, constI32] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [.ref (.addr (.arrayAddr a)), .num ⟨.i32, i⟩, v])
      (instruction := .arraySet x) rfl
      (by simp [directSuccessorsOf, harray, hoob])

theorem arraySetArray_mem_directSuccessors {z z' : State}
    {a : ArrayAddr} {i : U32} {v : Val} {x : TypeIdx} {dt : DefType}
    {ft : FieldType} {fv : FieldVal}
    (htype : z.typeOf x = some dt) (hexpand : Expand dt (.array ft))
    (hpack : releasedNumerics.packfield_ (fieldStorage ft) v = some fv)
    (hset : z.withArray a i.val fv = some z') :
    ((.arraySetArray x), (z', [])) ∈ directSuccessors
      (z, [.addrref (.arrayAddr a), constI32 i, v.toAdmin,
        .plain (.arraySet x)]) := by
  obtain ⟨ai, harray, hin⟩ := withArray_eq_some_arrayinst_and_bound hset
  simpa [vals, Val.toAdmin, constI32] using
    mem_directSuccessors_of_mem_directSuccessorsOf
      (z := z) (vs := [.ref (.addr (.arrayAddr a)), .num ⟨.i32, i⟩, v])
      (instruction := .arraySet x) rfl (by
        rcases hexpand with ⟨hexpand⟩
        simp only [directSuccessorsOf, harray,
          if_neg (Nat.not_le_of_lt hin), htype]
        rw [hexpand]
        simp only
        rw [hpack]
        simp [stateWrite?, hset])

end WasmGemmGnaf.Wasm.Core.Exec
